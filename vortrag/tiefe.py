"""2.5D für die Dias (Wunsch des Nutzers 2026-10-31: „Bildeffekte wie in Dopewars“): Tiefenkarte mit Depth Anything V2
Small -> zwei weiche Masken (Mittelgrund, Vordergrund) und die Lage kleiner Lichtquellen (Lampen, Kerzen, Fenster) für
ein flackerndes Leuchten. Vorgehen wie Dopewars tools/depth_maps.py und tools/find_lamps.py.

Läuft dauerhaft neben dem Diashow-Server mit der Python-Umgebung von ComfyUI (torch + transformers) und rechnet auf
der CPU – die Grafikkarte gehört Bild, Text und Stimme. Je Zeile auf stdin ein Bildpfad, je Zeile auf stdout JSON:
  {"bild": pfad, "tiefe": true|false, "lampen": [{"x", "y", "r", "c"}]}
Masken: <bild>_mid.webp und <bild>_near.webp neben dem Bild.
"""
import json
import os
import sys
from collections import deque

os.environ.setdefault("HF_HUB_OFFLINE", "1")   # das Modell liegt im Cache (aus Dopewars) – nichts nachladen

import numpy as np
from PIL import Image, ImageFilter

BREITE = 320   # Masken dürfen grob sein, sie werden weich gezeichnet


def maske(tiefe, lo, hi, groesse):
    a = np.clip((tiefe - lo) / max(1e-6, hi - lo), 0, 1)   # weicher Übergang zwischen lo und hi
    m = Image.fromarray((a * 255).astype(np.uint8)).resize(groesse, Image.BILINEAR).filter(ImageFilter.GaussianBlur(2))
    weiss = Image.new("L", groesse, 255)
    return Image.merge("RGBA", (weiss, weiss, weiss, m))


def lampen(bild):
    """Kleine helle Punkte in dunkler Umgebung (Laternen, Kerzen, Neon) – höchstens 6, in Prozent des Bildes."""
    w = 160
    h = max(1, round(bild.height * w / bild.width))
    a = np.asarray(bild.resize((w, h)), dtype=np.float32)
    lum = a @ np.array([0.299, 0.587, 0.114], dtype=np.float32)
    if np.percentile(lum, 50) > 120:   # helle Tagbilder: dort sind Lampen keine Hingucker
        return []
    heiss = lum > max(225, np.percentile(lum, 99.3))
    gesehen = np.zeros_like(heiss)
    gefunden = []
    for y in range(h):
        for x in range(w):
            if not heiss[y, x] or gesehen[y, x]:
                continue
            q = deque([(y, x)])
            gesehen[y, x] = True
            pix = []
            while q:
                cy, cx = q.popleft()
                pix.append((cy, cx))
                for ny, nx in ((cy + 1, cx), (cy - 1, cx), (cy, cx + 1), (cy, cx - 1)):
                    if 0 <= ny < h and 0 <= nx < w and heiss[ny, nx] and not gesehen[ny, nx]:
                        gesehen[ny, nx] = True
                        q.append((ny, nx))
            n = len(pix)
            if n < 2 or n > w * h * 0.012:   # Einzelpixel oder große helle Fläche (Himmel, Fenster) – keine Lampe
                continue
            ys = np.array([p[0] for p in pix])
            xs = np.array([p[1] for p in pix])
            Y0, Y1 = max(0, ys.min() - 6), min(h, ys.max() + 7)
            X0, X1 = max(0, xs.min() - 6), min(w, xs.max() + 7)
            umfeld = lum[Y0:Y1, X0:X1].copy()
            umfeld[ys - Y0, xs - X0] = np.nan
            if np.nanmean(umfeld) > 0.55 * float(lum[ys, xs].mean()):   # helle Umgebung: eher Gesicht oder Himmel
                continue
            y0, y1 = max(0, ys.min() - 3), min(h, ys.max() + 4)
            x0, x1 = max(0, xs.min() - 3), min(w, xs.max() + 4)
            ring = a[y0:y1, x0:x1].reshape(-1, 3)
            farbe = ring[ring.mean(axis=1) > 90].mean(axis=0) if (ring.mean(axis=1) > 90).any() else ring.mean(axis=0)
            gefunden.append({"x": round(float(xs.mean()) / w * 100, 1), "y": round(float(ys.mean()) / h * 100, 1),
                             "r": round(max(3.0, (n ** 0.5) / w * 100 * 2.2), 1),
                             "c": "%d,%d,%d" % tuple(int(v) for v in np.clip(farbe * 1.15, 0, 255)), "n": n})
    gefunden.sort(key=lambda f: -f["n"])
    return [{k: v for k, v in f.items() if k != "n"} for f in gefunden[:6]]


def main():
    pipe = None
    try:
        from transformers import pipeline
        pipe = pipeline("depth-estimation", model="depth-anything/Depth-Anything-V2-Small-hf", device=-1)
    except Exception as exc:  # noqa: BLE001 – ohne Tiefenmodell gibt es nur die Lampen
        print(json.dumps({"fehler": f"Tiefenmodell: {type(exc).__name__}: {exc}"}), flush=True)
    print(json.dumps({"bereit": pipe is not None}), flush=True)
    for zeile in sys.stdin:
        pfad = zeile.strip()
        if not pfad:
            continue
        aus = {"bild": pfad, "tiefe": False, "lampen": []}
        try:
            bild = Image.open(pfad).convert("RGB")
            aus["lampen"] = lampen(bild)
            if pipe is not None:
                tiefe = np.asarray(pipe(bild)["depth"], dtype=np.float32)   # hell = nah
                tiefe = (tiefe - tiefe.min()) / max(1e-6, tiefe.max() - tiefe.min())
                groesse = (BREITE, round(BREITE * bild.height / bild.width))
                q_mitte, q_nah = np.quantile(tiefe, [0.45, 0.78])   # je Bild: mittlere und vordere Ebene
                stamm = os.path.splitext(pfad)[0]
                maske(tiefe, q_mitte - 0.06, q_mitte + 0.06, groesse).save(stamm + "_mid.webp", "WEBP", quality=70)
                maske(tiefe, q_nah - 0.05, q_nah + 0.05, groesse).save(stamm + "_near.webp", "WEBP", quality=70)
                aus["tiefe"] = True
        except Exception as exc:  # noqa: BLE001
            aus["fehler"] = f"{type(exc).__name__}: {exc}"
        print(json.dumps(aus), flush=True)


if __name__ == "__main__":
    main()
