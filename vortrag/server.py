"""Diavortrag – Server für die Diashow im Browser.

Wird vom LM-Studio-Plugin „diashow-vortrag“ automatisch im Hintergrund gestartet (kein eigener Start nötig) und liefert
die Seite http://127.0.0.1:8430 aus. Das Plugin startet ihn über WMI als eigenständigen Prozess (--hintergrund): LM Studio
beendet Plugins ~20 s nach jeder Chat-Aktivität samt Kindprozessen (Server-Protokoll 2026-10-20 20:23:18 – der Server
verschwand mitten in der Gliederung). Aufbau übernommen aus dem Projekt „Rollenspiel“: nur Python-Standardbibliothek,
Text von dem in LM Studio geladenen Sprachmodell, Bilder über ComfyUI (FLUX.2 [klein]), Stimme über den Qwen3-TTS-
Stimmdienst (tts_dienst.py in der qwen-tts-venv, Ersatz: Piper), Musik aus einem Ordner oder neu über ACE-Step.

Vorausschauend: Gliederung -> Text -> Bild -> Stimme laufen als Fließband in eigenen Threads und arbeiten immer
VORLAUF Dias vor dem Dia, das gerade gezeigt wird. Wird die Zeit knapp, wird das nächste Dia zum Fazit – so endet der
Vortrag zur eingestellten Länge, auch wenn die Grafikkarte einmal langsamer ist.

  GET  /                          Startseite + Projektor (web/index.html)
  GET  /api/status                Sprachmodell, ComfyUI, Stimme, Musik, Version, läuft ein Vortrag?
  POST /api/ende                  Server beenden, wenn kein Vortrag läuft (Plugin ersetzt so eine veraltete Version)
  POST /api/beenden               Programm beenden (Knopf auf der Startseite): Vorträge, Stimmdienst und Server
  POST /api/vortrag               {"thema", "minuten", "musik": "ordner"|"erzeugen"|"aus"} -> {"id"}
  GET  /api/vortrag/<id>?pos=N    Stand des Vortrags; pos = Dia, das der Browser gerade zeigt (0 = Titel)
  POST /api/vortrag/<id>/stopp    Vortrag vorzeitig beenden
  POST /api/vorwaermen            Stimmdienst schon laden (die Startseite ruft das beim Öffnen auf)
  GET  /dateien/<id>/<datei>      Bilder und Ton eines Vortrags
  GET  /api/musik, /musik/<datei> Musik aus dem Musikordner
  GET  /api/geraeusche, /ton/<datei>  Saal-Geräusche (Gemurmel, Diawechsel, Husten, Applaus …), nach Art sortiert
"""

import contextlib
import hashlib
import io
import itertools
import json
import os
import queue
import random
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
import uuid
import wave
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HIER = Path(__file__).resolve().parent
WEB_DIR = HIER / "web"
# Saal-Geräusche (Wunsch des Nutzers 2026-10-20): einmalig mit Woosh erzeugt, mehrere Varianten je Art
# (<art>_<nr>.flac), damit sich nichts hörbar wiederholt. Liegen im Ordner „sounds“ des Plugin-Projekts (der Nutzer
# legt dort auch eigene ab); das Plugin kopiert ihn neben diese Datei.
TON_DIR = HIER / "sounds"
PLUGINS = Path.home() / "LMStudioLocalPlugins"

PORT = int(os.environ.get("DIASHOW_PORT", "8430"))
DATEN_DIR = Path(os.environ.get("DIASHOW_DATEN", str(PLUGINS / "diashow-daten")))
VORTRAEGE_DIR = DATEN_DIR / "vortraege"
VORTRAEGE_DIR.mkdir(parents=True, exist_ok=True)
# Version = Prüfsumme von server.py + index.html; das Plugin rechnet dieselbe und ersetzt einen veralteten Server.
def _dateinamen(ordner: Path) -> str:   # wie musikNamen() im Plugin
    if not ordner.is_dir():
        return ""
    return "\n".join(sorted(p.name for p in ordner.iterdir() if p.suffix.lower() in (".mp3", ".wav", ".flac", ".ogg", ".m4a")))


VERSION = hashlib.sha1((HIER / "server.py").read_bytes() + (WEB_DIR / "index.html").read_bytes()
                       + (_dateinamen(HIER / "musik") + "|" + _dateinamen(HIER / "sounds")).encode()).hexdigest()[:12]
VORTRAEGE_BEHALTEN = 5   # ältere Vortragsordner (Bilder, Ton) werden beim Start eines neuen gelöscht
# Musik (Nutzer 2026-10-20): der Ordner „musik“ im Plugin-Projekt mit den selbst ausgewählten Stücken. Das Plugin kopiert
# ihn neben diese Datei in den Programmordner. Ohne ihn: ACE-Steps Ausgabeordner. DIASHOW_MUSIK überschreibt beides.
_EIGENE_MUSIK = HIER / "musik"
MUSIK_DIR = Path(os.environ.get("DIASHOW_MUSIK") or (
    _EIGENE_MUSIK if _EIGENE_MUSIK.is_dir() and any(_EIGENE_MUSIK.iterdir())
    else PLUGINS / "ACE-Step-1.5" / ".cache" / "acestep" / "tmp" / "api_audio"))
MUSIK_ENDUNGEN = {".mp3": "audio/mpeg", ".wav": "audio/wav", ".flac": "audio/flac", ".ogg": "audio/ogg",
                  ".m4a": "audio/mp4"}

COMFYUI_URL = os.environ.get("COMFYUI_URL", "http://127.0.0.1:8188")
COMFYUI_DIR = Path(os.environ.get("COMFYUI_DIR", str(PLUGINS / "ComfyUI")))
MODELS_DIR = COMFYUI_DIR / "models"
BILD_GROESSE = (1024, 1024)   # wie die Dias der alten Version (generate_image-Standard; Wunsch des Nutzers 2026-10-20)
# Sprites (Wunsch des Nutzers 2026-10-20): kleine freigestellte Figuren, die ab und zu über den Bildschirm wandern.
# Gemalt in 2:1 (FLUX braucht Fläche für Details), dann freigestellt und auf den Inhalt zugeschnitten – in
# Originalgröße, nicht mehr verkleinert (Wunsch des Nutzers 2026-10-31).
SPRITE_MAL_GROESSE = (512, 256)
SPRITE_BEWEGUNGEN = ("fliegen", "schweben", "laufen", "rollen", "fallen", "schwimmen")
# Keine animierten Figuren, sondern in ihrer Bewegung GEMALT (Wunsch des Nutzers 2026-10-20: „ein Vogel fliegt, ein
# Mensch geht, eine Rakete stößt Feuer aus – leblose Gegenstände bleiben, wie sie sind“).
SPRITE_POSE = {
    "fliegen": "shown in full flight moving to the right, dynamic flying pose (wings spread wide; engines or rockets "
               "with a bright fiery exhaust flame trailing behind)",
    "laufen": "shown in mid-stride moving to the right, dynamic walking or running pose (vehicles driving, wheels turning)",
    "schwimmen": "shown swimming to the right, body curved in a dynamic swimming motion",
    "schweben": "gently drifting",
    "rollen": "",
    "fallen": "",
}

LMS_URL = os.environ.get("LMS_URL", "http://127.0.0.1:1234")
LMS_EXE = Path.home() / ".lmstudio" / "bin" / "lms.exe"
LMS_STANDARD_MODELL = os.environ.get("DIASHOW_LLM", "qwen3.8-9b-distill")   # nur, wenn gar keins geladen ist
LMS_TOKEN_DATEI = Path(os.environ.get("LMS_TOKEN_DATEI", str(PLUGINS / "case_files" / "lmstudio_token.txt")))

STIMMDIENST_URL = "http://127.0.0.1:8431"
TTS_PYTHON = Path(os.environ.get("DIASHOW_TTS_PYTHON", str(PLUGINS / "qwen-tts" / "venv" / "Scripts" / "python.exe")))
PIPER_PYTHON = PLUGINS / "mcp-servers" / "venv" / "Scripts" / "python.exe"
PIPER_STIMME = PLUGINS / "Piper" / "voices" / "de_DE-thorsten-high.onnx"
SPRECHER = ("erzaehler1", "erzaehler2", "erzaehler3", "erzaehler4", "erzaehler5")   # vortrag/stimmen/<name>_referenz.wav
# Sprachen der App (Wunsch des Nutzers 2026-10-20): Code -> (Name für die Anweisungen ans Sprachmodell, Qwen3-TTS-Sprache).
# Nur Sprachen mit Leerzeichen zwischen den Wörtern – Wortzählung und Satztrennung brauchen das (kein Chinesisch,
# Japanisch, Koreanisch, obwohl Qwen3-TTS sie spricht). Die Ersatzstimme Piper kann nur Deutsch.
SPRACHEN = {"de": ("German", "German"), "en": ("English", "English"), "fr": ("French", "French"),
            "es": ("Spanish", "Spanish"), "it": ("Italian", "Italian"), "pt": ("Portuguese", "Portuguese"),
            "ru": ("Russian", "Russian")}
SCHLUSS_ERSATZ = {   # falls das Sprachmodell am Ende keinen Text mehr liefert
    "de": "Damit sind wir am Ende unserer Reise angekommen. Ich hoffe, Sie nehmen ein wenig Staunen mit nach Hause. "
          "Vielen Dank für Ihre Aufmerksamkeit.",
    "en": "And so we have reached the end of our journey. I hope you take a little wonder home with you. "
          "Thank you very much for your attention.",
    "fr": "Nous voici arrivés au terme de notre voyage. J'espère que vous emporterez un peu d'émerveillement avec vous. "
          "Merci beaucoup de votre attention.",
    "es": "Así llegamos al final de nuestro viaje. Espero que se lleven a casa un poco de asombro. "
          "Muchas gracias por su atención.",
    "it": "Siamo così arrivati alla fine del nostro viaggio. Spero che portiate a casa un po' di meraviglia. "
          "Grazie mille per l'attenzione.",
    "pt": "Assim chegamos ao fim da nossa viagem. Espero que levem para casa um pouco de encanto. "
          "Muito obrigado pela vossa atenção.",
    "ru": "Вот мы и подошли к концу нашего путешествия. Надеюсь, вы унесёте с собой немного удивления. "
          "Большое спасибо за внимание.",
}

ACESTEP_URL = os.environ.get("ACESTEP_API_URL", "http://127.0.0.1:8001")

VORLAUF = 4              # so viele Dias darf das Fließband dem gezeigten Dia voraus sein
START_DIAS_MAX = 6       # Obergrenze für den mit der Vortragslänge wachsenden Startpuffer (siehe Vortrag.start_dias)
START_DIAS = 3           # so viele Dias müssen mindestens fertig sein, bevor der Projektor anläuft (mit 2 musste er 2026-10-20
                         # mitten im Vortrag warten: Stimme bis zu 2x langsamer als Echtzeit, solange alles rechnet)
WOERTER = (38, 50)       # Sprechtext je Dia, ~20 s
DIA_SEKUNDEN = 24.0      # geschätzte Dauer eines Dias (Sprechen + Pause + Diawechsel) – für die Planung
DIA_ZUSATZ = 3.2         # Pause + Diawechsel zusätzlich zum Ton (wie im Browser)
TITEL_SEKUNDEN = 8.0
SCHLUSS_SEKUNDEN = 10.0
SATZ_PAUSE = 0.28        # Stille zwischen zwei Sätzen

KEIN_FENSTER = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def log(text: str):
    print(f"{time.strftime('%H:%M:%S')} {text}", flush=True)


class Abgebrochen(Exception):
    """Der Vortrag wurde beendet, während ein Auftrag noch auf die Grafikkarte wartete."""


class GpuAmpel:
    """Wer darf gerade auf die Grafikkarte – der dringendste zuerst (kleinste Zahl = Dia, das als nächstes gezeigt wird).

    Gemessen 2026-10-20 (je 5-Minuten-Vortrag):
    - alles gleichzeitig: Bild 20–45 s statt 3 s, Stimme bis 3,5x Echtzeit, der Projektor wartete bis zu 35 s;
    - alles nacheinander: Stimme wieder ~1x Echtzeit, aber ~40 s Rechnen je Dia bei ~28 s Zeigen;
    - Stimme+Bild gleichzeitig 15 s statt 25 s nacheinander, Bild+Text 8 s statt 17 s – das lohnt sich;
    - Stimme+Text dauerhaft gleichzeitig: Stimme 52–67 s je Dia statt ~25 s – das bremst.
    Regel daher: je Art ein Auftrag zur Zeit, und Stimme und Text (Sprachmodell) nie gleichzeitig; Bilder dürfen neben
    Stimme oder Text laufen. Wer dringender ist, geht vor – auch ein dringender Wartender wird nicht von weniger
    dringenden überholt, die mit ihm unverträglich sind. Jeder Faden setzt mit vorrang() seine Dringlichkeit; die
    Aufrufe holen sich mit frei(art) ihren Platz (die Stimme je Satz)."""

    UNVERTRAEGLICH = {"stimme": {"stimme", "text"}, "text": {"text", "stimme"}, "bild": {"bild"}}

    def __init__(self):
        self._cv = threading.Condition()
        self._aktiv: dict[str, int] = {"stimme": 0, "text": 0, "bild": 0}
        self._warte: list[tuple] = []   # (dringlichkeit, nr, art)
        self._nr = itertools.count()
        self._faden = threading.local()

    def vorrang(self, dringlichkeit: float, abbruch: threading.Event | None = None):
        self._faden.d, self._faden.abbruch = dringlichkeit, abbruch

    def _darf(self, eintrag: tuple) -> bool:
        gegen = self.UNVERTRAEGLICH[eintrag[2]]
        if any(self._aktiv[a] for a in gegen):
            return False
        return not any(w < eintrag and w[2] in gegen for w in self._warte)

    @contextlib.contextmanager
    def frei(self, art: str):
        abbruch = getattr(self._faden, "abbruch", None)
        eintrag = (getattr(self._faden, "d", 50.0), next(self._nr), art)
        with self._cv:
            self._warte.append(eintrag)
            while not self._darf(eintrag):
                if abbruch is not None and abbruch.is_set():
                    self._warte.remove(eintrag)
                    self._cv.notify_all()
                    raise Abgebrochen()
                self._cv.wait(0.5)
            self._warte.remove(eintrag)
            self._aktiv[art] += 1
        try:
            yield
        finally:
            with self._cv:
                self._aktiv[art] -= 1
                self._cv.notify_all()


GPU = GpuAmpel()


def _http_json(url: str, daten: dict | None = None, timeout: float = 15, kopf: dict | None = None):
    body = json.dumps(daten).encode() if daten is not None else None
    h = {"Content-Type": "application/json"} if body else {}
    req = urllib.request.Request(url, data=body, headers={**h, **(kopf or {})})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        roh = r.read()
    return json.loads(roh) if roh.strip() else {}   # ComfyUIs /queue und /interrupt antworten ohne Inhalt


def port_offen(url: str) -> bool:
    teile = urllib.parse.urlsplit(url)
    try:
        with socket.create_connection((teile.hostname, teile.port), timeout=1):
            return True
    except OSError:
        return False


# --- Bilder: ComfyUI mit FLUX.2 [klein] (wie im Rollenspiel) ------------------------------------------------------

def _dateien(*ordner: str) -> list[str]:
    namen = []
    for o in ordner:
        d = MODELS_DIR / o
        if d.is_dir():
            namen += [p.name for p in d.iterdir() if p.suffix in (".safetensors", ".gguf")]
    return namen


def modell_erkennen() -> dict:
    """FLUX.2 [klein] in ComfyUIs Modellordnern; die distillierte Variante (4 Schritte, CFG 1) wird bevorzugt, dazu die
    kleine fp4-Fassung des Text-Encoders (passt neben Sprachmodell und Stimme in den Grafikspeicher)."""
    unet = os.environ.get("COMFYUI_UNET")
    if not unet:
        klein = [n for n in _dateien("diffusion_models", "unet") if "klein" in n.lower()]
        distill = [n for n in klein if "base" not in n.lower()]
        unet = (distill or klein or ["flux-2-klein-base-4b.safetensors"])[0]
    distilliert = "base" not in unet.lower()
    passend = "qwen_3_8b" if "9b" in unet.lower() else "qwen_3_4b"
    clip = os.environ.get("COMFYUI_CLIP")
    if not clip:
        kandidaten = [n for n in _dateien("text_encoders", "clip") if n.lower().startswith(passend)]
        kandidaten.sort(key=lambda n: (0 if "fp4" in n.lower() else 1 if "fp8" in n.lower() else 2, n))
        clip = (kandidaten or [passend + ".safetensors"])[0]
    vae = os.environ.get("COMFYUI_VAE")
    if not vae:
        vae = ([n for n in _dateien("vae") if "flux2" in n.lower()] or ["flux2-vae.safetensors"])[0]
    return {"unet": unet, "clip": clip, "vae": vae, "schritte": 4 if distilliert else 20, "cfg": 1.0 if distilliert else 5.0}


MODELL = modell_erkennen()
_comfy_start = threading.Lock()


def comfy_bereit() -> bool:
    try:
        _http_json(f"{COMFYUI_URL}/system_stats", timeout=3)
        return True
    except Exception:  # noqa: BLE001
        return False


def comfy_sicherstellen(abbruch: threading.Event | None = None) -> bool:
    """ComfyUI läuft normalerweise schon (vom Bild-Plugin in LM Studio gestartet). Sonst selbst starten – der Nutzer
    soll keinen Server von Hand starten müssen."""
    if comfy_bereit():
        return True
    py = COMFYUI_DIR / "venv" / "Scripts" / "python.exe"
    with _comfy_start:
        if not port_offen(COMFYUI_URL) and py.is_file():
            log("ComfyUI läuft nicht – wird gestartet")
            subprocess.Popen([str(py), "main.py"], cwd=str(COMFYUI_DIR), stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL, creationflags=KEIN_FENSTER)
    ende = time.time() + 180
    while time.time() < ende and not (abbruch and abbruch.is_set()):
        if comfy_bereit():
            return True
        time.sleep(1)
    return False


REFERENZ_MEGAPIXEL = 0.4   # Referenzbilder klein halten: jedes verlängert die Rechenzeit des Dias
REFERENZ_PERSONEN = 3      # höchstens so viele Figuren bekommen ein Referenzbild (je ~10 s beim Aufwärmen)
REFERENZEN_JE_DIA = 2


def workflow_bauen(prompt: str, seed: int, groesse: tuple[int, int] = BILD_GROESSE,
                   referenzen: list[str] | None = None) -> dict:
    """FLUX.2 [klein]. referenzen = Dateinamen in ComfyUIs input-Ordner (Figuren-Referenzbilder, Wunsch des Nutzers
    2026-10-31): sie hängen per ReferenceLatent an der Bedingung, damit dieselbe Figur auf jedem Dia gleich aussieht."""
    b, h = groesse
    wf = {
        "1": {"class_type": "UNETLoader", "inputs": {"unet_name": MODELL["unet"], "weight_dtype": "default"}},
        "2": {"class_type": "CLIPLoader", "inputs": {"clip_name": MODELL["clip"], "type": "flux2", "device": "default"}},
        "3": {"class_type": "VAELoader", "inputs": {"vae_name": MODELL["vae"]}},
        "4": {"class_type": "CLIPTextEncode", "inputs": {"clip": ["2", 0], "text": prompt}},
        "5": {"class_type": "CLIPTextEncode", "inputs": {"clip": ["2", 0], "text": ""}},
        "6": {"class_type": "EmptyFlux2LatentImage", "inputs": {"width": b, "height": h, "batch_size": 1}},
        "7": {"class_type": "RandomNoise", "inputs": {"noise_seed": seed}},
        "8": {"class_type": "KSamplerSelect", "inputs": {"sampler_name": "euler"}},
        "9": {"class_type": "Flux2Scheduler", "inputs": {"steps": MODELL["schritte"], "width": b, "height": h}},
        "10": {"class_type": "CFGGuider", "inputs": {"model": ["1", 0], "positive": ["4", 0], "negative": ["5", 0],
                                                     "cfg": MODELL["cfg"]}},
        "11": {"class_type": "SamplerCustomAdvanced", "inputs": {
            "noise": ["7", 0], "guider": ["10", 0], "sampler": ["8", 0], "sigmas": ["9", 0], "latent_image": ["6", 0]}},
        "12": {"class_type": "VAEDecode", "inputs": {"samples": ["11", 0], "vae": ["3", 0]}},
        # eindeutiger Name: bei einem wiederholten, gleichen Auftrag liefert ComfyUI sonst sein zwischengespeichertes
        # Ergebnis, dessen Datei wir schon aufgeräumt haben (/view -> 404, gemessen 2026-10-20)
        "13": {"class_type": "SaveImage", "inputs": {"filename_prefix": f"diashow_{uuid.uuid4().hex[:8]}", "images": ["12", 0]}},
    }
    pos, neg = ["4", 0], ["5", 0]
    for i, name in enumerate(referenzen or []):
        n = 20 + i * 5
        wf[str(n)] = {"class_type": "LoadImage", "inputs": {"image": name}}
        wf[str(n + 1)] = {"class_type": "ImageScaleToTotalPixels", "inputs": {
            "image": [str(n), 0], "upscale_method": "lanczos", "megapixels": REFERENZ_MEGAPIXEL, "resolution_steps": 1}}
        wf[str(n + 2)] = {"class_type": "VAEEncode", "inputs": {"pixels": [str(n + 1), 0], "vae": ["3", 0]}}
        wf[str(n + 3)] = {"class_type": "ReferenceLatent", "inputs": {"conditioning": pos, "latent": [str(n + 2), 0]}}
        wf[str(n + 4)] = {"class_type": "ReferenceLatent", "inputs": {"conditioning": neg, "latent": [str(n + 2), 0]}}
        pos, neg = [str(n + 3), 0], [str(n + 4), 0]
    wf["10"]["inputs"]["positive"], wf["10"]["inputs"]["negative"] = pos, neg
    return wf


def comfy_hochladen(quelle: Path, name: str) -> str:
    """Bild in ComfyUIs input-Ordner legen (für LoadImage). -> Dateiname dort"""
    grenze = uuid.uuid4().hex
    body = (f"--{grenze}\r\nContent-Disposition: form-data; name=\"image\"; filename=\"{name}\"\r\n"
            f"Content-Type: image/png\r\n\r\n").encode() + quelle.read_bytes() + (
            f"\r\n--{grenze}\r\nContent-Disposition: form-data; name=\"overwrite\"\r\n\r\ntrue\r\n--{grenze}--\r\n").encode()
    req = urllib.request.Request(f"{COMFYUI_URL}/upload/image", data=body,
                                 headers={"Content-Type": f"multipart/form-data; boundary={grenze}"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read())["name"]


def bild_erzeugen(prompt: str, seed: int, ziel: Path, vortrag: "Vortrag", groesse: tuple[int, int] = BILD_GROESSE,
                  referenzen: list[str] | None = None) -> bool:
    """Schickt den Graphen an ComfyUI, wartet auf das Bild und legt es unter ziel ab. False bei Abbruch."""
    with GPU.frei("bild"):
        return _bild_erzeugen(prompt, seed, ziel, vortrag, groesse, referenzen)


def _bild_erzeugen(prompt: str, seed: int, ziel: Path, vortrag: "Vortrag", groesse: tuple[int, int],
                   referenzen: list[str] | None = None) -> bool:
    pid = _http_json(f"{COMFYUI_URL}/prompt", {"prompt": workflow_bauen(prompt, seed, groesse, referenzen),
                                               "client_id": vortrag.id})["prompt_id"]
    vortrag.comfy_ids.add(pid)
    try:
        ende = time.time() + 600
        while time.time() < ende:
            if vortrag.abbruch.is_set():
                return False
            time.sleep(0.3)
            eintrag = _http_json(f"{COMFYUI_URL}/history/{pid}").get(pid)
            if not eintrag:
                continue
            for typ, d in eintrag.get("status", {}).get("messages", []):
                if typ == "execution_error":
                    raise RuntimeError(f"ComfyUI-Fehler in Node {d.get('node_id')}: {d.get('exception_message')}")
            for ausgabe in eintrag.get("outputs", {}).values():
                for bild in ausgabe.get("images", []):
                    q = urllib.parse.urlencode({"filename": bild["filename"], "subfolder": bild.get("subfolder", ""),
                                                "type": bild.get("type", "output")})
                    with urllib.request.urlopen(f"{COMFYUI_URL}/view?{q}", timeout=30) as r:
                        ziel.write_bytes(r.read())
                    if bild.get("type", "output") == "output":   # ComfyUIs eigene Kopie wird nicht gebraucht
                        try:
                            (COMFYUI_DIR / "output" / bild.get("subfolder", "") / bild["filename"]).unlink(missing_ok=True)
                        except OSError:
                            pass
                    return True
        raise RuntimeError("Zeitüberschreitung – ComfyUI hat kein Bild geliefert.")
    finally:
        vortrag.comfy_ids.discard(pid)


_rembg = {"sitzung": None, "fehler": False}
_rembg_sperre = threading.Lock()


def _weiss_entfernen(bild):
    """Ersatz ohne rembg: den weißen Hintergrund vom Rand her transparent machen (Flutfüllung)."""
    from PIL import ImageDraw
    rgb = bild.convert("RGB")
    w, h = rgb.size
    marke = (255, 0, 254)
    for xy in ((0, 0), (w - 1, 0), (0, h - 1), (w - 1, h - 1), (w // 2, 0), (w // 2, h - 1)):
        if sum(rgb.getpixel(xy)) > 690:   # nur, wo wirklich Weiß ist
            ImageDraw.floodfill(rgb, xy, marke, thresh=40)
    alpha = rgb.point(lambda _: 255).convert("L")
    alpha.putdata([0 if p == marke else 255 for p in rgb.getdata()])
    frei = bild.convert("RGBA")
    frei.putalpha(alpha)
    return frei


def sprite_freistellen(quelle: Path, ziel: Path) -> bool:
    """Figur freistellen (rembg, sonst weißen Hintergrund entfernen) und auf den Inhalt zuschneiden. False, wenn
    nichts Brauchbares übrig bleibt oder Pillow fehlt."""
    try:
        from PIL import Image
    except ImportError:
        log("Figuren: Pillow fehlt in dieser Python-Umgebung")
        return False
    bild = Image.open(quelle).convert("RGBA")
    frei = None
    if not _rembg["fehler"]:
        try:
            with _rembg_sperre:
                from rembg import new_session, remove
                if _rembg["sitzung"] is None:
                    _rembg["sitzung"] = new_session("u2net")   # lädt beim allerersten Mal ~175 MB
                frei = remove(bild, session=_rembg["sitzung"])
        except Exception as exc:  # noqa: BLE001
            _rembg["fehler"] = True
            log(f"Figuren: rembg nicht nutzbar ({type(exc).__name__}: {exc}) – Ersatz: weißen Hintergrund entfernen")
    if frei is None:
        frei = _weiss_entfernen(bild)
    box = frei.getchannel("A").point(lambda a: 255 if a > 40 else 0).getbbox()
    if not box or (box[2] - box[0]) * (box[3] - box[1]) < 0.02 * bild.width * bild.height:
        return False
    # Originalgröße behalten (Wunsch des Nutzers 2026-10-31): nur auf den Inhalt zuschneiden, nicht verkleinern
    frei.crop(box).save(ziel)
    return True


def comfy_abbrechen(ids: set[str]):
    """Eigene, noch wartende Aufträge aus ComfyUIs Warteschlange nehmen und einen laufenden unterbrechen."""
    if not ids:
        return
    try:
        stand = _http_json(f"{COMFYUI_URL}/queue", timeout=3)
        laufend = {e[1] for e in stand.get("queue_running", [])}
        _http_json(f"{COMFYUI_URL}/queue", {"delete": list(ids)}, timeout=3)
        if laufend & ids:
            _http_json(f"{COMFYUI_URL}/interrupt", {}, timeout=3)
    except Exception as exc:  # noqa: BLE001
        log(f"ComfyUI-Abbruch: {exc}")


# --- Text: das in LM Studio geladene Sprachmodell (wie im Rollenspiel) --------------------------------------------

def _lms(pfad: str, daten: dict | None = None, timeout: float = 120):
    kopf = {}
    try:
        kopf["Authorization"] = "Bearer " + LMS_TOKEN_DATEI.read_text(encoding="utf-8-sig").strip().splitlines()[0].strip()
    except (OSError, IndexError):
        pass
    return _http_json(f"{LMS_URL}{pfad}", daten, timeout, kopf)


def lms_modell() -> str | None:
    """Das gerade geladene Sprachmodell – es wird nie gewechselt."""
    try:
        for m in _lms("/api/v0/models", timeout=5)["data"]:
            if m.get("state") == "loaded" and m.get("type") in ("llm", "vlm"):
                return m["id"]
    except Exception:  # noqa: BLE001
        pass
    return None


def lms_sicherstellen() -> str | None:
    """LM-Studio-Server an und ein Sprachmodell geladen? Ist gar keins geladen, wird das Standardmodell geladen
    (wie start.bat im Rollenspiel) – ein schon geladenes Modell wird nie ersetzt."""
    modell = lms_modell()
    if modell or not LMS_EXE.is_file():
        return modell
    if not port_offen(LMS_URL):
        subprocess.run([str(LMS_EXE), "server", "start"], capture_output=True, timeout=60, creationflags=KEIN_FENSTER)
        modell = lms_modell()
        if modell:
            return modell
    log(f"kein Sprachmodell geladen – lade {LMS_STANDARD_MODELL}")
    subprocess.run([str(LMS_EXE), "load", LMS_STANDARD_MODELL, "-c", "16384", "--parallel", "1", "-y"],
                   capture_output=True, timeout=300, creationflags=KEIN_FENSTER)
    return lms_modell()


def qwen_json(system: str, nutzer: str, felder: dict, temperatur: float = 0.8, max_tokens: int = 1500,
              timeout: float = 60) -> dict:
    """Fragt das geladene Modell und erzwingt ein JSON mit genau diesen Feldern ({name: json-schema-typ})."""
    modell = lms_modell()
    if not modell:
        raise RuntimeError("In LM Studio ist kein Sprachmodell geladen (oder LM Studio ist nicht erreichbar).")
    schema = {"type": "object", "properties": felder, "required": list(felder)}
    anfrage = {
        "model": modell,
        "messages": [{"role": "system", "content": system}, {"role": "user", "content": nutzer}],
        # Ohne Nachdenken: sonst verbraucht das Modell alle Tokens im Denkteil (in LM Studio wirkt nur reasoning_effort).
        "reasoning_effort": "none",
        "temperature": temperatur, "max_tokens": max_tokens,
        "response_format": {"type": "json_schema", "json_schema": {"name": "antwort", "strict": True, "schema": schema}},
    }
    with GPU.frei("text"):
        # Zeitgrenze je Aufruf: LM Studio lief 2026-10-20 einmal mit 1 Token/s statt 77 (3 Minuten Stillstand, die
        # Stimme wartete mit) – lieber abbrechen und neu fragen, die nächste Anfrage war sofort wieder schnell.
        text = _lms("/v1/chat/completions", anfrage, timeout=timeout)["choices"][0]["message"]["content"]
    text = text.split("</think>")[-1].strip()
    if "{" not in text or "}" not in text:
        raise RuntimeError("Das Sprachmodell hat keine vollständige Antwort geliefert.")
    return json.loads(text[text.index("{"): text.rindex("}") + 1])


TEXT = {"type": "string"}

# Art des Vortrags (Wunsch des Nutzers 2026-10-31): Wissensvermittlung oder erzählte Geschichte – die KI entscheidet am
# Anfang, und für beide gibt es eine Richtschnur (Phasen), an der sich Gliederung, jedes Dia und der Lektor ausrichten.
ART_SYSTEM = """You decide what kind of illustrated slide talk fits a topic. Answer only with JSON:
- "art": "geschichte" if the audience wants a STORY to be told: a fairy tale, an adventure, a fable, a made-up tale
  about characters ("a dragon who is afraid of fire", "erzähl eine Geschichte über …", "a bedtime story", "a mystery in
  a castle"); "wissen" if the talk should EXPLAIN or inform about a real subject: history, science, nature, places,
  people, technology, how things work. Careful: "the history of coffee" or "die Geschichte des Fußballs" is KNOWLEDGE
  (history), not a story. Biographies and real events are knowledge."""

# Richtschnur je Art: Phase -> Aufgabe des Dias (englisch – Anweisung ans Modell). Reihenfolge = Ablauf des Vortrags;
# die ersten zwei Einträge nach dem Anfang und der vor dem Höhepunkt werden je nach Länge mehrfach belegt.
PHASEN = {
    "geschichte": {
        "anfang": "OPENING – a hook: drop the audience into the world of the story, its place and mood; introduce the "
                  "main character in a memorable first scene.",
        "einleitung": "INTRODUCTION – who the main character is, what they want or need, and what sets the story in "
                      "motion.",
        "mittelteil": "MIDDLE – the journey: attempts, encounters, obstacles; each slide raises the stakes a little. "
                      "Plant a small, subtle clue that will make sense after the twist – without revealing it.",
        "spannung": "RISING TENSION – things get difficult and uncertain, the conflict comes to a head, the audience "
                    "fears for the hero.",
        "hoehepunkt": "CLIMAX – the decisive moment of the whole story: vivid, pictorial language, strong sentences, the "
                      "audience holds its breath.",
        "twist": "TWIST – the surprising turn: something is different from what everyone believed; it makes sense in "
                 "hindsight because of the clue planted earlier.",
        "happy_end": "HAPPY END – the conflict is resolved, the characters find what they needed; end warm and hopeful "
                     "with a gentle thought for the audience. The last sentence thanks the audience.",
    },
    "wissen": {
        "einstieg": "HOOK – an astonishing question, scene or fact that makes the audience curious; introduce the topic.",
        "grundlagen": "BASICS – what you need to know: origins, how it works, the main people or places; clear and "
                      "vivid.",
        "vertiefung": "DEEPER – lesser-known details, connections and stories; each slide a little more surprising than "
                      "the one before.",
        "spannung": "TENSION – a problem, a race, a mystery or a danger: what was at stake, what was uncertain.",
        "hoehepunkt": "CLIMAX – the most fascinating, astonishing or moving aspect of the whole topic: vivid language, "
                      "wonder. The audience should remember this.",
        "wendung": "SURPRISING TURN – an unexpected fact, connection or change of perspective that shows the topic in a "
                   "new light (true and well known, not invented).",
        "fazit": "CONCLUSION – sum up in one sentence and end warmly, positively and hopefully with a thought connected "
                 "to the audience's own lives, so they leave with a good feeling. The last sentence thanks the audience.",
    },
}


PHASEN_NAMEN = {w.split(" –")[0].strip().lower() for t in PHASEN.values() for w in t.values()} | {
    "höhepunkt", "twist", "happy end", "wendung", "fazit", "spannung", "einleitung", "anfang", "mittelteil", "einstieg",
    "climax", "happy ending", "conclusion", "aftermath", "build-up"}


def ueberschrift_aus(kap: str) -> str:
    """Überschrift eines Gliederungspunkts („Überschrift: worum es geht“). Hat das Modell den Phasennamen als
    Überschrift genommen (gemessen 2026-10-31: „Climax“), stattdessen den Anfang der Beschreibung."""
    kopf, _, rest = kap.partition(":")
    kopf = re.sub(r"^\[[^\]]*\]\s*", "", kopf).strip()
    if kopf.lower() in PHASEN_NAMEN and rest.strip():
        woerter = rest.strip().rstrip(".").split()
        return " ".join(woerter[:6]) + (" …" if len(woerter) > 6 else "")
    return kopf


def phasen_verteilen(art: str, n: int) -> list[str]:
    """Phase je Dia: Anfang, Höhepunkt, Wendung/Twist und Schluss je einmal, die übrigen Dias auf Einleitung,
    Mittelteil und Spannung (Gewicht 1 : 2 : 1,5) – der Mittelteil trägt die Geschichte."""
    erste, a, b, c, hp, tw, letzte = PHASEN[art]
    if n < 4:   # sehr kurze Gliederung: Anfang, Höhepunkt, Schluss
        return [erste, hp, letzte][-n:] if n > 1 else [letzte]
    rest = n - 4
    if rest == 0:
        mitte = []
    elif rest == 1:
        mitte = [c]
    elif rest == 2:
        mitte = [a, c]
    else:
        anz, gewicht = {a: 1, b: 1, c: 1}, {a: 1.0, b: 2.0, c: 1.5}
        for _ in range(rest - 3):
            p = min(anz, key=lambda x: anz[x] / gewicht[x])
            anz[p] += 1
        mitte = [a] * anz[a] + [b] * anz[b] + [c] * anz[c]
    return [erste] + mitte + [hp, tw, letzte]


# Bildstil (Wunsch des Nutzers 2026-10-31): auf der Startseite gewählt; die KI ergänzt nur Licht, Farben und Stimmung.
BILDSTILE = {
    "foto": "photorealistic photograph, realistic textures, natural light, high detail",
    "aquarell": "watercolor painting, soft translucent washes of color, visible paper texture, delicate brush strokes",
    "anime": "anime illustration, cel shading, clean line art, vibrant colors, still from a Japanese animated film",
}

ART_TEXTE = {   # Platzhalter in GLIEDERUNG_SYSTEM je Art
    "geschichte": {
        "<ART>": "This talk TELLS A STORY: one coherent, entertaining and logical story with a clear main character, a "
                 "goal, obstacles, rising tension, a climax, a surprising twist and a happy end. Invent freely, but "
                 "everything must fit together.",
        "<HANDLUNG>": "the whole plot from beginning to end, including the twist and the happy end – the story bible "
                      "from which every slide will be written.",
        "<PERSONEN>": "1-4 recurring characters of the story (the main character first)",
        "<TWIST>": "the surprising turn after the climax, which makes sense in hindsight, and the small clue planted "
                   "earlier that hints at it.",
        "<KAPITEL>": "Every slide moves the plot forward by cause and effect, the same characters and places recur, "
                     "nothing comes out of nowhere; the twist slide reveals the twist, the last slide is the happy end "
                     "that resolves the conflict.",
        "<ART_REGELN>": "Tell the story like a gifted storyteller: past tense, concrete scenes, feelings, sensory "
                        "details, a touch of humour or wonder – entertaining to listen to. Stay true to the story bible "
                        "and the story so far: same names, characters, places and objects; every event has a cause. "
                        "Reveal the twist ONLY on the twist slide (a subtle hint before is fine).",
        "<ART_PRUEFUNG>": "Story logic: names, characters, their looks, places and objects stay consistent with the "
                          "story bible and the earlier slides; every event has a cause; no new main character out of "
                          "nowhere; the twist is not revealed before its slide. Entertainment: concrete scenes, emotions, "
                          "a touch of humour or wonder.",
        "<ART_PRUEFUNG_G>": "- One coherent plot that matches the story bible: the same main character(s) throughout, "
                            "cause and effect from point to point, no loose ends, the happy end resolves the conflict.\n"
                            "- The twist point reveals the planned twist; an earlier point plants a small clue but does "
                            "not reveal it.",
    },
    "wissen": {
        "<ART>": "This talk CONVEYS KNOWLEDGE like a gripping documentary: true, well-known facts, told so that "
                 "curiosity and tension rise up to the most astonishing insight, followed by a surprising turn and a "
                 "warm conclusion.",
        "<HANDLUNG>": "the red thread: the central question the talk answers and the path from the hook to the "
                      "conclusion.",
        "<PERSONEN>": "0-4 people, animals or figures that appear on several slides (may be empty)",
        "<TWIST>": "a surprising fact, connection or change of perspective for the slide after the climax – true and "
                   "well known, not invented.",
        "<KAPITEL>": "Every slide a NEW aspect, no repetition. Only use well-known facts; no invented names, dates or "
                     "inventions – if unsure, choose a more general aspect.",
        "<ART_REGELN>": "Informative, vivid and entertaining. Only state facts you are sure about: prefer well-known, "
                        "general knowledge; name people, years and numbers only if they are famous and you are certain "
                        "– otherwise describe without them. If the outline point itself sounds doubtful, tell what is "
                        "really known.",
        "<ART_PRUEFUNG>": "Doubtful facts: remove or soften claims that are probably wrong or invented (wrong inventors, "
                          "dates, places, made-up names or numbers). Keep only what is well known.",
        "<ART_PRUEFUNG_G>": "- Order: one clear, logical thread (e.g. chronological for history, from basics to details "
                            "for science) that follows the red thread of the story bible.\n"
                            "- Remove doubtful or invented facts (wrong inventors, dates, places, made-up names) – "
                            "replace such a point with a well-known aspect of the topic.",
    },
}

GLIEDERUNG_SYSTEM = """You plan an illustrated slide talk ("Diavortrag") for a <SPRACHE>-speaking audience, like a classic slide
show with a projector: each slide is ONE picture plus a few sentences that a narrator reads aloud. You get the topic
(in any language, it may also contain wishes about content or audience), the number of slides and the PHASE PLAN that
says which part of the arc each slide belongs to. <ART>
Answer only with JSON:
- "titel": <SPRACHE> title of the talk, max 7 words, catchy.
- "untertitel": <SPRACHE> subtitle, max 12 words.
- "handlung": <SPRACHE>, 4-7 sentences: <HANDLUNG>
- "personen": <PERSONEN>, each with "name" (<SPRACHE>), "rolle" (<SPRACHE>, who they are, max 10 words) and "aussehen"
  (English description for the image generator, 12-25 words: species or age, build, face, hair, clothing, typical
  colours – the picture of this character will always look exactly like this).
- "twist": <SPRACHE>, 1-2 sentences: <TWIST>
- "stimmung": English phrase, 6-15 words, ONLY light, colour palette and mood of all pictures, fitting the topic (e.g.
  "warm golden evening light, muted earthy colours, calm nostalgic mood"). The rendering style (photo, watercolour,
  anime …) is fixed elsewhere – name no medium or technique, and NEVER subjects, objects, places or motifs.
- "titel_prompt": English image prompt, 25-40 words: the opening picture of the talk, the essence of the topic, square
  composition. No text, no letters, no title.
- "schluss_prompt": English image prompt, 20-35 words: a warm, hopeful, beautiful closing picture that rounds off the
  topic and leaves a good feeling (e.g. golden light, an open horizon), square composition. No text, no letters.
- "musik": English description of fitting instrumental background music: genre, mood, instruments, tempo (max 25 words).
  Calm enough to talk over, warm and uplifting, no vocals.
- "sprecher": the narrator voice that fits the topic best, exactly one of: "erzaehler1" (old, wise storyteller – history,
  traditions, nature), "erzaehler2" (rich, resonant male baritone – epic, dramatic, big adventures, science, space),
  "erzaehler3" (clear, warm female alto, calm – culture, art, travel, everyday life, health, gentle topics),
  "erzaehler4" (dark, smoky male voice like film noir – crime, mysteries, dark history), "erzaehler5" (bright, friendly,
  lively – children, animals, food, hobbies, fun topics).
- "kapitel": list of EXACTLY the requested number of <SPRACHE> strings, one per slide in the order of the phase plan: a
  short heading (2-6 words) that names what happens – NEVER the phase name ("Climax", "Twist", "Happy End" …) –, a
  colon, and what happens or is explained on this slide (max 15 words). Each slide fulfils
  ITS phase of the plan. <KAPITEL> There is exactly ONE twist / surprising turn in the whole talk – on its own slide.
- "sprites": 2-4 small figures or objects that fit the topic and will now and then move across the screen during the
  talk as a playful decoration (e.g. a rocket that flies, autumn leaves that fall, a steam train that runs along the
  bottom, a fish that swims, a coffee bean that rolls). The FIRST figure is the main subject of the topic itself
  whenever it is a living being, vehicle or thing that can move (migratory birds -> a flying bird, railways -> a steam
  locomotive, whales -> a whale). Only concrete, visible things – never abstract ones (wind, time, ideas, sound). Each with:
  "name": German name (1-3 words);
  "prompt": English image prompt, 10-20 words, describing ONLY this single subject seen from the side, facing right,
  whole subject visible – no background, no scene, no text. Living or moving things are shown IN THEIR MOVEMENT (it
  will travel across the screen): a bird in flight with spread wings, a person in mid-stride, a horse galloping, a
  rocket with a fiery exhaust flame, a ship with full sails. Lifeless objects stay as they are;
  "bewegung": exactly one of "fliegen" (flies across), "schweben" (drifts slowly), "laufen" (walks/drives along the
  bottom), "rollen" (rolls along the bottom), "fallen" (falls from the top), "schwimmen" (swims in waves).
  The movement MUST be natural for the subject: rockets, planes, birds, insects fly ("fliegen"); planets, moons,
  balloons, clouds, satellites drift ("schweben"); people, animals on land, cars, trains walk/drive ("laufen"); balls,
  wheels, barrels roll ("rollen"); snowflakes, leaves, raindrops, petals, coins fall ("fallen"); fish, whales, boats
  swim ("schwimmen")."""

FOLIE_SYSTEM = """You write ONE slide of a <SPRACHE> slide talk. A narrator reads your text aloud while the slide's picture
is shown. Answer only with JSON:
- "text": <SPRACHE> narration for this slide, {wmin}-{wmax} words, 2-4 complete sentences in natural spoken <SPRACHE> made for
  listening: no lists, no headings, no abbreviations, no parentheses, no quotation marks. It continues smoothly from
  the previous slide without repeating it and fulfils this slide's PHASE. No greeting unless it is the first slide, no
  farewell unless it is the last slide. Never say "auf diesem Bild", "dieses Dia" or similar. <ART_REGELN>
- "prompt": English image prompt, 25-45 words, showing what this slide's text is about: concrete subject, setting,
  composition, light. Recurring characters look EXACTLY as described in the character list (copy their look: age,
  hair, clothing, colours). Follow the given camera direction. The picture must look clearly DIFFERENT from the previous
  slides' pictures (listed): another main subject, another place, another scale or perspective – a slide show where
  every picture shows the same thing is boring. The main object of the topic does NOT have to be in every picture:
  show the people, places, instruments, details, consequences or comparisons the text talks about. Square composition. No text, no letters, no captions, no logos, no
  charts, no maps."""

# Abwechslung in den Bildern (Nutzer 2026-10-20: „die Bilder sahen sich alle sehr ähnlich“ – beim Schwarzen Loch zeigten
# 11 Dias fast immer Raumschiff + Ereignishorizont aus gleichem Blickwinkel). Jedes Dia bekommt eine eigene Einstellung,
# in zufälliger Folge je Vortrag.
EINSTELLUNGEN = (
    "wide establishing shot of the whole setting",
    "close-up of one telling detail or object",
    "people in the scene, medium shot, faces and emotions visible",
    "bird's-eye view from high above",
    "low-angle shot looking up, monumental",
    "interior scene, looking into a room or vehicle",
    "portrait of a single person or creature",
    "quiet still life of objects that tell the story",
    "silhouettes against strong backlight",
    "a crowd or many figures at once",
    "macro view of textures and materials",
    "the setting at another time of day or in different weather",
    "over-the-shoulder view, seeing what a person sees",
)
EINSTELLUNG_ROLLE = {"hoehepunkt": "dramatic, cinematic wide shot of the key moment, strongest light and contrast",
                     "schluss": "calm, hopeful wide view with warm light and open space"}

# Lektor (Wunsch des Nutzers 2026-10-20): das Sprachmodell ist schwach – jede Gliederung und jedes Dia wird in einem
# zweiten, nüchternen Durchgang gegengeprüft, damit der Vortrag nicht widersprüchlich oder unlogisch wirkt. Der Lektor
# sieht dabei ALLE bisher gesprochenen Dias, der Schreiber nur die letzten zwei.
LEKTOR_GLIEDERUNG_SYSTEM = """You are the careful editor of a <SPRACHE> slide talk. A weaker planner drafted the outline
(one line per slide, each with its phase from the phase plan). Check it and repair it if needed:
<ART_PRUEFUNG_G>
- No point repeats or overlaps another one; no contradictions between points; no point that only makes sense before
  a point that comes later. Every point fits the topic and the wishes in it.
- Every point fulfils its phase: tension rises up to the CLIMAX point, which really is the strongest moment; exactly
  ONE twist / surprising turn, on its own point right after the climax; the last point ends warm, positive and hopeful
  so the audience leaves with a good feeling.
Keep EXACTLY the same number of points, the same order of phases and the same form ("Heading: what the slide tells")
– without the phase labels.
Answer only with JSON:
- "probleme": list of short German notes on what you changed and why (empty list if everything was fine).
- "kapitel": the final list of points."""

# Effekte über dem Dia (Wunsch des Nutzers 2026-10-31: „alles, was eine Diashow zusätzlich unterhaltsam macht“ –
# Sprühregen, Glitzer, Feuer, Rauch, Konfetti …); gezeichnet in web/index.html (fxTeile/fxSchritt).
EFFEKTE = ("keiner", "schnee", "regen", "spruehregen", "gewitter", "sterne", "funken", "feuer", "rauch", "nebel",
           "blasen", "gluehwuermchen", "konfetti", "glitzer", "feuerwerk", "blaetter", "blueten", "sonnenstrahlen",
           "staub", "herzen")
EFFEKT_WORTSTAEMME = ("schnee", "winter", "eis", "frost", "regen", "niesel", "sturm", "gewitter", "blitz", "donner",
                      "flut", "weltall", "weltraum", "all", "sterne", "stern", "kosmos", "galax", "planet", "astronaut",
                      "nachthimmel", "krieg", "schlacht", "feuer", "flamm", "brand", "kamin", "lagerfeuer", "rauch",
                      "qualm", "dampf", "explos", "bomb", "vulkan", "lava", "schmied", "nebel", "dunst", "geist",
                      "meer", "ozean", "unterwasser", "tauch", "fisch", "glühwürm", "zauber", "magie", "märchen", "fee",
                      "schatz", "gold", "funkel", "glitzer", "feier", "fest", "jubel", "sieg", "hochzeit", "silvester",
                      "feuerwerk", "herbst", "blätter", "laub", "frühling", "blüte", "kirsch", "sonne", "morgen",
                      "wüste", "sand", "staub", "dachboden", "liebe", "herz", "verliebt", "snow", "rain", "storm",
                      "space", "star", "fire", "smoke", "magic", "gold", "party", "autumn", "leaves", "blossom",
                      "love", "dust", "sun")

# Die Atmosphäre entscheidet der Lektor gleich mit (ein Modellaufruf weniger je Dia – gemessen 2026-10-20: mit drei
# Aufrufen je Dia brauchte die Stimme bis zu 87 s für 24 s Ton). ATMOSPHAERE_SYSTEM nur, wenn der Lektor ausfällt.
ATMOSPHAERE_FELDER = """- "effekt": the visual atmosphere the browser draws over the slide, exactly one of: "schnee" (snow, winter, ice,
  cold), "regen" (heavy rain, flood, bad weather), "spruehregen" (drizzle, fine spray, sea spray, waterfall mist, a
  grey wet day), "gewitter" (thunderstorm with lightning, storm at night, dramatic danger), "sterne" (night sky, space,
  universe, planets, astronauts), "funken" (war, battle, explosions, forge, industry furnace), "feuer" (flames, a
  campfire, a burning house, a fireplace, dragons breathing fire, volcano), "rauch" (smoke, steam engines, chimneys,
  battlefield smoke, ruins, incense), "nebel" (fog, mist, mystery, ghosts, swamp, early morning), "blasen" (under water,
  sea, diving, fish), "gluehwuermchen" (summer night, forest at dusk, fairy tale), "konfetti" (celebration, party,
  wedding, carnival), "glitzer" (magic, a spell, treasure, gold, jewels, wishes coming true, a wonderful surprise),
  "feuerwerk" (victory, New Year, a great triumph, a festival at night), "blaetter" (autumn, wind, forest, passing
  time), "blueten" (spring, cherry blossom, gardens, romance, new beginnings), "sonnenstrahlen" (sunrise, hope, a
  sacred or peaceful place, light breaking through clouds or a forest), "staub" (old attics, libraries, archaeology,
  desert, sunbeams in an old room), "herzen" (love, friendship, affection, a happy reunion) – or "keiner". Choose an
  effect if the narration talks about such a thing or the scene clearly is like that (a war or battle gets "funken",
  space gets "sterne", a happy end may get "konfetti", "glitzer" or "feuerwerk"); slides about ordinary things
  (people talking, planning, building, everyday life) get "keiner".
- "figur": the name of ONE of the talk's figures (list given) if it appears in or clearly fits what this slide tells
  (e.g. the figure "Rakete" when rockets fly, a bird when birds are mentioned), otherwise "".
  Words noticed in the text may be given as a hint – decide yourself whether they really describe the scene
  ("eisern" is not ice, a "Fest" can be a fortress)."""

ATMOSPHAERE_SYSTEM = ("You choose the visual atmosphere for ONE slide of a slide talk, based ONLY on what its "
                      "narration describes. Answer only with JSON:\n" + ATMOSPHAERE_FELDER)

LEKTOR_DIA_SYSTEM = """You are the careful editor of a <SPRACHE> slide talk. A weaker writer drafted the narration of ONE
slide. Check it against the outline, the story bible and EVERYTHING that was said on the earlier slides, and repair it
if needed:
1. Contradictions: nothing may contradict an earlier slide (dates, names, numbers, order of events, who did what).
2. Logic and flow: the slide must follow sensibly from the previous slide (time order, cause and effect) and cover its
   own outline point. No jumps that make the talk seem illogical, nothing told as new that was already explained.
3. Repetition: no sentence or fact that was already said on an earlier slide.
4. <ART_PRUEFUNG>
5. Form: {wmin}-{wmax} words, 2-4 complete sentences in natural spoken <SPRACHE> for listening, no lists, no parentheses, no
   quotation marks, never "auf diesem Bild" or "dieses Dia". Only the first slide may welcome the audience, only the
   last slide may thank them and say goodbye.
6. Phase (given with the slide): the slide must fulfil it – the climax is the most vivid moment, the twist / surprising
   turn appears ONLY on its own slide, the last slide ends warm, positive and hopeful so the audience leaves with a good
   feeling. Strengthen the draft where it misses its phase.
Change as little as necessary: if the draft is fine, return it unchanged.
Answer only with JSON:
- "probleme": list of short German notes on what was wrong (empty list if nothing).
- "text": the final narration.
- "prompt": the English image prompt – the draft's prompt unchanged, unless the subject of the text changed or it would
  look almost like one of the previous pictures (listed); then write one that shows something visibly different
  (another subject, place, scale or perspective) and keeps the given camera direction.
""" + ATMOSPHAERE_FELDER


# --- Stimme: Qwen3-TTS-Stimmdienst (Rollenspiel), Ersatz Piper -------------------------------------------------------

_dienst = {"prozess": None}
_dienst_sperre = threading.Lock()


def stimmdienst_status() -> str:
    try:
        st = _http_json(f"{STIMMDIENST_URL}/status", timeout=1)
        return "bereit" if st.get("bereit") else ("fehler" if st.get("fehler") else "lädt")
    except Exception:  # noqa: BLE001
        p = _dienst["prozess"]
        if p and p.poll() is None:
            return "lädt"
        return "aus" if TTS_PYTHON.is_file() else "fehlt"


def stimmdienst_starten():
    with _dienst_sperre:
        p = _dienst["prozess"]
        if port_offen(STIMMDIENST_URL) and stimmdienst_veraltet():
            stimmdienst_beenden()   # ein älterer Dienst kann nur Deutsch – ersetzen
        if (p and p.poll() is None) or port_offen(STIMMDIENST_URL) or not TTS_PYTHON.is_file():
            return
        log("Stimmdienst (Qwen3-TTS) wird gestartet")
        _dienst["prozess"] = subprocess.Popen(
            [str(TTS_PYTHON), str(HIER / "tts_dienst.py"), STIMMDIENST_URL.rsplit(":", 1)[1]], cwd=str(HIER),
            stdout=open(DATEN_DIR / "stimmdienst.log", "a", encoding="utf-8"), stderr=subprocess.STDOUT,
            creationflags=KEIN_FENSTER)


def stimmdienst_veraltet() -> bool:
    """Stimmdienst ohne Versionsangabe = vor der Sprachauswahl gestartet, spricht alles Deutsch."""
    try:
        return int(_http_json(f"{STIMMDIENST_URL}/status", timeout=2).get("version", 1)) < 2
    except Exception:  # noqa: BLE001
        return False


def stimmdienst_beenden(warten: float = 10):
    """Stimmdienst beenden (gibt ~5 GB Grafikspeicher frei) und warten, bis der Port frei ist."""
    try:
        _http_json(f"{STIMMDIENST_URL}/ende", {}, timeout=2)
    except Exception:  # noqa: BLE001
        pass
    ende = time.time() + warten
    while time.time() < ende and port_offen(STIMMDIENST_URL):
        time.sleep(0.3)
    _dienst["prozess"] = None


def _saetze(text: str) -> list[str]:
    teile = [s for s in re.split(r"(?<=[.!?…])\s+", text.strip()) if s]
    aus = []
    for s in teile:   # sehr kurze Sätze an den vorigen hängen – ein Aufruf weniger
        if aus and len(s.split()) < 4:
            aus[-1] += " " + s
        else:
            aus.append(s)
    return aus


def textlaenge_begrenzen(text: str, hoechstens: int = WOERTER[1] + 12) -> str:
    """Das Modell schreibt manchmal doppelt so viel wie verlangt (Dias mit 40 s statt 25 s) – ganze Sätze behalten,
    bis die Grenze erreicht ist."""
    if len(text.split()) <= hoechstens:
        return text
    aus = []
    for s in re.split(r"(?<=[.!?…])\s+", text):
        if aus and len(" ".join(aus + [s]).split()) > hoechstens:
            break
        aus.append(s)
    return " ".join(aus)


def _woerter(text: str) -> list[str]:
    return re.findall(r"\w+", text.lower())


def wiederholt(text: str, vorher: list[str]) -> bool:
    """Beginnt der Text wie eines der letzten Dias oder übernimmt er einen ganzen Satz daraus? (Gemessen 2026-10-20:
    Qwen schrieb Dia 7 mit demselben ersten Satz wie Dia 6.)"""
    neu = _woerter(text)
    for alt_text in vorher[-2:]:
        alt = _woerter(alt_text)
        if neu[:6] == alt[:6]:
            return True
        alte_saetze = {" ".join(_woerter(s)) for s in re.split(r"(?<=[.!?…])\s+", alt_text) if len(s.split()) >= 6}
        if any(" ".join(_woerter(s)) in alte_saetze for s in re.split(r"(?<=[.!?…])\s+", text)):
            return True
    return False


# Häufige Wörter je Sprache – erkennen, ob ein Text in der falschen Sprache kam (gemessen 2026-10-21: englischer
# Vortrag „The Beautiful Game“, Überschriften englisch, Sprechtext von Dia 5 und 7 deutsch).
STOPPWOERTER = {
    "de": {"der", "die", "das", "und", "ist", "nicht", "ein", "eine", "mit", "auf", "für", "von", "zu", "den", "dem",
           "sich", "auch", "wie", "wir", "sie", "im", "es", "war", "wurde", "noch", "einen", "seine", "ihre"},
    "en": {"the", "and", "is", "of", "to", "in", "that", "it", "was", "with", "for", "as", "on", "are", "this", "they",
           "his", "were", "but", "from", "by", "an", "their", "we", "you", "has", "have", "who"},
    "fr": {"le", "la", "les", "et", "est", "des", "une", "un", "du", "que", "qui", "dans", "pour", "pas", "sur", "au",
           "ce", "il", "elle", "nous", "vous", "son", "sa", "ses", "aux", "avec", "mais"},
    "es": {"el", "la", "los", "las", "y", "es", "de", "que", "en", "un", "una", "por", "con", "para", "del", "se",
           "no", "su", "sus", "al", "lo", "como", "pero", "fue", "muy", "más"},
    "it": {"il", "la", "le", "e", "è", "di", "che", "un", "una", "per", "con", "non", "del", "della", "sono", "gli",
           "nel", "nella", "si", "ha", "anche", "come", "ma", "più", "suo", "sua"},
    "pt": {"o", "a", "os", "as", "e", "é", "de", "que", "um", "uma", "para", "com", "não", "do", "da", "em", "no",
           "na", "se", "seu", "sua", "mais", "como", "mas", "foi", "dos", "das"},
}


def sprache_passt(text: str, sprache: str) -> bool:
    """Ist der Text erkennbar in der gewünschten Sprache? Im Zweifel ja – verworfen wird nur, was deutlich nach einer
    anderen Sprache aussieht."""
    buchstaben = re.findall(r"[^\W\d_]", text)
    if not buchstaben:
        return True
    kyrillisch = sum(1 for b in buchstaben if "Ѐ" <= b <= "ӿ") / len(buchstaben)
    if sprache == "ru" or kyrillisch > 0.5:
        return (kyrillisch > 0.5) == (sprache == "ru")
    woerter = _woerter(text)
    treffer = {s: sum(1 for w in woerter if w in liste) for s, liste in STOPPWOERTER.items()}
    beste = max(treffer, key=treffer.get)
    return beste == sprache or treffer[beste] < 3 or treffer.get(sprache, 0) * 2 > treffer[beste]


# --- 2.5D und Lampen (tiefe.py, Python-Umgebung von ComfyUI) ----------------------------------------------------

COMFY_PYTHON = COMFYUI_DIR / "venv" / "Scripts" / "python.exe"
_tiefe = {"prozess": None, "aus": False}
_tiefe_sperre = threading.Lock()


def tiefe_berechnen(bild: Path) -> dict | None:
    """Tiefenmasken und Lampen für ein Bild (tiefe.py, einmal gestartet, bleibt geladen). None, wenn nicht verfügbar –
    dann zeigt der Browser das Dia flach."""
    with _tiefe_sperre:
        if _tiefe["aus"]:
            return None
        p = _tiefe["prozess"]
        try:
            if p is None or p.poll() is not None:
                if not COMFY_PYTHON.is_file():
                    _tiefe["aus"] = True
                    return None
                p = _tiefe["prozess"] = subprocess.Popen(
                    [str(COMFY_PYTHON), "-I", str(HIER / "tiefe.py")], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL, text=True, encoding="utf-8", creationflags=KEIN_FENSTER)
                start = json.loads(p.stdout.readline() or "{}")
                if "fehler" in start:
                    log(f"2.5D: {start['fehler']}")
                    start = json.loads(p.stdout.readline() or "{}")
                log(f"2.5D: Tiefendienst {'bereit' if start.get('bereit') else 'ohne Tiefenmodell (nur Lampen)'}")
            p.stdin.write(str(bild) + "\n")
            p.stdin.flush()
            return json.loads(p.stdout.readline())
        except Exception as exc:  # noqa: BLE001
            log(f"2.5D nicht verfügbar: {type(exc).__name__}: {exc}")
            _tiefe["aus"] = True
            return None


def aehnlichkeit(a: str, b: str) -> float:
    """Anteil gemeinsamer Wörter (0..1) – grob, reicht für „hat der Lektor den Inhalt ausgetauscht?“."""
    wa, wb = set(_woerter(a)), set(_woerter(b))
    return len(wa & wb) / max(1, min(len(wa), len(wb)))


def doppelte_punkte(kapitel: list[str]) -> list[tuple[str, str]]:
    """Gliederungspunkte mit gleicher Überschrift (vor dem Doppelpunkt) – das Fazit am Ende zählt nicht mit."""
    gesehen, doppelt = {}, []
    for i, k in enumerate(kapitel[:-1], 1):
        kopf = " ".join(_woerter(k.split(":", 1)[0]))
        if kopf in gesehen:
            doppelt.append((f"Punkt {gesehen[kopf]}", f"Punkt {i}"))
        else:
            gesehen[kopf] = i
    return doppelt


def qwen_sprechen(satz: str, sprecher: str, sprache: str = "German") -> bytes:
    req = urllib.request.Request(f"{STIMMDIENST_URL}/sprechen", data=json.dumps({"text": satz, "stimme": sprecher, "sprache": sprache}).encode(),
                                 headers={"Content-Type": "application/json"})
    with GPU.frei("stimme"), urllib.request.urlopen(req, timeout=120) as r:   # je Satz – Bilder passen daneben
        return r.read()


def piper_sprechen(text: str) -> bytes:
    if not (PIPER_PYTHON.is_file() and PIPER_STIMME.is_file()):
        raise RuntimeError("Piper ist nicht verfügbar.")
    ziel = DATEN_DIR / f"piper_{uuid.uuid4().hex[:8]}.wav"
    try:
        subprocess.run([str(PIPER_PYTHON), "-m", "piper", "--model", str(PIPER_STIMME), "--output_file", str(ziel)],
                       input=text.encode("utf-8"), capture_output=True, timeout=120, creationflags=KEIN_FENSTER,
                       env={**os.environ, "PYTHONIOENCODING": "utf-8", "PYTHONUTF8": "1"}, check=True)
        return ziel.read_bytes()
    finally:
        ziel.unlink(missing_ok=True)


def wav_verbinden(stuecke: list[bytes], ziel: Path) -> list[tuple[float, float]]:
    """Hängt WAV-Stücke (gleiches Format) mit kurzer Stille aneinander. -> [(start, ende)] je Stück in Sekunden."""
    zeiten, rahmen, params = [], [], None
    pos = 0
    for roh in stuecke:
        with wave.open(io.BytesIO(roh)) as w:
            if params is None:
                params = w.getparams()
            daten = w.readframes(w.getnframes())
            n = w.getnframes()
        if rahmen:
            stille = int(params.framerate * SATZ_PAUSE)
            rahmen.append(b"\x00" * stille * params.sampwidth * params.nchannels)
            pos += stille
        zeiten.append((pos / params.framerate, (pos + n) / params.framerate))
        rahmen.append(daten)
        pos += n
    with wave.open(str(ziel), "wb") as aus:
        aus.setnchannels(params.nchannels)
        aus.setsampwidth(params.sampwidth)
        aus.setframerate(params.framerate)
        aus.writeframes(b"".join(rahmen))
    return zeiten


# --- Musik ------------------------------------------------------------------------------------------------------

def musik_liste() -> list[str]:
    if not MUSIK_DIR.is_dir():
        return []
    return sorted(p.name for p in MUSIK_DIR.iterdir() if p.suffix.lower() in MUSIK_ENDUNGEN and p.stat().st_size > 10000)


def _auspacken(x):
    return x["data"] if isinstance(x, dict) and "data" in x else x


# --- Der Vortrag ------------------------------------------------------------------------------------------------

class Vortrag:
    def __init__(self, thema: str, minuten: int, musik: str, figuren: bool = True, sprache: str = "de",
                 bildstil: str = "foto", stil_eigen: str = ""):
        self.id = uuid.uuid4().hex[:10]
        self.ordner = VORTRAEGE_DIR / self.id
        self.ordner.mkdir(parents=True)
        self.thema, self.minuten, self.musik_modus = thema, minuten, musik
        self.mit_figuren = figuren   # auf der Startseite abwählbar – dann wird auch keine Figur gemalt
        self.sprache = sprache if sprache in SPRACHEN else "de"   # Sprache von Text und Stimme (Startseite)
        # Bildstil von der Startseite: foto | aquarell | anime | eigen (dann stil_eigen, frei formuliert)
        self.bildstil = bildstil if bildstil in (*BILDSTILE, "eigen") and (bildstil != "eigen" or stil_eigen) else "foto"
        self.stil_eigen = stil_eigen
        self.art = "wissen"   # wissen | geschichte – entscheidet die KI am Anfang
        self.phasen: list[str] = []   # Phase der Richtschnur je Gliederungspunkt
        self.handlung = self.twist = ""   # Geschichtsbibel: jedes Dia kennt Handlung bzw. roten Faden und Twist
        self.personen: list[dict] = []   # {"name", "rolle", "aussehen", "referenz"} – referenz = Bild in ComfyUI
        self.tiefen: dict[str, dict] = {}   # Bild-URL -> {"mid", "near", "lampen"} für 2.5D im Browser
        self.geplant = max(4, round((minuten * 60 - TITEL_SEKUNDEN - SCHLUSS_SEKUNDEN) / DIA_SEKUNDEN))
        self.phase = "vorbereitung"   # vorbereitung -> bereit -> fertig | abgebrochen | fehler
        self.meldung = "Der Projektor wärmt sich auf …"
        self.fehler = ""
        self.titel = self.untertitel = ""
        self.titelbild = self.schlussbild = None
        self.titel_fertig = False
        self.gliederung_fertig = False
        self.texte = 0    # Sprechtexte fertig (für die Prozentanzeige beim Aufwärmen)
        self.bilder = 0   # Dia-Bilder fertig
        self.start = self.zuletzt_gefragt = time.time()
        self.stil = ""
        self.kapitel: list[str] = []
        self.hoehepunkt = 1
        self.sprites: list[dict] = []   # {"name", "prompt", "bewegung", "url"} – url erst, wenn freigestellt
        self.sprite_q: queue.Queue = queue.Queue()
        self.bild_prompts: list[str] = []   # bisherige Bildaufträge – das nächste Bild muss anders aussehen
        self.einstellung_folge = random.sample(range(len(EINSTELLUNGEN)), len(EINSTELLUNGEN))
        self.dias: list[dict] = []
        self.letztes: int | None = None   # Nummer des Schluss-Dias, sobald feststeht
        self.alles_fertig = False
        self.position = -1
        self.start_zeit = self.ende_zeit = None
        self.sprecher = "erzaehler3"
        self.stimme_art = ""
        self.musik_url = None
        self.musik_meldung = ""
        self.abbruch = threading.Event()
        self.sperre = threading.Lock()
        self.comfy_ids: set[str] = set()
        self.seed = int.from_bytes(os.urandom(4), "big") % 1_000_000_000
        self.bild_q: queue.Queue = queue.Queue()
        self.ton_q: queue.Queue = queue.Queue()
        threading.Thread(target=self._ablauf, daemon=True).start()

    def start_dias(self) -> int:
        """Wie viele Dias vor dem Projektorstart fertig sein müssen. Gemessen 2026-10-20: ~35 s Rechnen je Dia bei ~28 s
        Zeigen – der Vorsprung schmilzt um ~20 % eines Dias je Dia. Damit auch längere Vorträge durchlaufen, wächst der
        Startpuffer mit der Länge (11 Dias -> 3, 22 -> 5), höchstens 6 (sonst wird das Aufwärmen zu lang)."""
        return max(1, min(self.geplant, START_DIAS_MAX, max(START_DIAS, round(self.geplant * 0.2 + 0.8))))

    # -- Stand für den Browser --
    def _fortschritt(self) -> tuple[int, int]:
        """(unter self.sperre) Prozent der Vorbereitung bis zum Projektorstart und das nächste Etappenziel. Gewichte grob
        nach gemessener Dauer (2026-10-20): Gliederung ~10–40 s, Titelbild ~10 s, je Dia Text ~5 s, Bild ~10 s,
        Stimme ~25 s."""
        if self.phase != "vorbereitung":
            return 100, 100
        n = max(1, self.start_dias())
        je_dia = 70 / n
        etappen = [(17, self.gliederung_fertig), (10, self.titel_fertig)]
        for i in range(1, n + 1):
            # Text = Schreiber + Lektor (~10 s), Bild ~10 s, Stimme ~25 s
            etappen += [(je_dia * .25, self.texte >= i), (je_dia * .25, self.bilder >= i), (je_dia * .5, len(self.dias) >= i)]
        erreicht = 3 + sum(g for g, ok in etappen if ok)
        naechste = next((g for g, ok in etappen if not ok), 0)
        return min(99, round(erreicht)), min(99, round(erreicht + naechste))

    def stand(self) -> dict:
        with self.sperre:
            prozent, ziel = self._fortschritt()
            return {
                "fortschritt": prozent, "fortschritt_ziel": ziel, "sekunden": round(time.time() - self.start),
                "id": self.id, "phase": self.phase, "meldung": self.meldung, "fehler": self.fehler,
                "titel": self.titel, "untertitel": self.untertitel, "titelbild": self.titelbild,
                "schlussbild": self.schlussbild, "geplant": self.geplant, "letztes": self.letztes,
                "alles_fertig": self.alles_fertig, "dias": list(self.dias), "musik_url": self.musik_url,
                "sprites": [{"name": s["name"], "bewegung": s["bewegung"], "url": s["url"]} for s in self.sprites],
                "musik_meldung": self.musik_meldung, "stimme": self.stimme_art, "minuten": self.minuten,
                "rest_sekunden": None if self.ende_zeit is None else round(self.ende_zeit - time.time()),
                "art": self.art, "tiefen": dict(self.tiefen),
            }

    def position_setzen(self, pos: int):
        with self.sperre:
            self.zuletzt_gefragt = time.time()
            if pos >= 0 and self.start_zeit is None:
                self.start_zeit = time.time()
                self.ende_zeit = self.start_zeit + self.minuten * 60
            self.position = max(self.position, pos)

    def stoppen(self):
        if self.abbruch.is_set():
            return
        self.abbruch.set()
        with self.sperre:
            if self.phase not in ("fertig", "fehler"):
                self.phase, self.meldung = "abgebrochen", "Vortrag beendet."
        comfy_abbrechen(set(self.comfy_ids))
        log(f"Vortrag {self.id} abgebrochen")

    def _melden(self, text: str):
        with self.sperre:
            if self.phase == "vorbereitung":
                self.meldung = text

    def _url(self, name: str) -> str:
        return f"/dateien/{self.id}/{name}"

    # -- Fließband --
    def _ablauf(self):
        try:
            stimmdienst_starten()   # lädt ~30 s – parallel zur Gliederung
            GPU.vorrang(0, self.abbruch)   # die Gliederung braucht jeder als Erstes
            self._melden("Sprachmodell wird gefragt …")
            if not lms_sicherstellen():
                raise RuntimeError("In LM Studio ist kein Sprachmodell geladen, und es ließ sich keins laden.")
            self.art = self._art_bestimmen()
            self.phasen = phasen_verteilen(self.art, self.geplant)
            self._melden("Die Geschichte entsteht …" if self.art == "geschichte" else "Die Gliederung entsteht …")
            # Das Modell liefert manchmal viel weniger Punkte als verlangt (gemessen 2026-10-20: 5 statt 11 – der
            # Vortrag wäre nur halb so lang geworden). Dann einmal mit der konkreten Zahl nachfragen, das längere zählt.
            grund = (f"Topic: {self.thema}\nNumber of slides: {self.geplant}\nPhase plan:\n"
                     + "\n".join(f"{i}. {PHASEN[self.art][p]}" for i, p in enumerate(self.phasen, 1)) + "\n")
            g, auftrag = None, grund + self._sprachhinweis()
            for versuch in range(2):
                neu = qwen_json(self._p(GLIEDERUNG_SYSTEM), auftrag, {
                    "titel": TEXT, "untertitel": TEXT, "handlung": TEXT, "twist": TEXT, "stimmung": TEXT,
                    "personen": {"type": "array", "items": {"type": "object", "properties": {
                        "name": TEXT, "rolle": TEXT, "aussehen": TEXT}, "required": ["name", "rolle", "aussehen"]}},
                    "titel_prompt": TEXT, "schluss_prompt": TEXT,
                    "musik": TEXT, "sprecher": TEXT, "kapitel": {"type": "array", "items": TEXT},
                    "sprites": {"type": "array", "items": {"type": "object", "properties": {
                        "name": TEXT, "prompt": TEXT, "bewegung": {"type": "string", "enum": list(SPRITE_BEWEGUNGEN)}},
                        "required": ["name", "prompt", "bewegung"]}}}, temperatur=0.7, max_tokens=5500, timeout=180)
                if g is None or len(neu.get("kapitel", [])) > len(g.get("kapitel", [])):
                    g = neu
                n = len(g.get("kapitel", []))
                if n >= round(self.geplant * 0.85):
                    break
                log(f"Gliederung: nur {n} von {self.geplant} Punkten – frage nach")
                auftrag = (grund + f"ATTENTION: the list \"kapitel\" must have EXACTLY {self.geplant} entries (one per "
                           f"slide) – the last attempt had only {n}.\n{self._sprachhinweis()}")
            plan = [s for s in g.get("sprites", []) if isinstance(s, dict) and str(s.get("prompt", "")).strip()][:4]
            if not self.mit_figuren:
                plan = []
            with self.sperre:
                self.sprites = [{"name": str(s.get("name", "")).strip() or f"Figur {i + 1}", "prompt": str(s["prompt"]).strip(),
                                 "bewegung": s.get("bewegung") if s.get("bewegung") in SPRITE_BEWEGUNGEN else "fliegen",
                                 "url": None} for i, s in enumerate(plan)]
            if self.sprites:
                log(f"Vortrag {self.id}: Figuren " + ", ".join(f"{s['name']} ({s['bewegung']})" for s in self.sprites))
            kapitel = [re.sub(r"^\s*\d+[.)]\s*", "", str(k)).strip() for k in g.get("kapitel", []) if str(k).strip()]
            if len(kapitel) < 2:
                raise RuntimeError("Das Sprachmodell hat keine brauchbare Gliederung geliefert.")
            if len(kapitel) > self.geplant:
                kapitel = kapitel[:self.geplant - 1] + kapitel[-1:]   # das Ende (Happy End / Fazit) bleibt
            if len(kapitel) != len(self.phasen):
                self.phasen = phasen_verteilen(self.art, len(kapitel))
            hp = self.phasen.index(list(PHASEN[self.art])[4]) + 1 if len(kapitel) >= 3 else len(kapitel)
            self.handlung, self.twist = str(g.get("handlung", "")).strip(), str(g.get("twist", "")).strip()
            self.personen = [{"name": str(p.get("name", "")).strip(), "rolle": str(p.get("rolle", "")).strip(),
                              "aussehen": str(p.get("aussehen", "")).strip(), "referenz": None}
                             for p in g.get("personen", []) if isinstance(p, dict) and str(p.get("name", "")).strip()][:4]
            self._melden("Die Gliederung wird gegengeprüft …")
            kapitel = self._gliederung_pruefen(kapitel, hp)
            titel, untertitel = g["titel"].strip(), g["untertitel"].strip()
            if not sprache_passt(" ".join([titel, untertitel, *kapitel]), self.sprache):
                titel, untertitel, *kapitel = self._uebersetzen([titel, untertitel, *kapitel])
            with self.sperre:
                self.gliederung_fertig = True
                self.titel, self.untertitel = titel, untertitel
                self.kapitel = kapitel
                self.geplant = len(kapitel)
                self.hoehepunkt = hp
                self.sprecher = g["sprecher"] if g.get("sprecher") in SPRECHER else "erzaehler3"
            self.stil = self._stil_bauen(str(g.get("stimmung", "")).strip())
            log(f"Vortrag {self.id}: „{self.titel}“ ({self.art}), {self.geplant} Dias, Höhepunkt Dia {hp} "
                f"({kapitel[hp - 1].split(':', 1)[0]}), Sprecher {self.sprecher}, Stil: {self.stil}")
            log(f"Vortrag {self.id}: Handlung: {self.handlung[:300]} | Twist: {self.twist[:160]} | Personen: "
                + ", ".join(f"{p['name']} ({p['aussehen'][:50]})" for p in self.personen))
            if self.musik_modus == "erzeugen":
                threading.Thread(target=self._musik_erzeugen, args=(g.get("musik", ""),), daemon=True).start()

            self._melden("Das Titelbild wird gemalt …")
            if not comfy_sicherstellen(self.abbruch):
                raise RuntimeError("ComfyUI (Bildgenerierung) ist nicht erreichbar.")
            threading.Thread(target=self._bild_band, daemon=True).start()
            threading.Thread(target=self._ton_band, daemon=True).start()
            threading.Thread(target=self._sprite_band, daemon=True).start()
            self.bild_q.put(("titel", 0, g["titel_prompt"], None))
            # Referenzbilder der wiederkehrenden Figuren (Wunsch des Nutzers 2026-10-31): einmal malen, dann hängen
            # sie an jedem Dia, in dem die Figur vorkommt – so sieht sie überall gleich aus.
            for i, p in enumerate(self.personen[:REFERENZ_PERSONEN]):
                if p["aussehen"]:
                    self.bild_q.put(("referenz", i, p["aussehen"], None))
            self._text_band()
            self.bild_q.put(("schluss", 0, g["schluss_prompt"], None))
            self.bild_q.put(None)
        except Exception as exc:  # noqa: BLE001
            log(f"Vortrag {self.id}: {type(exc).__name__}: {exc}")
            with self.sperre:
                if self.phase != "abgebrochen":
                    self.phase, self.fehler = "fehler", str(exc)
            self.abbruch.set()

    def _zeit_knapp(self, k: int, reserve: float = 1.5) -> bool:
        """Reicht die Zeit nur noch für ein Dia (reserve 1.5) bzw. zwei (2.5)? Dann wird Dia k das Fazit bzw. der
        Höhepunkt."""
        with self.sperre:
            if self.ende_zeit is None:
                return False
            rest = self.ende_zeit - time.time()
            ungezeigt = [d for d in self.dias if d["nr"] > self.position]
            gepuffert = sum(d["dauer"] + DIA_ZUSATZ for d in ungezeigt)
            schnitt = (sum(d["dauer"] + DIA_ZUSATZ for d in self.dias) / len(self.dias)) if self.dias else DIA_SEKUNDEN
            in_arbeit = (k - 1) - len(self.dias)   # Text fertig, Bild/Ton noch nicht
        return gepuffert + schnitt * (in_arbeit + reserve) + SCHLUSS_SEKUNDEN >= rest

    def _gliederung_pruefen(self, kapitel: list[str], hp: int) -> list[str]:
        """Lektor-Durchgang über die Gliederung. Bleiben doppelte Überschriften stehen (gemessen 2026-10-20: der Lektor
        meldete „Wien“ doppelt, ersetzte es aber nicht), folgt ein zweiter Durchgang mit genau diesem Hinweis.
        Bei Fehlern oder anderer Länge bleibt der letzte brauchbare Stand."""
        hinweis = ""
        for durchgang in range(2):
            liste = "\n".join(f"{i}. [{PHASEN[self.art][p].split(' –')[0]}] {t}"
                              for i, (t, p) in enumerate(zip(kapitel, self.phasen), 1))
            try:
                erg = qwen_json(self._p(LEKTOR_GLIEDERUNG_SYSTEM), f"Topic: {self.thema}\n{self._bibel()}\n"
                                f"Number of points: {len(kapitel)}\nClimax: point {hp}\n\n"
                                f"Draft outline:\n{liste}{hinweis}\n\n{self._sprachhinweis()}",
                                {"probleme": {"type": "array", "items": TEXT}, "kapitel": {"type": "array", "items": TEXT}},
                                temperatur=0.3, max_tokens=4500, timeout=120)
            except Exception as exc:  # noqa: BLE001
                log(f"Lektor Gliederung: {exc} – Entwurf bleibt")
                return kapitel
            neu = [re.sub(r"^\s*\d+[.)]\s*(\[[^\]]*\]\s*)?", "", str(k)).strip()
                   for k in erg.get("kapitel", []) if str(k).strip()]
            probleme = [str(p).strip() for p in erg.get("probleme", []) if str(p).strip()]
            if len(neu) != len(kapitel):
                log(f"Lektor Gliederung: {len(neu)} statt {len(kapitel)} Punkte – Entwurf bleibt")
                return kapitel
            if not sprache_passt(" ".join(neu), self.sprache):
                log("Lektor Gliederung: falsche Sprache – Entwurf bleibt")
                return kapitel
            if probleme:
                log(f"Lektor Gliederung: {'; '.join(probleme)}")
            kapitel = neu
            doppelt = doppelte_punkte(kapitel)
            if not doppelt:
                break
            hinweis = ("\n\nATTENTION – these points are still duplicates, replace the later one of each pair with a new, "
                       "well-known aspect of the topic: " + "; ".join(f"{a} and {b}" for a, b in doppelt))
        return kapitel

    def _bild_prompt_neu(self, text: str, alt: str) -> str:
        try:
            erg = qwen_json("You write ONE English image prompt, 25-45 words, that shows what a slide's narration is "
                            "about: concrete subject, setting, composition, light. Square composition. No text, no "
                            "letters, no captions, no logos, no charts, no maps. Answer only with JSON: \"prompt\".",
                            f"Topic: {self.thema}\nNarration of the slide: {text}", {"prompt": TEXT}, temperatur=0.5,
                            max_tokens=200, timeout=30)
            return str(erg.get("prompt", "")).strip() or alt
        except Exception as exc:  # noqa: BLE001
            log(f"Neuer Bildauftrag: {exc}")
            return alt

    def _uebersetzen(self, texte: list[str]) -> list[str]:
        """Letzter Ausweg, wenn das Modell trotz Hinweis in der falschen Sprache schrieb: Wort für Wort in die
        Vortragssprache übersetzen lassen. Klappt das nicht, bleibt der Text, wie er ist."""
        ziel = SPRACHEN[self.sprache][0]
        try:
            erg = qwen_json(f"You translate texts into natural spoken {ziel}. Keep meaning, names and length; translate "
                            f"every text of the list in order. Answer only with JSON: \"texte\" (list of {ziel} strings).",
                            json.dumps(texte, ensure_ascii=False), {"texte": {"type": "array", "items": TEXT}},
                            temperatur=0.2, max_tokens=1500, timeout=45)
            neu = [str(t).strip() for t in erg.get("texte", [])]
            if len(neu) == len(texte) and all(neu) and sprache_passt(" ".join(neu), self.sprache):
                log(f"Übersetzt nach {ziel}: {texte[0][:60]} …")
                return neu
            log(f"Übersetzung nach {ziel} unbrauchbar – Text bleibt")
        except Exception as exc:  # noqa: BLE001
            log(f"Übersetzung nach {ziel}: {exc}")
        return texte

    def _bibel(self) -> str:
        """Geschichtsbibel für jeden Auftrag (Wunsch des Nutzers 2026-10-31: „Jedes dieser Teile muss wissen, welche
        Geschichte hier erzählt werden soll“): Art, Handlung bzw. roter Faden, Figuren mit Aussehen, der eine Twist."""
        teile = [f"Kind of talk: {'STORY (told, fictional)' if self.art == 'geschichte' else 'KNOWLEDGE (true facts)'}"]
        if self.handlung:
            teile.append(f"{'Story bible – the whole plot' if self.art == 'geschichte' else 'Red thread'}: {self.handlung}")
        if self.personen:
            teile.append("Characters:\n" + "\n".join(f"- {p['name']}: {p['rolle']}; look: {p['aussehen']}"
                                                     for p in self.personen))
        if self.twist:
            teile.append(f"The ONE {'twist' if self.art == 'geschichte' else 'surprising turn'} (only on its own "
                         f"slide): {self.twist}")
        return "\n".join(teile)

    def _gliederung_mit_phasen(self) -> str:
        return "\n".join(f"{i}. [{PHASEN[self.art][p].split(' –')[0]}] {t}"
                         for i, (t, p) in enumerate(zip(self.kapitel, self.phasen), 1))

    def _dia_pruefen(self, k: int, kap: str, f: dict, vorher: list[str], letztes: bool, rolle: str, phase: str) -> dict:
        """Lektor-Durchgang über ein Dia: Widersprüche, Logik, Wiederholungen, zweifelhafte Fakten bzw. Logik der
        Geschichte, Phase der Richtschnur. Taugt die Korrektur nicht (zu kurz, wiederholt), bleibt der Entwurf."""
        bisher = "\n".join(f"Slide {i}: {t}" for i, t in enumerate(vorher, 1)) or "(nothing yet – this is the first slide)"
        lage = "the FIRST slide" if k == 1 else ("the LAST slide" if letztes else f"slide {k}")
        auftrag = (f"Topic: {self.thema}\nTitle: {self.titel}\n{self._bibel()}\n\n"
                   f"Outline:\n{self._gliederung_mit_phasen()}\n\n"
                   f"This is {lage}, outline point: {kap}\nPhase: {PHASEN[self.art][phase]}\n\n"
                   f"Said so far:\n{bisher}\n\n"
                   f"Draft – text: {f['text']}\nDraft – prompt: {f.get('prompt', '')}\n"
                   f"Camera framing for this slide: {self._einstellung(k, rolle)}\n"
                   f"Previous pictures:\n{self._bisherige_bilder()}\n\n"
                   f"{self._atmosphaere_hinweis(f['text'])}\n\n{self._sprachhinweis()}")
        try:
            erg = qwen_json(self._p(LEKTOR_DIA_SYSTEM.format(wmin=WOERTER[0], wmax=WOERTER[1])), auftrag,
                            {"probleme": {"type": "array", "items": TEXT}, "text": TEXT, "prompt": TEXT,
                             **self._atmosphaere_felder()}, temperatur=0.3, max_tokens=950, timeout=45)
        except Exception as exc:  # noqa: BLE001
            log(f"Lektor Dia {k}: {exc} – Entwurf bleibt")
            return f
        effekt, sprite = self._atmosphaere_lesen(k, erg)
        text = textlaenge_begrenzen(str(erg.get("text", "")).strip())
        probleme = [str(p).strip() for p in erg.get("probleme", []) if str(p).strip()]
        if len(text.split()) < 12 or wiederholt(text, vorher) or not sprache_passt(text, self.sprache):
            log(f"Lektor Dia {k}: Korrektur unbrauchbar (zu kurz, wiederholt oder falsche Sprache) – Entwurf bleibt")
            return {**f, "effekt": effekt, "sprite": sprite}
        if probleme or text != f["text"]:
            log(f"Lektor Dia {k}: {'; '.join(probleme) or 'umformuliert'}")
        prompt = str(erg.get("prompt", "")).strip() or f.get("prompt", "")
        # Hat der Lektor den Inhalt deutlich geändert, passt das Bild oft nicht mehr (gemessen: Text über Wiener
        # Kaffeehäuser, Bild „arabische Händler mit Kamelen“) – dann einen neuen Bildauftrag schreiben lassen.
        if aehnlichkeit(text, f["text"]) < 0.5 and prompt == f.get("prompt", ""):
            prompt = self._bild_prompt_neu(text, prompt)
            log(f"Lektor Dia {k}: neuer Bildauftrag – {prompt[:80]}")
        return {"text": text, "prompt": prompt, "effekt": effekt, "sprite": sprite}

    def _text_band(self):
        """Schreibt Dia für Dia entlang der Richtschnur (Wunsch des Nutzers 2026-10-31: Anfang, Einleitung, Mittelteil,
        Spannung, Höhepunkt, Twist, Happy End – bzw. für Wissen Einstieg … Fazit). Jedes Dia kennt die Geschichtsbibel
        und – bei Geschichten – alles bisher Erzählte. Wird die Zeit knapp, kommen Höhepunkt, Twist und Schluss vorgezogen;
        fällt der Twist weg, erzählt ihn der Schluss in einem Satz mit."""
        vorher: list[str] = []
        geschrieben: set[int] = set()
        hp = self.hoehepunkt
        n = len(self.kapitel)
        hp_erreicht = False
        vorgezogen: list[int] = []
        for k in range(1, self.geplant + 1):
            while not self.abbruch.is_set() and k - max(self.position, 0) > VORLAUF + 1:
                time.sleep(0.3)
            GPU.vorrang(k + .2, self.abbruch)   # Text für Dia k: nach Stimme und Bild der früheren Dias
            if self.abbruch.is_set():
                return
            if vorgezogen:
                idx = vorgezogen.pop(0)
            elif k == self.geplant:
                idx = n - 1
            elif not hp_erreicht and k < hp and k >= 3 and self._zeit_knapp(k, reserve=3.5):
                idx = hp - 1   # Zeit nur noch für drei Dias: Höhepunkt, Twist, Schluss
                vorgezogen = [i for i in (hp, n - 1) if i > idx]
                log(f"Dia {k}: Zeit wird knapp – Höhepunkt wird vorgezogen")
            elif hp_erreicht and k >= 3 and self._zeit_knapp(k):
                idx = n - 1
            else:
                idx = k - 1
            letztes = idx == n - 1
            kap = self.kapitel[idx]
            phase = self.phasen[idx]
            rolle = ("schluss" if letztes else "hoehepunkt" if idx == hp - 1
                     else "aufbau" if idx < hp - 1 else "ausklang")
            if rolle == "hoehepunkt":
                hp_erreicht = True
            auftrag = (f"Topic: {self.thema}\nTitle of the talk: {self.titel}\n{self._bibel()}\n\n"
                       f"Outline:\n{self._gliederung_mit_phasen()}\n\n"
                       f"Now write slide {k}: {kap}\nPhase: {PHASEN[self.art][phase]}\n"
                       f"Camera framing for this slide: {self._einstellung(k, rolle)}\n"
                       f"Previous pictures (the new one must look different):\n{self._bisherige_bilder()}\n")
            if k == 1:
                auftrag += "This is the FIRST slide: introduce the topic briefly and make the audience curious.\n"
            twist_idx = hp if hp < n - 1 else None
            if letztes and twist_idx is not None and twist_idx not in geschrieben and self.twist:
                auftrag += (f"The twist has not been told yet (time ran short): reveal it in one sentence before the "
                            f"ending – {self.twist}\n")
            elif twist_idx is not None and idx < twist_idx:
                auftrag += "Do NOT reveal the twist / surprising turn yet.\n"
            if vorher:
                if self.art == "geschichte":   # die Geschichte muss zusammenhängen: alles bisher Erzählte
                    auftrag += ("\nThe story so far (continue it – take NO sentence from it and begin differently):\n"
                                + "\n".join(f"{i}. {t}" for i, t in enumerate(vorher[-12:], max(1, len(vorher) - 11)))
                                + "\n")
                else:
                    auftrag += ("\nThe last slides said (for orientation only – take NO sentence from them and begin "
                                "differently):\n" + "\n".join(f"- {t}" for t in vorher[-2:]) + "\n")
            # Die Sprache steht zuletzt: das schwache Modell richtet sich nach dem Ende des Auftrags
            sprachhinweis = f"\n{self._sprachhinweis()}"
            f = None
            for versuch in range(3):
                try:
                    f = qwen_json(self._p(FOLIE_SYSTEM.format(wmin=WOERTER[0], wmax=WOERTER[1])), auftrag + sprachhinweis,
                                  {"text": TEXT, "prompt": TEXT}, temperatur=0.75 + 0.1 * versuch, max_tokens=700,
                                  timeout=45)
                    f["text"] = textlaenge_begrenzen(f["text"].strip())
                    gleich = next((p for p in self.bild_prompts[-4:] if aehnlichkeit(f.get("prompt", ""), p) > 0.6), None)
                    sprache_ok = sprache_passt(f["text"], self.sprache)
                    if (len(f["text"].split()) >= 12 and not wiederholt(f["text"], vorher) and sprache_ok
                            and (not gleich or versuch == 2)):
                        break
                    if gleich:
                        auftrag += f"\nATTENTION: your image prompt is too similar to this earlier picture: {gleich} – show something else.\n"
                    if not sprache_ok:
                        sprachhinweis = (f"\nATTENTION: your last text was NOT in {SPRACHEN[self.sprache][0]}. "
                                         f"{self._sprachhinweis()}")
                    log(f"Dia {k}, Text (Versuch {versuch + 1}): zu kurz, wiederholt, gleiches Bild oder falsche Sprache")
                except Exception as exc:  # noqa: BLE001
                    if self.abbruch.is_set():
                        return
                    log(f"Dia {k}, Text (Versuch {versuch + 1}): {exc}")
                    f = None
                    time.sleep(1)
            if not f:
                if k <= 2:
                    raise RuntimeError("Das Sprachmodell liefert keinen Text.")
                letztes, rolle = True, "schluss"   # lieber sauber enden als hängen
                f = {"text": SCHLUSS_ERSATZ.get(self.sprache, SCHLUSS_ERSATZ["de"]), "prompt": ""}
            else:
                if not sprache_passt(f["text"], self.sprache):
                    f["text"] = self._uebersetzen([f["text"]])[0]
                f = self._dia_pruefen(k, kap, f, vorher, letztes, rolle, phase)
            if "effekt" in f:   # vom Lektor gleich mitentschieden
                effekt, sprite = f["effekt"], f["sprite"]
            else:
                effekt, sprite = self._atmosphaere(k, f["text"])
            ueberschrift = ueberschrift_aus(kap)
            if f.get("prompt"):
                self.bild_prompts.append(f["prompt"])
            figuren = self._figuren_im_dia(f["text"], f.get("prompt", ""))
            self.bild_q.put(("dia", k, f["prompt"], {"text": f["text"].strip(), "ueberschrift": ueberschrift,
                                                     "letztes": letztes, "rolle": rolle, "effekt": effekt,
                                                     "sprite": sprite, "figuren": figuren}))
            geschrieben.add(idx)
            if k == self.start_dias():   # Figuren erst nach den Start-Dias malen – sie verzögern den Start nicht
                for i, s in enumerate(self.sprites):
                    self.bild_q.put(("sprite", i, s["prompt"], None))
            vorher.append(f["text"].strip())
            with self.sperre:
                self.texte = k
            if letztes:
                with self.sperre:
                    self.letztes = k
                return

    def _figuren_im_dia(self, text: str, prompt: str) -> list[int]:
        """Welche wiederkehrenden Figuren kommen in diesem Dia vor? (Name im Sprechtext oder Bildauftrag)"""
        woerter = set(_woerter(text + " " + prompt))
        treffer = []
        for i, p in enumerate(self.personen):
            namen = [w for w in _woerter(p["name"]) if len(w) >= 3]
            if namen and any(w in woerter for w in namen):
                treffer.append(i)
        return treffer[:REFERENZEN_JE_DIA]

    def _referenz_malen(self, i: int, aussehen: str):
        """Referenzbild einer Figur: ganz, von vorn, neutraler Hintergrund – im selben Stil und mit demselben Seed wie
        die Dias. Danach in ComfyUIs input-Ordner, damit jedes Dia mit dieser Figur es per ReferenceLatent nutzt."""
        ziel = self.ordner / f"figur_{i}.png"
        t = time.perf_counter()
        try:
            if bild_erzeugen(f"Character reference sheet: one single character, full body, standing, front view, neutral "
                             f"pose, face clearly visible: {aussehen.strip().rstrip('.')}. Plain light grey background, "
                             f"nothing else. {self.stil}", self.seed, ziel, self):
                self.personen[i]["referenz"] = comfy_hochladen(ziel, f"diashow_{self.id}_figur_{i}.png")
                log(f"Referenzbild {self.personen[i]['name']}: {time.perf_counter() - t:.1f} s")
        except Exception as exc:  # noqa: BLE001
            log(f"Referenzbild {self.personen[i]['name']}: {exc}")

    def _tiefe(self, name: str):
        """2.5D-Masken und Lampen für ein fertiges Bild – im eigenen Thread, das Bild-Fließband wartet nicht darauf."""
        def rechnen():
            erg = tiefe_berechnen(self.ordner / name)
            if not erg or erg.get("fehler"):
                if erg and erg.get("fehler"):
                    log(f"2.5D {name}: {erg['fehler']}")
                return
            stamm = name.rsplit(".", 1)[0]
            with self.sperre:
                self.tiefen[self._url(name)] = {
                    "mid": self._url(f"{stamm}_mid.webp") if erg.get("tiefe") else None,
                    "near": self._url(f"{stamm}_near.webp") if erg.get("tiefe") else None,
                    "lampen": erg.get("lampen", [])}
        threading.Thread(target=rechnen, daemon=True).start()

    def _bild_band(self):
        while True:
            auftrag = self.bild_q.get()
            if auftrag is None:
                self.ton_q.put(None)
                return
            art, k, prompt, daten = auftrag
            if self.abbruch.is_set():
                continue
            # Titel zuerst, dann die Figuren-Referenzen, Dia k vor seinem Text-Nachfolger; Sprites nach den Start-Dias,
            # das Schlussbild ganz am Ende
            GPU.vorrang({"titel": .1, "referenz": .15, "sprite": self.start_dias() + .5,
                         "schluss": self.geplant + .1}.get(art, k + .1), self.abbruch)
            if art == "sprite":
                self._sprite_malen(k, prompt)
                continue
            if art == "referenz":
                self._referenz_malen(k, prompt)
                continue
            name = {"titel": "titel.png", "schluss": "schluss.png"}.get(art, f"dia_{k:03d}.png")
            ok = False
            if prompt:
                t = time.perf_counter()
                figuren = [self.personen[i] for i in (daten or {}).get("figuren", [])]
                refs = [p["referenz"] for p in figuren if p.get("referenz")]
                # Aussehen der Figuren mit in den Bildauftrag (wirkt auch ohne Referenzbild)
                aussehen = " ".join(f"{p['aussehen'].strip().rstrip('.')}." for p in figuren
                                    if p["aussehen"] and p["aussehen"][:30].lower() not in prompt.lower())
                try:
                    # ein Seed für den ganzen Vortrag (Wunsch des Nutzers 2026-10-31): der Stil bleibt gleich
                    ok = bild_erzeugen(f"{prompt.strip().rstrip('.')}. {aussehen} {self.stil}", self.seed,
                                       self.ordner / name, self, referenzen=refs)
                    log(f"Bild {name}: {time.perf_counter() - t:.1f} s" + (f" ({len(refs)} Referenz)" if refs else ""))
                    if ok:
                        self._tiefe(name)
                except Exception as exc:  # noqa: BLE001
                    log(f"Bild {name}: {exc}")
            if art == "titel":
                with self.sperre:
                    self.titelbild = self._url(name) if ok else None
                    self.titel_fertig = True
                    self._bereit_pruefen()
                self._melden("Die ersten Dias werden vorbereitet …")
            elif art == "schluss":
                with self.sperre:
                    self.schlussbild = self._url(name) if ok else None
            else:
                daten["bild"] = self._url(name) if ok else None
                with self.sperre:
                    self.bilder = k
                self.ton_q.put((k, daten))

    # -- Figuren und Atmosphäre (Wunsch des Nutzers 2026-10-20) --
    def _sprite_malen(self, i: int, prompt: str):
        """Figur malen (im Bild-Fließband, damit sie ComfyUI nicht doppelt belegt); freigestellt wird im eigenen Thread,
        weil rembg beim allerersten Mal sein Modell (~175 MB) lädt."""
        roh = self.ordner / f"sprite_{i}_roh.png"
        t = time.perf_counter()
        try:
            ok = bild_erzeugen(f"{prompt.strip().rstrip('.')}, {SPRITE_POSE.get(self.sprites[i]['bewegung'], '')}. "
                               f"{self.stil}. Single isolated subject, side view facing right, whole subject visible and "
                               f"centered, on a plain pure white background, no ground, no shadow, no text.",
                               self.seed, roh, self, SPRITE_MAL_GROESSE)
        except Exception as exc:  # noqa: BLE001
            log(f"Figur {i}: {exc}")
            return
        if ok:
            log(f"Figur {i} gemalt: {time.perf_counter() - t:.1f} s")
            self.sprite_q.put((i, roh))

    def _sprite_band(self):
        while not self.abbruch.is_set():
            try:
                i, roh = self.sprite_q.get(timeout=1)
            except queue.Empty:
                continue
            ziel = self.ordner / f"sprite_{i}.png"
            t = time.perf_counter()
            if sprite_freistellen(roh, ziel):
                with self.sperre:
                    self.sprites[i]["url"] = self._url(ziel.name)
                log(f"Figur {i} freigestellt: {time.perf_counter() - t:.1f} s")
            roh.unlink(missing_ok=True)

    def _sprachhinweis(self) -> str:
        ziel = SPRACHEN[self.sprache][0]
        return (f"LANGUAGE OF THE TALK: {ziel}. Write everything the audience hears or reads (title, subtitle, outline, "
                f"narration) in {ziel} only – no matter in which language the topic or these instructions are written.")

    def _p(self, system: str) -> str:
        """Anweisung an das Sprachmodell in der gewählten Vortragssprache (Platzhalter <SPRACHE>) und für die Art des
        Vortrags (<ART>, <ART_REGELN> … aus ART_TEXTE)."""
        for platzhalter, text in ART_TEXTE[self.art].items():
            system = system.replace(platzhalter, text)
        return system.replace("<SPRACHE>", SPRACHEN[self.sprache][0])

    def _art_bestimmen(self) -> str:
        """Wissensvermittlung oder Geschichte? (Wunsch des Nutzers 2026-10-31: das stellt die KI am Anfang fest)"""
        try:
            erg = qwen_json(ART_SYSTEM, f"Topic: {self.thema}",
                            {"art": {"type": "string", "enum": ["wissen", "geschichte"]}},
                            temperatur=0.1, max_tokens=40, timeout=30)
            art = erg.get("art") if erg.get("art") in PHASEN else "wissen"
        except Exception as exc:  # noqa: BLE001
            log(f"Art des Vortrags: {exc} – Wissen")
            art = "wissen"
        log(f"Vortrag {self.id}: Art {art}")
        return art

    def _stil_bauen(self, stimmung: str) -> str:
        """Bildstil von der Startseite (Foto, Aquarell, Anime oder eigener Wunsch) + Licht und Stimmung der KI."""
        if self.bildstil == "eigen":
            basis = self._stil_saeubern(self.stil_eigen, uebersetzen=True)
        else:
            basis = BILDSTILE[self.bildstil]
        stimmung = self._stil_saeubern(stimmung) if stimmung else ""
        return f"{basis}, {stimmung}" if stimmung else basis

    def _stil_saeubern(self, stil: str, uebersetzen: bool = False) -> str:
        """Motive aus dem Stil entfernen: er hängt an JEDEM Bildauftrag – stand darin „event horizon glows“, zeigte jedes
        Bild ein Schwarzes Loch (2026-10-20; die Anweisung in der Gliederung allein befolgte das Modell nicht)."""
        try:
            erg = qwen_json(("The user describes, in any language, the art style they want for all pictures of a slide "
                             "show. Turn it into an English style phrase for an image generator. " if uebersetzen else
                             "You clean an art style phrase for image prompts. ")
                            + "Remove every subject, object, creature, place "
                            "and motif (e.g. 'black hole', 'nebulae', 'ships', 'event horizon glows', 'castle'). Keep only "
                            "how it is rendered: medium, technique, colour palette, light, texture, film or paper look. "
                            "Answer only with JSON: \"stil\" (English, max 20 words).", stil, {"stil": TEXT},
                            temperatur=0.2, max_tokens=120, timeout=30)
            neu = str(erg.get("stil", "")).strip().rstrip(".")
            if neu and neu != stil:
                log(f"Stil gesäubert: {stil}  ->  {neu}")
            return neu or stil
        except Exception as exc:  # noqa: BLE001
            log(f"Stil säubern: {exc}")
            return stil

    def _einstellung(self, k: int, rolle: str) -> str:
        """Kameraeinstellung für Dia k: Höhepunkt und Schluss fest, sonst reihum in der zufälligen Folge dieses Vortrags."""
        return EINSTELLUNG_ROLLE.get(rolle) or EINSTELLUNGEN[self.einstellung_folge[(k - 1) % len(self.einstellung_folge)]]

    def _bisherige_bilder(self) -> str:
        return "\n".join(f"- {p}" for p in self.bild_prompts[-4:]) or "(none yet)"

    def _atmosphaere_hinweis(self, text: str) -> str:
        """Figurenliste und auffällige Wörter für die KI (gemessen 2026-10-20: „Raketen flogen im Krieg über den
        Ärmelkanal“ -> „keiner“) – entscheiden muss sie trotzdem selbst."""
        namen = [s["name"] for s in self.sprites]
        woerter = set(_woerter(text))
        auffaellig = sorted({w for w in woerter if any(w.startswith(st) for st in EFFEKT_WORTSTAEMME)})
        auffaellig += [n for n in namen if _woerter(n) and any(w.startswith(_woerter(n)[0][:5]) for w in woerter)]
        return (f"Figures of the talk: {', '.join(namen) if namen else '(none)'}"
                + (f"\nNotable words in the text: {', '.join(auffaellig)}" if auffaellig else ""))

    def _atmosphaere_felder(self) -> dict:
        return {"effekt": {"type": "string", "enum": list(EFFEKTE)},
                "figur": {"type": "string", "enum": [s["name"] for s in self.sprites] + [""]}}

    def _atmosphaere_lesen(self, k: int, erg: dict) -> tuple[str, int | None]:
        namen = [s["name"] for s in self.sprites]
        effekt = erg.get("effekt") if erg.get("effekt") in EFFEKTE else "keiner"
        sprite = namen.index(erg["figur"]) if erg.get("figur") in namen else None
        if effekt != "keiner" or sprite is not None:
            log(f"Atmosphäre Dia {k}: {effekt}" + (f", Figur {namen[sprite]}" if sprite is not None else ""))
        return effekt, sprite

    def _atmosphaere(self, k: int, text: str) -> tuple[str, int | None]:
        """Eigener Aufruf nur, wenn der Lektor ausgefallen ist: passt ein Effekt (Schnee, Regen, Sterne …) oder eine
        der Figuren? Meistens nicht – dann bleibt die Bühne ruhig."""
        try:
            erg = qwen_json(ATMOSPHAERE_SYSTEM, f"Topic: {self.thema}\n{self._atmosphaere_hinweis(text)}\n\n"
                            f"Narration of the slide: {text}", self._atmosphaere_felder(), temperatur=0.2, max_tokens=80,
                            timeout=30)
        except Exception as exc:  # noqa: BLE001
            log(f"Atmosphäre Dia {k}: {exc}")
            return "keiner", None
        return self._atmosphaere_lesen(k, erg)

    def _stimme_abwarten(self) -> bool:
        ende = time.time() + 150
        while time.time() < ende and not self.abbruch.is_set():
            st = stimmdienst_status()
            if st == "bereit":
                return True
            if st in ("fehler", "fehlt", "aus") and not (_dienst["prozess"] and _dienst["prozess"].poll() is None):
                return False
            time.sleep(1)
        return False

    def _ton_band(self):
        qwen_ok = None
        while True:
            auftrag = self.ton_q.get()
            if auftrag is None:
                with self.sperre:
                    self.alles_fertig = True
                    if self.phase == "vorbereitung":
                        self.phase = "bereit"
                return
            k, daten = auftrag
            if self.abbruch.is_set():
                continue
            GPU.vorrang(k, self.abbruch)   # die Stimme für Dia k ist das Dringendste an Dia k
            if qwen_ok is None:
                self._melden("Die Stimme wird geladen …")
                qwen_ok = self._stimme_abwarten()
                if not qwen_ok:
                    log("Stimmdienst nicht bereit – Ersatzstimme Piper")
            saetze = _saetze(daten["text"]) or [daten["text"]]
            ziel = self.ordner / f"dia_{k:03d}.wav"
            t = time.perf_counter()
            zeiten = None
            if qwen_ok:
                try:
                    zeiten = wav_verbinden([qwen_sprechen(s, self.sprecher, SPRACHEN[self.sprache][1]) for s in saetze], ziel)
                    self.stimme_art = "Qwen3-TTS"
                except Exception as exc:  # noqa: BLE001
                    if self.abbruch.is_set():
                        continue
                    log(f"Dia {k}, Stimme: {exc} – Ersatzstimme Piper")
            if zeiten is None and self.sprache == "de":   # Piper (Thorsten) spricht nur Deutsch – sonst nur Text
                try:
                    zeiten = wav_verbinden([piper_sprechen(" ".join(saetze))], ziel)
                    gesamt = zeiten[0][1]   # Satzzeiten nach Länge schätzen
                    laengen = [len(s) for s in saetze]
                    pos, zeiten = 0.0, []
                    for n in laengen:
                        zeiten.append((pos, pos + gesamt * n / sum(laengen)))
                        pos = zeiten[-1][1]
                    self.stimme_art = "Piper (Ersatz)"
                except Exception as exc:  # noqa: BLE001
                    log(f"Dia {k}, Ersatzstimme: {exc}")
            if self.abbruch.is_set():
                continue
            dauer = zeiten[-1][1] if zeiten else len(daten["text"].split()) / 2.3
            dia = {"nr": k, "ueberschrift": daten["ueberschrift"], "text": daten["text"], "bild": daten["bild"],
                   "ton": self._url(ziel.name) if zeiten else None, "dauer": round(dauer, 2),
                   "saetze": [{"text": s, "start": round(a, 2), "ende": round(b, 2)}
                              for s, (a, b) in zip(saetze, zeiten or [(0, dauer)] * len(saetze))],
                   "letztes": daten["letztes"], "rolle": daten.get("rolle", "aufbau"),
                   "effekt": daten.get("effekt", "keiner"), "sprite": daten.get("sprite")}
            log(f"Dia {k}: {dauer:.1f} s Ton in {time.perf_counter() - t:.1f} s")
            with self.sperre:
                self.dias.append(dia)
                if self.phase == "vorbereitung":
                    self.meldung = f"Dia {len(self.dias)} von {self.start_dias()} liegt bereit …"
                self._bereit_pruefen()

    def _bereit_pruefen(self):
        """(unter self.sperre) Titelbild und die ersten Dias fertig -> der Projektor darf anlaufen."""
        if self.phase == "vorbereitung" and self.titel_fertig and self.dias and (
                len(self.dias) >= self.start_dias() or self.dias[-1]["letztes"]):
            self.phase = "bereit"

    def _musik_erzeugen(self, beschreibung: str):
        """Passende Musik über ACE-Step (nur, wenn es schon läuft – es braucht viel Grafikspeicher). Bis sie fertig ist,
        spielt der Browser Musik aus dem Ordner."""
        if not port_offen(ACESTEP_URL):
            with self.sperre:
                self.musik_meldung = "ACE-Step läuft nicht – Musik aus dem Ordner."
            return
        try:
            caption = (beschreibung or "calm instrumental documentary background music").strip() + ", instrumental, no vocals"
            erg = _auspacken(_http_json(f"{ACESTEP_URL}/release_task", {
                "caption": caption, "lyrics": "[Instrumental]", "audio_duration": 240, "thinking": False}, timeout=30))
            task = erg["task_id"]
            with self.sperre:
                self.musik_meldung = "Passende Musik wird erzeugt …"
            ende = time.time() + 900
            while time.time() < ende and not self.abbruch.is_set():
                time.sleep(3)
                items = _auspacken(_http_json(f"{ACESTEP_URL}/query_result", {"task_id_list": [task]}, timeout=10))
                if not items:
                    continue
                item = items[0]
                if item.get("status") == 1:
                    res = json.loads(item["result"])
                    res = res[0] if isinstance(res, list) else res
                    rel = res["file"]
                    endung = (re.search(r"\.(mp3|wav|flac|ogg|m4a)", rel, re.I) or [".mp3"])[0].lower()
                    with urllib.request.urlopen(ACESTEP_URL + rel, timeout=60) as r:
                        (self.ordner / f"musik{endung}").write_bytes(r.read())
                    with self.sperre:
                        self.musik_url, self.musik_meldung = self._url(f"musik{endung}"), "Passende Musik ist fertig."
                    log(f"Vortrag {self.id}: Musik erzeugt")
                    return
                if item.get("status") not in (None, 0, 1):
                    raise RuntimeError(str(item.get("progress_text") or item.get("status")))
        except Exception as exc:  # noqa: BLE001
            log(f"Musik erzeugen: {exc}")
            with self.sperre:
                self.musik_meldung = "Musik-Erzeugung fehlgeschlagen – Musik aus dem Ordner."


VORTRAEGE: dict[str, Vortrag] = {}


def vortrag_laeuft() -> bool:
    """Ein Vortrag gilt als laufend, solange er nicht abgebrochen ist und der Browser in den letzten 30 s nachgefragt hat."""
    jetzt = time.time()
    return any(not v.abbruch.is_set() and jetzt - v.zuletzt_gefragt < 30 for v in VORTRAEGE.values())


def alte_vortraege_loeschen():
    ordner = sorted((p for p in VORTRAEGE_DIR.iterdir() if p.is_dir()), key=lambda p: p.stat().st_mtime)
    for p in ordner[:-VORTRAEGE_BEHALTEN]:
        if p.name not in VORTRAEGE or VORTRAEGE[p.name].abbruch.is_set():
            shutil.rmtree(p, ignore_errors=True)
            VORTRAEGE.pop(p.name, None)


# --- HTTP ---------------------------------------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _json(self, code: int, daten):
        body = json.dumps(daten, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _datei(self, pfad: Path, typ: str):
        if not pfad.is_file():
            return self.send_error(404)
        body = pfad.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", typ)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        try:
            self.wfile.write(body)
        except (ConnectionError, OSError):
            pass

    def do_GET(self):
        url = urllib.parse.urlparse(self.path)
        pfad = url.path
        if pfad in ("/", "/index.html"):
            return self._datei(WEB_DIR / "index.html", "text/html; charset=utf-8")
        if pfad == "/api/status":
            if urllib.parse.parse_qs(url.query).get("kurz"):   # für das Plugin: schnell, ohne andere Dienste zu fragen
                return self._json(200, {"version": VERSION, "vortrag_laeuft": vortrag_laeuft()})
            return self._json(200, {"sprachmodell": lms_modell(), "comfyui": comfy_bereit(), "stimme": stimmdienst_status(),
                                    "musik": len(musik_liste()), "acestep": port_offen(ACESTEP_URL), "version": VERSION,
                                    "vortrag_laeuft": vortrag_laeuft()})
        if pfad == "/api/geraeusche":
            arten: dict[str, list[str]] = {}
            for p in sorted(TON_DIR.glob("*_*.flac")) if TON_DIR.is_dir() else []:
                arten.setdefault(p.stem.rsplit("_", 1)[0], []).append(f"/ton/{urllib.parse.quote(p.name)}")
            return self._json(200, arten)
        if pfad.startswith("/ton/"):
            name = Path(urllib.parse.unquote(pfad[len("/ton/"):])).name
            return self._datei(TON_DIR / name, "audio/flac")
        if pfad == "/api/musik":
            return self._json(200, {"lieder": [f"/musik/{urllib.parse.quote(n)}" for n in musik_liste()]})
        if pfad.startswith("/musik/"):
            name = Path(urllib.parse.unquote(pfad[len("/musik/"):])).name
            return self._datei(MUSIK_DIR / name, MUSIK_ENDUNGEN.get(Path(name).suffix.lower(), "application/octet-stream"))
        if pfad.startswith("/dateien/"):
            teile = pfad.split("/")
            if len(teile) != 4 or not re.fullmatch(r"[0-9a-f]{10}", teile[2]):
                return self.send_error(404)
            name = Path(urllib.parse.unquote(teile[3])).name
            typ = {".png": "image/png", ".wav": "audio/wav", ".webp": "image/webp"}.get(Path(name).suffix.lower(),
                                                                 MUSIK_ENDUNGEN.get(Path(name).suffix.lower(), "application/octet-stream"))
            return self._datei(VORTRAEGE_DIR / teile[2] / name, typ)
        m = re.fullmatch(r"/api/vortrag/([0-9a-f]{10})", pfad)
        if m:
            v = VORTRAEGE.get(m.group(1))
            if not v:
                return self._json(404, {"fehler": "Diesen Vortrag gibt es nicht (mehr)."})
            pos = urllib.parse.parse_qs(url.query).get("pos", [""])[0]
            if re.fullmatch(r"-?\d+", pos):
                v.position_setzen(int(pos))
            return self._json(200, v.stand())
        self.send_error(404)

    def do_POST(self):
        pfad = urllib.parse.urlparse(self.path).path
        try:
            anfrage = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")
        except ValueError:
            return self._json(400, {"fehler": "Ungültige Anfrage."})
        if pfad == "/api/vortrag":
            thema = str(anfrage.get("thema", "")).strip()[:1500]
            if not thema:
                return self._json(400, {"fehler": "Bitte ein Thema eingeben."})
            try:
                minuten = max(5, min(30, int(anfrage.get("minuten", 10))))
            except (TypeError, ValueError):
                minuten = 10
            musik = anfrage.get("musik") if anfrage.get("musik") in ("ordner", "erzeugen", "aus") else "ordner"
            for alt in list(VORTRAEGE.values()):   # nur ein Vortrag zur Zeit (eine Grafikkarte)
                alt.stoppen()
            alte_vortraege_loeschen()
            v = Vortrag(thema, minuten, musik, anfrage.get("figuren") is not False, str(anfrage.get("sprache", "de")),
                        str(anfrage.get("bildstil", "foto")), str(anfrage.get("stil_eigen", "")).strip()[:200])
            VORTRAEGE[v.id] = v
            log(f"Neuer Vortrag {v.id}: {minuten} min, Musik {musik}: {thema[:80]}")
            return self._json(200, {"id": v.id})
        if pfad == "/api/beenden":
            # Knopf „Programm beenden“ auf der Startseite (Wunsch des Nutzers 2026-10-20): Vorträge stoppen, Stimmdienst
            # beenden (gibt den Grafikspeicher frei), dann den Server. Beim nächsten Chat in LM Studio startet ihn das
            # Plugin wieder.
            for v in list(VORTRAEGE.values()):
                v.stoppen()
            self._json(200, {"beendet": True})
            log("Programm wird beendet (Knopf auf der Startseite)")
            threading.Thread(target=lambda: (stimmdienst_beenden(), os._exit(0)), daemon=True).start()
            return
        if pfad == "/api/ende":
            # Das Plugin ersetzt so eine veraltete Server-Version – nie mitten in einem Vortrag.
            if vortrag_laeuft():
                return self._json(409, {"ende": False, "grund": "Ein Vortrag läuft."})
            self._json(200, {"ende": True})
            log("Server wird beendet (neue Version)")
            threading.Timer(0.3, lambda: os._exit(0)).start()
            return
        if pfad == "/api/vorwaermen":
            # Startseite geöffnet: die Stimme schon laden, während der Nutzer das Thema tippt (~30 s gespart).
            # Ohne Anfrage beendet sich der Stimmdienst nach 15 Minuten selbst.
            stimmdienst_starten()
            return self._json(200, {"stimme": stimmdienst_status()})
        m = re.fullmatch(r"/api/vortrag/([0-9a-f]{10})/stopp", pfad)
        if m:
            v = VORTRAEGE.get(m.group(1))
            if v:
                v.stoppen()
            return self._json(200, {"gestoppt": True})
        self.send_error(404)


if __name__ == "__main__":
    if "--hintergrund" in sys.argv:   # vom Plugin über WMI gestartet: ohne Konsole, alles ins Protokoll
        DATEN_DIR.mkdir(parents=True, exist_ok=True)
        sys.stdout = sys.stderr = open(DATEN_DIR / "server.log", "a", encoding="utf-8", buffering=1)
    log(f"Diavortrag: http://127.0.0.1:{PORT}  –  Version {VERSION}, PID {os.getpid()}, Bilder: {MODELL['unet']} "
        f"({MODELL['schritte']} Schritte), Musikordner: {MUSIK_DIR} ({len(musik_liste())} Stücke)")
    ThreadingHTTPServer.allow_reuse_address = os.name != "nt"   # Windows: sonst laufen zwei Server auf einem Port
    server = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    if os.environ.get("DIASHOW_BROWSER"):
        import webbrowser
        threading.Timer(0.5, webbrowser.open, args=[f"http://127.0.0.1:{PORT}"]).start()
    server.serve_forever()
