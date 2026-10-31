Slideshow Presentation – Browser-based AI Slide Presentation (LM Studio Plugin) early access

<img width="1539" height="661" alt="slideshow" src="https://github.com/user-attachments/assets/2e634764-edef-4bfa-a444-0f4694790592" />

Install LM Studio and select the "Qwen 9b" model within it. Install Python and this plugin. That’s it. The application should automatically detect and download any missing components.

How It Works

Enter your topic into the HTML window:
- Stories, fairy tales
- Technical or historical subjects
- Love stories or cartoons
- Science, sports, wars—ranging from factual to fantastical
Anything is possible; the quality may vary depending on the language model used.

You determine the duration of the presentation—whether it’s intended for children, designed to help with falling asleep, or simply meant for entertainment or education.

## How a talk is made

- **Story or knowledge:** at the start the AI decides whether the topic asks for a told *story* or for *knowledge*.
  Each kind follows its own guideline – story: opening, introduction, middle part, rising tension, climax, **one**
  twist, happy end; knowledge: hook, basics, deeper details, tension, climax, one surprising turn, conclusion.
- **Story bible:** the outline comes with the whole plot (or the red thread), the recurring characters with their look,
  and the one planned twist. Every slide and the editor see it, so the story stays coherent and logical.
- **Editor pass:** the loaded language model (e.g. `qwen3.8-9b-distill`) writes outline and slides; a second pass
  checks every one for contradictions, logic and – in stories – consistency with the story bible.
- **Picture style:** photorealistic, watercolour, anime or your own (free text). One seed per talk keeps the style
  consistent; recurring characters get a reference picture (FLUX.2 *ReferenceLatent*) so they look the same on every
  slide.
- **Picture effects** (as in the Dopewars project): 2.5D depth parallax (Depth Anything V2 Small, on the CPU), a slow
  camera move per slide (Ken Burns), flickering glow on lamps, film grain and vignette, plus weather and mood effects
  chosen per slide: snow, rain, drizzle, thunderstorm, stars, sparks, fire, smoke, fog, bubbles, fireflies, confetti,
  glitter, fireworks, autumn leaves, blossoms, sunbeams, dust, hearts.

You decide whether to include visual effects and music.

You can even have music generated specifically for your presentation—the system attempts to identify the musical style that best suits your content.
Please note that this requires VRAM (video memory); I recommend at least 12 GB, though the exact requirement depends on the specific language model being used.

Image quality depends on the image generation model. I use a distilled version of Flux for the sake of speed.

The slideshow begins after a short warm-up phase (typically lasting between 2 and 5 minutes, depending on your computer). Once it starts, you will see slide transitions, hear ambient sounds—such as coughing, the clinking of glasses, or other background noises—and observe graphical elements like snowflakes, confetti, or stars, all perfectly tailored to the specific scene. These, too, are generated locally by AI.

Available in multiple languages. Currently under development. Everything runs locally—there is no access to the internet or external AI models. This ensures your presentations remain private. Usage

Open the page at http://127.0.0.1:8430 (save it as a bookmark!) – or simply say "Open the slideshow" in the LM Studio chat (using the "diashow_oeffnen" tool).

Enter your topic (you can also add specific preferences, such as "for children" or "in a comic-book style"), select the duration, and turn on the projector. It will launch in full-screen mode, though it can, of course, also be viewed in a window.

You can also start the presentation by pressing Ctrl+Enter within the topic input field. ## Installation / After Making Changes

cd <project_folder>
npm install
npm run build
lms dev --install

Afterward, in LM Studio, go to the sidebar on the right → "Program" → "Plugins" → and enable `eliot/diashow-vortrag`. LM Studio only initializes plugins when there is activity in the chat; once the plugin has been triggered, the slideshow server will continue running independently. Files

diashow/
├── manifest.json, package.json, tsconfig.json
├── src/                    LM Studio plugin (TypeScript)
│   ├── index.ts            Launches the slideshow server upon loading
│   ├── server.ts           Starts the server / opens the browser
│   └── toolsProvider.ts    `diashow_oeffnen` (open slideshow) tool
├── vortrag/                The actual slideshow presentation (Python, standard library only)
│   ├── server.py           Web server + processing pipeline (outline, text, images, speech, music)
│   ├── web/index.html      Landing page and projector view
│   ├── tts_dienst.py       Qwen3 TTS speech service (port 8431, qwen-tts-venv)
│   ├── erzaehler.py, tts_schnell.py   Speech processing + acceleration (from the role-playing game system)
│   ├── tiefe.py            Depth masks (2.5D) and lamp positions per picture (runs with ComfyUI's Python)
│   └── stimmen/            Reference recordings for the five speakers
├── musik/                  Background music (included in the installation)
└── sounds/                 Ambient sounds – `<type>_<number>.flac` (included in the installation)

Generated images and audio files are stored in `%USERPROFILE%\LMStudioLocalPlugins\diashow-daten\vortraege\` (the 5 most recent presentations are kept; older ones are deleted the next time the program starts). Logs: diashow-daten\server.log, diashow-daten\stimmdienst.log.
