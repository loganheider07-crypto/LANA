# L.A.N.A.

**Listen. Assist. Navigate. Adapt.**

L.A.N.A. is a Windows-focused local AI assistant built in Python. This repository contains the main L.A.N.A. application and its local voice/wake-word assets.

## Included

- `LANA.py` — main application
- `LANA.ico` — application icon
- Piper voice models for L.A.N.A., J.A.R.V.I.S., and F.R.I.D.A.Y.
- Piper voice metadata (`.onnx.json`)
- L.A.N.A. wake-word model files
- Existing local speech/acknowledgement WAV assets
- `Modelfile`
- `requirements.txt`

Private tokens, local links, memories, reminders, Spotify cache data, and `.env` are intentionally excluded.

## Setup

Create a virtual environment:

```bat
py -m venv .venv
.venv\Scripts\activate
```

Install dependencies:

```bat
python -m pip install -r requirements.txt
```

For Playwright browser support:

```bat
python -m playwright install chromium
```

Copy the environment template:

```bat
copy .env.example .env
```

Fill in only the optional settings you use, then run:

```bat
python LANA.py
```

## Voice models

The repository includes the three Piper personality voices used by L.A.N.A.:

- `en_US-amy-medium.onnx` — L.A.N.A.
- `en_GB-alan-medium.onnx` — J.A.R.V.I.S.
- `en_GB-alba-medium.onnx` — F.R.I.D.A.Y.

## Privacy

Do not commit `.env`, access tokens, generated mobile links, browser profiles, memories, reminders, or service caches. The included `.gitignore` blocks these local files.

## Mobile access isolation

Each L.A.N.A. installation generates its own high-entropy mobile access token on first run and stores it locally in `lana_mobile_access_token.txt`. That file and the generated `lana_mobile_link.txt` are ignored by Git and are never shipped in this repository. The mobile server defaults to the current user's own PC on port `8765`. Remote Tailscale access is created only when that user explicitly configures their own `LANA_TAILSCALE_IP` value in `.env`.
