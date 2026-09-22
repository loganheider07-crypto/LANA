# L.A.N.A.

**Listen. Assist. Navigate. Adapt.**

L.A.N.A. is a Windows-focused local AI assistant built in Python. It combines voice interaction, local Ollama models, screen/camera understanding, Spotify controls, reminders/calendar features, PC controls, and a built-in mobile interface.

> This repository currently contains **main L.A.N.A. only**. L.A.N.A. Vision, Control, 3D, and other companion projects are intentionally not included.

## Highlights

- Voice wake/command pipeline
- Local Ollama AI
- Screen and webcam questions
- Built-in L.A.N.A. Mobile server (default port `8765`)
- Spotify integration
- Reminders and calendar
- Windows system/media controls
- Multiple assistant personalities
- Optional browser automation/research support
- Optional connection to a separately running L.A.N.A. Vision service

## Requirements

- Windows
- Python 3
- Ollama
- A microphone for voice features

Install Python packages:

```bat
py -m pip install -r requirements.txt
```

Optional Playwright browser support also needs:

```bat
py -m playwright install chromium
```

## Configuration

Copy `.env.example` to `.env`:

```bat
copy .env.example .env
```

Then edit `.env` for the optional features you use.

**Never commit `.env`, mobile tokens, Spotify token caches, browser profiles, memories, or other private runtime data.**

## Run

```bat
py LANA.py
```

## Privacy

L.A.N.A. stores several features locally, including memories, reminders, settings, browser sessions, and access tokens. These runtime files are excluded from this repository by default.

## Status

Personal project under active development.
