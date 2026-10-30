# DigiWave browser regression checks

Run from the repository root with Node.js, Playwright and Chromium available:

```sh
node tests/digiwave.browser.cjs
```

The cloud environment already provides Playwright and `/usr/bin/chromium`.
Elsewhere, install Playwright in your development environment and optionally set
`CHROMIUM_PATH` to the browser executable. The test starts and closes its own
loopback HTTP server and headless browser. It does not change project files.

Checks cover high-DPI rendering initialization, duration unit reuse, keyboard
undo/redo, edge dragging, cross-track selection and paste, exact JSON backup
recovery, rejection of invalid project data, parameterized clock generation,
JSON export, measurement cursors and grouping safeguards. A screenshot is written
to `/tmp/digiwave-editor.png`. This is not a large-project performance benchmark.
