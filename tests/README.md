# DigiWave browser regression checks

Run from the repository root with Node.js, Playwright, pngjs and Chromium available:

```sh
node tests/digiwave.browser.cjs
```

The cloud environment already provides Playwright, pngjs and `/usr/bin/chromium`.
Elsewhere, install Playwright in your development environment and optionally set
`CHROMIUM_PATH` to the browser executable. The test starts and closes its own
loopback HTTP server and headless browser. It does not change project files.

Checks cover high-DPI rendering initialization, duration unit reuse, keyboard
undo/redo, edge dragging, cross-track selection and paste, exact JSON backup
recovery, rejection of invalid project data, parameterized clock generation,
JSON export, measurement cursors and grouping safeguards. A screenshot is written
to `/tmp/digiwave-editor.png`. This is not a large-project performance benchmark.


Protocol example checks use only Python's standard library:

```sh
python3 scripts/generate_digiwave_examples.py
python3 tests/test_digiwave_examples.py
```

The generator updates both the built-in offline catalog and the downloadable JSON
projects. Checks cover AXI handshakes, stalled payload stability, burst lengths
and LAST, APB completion, SPI sampled bytes and UART framing. Browser checks also
exercise the import/example dialog, cancellation, downloads and undo.
