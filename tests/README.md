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

Paint regression checks cover literal Bus labels (including spaces and leading
zeros), blank-area deselection, real-edge/K ranges, high/low half-height and
Bus full-height rendering, default/custom/clear colours, gray print pixels,
undo/redo, JSON roundtrips and fill movement/copying.

## HTML 表格编辑器

```bash
node tests/table-editor.browser.cjs
```

需要 Playwright 和 Chromium，默认可执行文件为 `/usr/bin/chromium`，可用 `CHROMIUM_PATH` 覆盖。测试启动本地 HTTP 服务，使用真实页面验证双向同步、矩形合并/拆分、跨跨度增删行列、局部与整格格式、基础色卡及同色重复应用、选中文字保留、自定义颜色记忆、Shift/Alt+Enter 换行、拖拽/数值调整行高列宽、整表缩放、局部/全表字号、HTML/TSV 剪贴板、拒绝冲突粘贴、导出/导入、撤销、本地恢复及手机布局。
