"""Generate paired monochrome RC schematics from identical vector primitives."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'docs/img/filters'


def component(kind, cx, cy, rotation=0):
    if kind == 'R':
        symbol = '<path d="M-24 0L-20 -6L-12 6L-4 -6L4 6L12 -6L20 6L24 0"/>'
    else:
        symbol = ('<path d="M-24 0H-4M4 0H24"/>'
                  '<path d="M-4 -15V15M4 -15V15" stroke-width="3.5"/>')
    return f'<g transform="translate({cx} {cy}) rotate({rotation})">{symbol}</g>'


def diagram(lowpass):
    name = '低通' if lowpass else '高通'
    series, shunt = ('R', 'C') if lowpass else ('C', 'R')
    return f'''<svg xmlns="http://www.w3.org/2000/svg" width="320" height="180" viewBox="0 0 320 180" role="img" aria-labelledby="title desc">
  <title id="title">RC {name}电路</title>
  <desc id="desc">{series} 串联，{shunt} 从输出节点连接至公共参考线。输入和输出电压箭头均从上方节点指向下方公共参考端。</desc>
  <rect width="320" height="180" fill="#fff"/>
  <g fill="none" stroke="#000" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round">
    <path d="M22 50H92M140 50H298M22 164H298M200 50V82M200 130V164"/>
    {component(series, 116, 50)}
    {component(shunt, 200, 106, 90)}
    <path d="M22 67V144M298 67V144" stroke-width="1.8"/>
  </g>
  <g fill="#000">
    <path d="M22 149L18 137L22 140L26 137Z"/>
    <path d="M298 149L294 137L298 140L302 137Z"/>
    <circle cx="200" cy="50" r="3.6"/>
    <circle cx="200" cy="164" r="3.6"/>
  </g>
  <g fill="#fff" stroke="#000" stroke-width="2.2">
    <circle cx="22" cy="50" r="5"/>
    <circle cx="298" cy="50" r="5"/>
    <circle cx="22" cy="164" r="5"/>
    <circle cx="298" cy="164" r="5"/>
  </g>
  <g fill="#000" font-family="Times New Roman, Times, serif" font-style="italic" font-size="22">
    <text x="116" y="27" text-anchor="middle">{series}</text>
    <text x="175" y="113" text-anchor="end">{shunt}</text>
    <text x="32" y="117">v<tspan baseline-shift="sub" font-size="14" font-style="normal">in</tspan></text>
    <text x="285" y="117" text-anchor="end">v<tspan baseline-shift="sub" font-size="14" font-style="normal">out</tspan></text>
  </g>
</svg>
'''


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    for name, lowpass in [('rc-low-pass-matched.svg', True), ('rc-high-pass-matched.svg', False)]:
        (OUT / name).write_text(diagram(lowpass), encoding='utf-8')
