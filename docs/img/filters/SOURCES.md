# RC 电路图片来源与许可

## 第一个对比表：理想 RC 电路图

| 本站图片 | 电路结构 |
| --- | --- |
| [理想 RC 低通](rc-low-pass-matched.svg) | 电阻串联，电容从输出节点接至公共参考线 |
| [理想 RC 高通](rc-high-pass-matched.svg) | 电容串联，电阻从输出节点接至公共参考线 |

两图均为本站通过 `scripts/generate_rc_diagrams.py` 绘制的黑白 SVG，使用完全相同的画布、元件符号、线宽、端点、字体和电压箭头，仅交换电阻与电容的位置。底部为公共参考线；箭头从上方节点指向下方公共参考端，表示输入或输出的参考电压降方向，不表示电流。

可在仓库根目录运行 `python scripts/generate_rc_diagrams.py` 重新生成。这两张图不再使用此前的外部位图；下方教材图片的来源与许可不受影响。

## 第 3 节：教材电路图

两幅电路图摘自 Tony R. Kuphaldt 的 *Lessons In Electric Circuits, Volume II — AC*，Filters 章。

**Copyright © 2000–2017, Tony R. Kuphaldt.** 图片遵循 **Design Science License**，不适用本站其他内容可能使用的许可。

| 本站图片 | 教材原始文件 |
| --- | --- |
| [RC 低通](rc-low-pass.png) | [02117.eps](https://github.com/FauxFaux/lessons-in-electric-circuits/blob/594fe93dbf3d12d188000fb901f04f08b6627e8d/AC/images/02117.eps) · [本站 EPS 源文件](source/02117.eps) |
| [RC 高通](rc-high-pass.png) | [02118.eps](https://github.com/FauxFaux/lessons-in-electric-circuits/blob/594fe93dbf3d12d188000fb901f04f08b6627e8d/AC/images/02118.eps) · [本站 EPS 源文件](source/02118.eps) |

来源固定于公开教材镜像提交 `594fe93dbf3d12d188000fb901f04f08b6627e8d`。可查阅[原教材 Filters 章](https://github.com/FauxFaux/lessons-in-electric-circuits/blob/594fe93dbf3d12d188000fb901f04f08b6627e8d/AC/src/filters.sml)、[版权声明](https://github.com/FauxFaux/lessons-in-electric-circuits/blob/594fe93dbf3d12d188000fb901f04f08b6627e8d/AC/hi.latex)和[原始许可](https://github.com/FauxFaux/lessons-in-electric-circuits/blob/594fe93dbf3d12d188000fb901f04f08b6627e8d/AC/src/dsl.sml)。

2026-11-05：为网页显示，将原始 EPS 用 Ghostscript 转换为 PNG；未改变电路内容。原始可编辑 EPS 与[完整许可文本](source/DESIGN-SCIENCE-LICENSE.txt)一并提供。

图片按原样提供，不作任何明示或暗示的担保，包括适销性或特定用途适用性的担保；责任限制及其他条款以完整许可为准。
