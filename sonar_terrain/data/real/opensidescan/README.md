# StarFish 原始 XTF 测线摘录

本次实际下载了 OpenSidescan 公共测试数据中的原始二进制测线片段，**不是 JPEG 截图或合成声呐图**。

## 来源与可复现性

- 上游仓库：[CIDCO-dev/OpenSidescan](https://github.com/CIDCO-dev/OpenSidescan)
- 固定提交：`ed8bb3ea891343df150a5568f30296c947b06925`
- 原文件：[test/data/starfish/22_07_2020_C2.xtf](https://github.com/CIDCO-dev/OpenSidescan/blob/ed8bb3ea891343df150a5568f30296c947b06925/test/data/starfish/22_07_2020_C2.xtf)
- 本地文件：`starfish_excerpt.xtf`，**1,047,600 字节**。
- 截取方法：读取原文件前 1 MiB，剔除最后不完整的记录，保留连续前缀。保留原始文件头和完整记录，未改动回波或元数据。
- 下载日期：2026-11-06。逐文件 URL、SHA-256、截取方式见 `manifest.json`。
- 上游仓库许可原样保存在 `LICENSE`（开头为 CIDCO 的 MIT 许可，后附第三方许可）；上游 README 保存为 `UPSTREAM_README.md`。未发现另附的测试数据专用许可或采集报告，因此不额外宣称其测量精度、采集者身份或数据集授权范围。

## 实际核验的字段

pyxtf 1.5.0 能完整解析所有记录，末尾没有半个 ping：

| 项目 | 实际内容 |
| --- | --- |
| 声呐 ping 数 | 439 |
| 声呐通道 | 左右舷各一个，每侧每 ping 1000 个采样 |
| 斜距范围 | 每侧 25 m |
| 主高度字段 | 非零，整段约 2.30～4.29 m |
| GPS | 412 个 ping 有非零传感器经纬度，27 个无效位置被排除 |
| 导航分辨率 | 大量 ping 复用 GPS，去除重复位置后仅保留 15 个位置，不能据此声称有 439 个独立空间定位 |
| 本次导航子段长度 | 约 21.53 m，采用局部投影累加路径长度 |
| 记录时间 | 文件头数据对应 2020-07-24；不依据文件名猜测采集日期 |
| 辐射标定/海底真值 | 未找到；增益、散射和几何仍有假设 |

还抽查了同仓库的 `crabtrap1.xtf` 和 `s4.xtf`，其抽样区段的高度字段全为零，因此没有拿它们伪装成带高度的重建数据。`scotsman-iver2.xtf` 抽样中也有高度和导航，但出现较大俯仰，当前轻量模型未做完整姿态补偿，暂不作为主要演示。

## 校验或补下载

在仓库根目录执行：

```bash
python sonar_terrain/download_real_data.py --dataset opensidescan --verify-only
python sonar_terrain/download_real_data.py --dataset opensidescan
```

补下载仅读取清单规定的连续前缀并核验哈希，不会下载整条大型测线。已下载的片段可离线使用。

## 已生成的真实数据结果

见 [`examples/real_starfish/`](../../../examples/real_starfish/)：

- `raw_all_pings.png`：全部 439 个原始 ping 的左右舷回波，不依赖增益假设；显示使用对数和分位数对比度。
- `real_waterfall.png`：有效且不同 GPS 位置的回波，使用实测高度做参考平面斜距校正。
- `navigation.csv`：实际位置、高度和姿态字段。
- `port/surface.png`、`starboard/surface.png`：分别生成的探索性地形假设。
- 各侧 `reconstruction.npz`、`points.csv`、`report.json`：数值结果与有效观测掩码。
- `metadata.json`：筛选数量、范围、收敛结果和假设。

### 探索性结果的含义

高度和 GPS 来自真实记录。**辐射增益没有实测标定**，因此预览显式启用“平坦海底统计校正”：用各横向距离单元的中位回波拟合一个公共距离响应，再将剩余强度变化作为坡度线索。这会同时消除真实地形中沿测线不变的横向结构，材料变化也可能被误当作坡度。

本次未做完整波束图、TVG、姿态、手工阴影掩码或传播损耗校正；按近到远采样解释通道，尚无独立采集报告核验。导航稀疏，左右侧分别置零且不能直接拼成真实地形。结果中的“米”只是上述假设下的模型尺度，**不等于已测得的真实高程或绝对水深**。没有对应测深真值，所以不报告 RMSE，不用先前合成数据的误差冒充本数据精度。

## 运行

```bash
python -m pip install -r sonar_terrain/requirements-xtf.txt
# 默认只导出真实回波和元数据，不默认估计未知标定。
python sonar_terrain/xtf_preview.py \
  sonar_terrain/data/real/opensidescan/starfish_excerpt.xtf \
  --output sonar_terrain/outputs/real_starfish

# 显式同意经验平坦标定假设后，生成左右舷地形预览。
python sonar_terrain/xtf_preview.py \
  sonar_terrain/data/real/opensidescan/starfish_excerpt.xtf \
  --output sonar_terrain/outputs/real_starfish \
  --exploratory-flat-calibration
```
