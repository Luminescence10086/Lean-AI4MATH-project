# 文献工具 · 非我方成果

Oliver Kullmann, *Constraint satisfaction problems in clausal form*, arXiv:1103.3693v1,
2011-03-18，91 页。https://arxiv.org/pdf/1103.3693

用途：一般有限值域、负单值文字（x≠a）组成的子句系统；不是原题答案检索。

核对位置：

- §1.7.2：加权变量数 wn(F)=Σv(|Dv|−1)，亏格 δ(F)=c(F)−wn(F)。
- Lemma 1.9.4(3)，PDF 第 40 页：matching lean 等价于每个真子族亏格严格更小。
- Corollaries 1.9.8–1.9.9，PDF 第 41 页：极小不可满足系统具有 δ*=δ≥1。
- 极小不可满足系统是 lean，因而也是 matching lean。

本项目应用：CRT 和 p 进位坐标把整数等差数列块转成柱形盒，其补为负单值子句。
每个公差 ν 的子句支持权重是 bound(ν)−1。拟通过全槽匹配再加一个余块直接证明截断目标。
接驳推导详见 ../proof_paths_2026-10-10.md。

成果归属：上述亏格与匹配一般定理是已有文献工具，不能列入我方独立成果。
本项目给出的应用推导也明确注明依赖该工具；不声称一般定理或应用具有文献原创性。
后续可以在 Lean 中从 Mathlib 的 Hall 定理重新证明一般工具，不使用未证公理。
