# explore/ · 验证脚本群说明（README）

## 2026-10-10 状态更正

最新：全局匹配路线已完整证明 `T23prime`、`problem7` 与 `main_induction_strong`，
全文件编译通过且最终定理无 `sorryAx`。详见 `t23prime-math-state.md` 顶部；以下为旧路线审计记录。

原 (A)/(B)/(V)/(U''-nt)/deep_saturation 方案已被真实 n=720 的两个全本质覆盖反例证伪。
运行 `python explore/audit_sigma_route.py`（从项目根目录），可重现全部数值和独占点检查。
完整数据在 `sigma_route_counterexample.json`、`sigma_route_counterexample_B.json`；
主 Lean 文件末的 `SigmaRouteAudit` 给出无 sorry 的合法性与否定证明。
后续状态见 `t23prime-math-state.md`。下文的旧候选验证记录只作历史档案。

本目录是"覆盖系统下界"项目的**数值验证与对抗搜索脚本群**（配合 `../IMO组合预选题.lean`）。
多数脚本为一次性验证工具，通过 `python xxx.py` 运行；0 违例仅表示该批样本未证伪，不能代替证明。
本轮审计脚本以成功核验显式反例为通过标准。

## 0. 记号约定（与 Lean 文件头部 Glossary 一致）
- `fam`：族 `[(a,d), ...]`，即块 a + dℤ（对应 Lean 的 `(a i, d i)`）。
- `N`（脚本内变量名）：**注意**——必须是用 `lcmlist` 算出的**真实 lcmDiff**；
  严禁用"选定的模数"代替（第七次陷阱：模数≠lcm 导致假证伪，见 Lean 注释区）。
- `boundv(n)` = Lean `bound n` = 1 + Σ_{p|n} v_p(n)(p−1)；`vp(n,p)` = v_p(n)。
- `mv = Counter(d for a,d in fam)`：普查 m_ν；**过载组** ⟺ m_ν > boundv(ν)。
- `O`：过载层集 {v_p(ν): ν 过载且 p|ν}；`alpha` = v_p(N)；`M = N // p**alpha`（p-自由部分）。
- 线 y ∈ [0, M)：`Mb[b]` = M_β(y)（满足 y ≡ a mod μ 的层 b 块数，μ = d // p^vp(d)）；
  `F = Σ_b min(Mb[b], boundv(p**b))`；**达标线** ⟺ F ≥ boundv(p**alpha)。
- 命题缩写 (P_p)/(L)/(L⁺)/(PC)/(R)/(Rp)/(R'')/(V)/(A)/(B)/(††) 等见 Lean 文件 Glossary。

## 1. 验证规范（每个脚本应遵守）
1. **lcmlist 铁律**：任何用到 `n` 的检查前先 `assert lcmlist(...) == N` 或显式过滤。
2. **族合法化**：覆盖（每点 ≥1 次）+ **全本质**（每块含独占点，`cnt==1`）+ lcm = N。
3. **采样器形状覆盖**：仅用"补类差-N 块"整流会系统性掩盖形状（使顶层过载 ⟹ 落回平凡区）；
   需并用多种采样（见 §3）。
4. **证伪**：输出完整反例（族/普查/参数）并写入 Lean 注释区存档。
5. 随机种子固定（便于复现）；大规模搜索建议 `nohup ... &` + 输出到文件，避免管道缓冲。

## 2. 脚本清单（按用途）
### 早期候选断言验证（多数已被后续轮次取代，保留为档案）
- `check_TGT.py` / `check_sigma.py` / `check_rec.py` / `check_claimC.py` / `check_D.py` / `check_Dproof.py`
  / `check_delta.py` / `check_App.py` / `check_Aprime*.py` / `check_L2.py` / `check_pp_gap.py`
  / `check_overlap.py` / `check_strategy*.py` / `check_star*.py` / `check_s4_deep*.py`
  / `search_t7.py` / `tight_scan.py` / `extremal.py` / `inspect_case2.py`：T²³ 架构各候选
  （T⁷、(A′)、(S5)、σ_rec、(D)、δ、(★) 族等）的枚举/压力验证与紧例扫描。
- `check_Pp.py` / `verify_Pp_proof.py`：**(P_p)**（单素数命题）的验证与 v_p=1 证明的实例核验。
- `check_pfc.py`：逐纤维 (PFC)。
- `check_Qm.py`：**(Q)** 普通类覆盖最小值 = p。

### 核心路线（(PC)⟹(L⁺)⟹(L)⟹(P_p) 及其前置）
- `verify_yline.py`：y*-线归约（κ 一般；μ 用 p-自由部分）。
- `verify_L.py` / `verify_carrier_line.py`：**(L)** 最优线引理 / **(L⁺)** 载体私有线版本。
- `verify_pairing_level.py`：逐层配对 (PL-ℓ) 与前缀瀑布的判定（失败候选的记录）；
  投影归纳与静态不等式的验证前身。
- `verify_identity.py`：精确递归恒等式 E_κ = prov + excess − ΣD 的数值核验。
- `build_n60.py` / `record_n60.py`：n=60 关键反例的构造与记录（杀死多条朴素路线的实例）。

### 多素配平路线（(R)/(Rp)/(R'')/(V) 及其证伪候选）
- `verify_R.py` / `verify_R_stress.py`：**(R)**（ΣE_p ≥ D−(ω−1)）的验证与压力。
- `verify_T2pp.py`：**(T'')** 的扫描（后续被真反例证伪，档案）。
- `verify_PQ.py`：投影静态 **(PQ)** 的证伪（枚举反例）。
- `verify_Cstrong.py` / `verify_Cstrong2.py`：单线付 t_p 的 **(C-strong)** 证伪。
- `verify_U.py`：**(U''-nt)**（达标线过载层普查上界）验证。
- `verify_all_rich.py`：富采样（混合差贪心补全）全链验证器。
- `verify_planted.py`：**植入私有点采样器**（按构造保全本质；全链验证）。
- `hunt_true_danger.py`：真·危险区定向搜索（浅层 1,2 过载 + 深层 v₂≥4 补全 + lcm 强制）；
  找到 (T'') 真反例 {10:8, 12:6, 80:8}。
- `decisive_test.py`：自由单元（6-块）与深层的共存判定（(iii) 的定量实验）。
- `stress_T23prime.py`：T23prime 的大 n 对抗压力（分层随机 + 补类整流）。

## 3. 采样器形状对照（重要）
- **补类整流**（`fam + [(g,N) for uncovered g]`）：保证 lcm = N，但把顶层推成过载 ⟹ 落回平凡区。
- **植入私有点**（verify_planted.py）：先随机块+私有点再补全，形状多样。
- **危险形状类穷举 / 邻域扰动**（hunt_true_danger.py、decisive_test.py）：非平凡区（Σ*_Oβ < α）
  的唯一可靠来源（n=240 型 {10:a,12:b,80:c}，扰反例 ±1–6 步）。
- **自由单元对抗**：把浅块换成 μ' ∤ μ*_deep 的差（如 6-块对 μ*=5），检验封锁机制边界。

## 4. 文献（lit/，非我方成果，仅备查）
- `struct.pdf` / `struct.txt`：arXiv:1904.04806（Balister–Bollobás–Morris–Sahasrabudhe–Tiba，
  "The structure and number of Erdős covering systems"）——**附录 A 含 Simpson 定理（原题断言）
  的自足证明**（本项目原题即该定理；不计入我方成果）。
- `cref.pdf` / `cref.txt`：Z.-W. Sun 的分类文献表（覆盖系统）。
- 其余（camthesis/robmorris/impan/zb/try_*）为检索过程中的中间下载，可忽略。

## 5. 运行速查
```bash
# 典型：危险区搜索（后台）
nohup python hunt_true_danger.py > hunt_out.txt 2>&1 &
# 全链验证器
python verify_all_rich.py
# Lean 侧编译检查（在仓库根目录）
lake env lean "IMO组合预选题.lean"
```
# 2026-10-10 最新完成状态

全局匹配路线已完整闭合 `IMO组合预选题.lean` 中的 `T23prime`、`problem7` 与
`main_induction_strong`；全文件编译通过，最终定理公理检查无 `sorryAx`。
一般匹配理论的文献归属、最终依赖链与旧辅助目标状态见 `t23prime-math-state.md` 顶部。
`MinimalCoverMatching.lean`、`DigitCoordinates.lean`、`MatchingCapacity.lean` 是无 sorry 开发模块。
主文件还保留旧路线 `Pp_bound` / `Rp_bound` 两个开放目标，它们不参与最终主证明。

