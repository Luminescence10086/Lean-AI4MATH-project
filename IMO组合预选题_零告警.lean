import Mathlib

/-! 零告警副本（2026-10-10）：旧版本 IMO组合预选题.lean 原样保留。
本副本移除未被最终证明使用、且含占位证明的 Pp_bound/Rp_bound 两个辅助目标；
其原始陈述与探索记录保留在旧版本中。sum_bp_eq_bound_add 的未引用参数改名为 _hν。
未关闭任何 linter，未屏蔽占位证明警告；所有最终定理与反例证明保持不变。
本节状态优先于复制下来的历史注释。 -/

/-! # 第7题：极小等差数列覆盖族的规模下界

设 P₁, …, P_s 是 s 个整数等差数列：
(1) 每个整数至少属于其中一个数列；
(2) 每个等差数列都包含一个不属于其他 s-1 个数列的数（独占数）。
设各公差的最小公倍数为 n = p₁^α₁ ⋯ p_k^α_k。求证：s ≥ 1 + Σ αᵢ(pᵢ - 1)。
-/

/-!
## 2026-10-10 勘误（优先于下文历史交接与探索记录）

【宏观选路更新（优先于本节先前的 D+H 研究建议）】用户要求先设计多路再选路。
已选择并完整形式化“位坐标→极小不可满足→Hall 全槽匹配→组选中容量”路径。
文件末 truncated_cover_bound → T23prime → problem7 已闭合，公理检查无 sorryAx。
一般亏格稳定性是文献工具，明确非我方成果；这里从 Hall 重新证明，不添加公理。
旧归纳目标 main_induction_strong 也由极小子覆盖接到最终链；本副本已移除旧 Pp/Rp
开放辅助目标，原始陈述仍在旧版本中，不参与上述已完成定理的证明。

【同日补充：重组链也需更正】旧注释从 A=Σν min(mν,Σp bp(ν)) 推出
A≥ΣνΣp min(mν,bp(ν))，方向错误；真实关系是 ≤。因此 (R)→TGT
的既有证明无效，不能把下文 TGT←R←ΣRp←R'' 称为已证归约链。
在非平凡 n>1、全本质覆盖（无 d=1 块）的情形，定义损失
H:=Σν[Σp|ν min(mν,bp(ν))−min(mν,Σp|ν bp(ν))]≥0，则精确关系为
TGT ↔ Σp E_p ≥ D+H−(ω(n)−1)。旧 (R) 遗漏 H；仅证明旧 Rp/R'' 不足以
按既有算术推导闭合目标。这条 D+H 研究建议已归档，最终匹配证明无需此分支。
例如单组 ν=6、m=3：Σp min(m,bp)=2+3=5，而 min(m,Σp bp)=3，H=2。
这是算术方向的反例，不是合法覆盖族反例；不能据此宣称全本质覆盖上的 R 假。

按原 σ-路线继续证明时，发现 (A)/(B)/(V)/(U''-nt)/deep_saturation 均有真实反例。
详见文件末 `SigmaRouteAudit`：51 块全本质覆盖，真实 lcm=720，p=2、α=4、O={1,2}。
y=6 上 M₁=2、M₂=3、M₃=M₄=0，F=5 达标；两过载层同时饱和。
最深层全局普查 S₄=2<5。再把最后一个 47 mod 48 块扩为 15 mod 16：
全本质覆盖仍保持，真实 lcm 与 O 不变；y=6 上 M₄=1、F=6、两层饱和，故 (B) 也为假。
深块在线上存在，不表示它在该线上有独占点。因此这些目标不可证明，原 (V) 闭合方案在此中断。
原 Lean 陈述另有形式化错误：M 是任意函数，未与真实线普查关联；本轮引入
`lineCount`/`lineScore`/`overfullLayers`，将已证伪目标改成 Prop 定义（不能作为证明引用），
补上真实普查关联后的 (B) 也已证伪并改为 Prop。旧 (T'') 假定理也改成 Prop 档案。
反例的覆盖、本质性、真实 lcm 与违例数值均以 Lean 内核检查的证书存档，无 sorry。

反例上 (P_p)/(Rp)/(R'')/(R)/TGT 均成立；它只否定以上充分条件，不否定最终 σ-目标。
先前建议是修复含 H 的重组；本轮宏观选路后改用全槽匹配，避免逐素重叠的分开付款。
本文件此前“全链全部已形式化”“只剩唯一 (V) 缺口”等表述不准确：
当时有 9 处 sorry；若干蕴含只有注释中的数学推导，`T23prime` 尚无这些引理的装配证明；
当时 `problem7` 仍经带 sorry 的 `main_induction_strong`；文件末最终证明已改接匹配路线。
编译 0 错误不等于证明完成，最终状态须以 #print axioms 检查为准。
复核脚本及完整数据：`explore/audit_sigma_route.py`、`explore/sigma_route_counterexample*.json`。

# 交接说明（Handoff · 供后续 agent 阅读）

## 1. 本文件是什么 / 已完成的工作概述
本文件是"覆盖系统下界"项目（原题见上）的 Lean 4 + Mathlib 工作区。历次会话完成：

(a) **基础设施**：MemAP/Essential/lcmDiff/bound 等定义；T″-架构与 T²³/T²³⁺/T²³′ 等价链；
    多轮候选断言的大规模验证与**十次陷阱勘误档案**（全部记录于本文件注释区，约 2418–2840 行）。

(b) **我方独立定理（已证 + 已形式化，带完整证明）**：
    · (††) 无包含块引理及其推论（`no_containment_of_essential` 等，约 2495 行）；
    · **B-核引理**（深块偏移禁区，`B_core_perCell`）；
    · bound 乘性（`bound_mul_add_one`）、配平枢纽恒等（`sum_bp_eq_bound_add`）、
      min-平移恒等（`min_sub_min_eq`）；
    · 数学侧另已证：(PC)-一般 κ 定理、(P_p) 全部情形（一切素数与指数）、(R'') 的 |O|≤1 情形
      （证明以注释与 explore 脚本存档，形式化接驳待续）。

(c) **我方独立架构（σ-强化路线；2026-10-10 已修正状态）**：
    TGT ⟸ (R) ⟸ Σ_p(Rp) ⟸ (R'') 为注释中的归约，Lean 装配尚待完成；
    (V)/(A)/(B)/deep_saturation_candidate 已由文件末反例证伪。
    验证矩阵：危险形状类穷举 4500 + 邻域扰动 4710 + 植入采样 3189 + 补类压力 25 万+，
    全链（TGT/Pp/Rp/R''/R）0 违例。

(d) **文献参照（非我方成果，仅备查）**：原题断言即 Simpson 定理（Acta Arith. 45 (1985)），
    其复证全文在 arXiv:1904.04806 附录 A（存档于 explore/lit/）。**不计入我方成果。**

## 2. 用户要求与工作规范（后续 agent 必须遵守）
2.1 协作方式：**最小步推进**——用户给出逐步指示，每次推进后汇报并等待下一步指示；
    不要擅自扩大行动范围；路径选择权在用户（**不评判路径**：用户选定路线即执行，
    不在执行中反复质疑或推荐替代路线，除非发现硬错误）。
2.2 检索规则（2026-10 更新）：**允许检索强大理论与定理**（文献结果、工具、教材结论）用于
    辅助证明；**禁止直接检索原题解答/答案**（如搜"WISL 解答/官方 solution"）。
    检索到的文献须标注"非我方成果"并入档（explore/lit/）。
2.3 验证纪律（本项目十次陷阱的教训结晶，违反即可能重蹈覆辙）：
    · **lcmlist 铁律**：一切验证脚本必须用 `lcmlist` 计算真实 n 来驱动 α=b(n) 的参数——
      严禁用选定模数代替（第七次陷阱：模数≠lcm 导致假证伪）。
    · **压力等级**：候选断言必须通过 K≥7 深枚举 且 n ≥ 60 级压力测试方可相信；
      小 n 结论不可外推（第五次陷阱：K=5/6 两次漏检）。
    · **采样器形状覆盖**："补类差-N 块"采样会系统性掩盖某些形状（其把顶层变过载 ⟹ 落回平凡区）；
      需并用：植入私有点采样（verify_planted.py）、危险形状类穷举、邻域扰动（反例±6 步）。
    · **证伪须显式反例并存档**（含 lcm 核算）；**验证≠证明**——0 反例不得包装成"已证"。
2.4 Lean 规范：修改后必须 `lake env lean "IMO组合预选题.lean"` **全文件 0 错误**；
    sorry 只允许出现在**标注为目标陈述**的定理上；已证伪陈述只能用 Prop 定义存档；所有新增数学结论/反例/勘误
    必须写入本文件注释区（保持注释区块格式）；每次会话末同步记忆（t23prime-math-state）。
2.5 成果归属规则（本会话末用户决定）：**只保留我方独立成果**；文献结果仅作参照，
    不得混入我方成果清单；我方成果清单以本文件【文献参照·非我方成果】与
    【我方独立成果清单】注释块为准（约 2668–2685 行区）。

## 3. 数学内容地图（快速定位）
· 术语表(行~74)与基础定义至 early lemmas：行 ~141–1100；拆n化归与投影骨架：~1160–1600；强化归纳（T″）：~1600–2418；
· 新架构·可存活部件（σ、T²³′、等价链、全部路线与勘误档案）：~2418–2840；
· 我方目标陈述（Pp_bound/Rp_bound/overfullCount/deep_saturation/(A)(B)(V)）：~2530–2680；
· T23prime 主页（σ-版，带 sorry）+ assembly（已证）：~2960–3120；
· 主定理 problem7 与其推导：文件末。文献存档：explore/lit/（struct.pdf/txt 含 Simpson 复证全文）；
· 验证脚本：explore/ 47+ 个（verify_*.py / check_*.py / hunt_*.py / decisive_test.py 等）。

## 4. 剩余工作
数学缺口：**σ-强化版 T²³′ 的 (Rp)/(R'') 证明**及其 Lean 接驳。
(V)/(U''-nt)/deep_saturation 是曾经的充分条件候选，并非等价命题；现均已证伪。
本质性 (††) 与 B-核仍可用，但其单胞封锁界不足以推出已证伪的全线结论。
下一步亦可选：形式化 Simpson 附录 A 的干净归纳（衔接本文件的 assembly 定理）。
-/
/-!
## 术语与符号表（Glossary · 阅读全文注释的钥匙）

以下符号/术语全部为**本项目自引入**（非标准记号），凡在注释区出现即按本表定义理解。

### 一、对象与基本量
· `ι`（[Fintype ι]）：块（等差数列）的指标集；`(a i, d i)`：第 i 块 aᵢ + dᵢℤ；
  `MemAP a d i m` ⟺ m = aᵢ + dᵢ·k (k∈ℤ) 即 m 属于第 i 块。
· `n := lcmDiff d` = 各 dᵢ 的最小公倍数（`Finset.univ.lcm d`）。
· `v_p(x) := x.factorization p`（p-进指数）；`ω(x) := x.primeFactors.card`（素因子个数）。
· 全文记 **α := v_p(n)**、**M := n / p^α**（n 的 p-自由部分）、**κ 同 α**（旧注释用 κ）。
· `bound n := 1 + Σ_{p ∈ n.primeFactors} v_p(n)·(p−1)`（题目的下界，RHS）。
  缩写：**b(ν) := bound ν**；**b_p(ν) := (p−1)·v_p(ν) + 1**（单素数容量）；
  **b(p^β) := (p−1)β + 1 = bound(p^β)**（p-层容量）。恒等式：b(ν) = Σ_{p|ν} b_p(ν) − (ω(ν)−1)。
· `diffCount d ν`（记 **m_ν**）：差恰为 ν 的块数（"共差组 ν"的组大小）。
· `sigma d`（记 **σ**）：Σ_ν (m_ν − b(ν))₊（同差组超额；Nat 截断即 ₊）。
· `overfullCount d p`（记 **t_p**）：**过载组**数 #{ν : p | ν 且 m_ν > b(ν)}；
  "组 ν **过载**" ⟺ m_ν > b(ν)。
· `Essential a d i`：第 i 块含**独占元**（仅属于它的整数）；全族全本质 = 题设 (2)。
· `CoverWithout`：删去第 i 块后其余仍覆盖 ℤ；定理 essential_iff_not_coverWithout 给出等价。

### 二、p-层结构与普查（census）
· 块 j 的 **p-层** β_j := v_p(d_j)；**p-自由部分** μ_j := d_j / p^{β_j}（p ∤ μ_j）。
  **纯块** = p | d_j 的块；**裂块** = p ∤ d_j 的块（裂块整条 p-线全覆盖，见注释区）。
· **层 β 普查**（实例级）：S_β := Σ_μ min(m_{(β,μ)}, b(p^β))（(β,μ)-单元 = 差为 p^βμ 的组）；
  记 **δ_β := b(p^β) − S_β**（可正可负；负数 = 多单元溢出）。
· **过载层集 O** := {β : ∃ν, p|ν 且 v_p(ν)=β 且 m_ν > b(ν)}（含过载组的层）。
  记 **Σ_Oβ := Σ_{β∈O} β**（按层去重）与 **Σ*_Oβ := Σ_{过载组} v_p(ν)**（**带重数**，两者不同！）。
  **平凡区** : Σ*_Oβ ≥ α；**非平凡区** : Σ*_Oβ < α（(V) 等陈述只在此区有内容）。
· **线 y**（y ∈ [0, M)）：第 y 条 p-线；线上层普查 **M_β(y)** := #{纯块 j : y ≡ a_j (mod μ_j)}；
  **F(y) := Σ_{β=1}^α min(M_β(y), b(p^β))**（线普查和）；**达标线** ⟺ F(y) ≥ b(p^α)。
  线路内容量记 **c_β := min(M_β(y), b(p^β))**（"层 β 在线 y 的普查"）。
· **挖点（puncture）**：点 x* 仅被自己的点类 {x*}（β=α）覆盖（(PC) 的假设）。
  **载体块**：v_p(d) = α 的块；**载体私有线**：y° := x mod M（x 为载体块独占元）。
· **UA**（回避计数）：不被任何"非深层块"（v_p ≤ 某界）覆盖的点数下界（(iii-quant) 用）。

### 三、命题缩写（注释区与脚本通用；`explore/` 中同义）
· **(P_p)**（已证，我方 A2）：Σ_{ν: p|ν} min(m_ν, b_p(ν)) ≥ b_p(n)。
· **(W)**：Σ_ν (ω(ν)−1)·min(m_ν, b(ν)) ≥ ω(n) − 1。
· **(L)/(L⁺)**（已验）：最优线引理 / 载体私有线版本 ⟹ (P_p)（链条 (PC)⟹(L⁺)⟹(L)⟹(P_p)）。
· **(PC)**（已证，我方 A1）：挖点类覆盖 ℤ/p^κ ⟹ Σ_β min(M_β, b(p^β)) ≥ b(p^κ)。
· **(Q)**：普通（无挖点）类覆盖的最小普查 = p。
· **(TGT)**：Σ_ν min(m_ν, b(ν)) ≥ b(lcmDiff)（T²³′ 的 min-形式）。
· **T²³′/T²³⁺/T²³**（旧架构名）：带 σ 的强化目标 card ≥ b(n) + σ 及其前身；
  **(A′)/(S5)/(C′)**：其等价/归纳形式；**σ_rec**：递归定义的割值（slack/net/q*/I₀/M_p/C_i 见旧注释区，
  均为旧架构量：slack(F) := card − b(n)，net(F,q) := Σ_p(p−1)M_p − Σ_{i∈I₀}(aᵢ−1)）。
· **E_p := L_p − b_p(n)**（素 p 的 (P_p) 超额），其中 **L_p := Σ_{ν∋p} min(m_ν, b_p(ν))**。
· **(R)**：Σ_p E_p ≥ D − (ω(n)−1)，**D := Σ_ν min((m_ν−b(ν))₊, ω(ν)−1)**（吸收量，见 (R) 注释推导）。
· **(Rp)**：L_p ≥ b_p(n) + t_p；(Rp) ⟺ 有符号 δ-形（见注释区）。
· **(R'')**：Σ_{β∉O} S_β ≥ (p−1)·(α − Σ_Oβ)；|O|≤1 情形已证（我方 A3）。
· **(Q_p)**：(Rp) 的单元-位点等价形式（注释区）。
· **(V)（已证伪，2026-10-10）**：非平凡区达标线上 Σ_{β∈O} max(0, c_β − (p−1)β) ≤ 1
  （等价表述：达标线上过载层至多一层饱和）；**(V-strong)**：零饱和（已验更强版，
  非平凡区外有反例，见 (V-reverse) 注释）。最终：(V)⟹(U''-nt)⟹(R'')⟹(R)⟹TGT。
· **(A)（已证伪，2026-10-10）**：达标 ⟹ M_α(y) ≥ 1；**(B)（已证伪）**：深层+非平凡 ⟹ 饱和 ≤ 1。
· **(††)**：无包含块引理（已证）；**B-核引理** B_core_perCell（已证）：深块偏移对可整除更浅块是禁区。
· **deep_saturation_candidate（已证伪，2026-10-10）**：|O|≥2 且 α∉O ⟹ α-层普查吃满 b(p^α)。
· **已证伪存档（勿用）**：(T'')（真反例 n=240 {10:8,12:6,80:8}）、(K-t)、(D3'-正部)、PQ、(T2)、
  C-strong、(SQ-p)、V-b、V-c —— 各附显式反例于注释区。
· **Tpp_levels_falsified_record**：上述 (T'') 反例的 Lean 存档（仅档案，勿引用）。

### 四、求和约定（全文一致）
· Σ_{p | ν} / Σ_{ν ∋ p}：对 ν 的素因子 / 对含 p 的差组（取自 `Finset.univ.image d` 的过滤）。
· 层求和 Σ_β：β 遍历 1..α（`Finset.range (α+1)` 或注释中的显式区间，跳过 β=0 即裂块层）。
· 单元求和 Σ_μ：同一层内按 p-自由部分 μ 分组（μ | M）。
· 线求和 Σ_y：y 遍历 ℤ/M = [0, M)。
-/

/-! ## 基础定义 -/

/-- 第 i 个等差数列是否包含整数 m：m = aᵢ + dᵢ·k（k ∈ ℤ） -/
def MemAP {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) (m : ℤ) : Prop :=
  ∃ k : ℤ, m = a i + (d i : ℤ) * k

/-- s 个公差的最小公倍数 n -/
def lcmDiff {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ :=
  Finset.univ.lcm d

/-- 【下界函数】固定 n 时所需块数的下界（即题目的 RHS） -/
def bound (n : ℕ) : ℕ := 1 + ∑ p ∈ n.primeFactors, n.factorization p * (p - 1)

/-- 条件(2)的提纯形式：P_i 含独占数 -/
def Essential {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) : Prop :=
  ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m

/-- 去掉 P_i 之后，其余数列仍覆盖 ℤ -/
def CoverWithout {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) : Prop :=
  ∀ m : ℤ, ∃ j, j ≠ i ∧ MemAP a d j m

/-! ## 想法1：极小覆盖族的等价刻画 -/

/-- 在覆盖的前提下：P_i 含独占数 ⟺ 去掉 P_i 后覆盖被破坏 -/
theorem essential_iff_not_coverWithout {ι : Type*} {a : ι → ℤ} {d : ι → ℕ}
    (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m) (i : ι) :
    Essential a d i ↔ ¬ CoverWithout a d i := by
  constructor
  · rintro ⟨m, hm, hpriv⟩ hcw
    obtain ⟨j, hj, hjm⟩ := hcw m
    exact hpriv j hj hjm
  · intro h
    simp only [CoverWithout] at h
    push Not at h
    obtain ⟨m, hm⟩ := h
    obtain ⟨j, hj⟩ := hcover m
    rcases eq_or_ne j i with rfl | hne
    · exact ⟨m, hj, hm⟩
    · exact absurd hj (hm j hne)

/-! ## 路径A 基建：公差的最小公倍数 -/

theorem dvd_lcmDiff {ι : Type*} [Fintype ι] {d : ι → ℕ} (i : ι) : d i ∣ lcmDiff d :=
  Finset.dvd_lcm (Finset.mem_univ i)

/-- n > 0（所有公差为正；s = 0 时 n = lcm ∅ = 1，同样成立） -/
theorem lcmDiff_pos {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ i, 0 < d i) :
    0 < lcmDiff d := by
  by_contra h0
  have h0' : lcmDiff d = 0 := Nat.le_zero.mp (Nat.not_lt.1 h0)
  obtain ⟨i, -, hi0⟩ := Finset.lcm_eq_zero_iff.1 h0'
  exact absurd hi0 (ne_of_gt (hd i))

/-- n / d i > 0 -/
theorem div_lcmDiff_pos {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ i, 0 < d i) (i : ι) :
    0 < lcmDiff d / d i :=
  Nat.div_pos (Nat.le_of_dvd (lcmDiff_pos hd) (dvd_lcmDiff i)) (hd i)

/-- n = d i · (n / d i) 的整型版本 -/
theorem cast_lcmDiff_eq {ι : Type*} [Fintype ι] {d : ι → ℕ} (i : ι) :
    (lcmDiff d : ℤ) = (d i : ℤ) * ((lcmDiff d / d i : ℕ) : ℤ) := by
  have h : d i * (lcmDiff d / d i) = lcmDiff d := Nat.mul_div_cancel' (dvd_lcmDiff i)
  exact_mod_cast h.symm

/-! ## 路径A 基建：模 n 的有限模型 -/

/-- 有限模型：P_i 模 n 后对应的块。
    定义为 c ↦ a i + d i·c.val (c : Fin (n / d i)) 在 ZMod n 中的像，
    故其基数恰为 n / d i（见 card_block）。 -/
def Block {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (i : ι) :
    Finset (ZMod (lcmDiff d)) :=
  Finset.univ.image fun c : Fin (lcmDiff d / d i) =>
    (a i : ZMod (lcmDiff d)) + ((d i * c.val : ℕ) : ZMod (lcmDiff d))

/-- 桥引理：整数 m 属于 P_i ⟺ m 的模 n 剩余属于 Block i -/
theorem mem_block_iff {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) (i : ι) {m : ℤ} :
    MemAP a d i m ↔ (m : ZMod (lcmDiff d)) ∈ Block a d i := by
  have hq : 0 < lcmDiff d / d i := div_lcmDiff_pos hd i
  constructor
  · rintro ⟨k, rfl⟩
    -- 取 k mod (n / d i) 的代表元作为 Fin 中的 c
    have h1 : 0 ≤ (k : ℤ) % ((lcmDiff d / d i : ℕ) : ℤ) :=
      Int.emod_nonneg k (by exact_mod_cast ne_of_gt hq)
    have h2 : (k : ℤ) % ((lcmDiff d / d i : ℕ) : ℤ) < ((lcmDiff d / d i : ℕ) : ℤ) :=
      Int.emod_lt_of_pos k (by exact_mod_cast hq)
    have h3 : ((k % (lcmDiff d / d i)).toNat : ℤ) = (k : ℤ) % ((lcmDiff d / d i : ℕ) : ℤ) :=
      Int.toNat_of_nonneg h1
    have h4 : (k % (lcmDiff d / d i)).toNat < lcmDiff d / d i := by
      refine Nat.cast_lt (α := ℤ) |>.mp ?_
      rw [h3]
      exact h2
    have hdvdq : ((lcmDiff d / d i : ℕ) : ℤ) ∣
        (k : ℤ) - (k : ℤ) % ((lcmDiff d / d i : ℕ) : ℤ) :=
      Int.modEq_iff_dvd.1 (Int.mod_modEq k _)
    have hdvdn : (lcmDiff d : ℤ) ∣
        (d i : ℤ) * ((k : ℤ) - (k : ℤ) % ((lcmDiff d / d i : ℕ) : ℤ)) := by
      rw [cast_lcmDiff_eq]
      exact mul_dvd_mul_left (d i : ℤ) hdvdq
    have hmeq : (a i : ℤ) + (d i : ℤ) * (k : ℤ)
        ≡ (a i : ℤ) + (d i : ℤ) * ((k % (lcmDiff d / d i)).toNat : ℤ)
        [ZMOD (lcmDiff d : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have hdiff : (a i : ℤ) + (d i : ℤ) * ((k % (lcmDiff d / d i)).toNat : ℤ)
          - ((a i : ℤ) + (d i : ℤ) * (k : ℤ))
          = -((d i : ℤ) * ((k : ℤ) - ((k % (lcmDiff d / d i)).toNat : ℤ))) := by ring
      rw [hdiff, h3]
      exact Int.dvd_neg.mpr hdvdn
    have hz := Iff.mpr (ZMod.intCast_eq_intCast_iff _ _ _) hmeq
    refine Finset.mem_image.2 ⟨⟨(k % (lcmDiff d / d i)).toNat, h4⟩, Finset.mem_univ _, ?_⟩
    rw [hz]
    push_cast
    rfl
  · intro hmem
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 hmem
    have hzero : (↑((m : ℤ) - (a i : ℤ) - (d i : ℤ) * ((c.val : ℕ) : ℤ)) :
        ZMod (lcmDiff d)) = ((0 : ℤ) : ZMod (lcmDiff d)) := by
      show (Int.castRingHom (ZMod (lcmDiff d)))
          ((m : ℤ) - (a i : ℤ) - (d i : ℤ) * ((c.val : ℕ) : ℤ)) =
        ((0 : ℤ) : ZMod (lcmDiff d))
      rw [map_sub, map_sub, map_mul]
      show (m : ZMod (lcmDiff d)) - (a i : ZMod (lcmDiff d)) -
        ((d i : ℤ) : ZMod (lcmDiff d)) * (((c.val : ℕ) : ℤ) : ZMod (lcmDiff d)) = _
      rw [sub_eq_of_eq_add' hc.symm, Nat.cast_mul]
      push_cast
      ring
    have hdvd : (lcmDiff d : ℤ) ∣
        (m : ℤ) - (a i : ℤ) - (d i : ℤ) * ((c.val : ℕ) : ℤ) := by
      have h1 : ((m : ℤ) - (a i : ℤ) - (d i : ℤ) * ((c.val : ℕ) : ℤ)) ≡ (0 : ℤ)
          [ZMOD (lcmDiff d : ℤ)] :=
        Iff.mp (ZMod.intCast_eq_intCast_iff _ _ _) hzero
      rw [Int.modEq_iff_dvd, zero_sub] at h1
      exact Int.dvd_neg.mp h1
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨(c.val : ℤ) + t * ((lcmDiff d / d i : ℕ) : ℤ), ?_⟩
    have hexp : (d i : ℤ) * (((c.val : ℕ) : ℤ) + t * ((lcmDiff d / d i : ℕ) : ℤ))
        = (d i : ℤ) * ((c.val : ℕ) : ℤ) + t * ((d i : ℤ) * ((lcmDiff d / d i : ℕ) : ℤ)) := by
      ring
    have ht2 : m = (a i : ℤ) + (d i : ℤ) * ((c.val : ℕ) : ℤ) + t * (lcmDiff d : ℤ) := by
      linarith
    rw [hexp, ← cast_lcmDiff_eq]
    linarith

/-- 条件(1) 下降：ZMod n 的每个剩余类都被某个块覆盖 -/
theorem cover_block {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m) :
    ∀ x : ZMod (lcmDiff d), ∃ i, x ∈ Block a d i := by
  have : NeZero (lcmDiff d) := ⟨ne_of_gt (lcmDiff_pos hd)⟩
  intro x
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective x
  obtain ⟨i, hi⟩ := hcover m
  refine ⟨i, ?_⟩
  rw [← hm]
  exact (mem_block_iff hd i).1 hi

/-- 条件(2) 下降：每个块在 ZMod n 中仍有独占剩余类 -/
theorem private_block {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) (hess : ∀ i, Essential a d i) (i : ι) :
    ∃ x, x ∈ Block a d i ∧ ∀ j, j ≠ i → x ∉ Block a d j := by
  obtain ⟨m, hm, hpriv⟩ := hess i
  refine ⟨(m : ZMod (lcmDiff d)), (mem_block_iff hd i).1 hm, ?_⟩
  intro j hj hmem
  exact hpriv j hj ((mem_block_iff hd j).2 hmem)

/-- 块的基数：|Block i| = n / d i -/
theorem card_block {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) (i : ι) :
    (Block a d i).card = lcmDiff d / d i := by
  have hq : 0 < lcmDiff d / d i := div_lcmDiff_pos hd i
  have hinj : Function.Injective
      (fun c : Fin (lcmDiff d / d i) =>
        (a i : ZMod (lcmDiff d)) + ((d i * c.val : ℕ) : ZMod (lcmDiff d))) := by
    intro c₁ c₂ hcc
    have hcc' : ((d i * c₁.val : ℕ) : ZMod (lcmDiff d))
        = ((d i * c₂.val : ℕ) : ZMod (lcmDiff d)) := by
      exact add_left_cancel hcc
    have hcc'' : (((d i * c₁.val : ℕ) : ℤ) : ZMod (lcmDiff d)) =
        (((d i * c₂.val : ℕ) : ℤ) : ZMod (lcmDiff d)) := by
      rw [Int.cast_natCast, Int.cast_natCast]
      exact hcc'
    have hI : ((d i * c₁.val : ℕ) : ℤ)
        ≡ ((d i * c₂.val : ℕ) : ℤ) [ZMOD (lcmDiff d : ℤ)] :=
      Iff.mp (ZMod.intCast_eq_intCast_iff _ _ _) hcc''
    rw [Int.modEq_iff_dvd] at hI
    -- hI : ↑n ∣ d i·c₂.val - d i·c₁.val，消去 d i 得 q ∣ c₂.val - c₁.val
    have hq2 : ((lcmDiff d : ℕ) : ℤ) = (d i : ℤ) * ((lcmDiff d / d i : ℕ) : ℤ) :=
      cast_lcmDiff_eq i
    have h2 : ((lcmDiff d / d i : ℕ) : ℤ) ∣ ((c₂.val : ℤ) - (c₁.val : ℤ)) := by
      have hdi : (d i : ℤ) ≠ 0 := ne_of_gt (by exact_mod_cast hd i)
      have hI2 := hI
      rw [hq2] at hI2
      have hprod : ((d i * c₂.val : ℕ) : ℤ) - ((d i * c₁.val : ℕ) : ℤ)
          = (d i : ℤ) * ((c₂.val : ℤ) - (c₁.val : ℤ)) := by
        push_cast
        ring
      rw [hprod] at hI2
      exact (Int.mul_dvd_mul_iff_left hdi).1 hI2
    have heq : (c₁.val : ℤ) ≡ (c₂.val : ℤ) [ZMOD ((lcmDiff d / d i : ℕ) : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      exact h2
    have hmod1 : ((c₁.val : ℤ)) % ((lcmDiff d / d i : ℕ) : ℤ) = (c₁.val : ℤ) :=
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast c₁.isLt)
    have hmod2 : ((c₂.val : ℤ)) % ((lcmDiff d / d i : ℕ) : ℤ) = (c₂.val : ℤ) :=
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast c₂.isLt)
    have hval : (c₁.val : ℕ) = (c₂.val : ℕ) := by
      have hE : ((c₁.val : ℤ)) % ((lcmDiff d / d i : ℕ) : ℤ)
          = ((c₂.val : ℤ)) % ((lcmDiff d / d i : ℕ) : ℤ) := heq
      rw [hmod1, hmod2] at hE
      exact_mod_cast hE
    exact Fin.val_inj.1 hval
  rw [Block, Finset.card_image_of_injective _ hinj]
  rw [Finset.card_univ, Fintype.card_fin]

/-! ## 蓝图：拆 n 主归纳（2026-09-30）

思路：固定 n，证明"参数为 n 的极小覆盖族至少需要 bound n 个块"，对 n 强归纳。
归纳步的基本操作是【把素数幂 p^α 从 n 的分解中拆出来】——这是当前的决策点，
保留两个方向：①拆 n 化归；②拼素数幂后计数。 -/

/-- bound 1 = 1（n = 1 时无质因子） -/
theorem bound_one : bound 1 = 1 := by
  simp [bound]

/-- 基例：n = 1 时由覆盖性直接得 s ≥ 1 -/
theorem base_case {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m) : Fintype.card ι ≥ bound 1 := by
  obtain ⟨i, -⟩ := hcover (0 : ℤ)
  have hs : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
  rw [bound_one]
  omega

/-- 【拆n簿记】把素数幂 p^k 从 n 中拆出后，下界恰好减少 k·(p−1)：
    bound (p^k·m) = bound m + k·(p−1)（p 素且 p ∤ m） -/
theorem bound_mul_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) {m : ℕ} (hm : m ≠ 0)
    (hpm : ¬ p ∣ m) : bound (p ^ k * m) = bound m + k * (p - 1) := by
  by_cases hk : k = 0
  · subst hk
    simp [bound]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hpk : p ^ k ≠ 0 := pow_ne_zero k (ne_of_gt (hp.pos))
    have hprod : p ^ k * m ≠ 0 := Nat.mul_ne_zero hpk hm
    -- 质因子集合：{p} ∪ m.primeFactors
    have hpkf : (p ^ k).primeFactors = {p} := by
      rw [Nat.primeFactors_pow p hk]
      simp [hp]
    have hpf : (p ^ k * m).primeFactors = {p} ∪ m.primeFactors := by
      rw [Nat.primeFactors_mul hpk hm, hpkf]
    -- 分解处的值
    have hvalp : (p ^ k * m).factorization p = k := by
      rw [Nat.factorization_mul hpk hm, Nat.factorization_pow]
      simp [hp.factorization, Nat.factorization_eq_zero_of_not_dvd hpm]
    have hvalq : ∀ q ∈ m.primeFactors, (p ^ k * m).factorization q = m.factorization q := by
      intro q hq
      have hdq : p ≠ q := by
        intro he
        subst he
        exact hpm (Nat.mem_primeFactors.1 hq).2.1
      have hzero : p.factorization q = 0 := by
        simp [hp.factorization, hdq]
      have h1 : (p ^ k * m).factorization q
          = k * (p.factorization q) + m.factorization q := by
        rw [Nat.factorization_mul hpk hm, Nat.factorization_pow]
        simp
      rw [h1, hzero]
      simp
    -- 两质因子集合不交
    have hpnf : p ∉ m.primeFactors := fun h => hpm (Nat.mem_primeFactors.1 h).2.1
    have hdisj : Disjoint {p} m.primeFactors :=
      (Finset.disjoint_singleton_right.2 hpnf).symm
    -- 求和
    simp only [bound, hpf]
    rw [Finset.sum_union hdisj, Finset.sum_singleton, hvalp]
    have hsum : ∑ q ∈ m.primeFactors, (p ^ k * m).factorization q * (q - 1)
        = ∑ q ∈ m.primeFactors, m.factorization q * (q - 1) :=
      Finset.sum_congr rfl fun q hq => by rw [hvalq q hq]
    rw [hsum]
    ring


/-- 素数幂的下界：bound (p^k) = 1 + k·(p−1) -/
theorem bound_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    bound (p ^ k) = 1 + k * (p - 1) := by
  have h1 : ¬ p ∣ 1 := fun hd => hp.ne_one (Nat.eq_one_of_dvd_one hd)
  have h2 := bound_mul_prime_pow hp k (m := 1) one_ne_zero h1
  rw [Nat.mul_one, bound_one] at h2
  exact h2

/-- 公差为 1 的列等于 ℤ，会吞掉所有其他列的独占数；
    故当 lcmDiff d > 1 时所有公差 ≠ 1。 -/
theorem no_diff_one {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (_hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m)
    (hnl : 1 < lcmDiff d) : ∀ i, d i ≠ 1 := by
  intro i hi
  by_cases hcard : Fintype.card ι = 1
  · have : Subsingleton ι :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
    have hle : lcmDiff d ∣ d i :=
      Finset.lcm_dvd (fun j _ => by rw [Subsingleton.elim j i])
    have heq : lcmDiff d = d i := Nat.dvd_antisymm hle (dvd_lcmDiff i)
    omega
  · have h1 : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    have h2 : 1 < Fintype.card ι := by omega
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card h2 i
    obtain ⟨m, hm, hpriv⟩ := hess j
    have hmi : MemAP a d i m := ⟨m - a i, by rw [hi]; ring⟩
    exact hpriv i (Ne.symm hj) hmi

/-! ## 蓝图·素数幂试点：n = p²（p 推 p²） -/

/-- 辅助：由模同余直接构造 MemAP -/
theorem memAP_of_modEq {s : ℕ} {a : Fin s → ℤ} {d : Fin s → ℕ} {i : Fin s} {m : ℤ}
    (h : m ≡ a i [ZMOD (d i : ℕ)]) : MemAP a d i m := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  have hprod : (d i : ℤ) * (-k) = -(k * (d i : ℤ)) := by ring
  rw [hprod]
  linarith

/-- 【蓝图·试点】n = p² 时 s ≥ 2p−1 = bound n（p 推 p²，降幂试点）。
    论证：公差只能是 p 或 p²。满块（d=p，整根 mod p 纤维）与点块（d=p²）：
    ① 满块的 mod p 残差两两不同（同则两块重合，独占性破灭）⟹ t ≤ p；
    ② 点块必须避开满块的残差（满块盖住整根纤维，同纤维的点块无独占类）；
    ③ 覆盖性：残差无满块的 (p−t)·p 个类只能由点块盖 ⟹ q ≥ p·(p−t)；
    ④ lcm 条件：必须有 d = p² 的列 ⟹ q ≥ 1 ⟹ t < p；
    ⑤ s = t + q ≥ t + p(p−t) ≥ 2p−1。 -/
theorem case_prime_sq {s : ℕ} {p : ℕ} {a : Fin s → ℤ} {d : Fin s → ℕ}
    {n : ℕ} (hp : p.Prime) (hn : n = p ^ 2) (heq : lcmDiff d = n) (hd : ∀ i, 0 < d i)
    (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m) :
    s ≥ bound n := by
  subst heq
  have hp2 : p * p = lcmDiff d := by rw [hn, pow_two]
  have : NeZero p := ⟨ne_of_gt hp.pos⟩
  have hnl : 1 < lcmDiff d := by
    rw [← hp2]
    have h1 : 1 < p := hp.one_lt
    nlinarith
  -- 分类：每个公差是 p 或 p·p
  have hcls : ∀ i, d i = p ∨ d i = p * p := by
    intro i
    have hdvd : d i ∣ lcmDiff d := dvd_lcmDiff i
    rw [hn] at hdvd
    rcases (Nat.dvd_prime_pow hp).1 hdvd with ⟨j, hj, hjd⟩
    rcases j with _ | j
    · rw [Nat.pow_zero] at hjd
      exact absurd hjd (no_diff_one hcover hess hnl i)
    rcases j with _ | k
    · rw [Nat.pow_one] at hjd
      exact Or.inl hjd
    · have hdvd2 : p ^ (k + 1 + 1) ∣ p ^ 2 := by rw [← hjd]; exact hdvd
      have hk2 : k + 1 + 1 ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd2
      have hk0 : k = 0 := by omega
      rw [hk0, Nat.zero_add, Nat.pow_two] at hjd
      exact Or.inr hjd
  -- 指标集：T = 满块（d = p），Q = 点块（d = p²）
  set T : Finset (Fin s) := Finset.univ.filter (fun i => d i = p) with hTdef
  set Q : Finset (Fin s) := Finset.univ.filter (fun i => d i = p * p) with hQdef
  have hmemT : ∀ i, i ∈ T ↔ d i = p := fun i => Finset.mem_filter.trans
    ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hmemQ : ∀ i, i ∈ Q ↔ d i = p * p := fun i => Finset.mem_filter.trans
    ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hunion : T ∪ Q = Finset.univ := by
    ext i
    rcases hcls i with h | h
    · exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_union.2 (Or.inl ((hmemT i).2 h))⟩
    · exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_union.2 (Or.inr ((hmemQ i).2 h))⟩
  have hdisj : Disjoint T Q := by
    rw [Finset.disjoint_iff_ne]
    intro i hi j hj hne
    rw [hmemT] at hi
    rw [hmemQ] at hj
    rw [← hne, hi] at hj
    have h1 : 1 < p := hp.one_lt
    exact absurd hj (by nlinarith)
  have hdisjne : ∀ i ∈ T, ∀ j ∈ Q, i ≠ j := Finset.disjoint_iff_ne.1 hdisj
  have hspl : s = T.card + Q.card := by
    have hu : (Finset.univ : Finset (Fin s)).card = s := by
      rw [Finset.card_univ, Fintype.card_fin]
    calc s = Finset.univ.card := hu.symm
      _ = (T ∪ Q).card := by rw [hunion]
      _ = T.card + Q.card := Finset.card_union_of_disjoint hdisj
  -- ① 满块的 mod p 残差两两不同
  have hTres : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ (a i ≡ a j [ZMOD (p : ℕ)]) := by
    intro i hi j hj hij hae
    rw [Int.modEq_iff_dvd] at hae
    obtain ⟨m, hm, hpriv⟩ := hess i
    simp only [MemAP] at hm
    rw [(hmemT i).1 hi] at hm
    obtain ⟨k, hk⟩ := hm
    have hme : m ≡ a j [ZMOD (p : ℕ)] := by
      rw [Int.modEq_iff_dvd, hk]
      obtain ⟨u, hu⟩ := hae
      refine ⟨u - k, ?_⟩
      linarith
    rw [← (hmemT j).1 hj] at hme
    exact hpriv j (Ne.symm hij) (memAP_of_modEq (a := a) (d := d) (i := j) (m := m) hme)
  -- 满块残差函数在 T 上单射 ⟹ t ≤ p
  have hinj : Set.InjOn (fun i : Fin s => ((a i : ℤ) : ZMod p)) (↑T : Set (Fin s)) := by
    intro i hi j hj heq
    by_contra hne
    exact absurd ((ZMod.intCast_eq_intCast_iff _ _ _).1 heq) (hTres i hi j hj hne)
  have hcard : (T.image (fun i : Fin s => ((a i : ℤ) : ZMod p))).card = T.card :=
    Finset.card_image_of_injOn hinj
  have hTle : T.card ≤ p := by
    have hsub : T.image (fun i : Fin s => ((a i : ℤ) : ZMod p))
        ⊆ (Finset.univ : Finset (ZMod p)) :=
      Finset.image_subset_iff.2 fun i _ => Finset.mem_univ _
    calc T.card = (T.image (fun i : Fin s => ((a i : ℤ) : ZMod p))).card := hcard.symm
      _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card hsub
      _ = p := by rw [Finset.card_univ, ZMod.card]
  -- ② 点块避开满块残差
  have hQres : ∀ i ∈ T, ∀ j ∈ Q, ¬ (a j ≡ a i [ZMOD (p : ℕ)]) := by
    intro i hi j hj hae
    rw [Int.modEq_iff_dvd] at hae
    obtain ⟨m, hm, hpriv⟩ := hess j
    simp only [MemAP] at hm
    obtain ⟨k, hk⟩ := hm
    obtain ⟨u, hu⟩ := hae
    have hai : a i = a j + (p : ℤ) * u := by linarith
    have hme : m ≡ a i [ZMOD (p : ℕ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨u - (p : ℤ) * k, ?_⟩
      rw [hk, hai, (hmemQ j).1 hj]
      push_cast [Nat.cast_pow, Nat.cast_mul]
      ring
    rw [← (hmemT i).1 hi] at hme
    exact hpriv i (hdisjne i hi j hj) (memAP_of_modEq (a := a) (d := d) (i := i) (m := m) hme)
  -- ④ 点块存在（否则 lcm = p ≠ p²）
  have hQne : Q ≠ ∅ := by
    intro hQe
    have hall : ∀ i, d i = p := by
      intro i
      rcases hcls i with h | h
      · exact h
      · exact absurd ((hmemQ i).2 h) (by rw [hQe]; simp)
    have hle : lcmDiff d ∣ p := Finset.lcm_dvd (fun i _ => by rw [hall i])
    obtain ⟨i₀, -⟩ := hcover (0 : ℤ)
    have hge : p ∣ lcmDiff d := (hall i₀) ▸ dvd_lcmDiff i₀
    have hEq : lcmDiff d = p := Nat.dvd_antisymm hle hge
    rw [hEq, pow_two] at hn
    have hz : p * (p - 1) = 0 := by nlinarith [hn]
    rcases Nat.mul_eq_zero.1 hz with h | h
    · exact absurd h hp.pos.ne'
    · exact absurd (by omega : p = 1) hp.ne_one
  -- ④' 于是 t < p
  have hTlt : T.card < p := by
    by_contra hc
    push Not at hc
    have hTeq : T.card = p := by omega
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hQne
    have hmem : ((a j : ℤ) : ZMod p) ∈ T.image (fun i : Fin s => ((a i : ℤ) : ZMod p)) := by
      by_contra hmem0
      have hsub : T.image (fun i : Fin s => ((a i : ℤ) : ZMod p))
          ⊆ (Finset.univ (α := ZMod p)).erase ((a j : ℤ) : ZMod p) := by
        intro x hx
        obtain ⟨i, hiT, hAI⟩ := Finset.mem_image.1 hx
        rw [Finset.mem_erase]
        refine ⟨fun he => hQres i hiT j hj (Int.ModEq.symm
          ((ZMod.intCast_eq_intCast_iff _ _ _).1 (by rw [he] at hAI; exact hAI))),
          Finset.mem_univ _⟩
      have hle2 := Finset.card_le_card hsub
      have hpp : 0 < p := hp.pos
      rw [hcard, hTeq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ZMod.card] at hle2
      omega
    obtain ⟨i, hiT, hAI⟩ := Finset.mem_image.1 hmem
    exact hQres i hiT j hj ((ZMod.intCast_eq_intCast_iff _ _ _).1 hAI.symm)
  -- T 内块两两不交
  have hbij : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ x, x ∈ Block a d i → x ∉ Block a d j := by
    intro i hi j hj hij x hxI hxJ
    obtain ⟨m, hmx⟩ := ZMod.intCast_surjective x
    rw [← hmx] at hxI hxJ
    have hmI : MemAP a d i m := (mem_block_iff hd i).2 hxI
    have hmJ : MemAP a d j m := (mem_block_iff hd j).2 hxJ
    simp only [MemAP] at hmI hmJ
    rw [(hmemT i).1 hi] at hmI
    rw [(hmemT j).1 hj] at hmJ
    obtain ⟨c, hcI⟩ := hmI
    obtain ⟨e, hcJ⟩ := hmJ
    have hmod : a i ≡ a j [ZMOD (p : ℕ)] := by
      rw [Int.modEq_iff_dvd]
      have h1 : a i = m - (p : ℤ) * c := by rw [hcI]; ring
      have h2 : a j = m - (p : ℤ) * e := by rw [hcJ]; ring
      rw [h1, h2]
      exact ⟨c - e, by ring⟩
    exact absurd hmod (hTres i hi j hj hij)
  -- ③ 无满块残差上的类全部由点块覆盖
  have : NeZero (lcmDiff d) := ⟨ne_of_gt (lcmDiff_pos hd)⟩
  set U : Finset (ZMod (lcmDiff d)) := T.biUnion (fun i => Block a d i) with hUdef
  have hpair : (T : Set (Fin s)).PairwiseDisjoint (fun i : Fin s => Block a d i) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.2 fun x hx₁ hx₂ => ?_
    exact hbij i hi j hj hij x hx₁ hx₂
  have hUcard : U.card = T.card * p := by
    rw [hUdef, Finset.card_biUnion hpair]
    have hsum : ∑ i ∈ T, (Block a d i).card = ∑ _i ∈ T, p := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hdi := (hmemT i).1 hi
      have hc := card_block (a := a) hd i
      rw [hc, hdi, ← hp2]
      exact Nat.mul_div_cancel_left _ hp.pos
    rw [hsum, Finset.sum_const, smul_eq_mul]
  have hYsub : Uᶜ ⊆ Q.image (fun j => (a j : ZMod (lcmDiff d))) := by
    intro x hx
    obtain ⟨i, hi⟩ := cover_block hd hcover x
    by_cases hiT : i ∈ T
    · refine absurd (Finset.mem_biUnion.2 ⟨i, hiT, hi⟩) ?_
      rw [hUdef] at hx
      exact Finset.mem_compl.1 hx
    · have hiQ : i ∈ Q := by
        rw [hmemQ]
        rw [hmemT] at hiT
        rcases hcls i with h | h
        · exact absurd h hiT
        · exact h
      refine Finset.mem_image.2 ⟨i, hiQ, ?_⟩
      obtain ⟨m, hmx⟩ := ZMod.intCast_surjective x
      rw [← hmx] at hi
      have hxI : MemAP a d i m := (mem_block_iff hd i).2 hi
      simp only [MemAP] at hxI
      rw [(hmemQ i).1 hiQ] at hxI
      obtain ⟨k, hkx⟩ := hxI
      have hc0 : ((p * p : ℕ) : ZMod (lcmDiff d)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact (by rw [hp2] : lcmDiff d ∣ p * p)
      rw [← hmx, hkx]
      push_cast [Nat.cast_mul] at hc0 ⊢
      rw [hc0, zero_mul, add_zero]
  -- 计数与收尾
  have hYcard : Uᶜ.card = p * (p - T.card) := by
    rw [Finset.card_compl, ZMod.card, hUcard, ← hp2, Nat.mul_sub, Nat.mul_comm T.card p]
  have hQge : p * (p - T.card) ≤ Q.card := by
    calc p * (p - T.card) = Uᶜ.card := hYcard.symm
      _ ≤ (Q.image (fun j => (a j : ZMod (lcmDiff d)))).card :=
          Finset.card_le_card (fun x hx => hYsub hx)
      _ ≤ Q.card := Finset.card_image_le
  rw [hn, bound_prime_pow hp 2, hspl]
  have key : p * (p - T.card) + T.card ≥ 1 + 2 * (p - 1) := by
    have h2 : T.card + 1 ≤ p := by omega
    obtain ⟨d, hpe⟩ : ∃ d : ℕ, p = T.card + 1 + d := ⟨p - (T.card + 1), by omega⟩
    have hp1 : p - 1 = T.card + d := by omega
    have hpT : p - T.card = 1 + d := by omega
    rw [hpT, hp1]
    nlinarith [sq_nonneg d, mul_nonneg (Nat.zero_le T.card) (Nat.zero_le d)]
  omega

/-! ## 降幂机器（一）：ℤ 层纤维构造

把 ℤ 按模 p 的残差分成 p 根纤维；纤维内的子族首项 a'_i = (a_i − c)/p、
公差 d'_i = d_i / p。桥引理把纤维内的成员关系翻译回原族（坐标 t ↔ c + p·t），
覆盖与独占随即整体下降。 -/

/-- 模 p 残差为 c 的纤维（子族） -/
abbrev Fiber {ι : Type*} (p : ℕ) (a : ι → ℤ) (c : ℤ) : Type _ :=
  {i : ι // (p : ℤ) ∣ a i - c}

/-- 纤维子族的首项：a'_i = (a_i − c)/p -/
def fibA {ι : Type*} (p : ℕ) (a : ι → ℤ) (c : ℤ) : Fiber p a c → ℤ :=
  fun i => (a i.1 - c) / (p : ℤ)

/-- 纤维子族的公差：d'_i = d_i / p -/
def fibD {ι : Type*} (p : ℕ) (a : ι → ℤ) (c : ℤ) (d : ι → ℕ) : Fiber p a c → ℕ :=
  fun i => d i.1 / p

instance fibFintype {ι : Type*} [Fintype ι] (p : ℕ) (a : ι → ℤ) (c : ℤ) :
    Fintype (Fiber p a c) := inferInstance

/-- 【桥引理】纤维内成员关系 ⟺ 原族成员关系：t ∈ P'_i ⟺ c + p·t ∈ P_i -/
theorem fiber_memAP_iff {ι : Type*} {p : ℕ} (hp : p.Prime) {a : ι → ℤ} {d : ι → ℕ}
    (hpd : ∀ i, p ∣ d i) (c : ℤ) (i : Fiber p a c) (t : ℤ) :
    MemAP (fibA p a c) (fibD p a c d) i t ↔ MemAP a d i.1 (c + (p : ℤ) * t) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : (p : ℤ) * fibA p a c i = a i.1 - c := by
    rw [fibA]
    exact Int.mul_ediv_cancel' i.2
  have h2 : (p : ℤ) * ((fibD p a c d i : ℕ) : ℤ) = (d i.1 : ℤ) := by
    rw [fibD]
    exact_mod_cast Nat.mul_div_cancel' (hpd i.1)
  have hexp : ∀ k : ℤ, (p : ℤ) * (fibA p a c i + ((fibD p a c d i : ℕ) : ℤ) * k) =
      (p : ℤ) * fibA p a c i + (p : ℤ) * ((fibD p a c d i : ℕ) : ℤ) * k := fun k => by ring
  have h2k : ∀ k : ℤ, (p : ℤ) * ((fibD p a c d i : ℕ) : ℤ) * k = (d i.1 : ℤ) * k :=
    fun k => by rw [h2]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk, hexp k, h1, h2k k]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    refine mul_left_cancel₀ hp0 ?_
    rw [hexp k, h1, h2k k]
    linarith

/-- 覆盖下降：原族覆盖 ℤ ⟹ 每根纤维的子族覆盖 ℤ -/
theorem fiber_cover {ι : Type*} {p : ℕ} (hp : p.Prime) {a : ι → ℤ} {d : ι → ℕ}
    (hpd : ∀ i, p ∣ d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m) (c : ℤ) :
    ∀ t : ℤ, ∃ i : Fiber p a c, MemAP (fibA p a c) (fibD p a c d) i t := by
  intro t
  obtain ⟨i, hi⟩ := hcover (c + (p : ℤ) * t)
  have hdiv_d : (p : ℤ) ∣ (d i : ℤ) := by
    obtain ⟨q, hq⟩ := hpd i
    exact ⟨(q : ℤ), by exact_mod_cast hq⟩
  have hmem : (p : ℤ) ∣ a i - c := by
    obtain ⟨k, hk⟩ := hi
    have hpk : (p : ℤ) ∣ (d i : ℤ) * k := dvd_mul_of_dvd_left hdiv_d k
    have hEq : a i - c = (p : ℤ) * t - (d i : ℤ) * k := by linarith
    rw [hEq]
    exact dvd_sub (dvd_mul_right _ _) hpk
  exact ⟨⟨i, hmem⟩, (fiber_memAP_iff hp hpd c ⟨i, hmem⟩ t).2 hi⟩

/-- 独占下降：原族中 i 的独占数 ⟹ 其纤维坐标在子族中独占 -/
theorem fiber_essential {ι : Type*} {p : ℕ} (hp : p.Prime) {a : ι → ℤ} {d : ι → ℕ}
    (hpd : ∀ i, p ∣ d i) (c : ℤ)
    (hess : ∀ i : ι, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m)
    (i : Fiber p a c) :
    ∃ t, MemAP (fibA p a c) (fibD p a c d) i t ∧
      ∀ j : Fiber p a c, j ≠ i → ¬ MemAP (fibA p a c) (fibD p a c d) j t := by
  obtain ⟨m, hm, hpriv⟩ := hess i.1
  have hdiv_d : (p : ℤ) ∣ (d i.1 : ℤ) := by
    obtain ⟨q, hq⟩ := hpd i.1
    exact ⟨(q : ℤ), by exact_mod_cast hq⟩
  have hdiv : (p : ℤ) ∣ m - c := by
    obtain ⟨k, hk⟩ := hm
    have : m - c = (a i.1 - c) + (d i.1 : ℤ) * k := by linarith
    rw [this]
    exact dvd_add i.2 (dvd_mul_of_dvd_left hdiv_d k)
  have hkey : c + (p : ℤ) * ((m - c) / (p : ℤ)) = m := by
    rw [Int.mul_ediv_cancel' hdiv]
    ring
  refine ⟨(m - c) / (p : ℤ), ?_, ?_⟩
  · rw [fiber_memAP_iff hp hpd c i ((m - c) / (p : ℤ)), hkey]
    exact hm
  · intro j hj hmem
    rw [fiber_memAP_iff hp hpd c j ((m - c) / (p : ℤ)), hkey] at hmem
    exact hpriv j.1 (fun hje => hj (Subtype.ext hje)) hmem

/-- p^k / p = p^{k−1}（k ≥ 1） -/
theorem pow_div_self {p k : ℕ} (hp : 0 < p) (hk : 1 ≤ k) : p ^ k / p = p ^ (k - 1) := by
  have hk' : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk', Nat.pow_succ']
  exact Nat.mul_div_cancel_left _ hp

/-! ## 降幂机器（二）：lcm 簿记 -/

/-- 上界：每根纤维的子族 lcm 整除 p^{k−1} -/
theorem fibD_lcm_dvd {ι : Type*} [Fintype ι] {p k : ℕ} (hp : p.Prime) {a : ι → ℤ}
    {d : ι → ℕ} {c : ℤ} (heq : lcmDiff d = p ^ k) (hpd : ∀ i, p ∣ d i) :
    lcmDiff (fibD p a c d) ∣ p ^ (k - 1) := by
  refine Finset.lcm_dvd (fun i _ => ?_)
  obtain ⟨j, hjk, hjd⟩ := (Nat.dvd_prime_pow hp).1 (heq ▸ dvd_lcmDiff i.1)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      rw [h, Nat.pow_zero] at hjd
      exact hp.ne_one (Nat.dvd_one.1 (hjd ▸ hpd i.1))
    · exact h
  rw [fibD, hjd, pow_div_self hp.pos hj1]
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 (by omega)

/-- 取等：含公差 p^k 的纤维，其子族 lcm 恰为 p^{k−1} -/
theorem fibD_lcm_eq {ι : Type*} [Fintype ι] {p k : ℕ} (hp : p.Prime) {a : ι → ℤ}
    {d : ι → ℕ} {c : ℤ} (heq : lcmDiff d = p ^ k) (hpd : ∀ i, p ∣ d i)
    (hk : 1 ≤ k) (i₀ : Fiber p a c) (hi₀ : d i₀.1 = p ^ k) :
    lcmDiff (fibD p a c d) = p ^ (k - 1) := by
  refine Nat.dvd_antisymm (fibD_lcm_dvd hp heq hpd) ?_
  have h1 : fibD p a c d i₀ ∣ lcmDiff (fibD p a c d) := dvd_lcmDiff i₀
  rw [fibD, hi₀, pow_div_self hp.pos hk] at h1
  exact h1

/-- 存在性：lcmDiff d = p^k（k ≥ 1）时，必有某个公差恰为 p^k -/
theorem exists_max_dvd {ι : Type*} [Fintype ι] {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {d : ι → ℕ} (heq : lcmDiff d = p ^ k) : ∃ i, d i = p ^ k := by
  by_contra h
  push Not at h
  have hdvd : ∀ i, d i ∣ p ^ (k - 1) := by
    intro i
    obtain ⟨j, hjk, hjd⟩ := (Nat.dvd_prime_pow hp).1 (heq ▸ dvd_lcmDiff i)
    have hjne : j ≠ k := fun hjk' => h i (by rw [hjd, hjk'])
    rw [hjd]
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 (by omega)
  have hpk : p ^ k ∣ p ^ (k - 1) := by
    rw [← heq]
    exact Finset.lcm_dvd (fun i _ => hdvd i)
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hpk
  omega

/-! ## 降幂机器（三）：纤维分割

模 p 的残差给出一个映射 ι → Fin p，纤维即其各层原像。由此把 card ι 拆成
p 根纤维的基数之和（下面 card_eq_sum_fiber）。 -/

/-- 整数 x 模 p 的规范残差，取值于 Fin p -/
def residue (p : ℕ) (hp : 0 < p) (x : ℤ) : Fin p :=
  ⟨(x % (p : ℤ)).toNat, by
    have h1 : 0 ≤ x % (p : ℤ) := Int.emod_nonneg x (by exact_mod_cast hp.ne')
    have h2 : x % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos x (by exact_mod_cast hp)
    have h3 : ((x % (p : ℤ)).toNat : ℤ) < (p : ℤ) := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3⟩

/-- 引理：residue 的取值还原为 ℤ 的取模结果（`(residue p hp x : ℕ) = x % p`）。 -/
theorem residue_cast (p : ℕ) (hp : 0 < p) (x : ℤ) :
    ((residue p hp x : ℕ) : ℤ) = x % (p : ℤ) := by
  have h1 : 0 ≤ x % (p : ℤ) := Int.emod_nonneg x (by exact_mod_cast hp.ne')
  simp only [residue]
  rw [Int.toNat_of_nonneg h1]

/-- 引理：residue 非负。 -/
theorem residue_nonneg (p : ℕ) (hp : 0 < p) (x : ℤ) : 0 ≤ ((residue p hp x : ℕ) : ℤ) := by
  rw [residue_cast p hp x]
  exact Int.emod_nonneg x (by exact_mod_cast hp.ne')

/-- 引理：residue < p。 -/
theorem residue_lt (p : ℕ) (hp : 0 < p) (x : ℤ) : ((residue p hp x : ℕ) : ℤ) < (p : ℤ) := by
  rw [residue_cast p hp x]
  exact Int.emod_lt_of_pos x (by exact_mod_cast hp)

/-- 每个下标都落在自己残差所在的纤维里 -/
theorem mem_fiber_residue {ι : Type*} {p : ℕ} (hp : p.Prime) (a : ι → ℤ) (i : ι) :
    (p : ℤ) ∣ a i - ((residue p hp.pos (a i) : ℕ) : ℤ) := by
  rw [residue_cast p hp.pos (a i)]
  exact Int.modEq_iff_dvd.1 (Int.mod_modEq (a i) (p : ℤ))

/-- 残差在 [0,p) 内的代表性：一个下标至多属于一根纤维 -/
theorem fiber_residue_unique {ι : Type*} {p : ℕ} {a : ι → ℤ} {i : ι} {c c' : ℤ}
    (hc : 0 ≤ c) (hc' : c < (p : ℤ)) (hd : 0 ≤ c') (hd' : c' < (p : ℤ))
    (h1 : (p : ℤ) ∣ a i - c) (h2 : (p : ℤ) ∣ a i - c') : c = c' := by
  have hmod : c ≡ c' [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have hh : (p : ℤ) ∣ c - c' := by
      have h := dvd_sub h2 h1
      rwa [show (a i - c') - (a i - c) = c - c' by ring] at h
    simpa using Int.dvd_neg.mpr hh
  have := hmod
  rw [Int.ModEq] at this
  rwa [Int.emod_eq_of_lt hc hc', Int.emod_eq_of_lt hd hd'] at this

/-- 纤维归属 ⟺ 残差等于该代表元 -/
theorem residue_eq_iff_dvd {ι : Type*} {p : ℕ} (hp : p.Prime) (a : ι → ℤ) (c : Fin p) (i : ι) :
    residue p hp.pos (a i) = c ↔ (p : ℤ) ∣ a i - ((c : ℕ) : ℤ) := by
  constructor
  · intro h
    rw [← h]
    exact mem_fiber_residue hp a i
  · intro h
    refine Fin.ext ?_
    have hh := fiber_residue_unique (residue_nonneg p hp.pos (a i)) (residue_lt p hp.pos (a i))
      (Nat.cast_nonneg (c : ℕ)) (by exact_mod_cast c.isLt) (mem_fiber_residue hp a i) h
    exact_mod_cast hh

/-- 【纤维分割】card ι = Σ_c card (纤维 c) -/
theorem card_eq_sum_fiber {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime) (a : ι → ℤ) :
    Fintype.card ι = ∑ c : Fin p, Fintype.card (Fiber p a ((c : ℕ) : ℤ)) := by
  have h1 : (Finset.univ : Finset ι).card
      = ∑ c ∈ (Finset.univ : Finset (Fin p)),
          ((Finset.univ : Finset ι).filter (fun i => residue p hp.pos (a i) = c)).card :=
    Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι))
      (t := (Finset.univ : Finset (Fin p))) (f := fun i => residue p hp.pos (a i))
      (by intro x _; exact Finset.mem_univ _)
  rw [Finset.card_univ] at h1
  rw [h1]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact residue_eq_iff_dvd hp a c i

/-! ## 降幂机器（四）：组装 -/

/-- 【降幂主步】n = p^k（k ≥ 1）：把族按 mod p 纤维拆开，逐纤维套用归纳假设再求和。 -/
theorem case_prime_pow_step.{u} {ι : Type u} [Fintype ι] {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {a : ι → ℤ} {d : ι → ℕ} (heq : lcmDiff d = p ^ k) (hd : ∀ i, 0 < d i)
    (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m) (hess : ∀ i, Essential a d i)
    (IH : ∀ j < k, ∀ (ι' : Type u) [Fintype ι'] (a' : ι' → ℤ) (d' : ι' → ℕ),
      lcmDiff d' = p ^ j → (∀ i, 0 < d' i) → (∀ m', ∃ i, MemAP a' d' i m') →
      (∀ i, Essential a' d' i) → Fintype.card ι' ≥ bound (p ^ j)) :
    Fintype.card ι ≥ bound (p ^ k) := by
  have hnl : 1 < lcmDiff d := by
    rw [heq]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have hpd : ∀ i, p ∣ d i := by
    intro i
    obtain ⟨j, hjk, hjd⟩ := (Nat.dvd_prime_pow hp).1 (heq ▸ dvd_lcmDiff i)
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exfalso
        rw [h, Nat.pow_zero] at hjd
        exact (no_diff_one hcover hess hnl i) hjd
      · exact h
    rw [hjd]
    exact dvd_pow_self p (by omega)
  have hd_c : ∀ (c : Fin p) (i : Fiber p a ((c:ℕ):ℤ)), 0 < fibD p a ((c:ℕ):ℤ) d i := by
    intro c i
    exact Nat.div_pos (Nat.le_of_dvd (hd i.1) (hpd i.1)) hp.pos
  classical
  have hjf : ∀ c : Fin p, ∃ j, lcmDiff (fibD p a ((c:ℕ):ℤ) d) = p ^ j := by
    intro c
    obtain ⟨j, _, hjd⟩ := (Nat.dvd_prime_pow hp).1
      (fibD_lcm_dvd (a := a) (d := d) hp heq hpd (c := ((c:ℕ):ℤ)))
    exact ⟨j, hjd⟩
  let jf : Fin p → ℕ := fun c => Classical.choose (hjf c)
  have hjf_spec : ∀ c : Fin p, lcmDiff (fibD p a ((c:ℕ):ℤ) d) = p ^ (jf c) :=
    fun c => Classical.choose_spec (hjf c)
  have hjf_le : ∀ c : Fin p, jf c ≤ k - 1 := by
    intro c
    have h := fibD_lcm_dvd (a := a) (d := d) hp heq hpd (c := ((c:ℕ):ℤ))
    rw [hjf_spec c] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hIH : ∀ c : Fin p, Fintype.card (Fiber p a ((c:ℕ):ℤ))
      ≥ bound (lcmDiff (fibD p a ((c:ℕ):ℤ) d)) := by
    intro c
    have hcov_c : ∀ t : ℤ, ∃ i : Fiber p a ((c:ℕ):ℤ),
        MemAP (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i t :=
      fiber_cover (a := a) (d := d) hp hpd hcover ((c:ℕ):ℤ)
    have hess_c : ∀ i : Fiber p a ((c:ℕ):ℤ),
        Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i :=
      fun i => fiber_essential (a := a) (d := d) hp hpd ((c:ℕ):ℤ) hess i
    rw [hjf_spec c]
    refine IH (jf c) (by have := hjf_le c; omega) (Fiber p a ((c:ℕ):ℤ)) (fibA p a ((c:ℕ):ℤ))
      (fibD p a ((c:ℕ):ℤ) d) (hjf_spec c) (hd_c c) hcov_c hess_c
  have hexp : k - 1 ≤ ∑ c : Fin p, jf c := by
    obtain ⟨i₀, hi₀⟩ := exists_max_dvd hp hk heq
    have hmem₀ : (p : ℤ) ∣ a i₀ - ((residue p hp.pos (a i₀) : ℕ) : ℤ) :=
      mem_fiber_residue hp a i₀
    have hfib₀ : lcmDiff (fibD p a ((residue p hp.pos (a i₀) : ℕ) : ℤ) d) = p ^ (k - 1) :=
      fibD_lcm_eq (a := a) (d := d) hp heq hpd hk ⟨i₀, hmem₀⟩ hi₀
    have hj₀ : jf (residue p hp.pos (a i₀)) = k - 1 := by
      have h := hjf_spec (residue p hp.pos (a i₀))
      rw [hfib₀] at h
      exact (Nat.pow_right_injective hp.two_le h).symm
    calc k - 1 = jf (residue p hp.pos (a i₀)) := hj₀.symm
      _ ≤ ∑ c : Fin p, jf c :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
  have hfinal : ∑ c : Fin p, (1 + jf c * (p - 1)) = p + (∑ c : Fin p, jf c) * (p - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  rw [bound_prime_pow hp k, card_eq_sum_fiber hp a]
  calc ∑ c : Fin p, Fintype.card (Fiber p a ((c:ℕ):ℤ))
      ≥ ∑ c : Fin p, (1 + jf c * (p - 1)) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        have := hIH c
        rw [hjf_spec c] at this
        rwa [bound_prime_pow hp (jf c)] at this
    _ = p + (∑ c : Fin p, jf c) * (p - 1) := hfinal
    _ ≥ p + (k - 1) * (p - 1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hexp) p
    _ = 1 + k * (p - 1) := by
        have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
        have h1 : k * (p - 1) = (k - 1) * (p - 1) + (p - 1) := by
          conv_lhs => rw [hk1, Nat.add_mul, one_mul]
        have hpp : 0 < p := hp.pos
        omega

/-! ## 蓝图·素数幂：n = p^k -/

/-- 【蓝图·素数幂】n = p^k 时 s ≥ 1 + k(p−1) = bound (p^k)。
    证明路线（数学上已论证完毕，形式化进行中）：
    ① 公差 1 被排除（no_diff_one），故所有 d_i = p^{β_i}，β_i ≥ 1；
    ② 按 mod p 分成 p 根纤维 F_c（c ∈ ZMod p）；每块整体落在一根纤维里；
    ③ 纤维内坐标代换 x = c + p·t 把 F_c 等同于 ZMod p^{k−1}，
       纤维内的块变为差 p^{β_i−1} 的类，覆盖 F_c 且独占性保持；
    ④ 归纳假设：s_c ≥ 1 + (max_c − 1)(p−1)，max_c = 纤维 c 内最大 β；
    ⑤ 求和 s = Σ s_c ≥ p + (p−1)·Σ(max_c−1) ≥ p + (p−1)(k−1) = 1 + k(p−1)。 -/
theorem case_prime_pow.{u} {ι : Type u} [Fintype ι] {p : ℕ} {k : ℕ}
    (hp : p.Prime) {a : ι → ℤ} {d : ι → ℕ}
    (heq : lcmDiff d = p ^ k) (hd : ∀ i, 0 < d i)
    (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m) :
    Fintype.card ι ≥ bound (p ^ k) := by
  have key : ∀ k' : ℕ, ∀ (ι' : Type u) [Fintype ι'] (a' : ι' → ℤ) (d' : ι' → ℕ),
      lcmDiff d' = p ^ k' → (∀ i, 0 < d' i) → (∀ m : ℤ, ∃ i, MemAP a' d' i m) →
      (∀ i, ∃ m, MemAP a' d' i m ∧ ∀ j, j ≠ i → ¬ MemAP a' d' j m) →
      Fintype.card ι' ≥ bound (p ^ k') := by
    intro k'
    refine Nat.strongRecOn k' (fun k' ih => ?_)
    intro ι' _inst a' d' heq' hd' hcover' hess'
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · rw [Nat.pow_zero]
      simpa using base_case hcover'
    · refine case_prime_pow_step hp hk' heq' hd' hcover' hess' ?_
      intro j hj ι'' _inst a'' d'' heq'' hd'' hcov'' hess''
      exact ih j hj ι'' a'' d'' heq'' hd'' hcov'' hess''
  exact key k ι a d heq hd hcover hess

/-! ## 蓝图·元情况：n 为素数 -/

/-- 素数的下界就是它本身 -/
theorem bound_prime {p : ℕ} (hp : p.Prime) : bound p = p := by
  have h1 : p.factorization p = 1 := by
    rw [hp.factorization]
    simp
  have h2 : p.primeFactors = {p} := hp.primeFactors
  have h3 : bound p = 1 + ∑ q ∈ {p}, p.factorization q * (q - 1) := by
    rw [bound, h2]
  have hpos : 0 < p := hp.pos
  rw [h3, Finset.sum_singleton, h1, one_mul]
  omega

/-- 【元情况】n 为素数时 s ≥ n = bound n。
    论证：每个公差整除素数 n，故为 1 或 n；公差为 1 的列等于 ℤ，
    会吞掉其他列的独占数（s = 1 则与 lcm = n 矛盾），故所有公差 = n；
    每块是单个剩余类（card_block），覆盖全部 n 个剩余类 ⟹ s ≥ n。 -/
theorem case_prime {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    {n : ℕ} (hn : n.Prime) (heq : lcmDiff d = n) (hd : ∀ i, 0 < d i)
    (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m) :
    Fintype.card ι ≥ bound n := by
  subst heq
  have hbound : bound (lcmDiff d) = lcmDiff d := bound_prime hn
  -- 所有公差 = lcmDiff d
  have hall : ∀ i, d i = lcmDiff d := by
    intro i
    rcases (Nat.dvd_prime hn).1 (dvd_lcmDiff i) with h1 | h1
    · exfalso
      by_cases hcard : Fintype.card ι = 1
      · have : Subsingleton ι :=
          Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
        have hle : lcmDiff d ∣ d i :=
          Finset.lcm_dvd (fun j _ => by rw [Subsingleton.elim j i])
        have heq' : lcmDiff d = d i := Nat.dvd_antisymm hle (dvd_lcmDiff i)
        exact hn.ne_one (heq'.trans h1)
      · have h1' : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
        have h2 : 1 < Fintype.card ι := by omega
        obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card h2 i
        obtain ⟨m, hm, hpriv⟩ := hess j
        -- d i = 1 ⟹ P_i = ℤ ⟹ m ∈ P_i，与 m 的独占性矛盾
        have hmi : MemAP a d i m := ⟨m - a i, by rw [h1]; ring⟩
        exact hpriv i (Ne.symm hj) hmi
    · exact h1
  -- 每块是单个剩余类：|Block i| = lcmDiff d / d i = 1
  have hcard : ∀ i, (Block a d i).card = 1 := by
    intro i
    have hc := card_block (a := a) hd i
    rw [hall i, Nat.div_self hn.pos] at hc
    exact hc
  have : NeZero (lcmDiff d) := ⟨ne_of_gt hn.pos⟩
  have hcov : ∀ x : ZMod (lcmDiff d), ∃ i, x ∈ Block a d i := cover_block hd hcover
  -- 覆盖 n 个剩余类，每块大小 1 ⟹ s ≥ n
  have hsub : Finset.univ ⊆ Finset.univ.biUnion (fun i : ι => Block a d i) := by
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩
  have hUle : (Finset.univ.biUnion (fun i : ι => Block a d i)).card ≤ Fintype.card ι := by
    calc (Finset.univ.biUnion (fun i : ι => Block a d i)).card
        ≤ ∑ i : ι, (Block a d i).card := Finset.card_biUnion_le
      _ = ∑ _i : ι, 1 := Finset.sum_congr rfl fun i _ => by rw [hcard i]
      _ = Fintype.card ι := by simp
  have h1 : lcmDiff d ≤ (Finset.univ.biUnion (fun i : ι => Block a d i)).card := by
    have hcu : Fintype.card (ZMod (lcmDiff d))
        ≤ (Finset.univ.biUnion fun i : ι => Block a d i).card := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card hsub
    rwa [ZMod.card] at hcu
  rw [hbound]
  linarith

/-! ## 蓝图·拆n簿记：素数幂逮块 -/

/-- 【拆n簿记】素数幂整除二元 lcm 当且仅当整除其中之一（q 素） -/
theorem prime_pow_dvd_lcm_iff {q : ℕ} (hq : q.Prime) (e : ℕ) (a b : ℕ) :
    q ^ e ∣ Nat.lcm a b ↔ q ^ e ∣ a ∨ q ^ e ∣ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  rw [hq.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero (by omega) (by omega)),
    Nat.factorization_lcm (by omega) (by omega)]
  have hsup : (a.factorization ⊔ b.factorization) q
      = max (a.factorization q) (b.factorization q) := by simp
  rw [hsup, le_max_iff, hq.pow_dvd_iff_le_factorization (by omega),
    hq.pow_dvd_iff_le_factorization (by omega)]

/-- 【拆n簿记】素数幂整除有限族 lcm 就能逮住单块（q 素，e ≥ 1） -/
theorem exists_of_prime_pow_dvd_lcm_finset {q : ℕ} (hq : q.Prime) {e : ℕ} (he : 0 < e)
    {β : Type*} [DecidableEq β] (s : Finset β) (f : β → ℕ)
    (h : q ^ e ∣ s.lcm f) : ∃ b ∈ s, q ^ e ∣ f b := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.lcm_empty] at h
    have h1 : q ^ e = 1 := Nat.dvd_one.1 h
    have h2 : 1 < q ^ e := Nat.one_lt_pow (by omega) hq.one_lt
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  | insert b s hb ih =>
    rw [Finset.lcm_insert] at h
    rcases (prime_pow_dvd_lcm_iff hq e (f b) (s.lcm f)).1 h with h1 | h1
    · exact ⟨b, Finset.mem_insert_self b s, h1⟩
    · obtain ⟨c, hc, hc2⟩ := ih h1
      exact ⟨c, Finset.mem_insert_of_mem hc, hc2⟩

/-- 【拆n簿记】q^e ∣ lcmDiff d ⇒ ∃ i, q^e ∣ d i（q 素；e = 0 时平凡取任意块） -/
theorem exists_of_prime_pow_dvd_lcmDiff {ι : Type*} [Fintype ι] {q : ℕ} (hq : q.Prime)
    (e : ℕ) (hne : Nonempty ι) (d : ι → ℕ) (h : q ^ e ∣ lcmDiff d) : ∃ i, q ^ e ∣ d i := by
  classical
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨Classical.arbitrary ι, Nat.one_dvd _⟩
  · obtain ⟨i, _, hi⟩ := exists_of_prime_pow_dvd_lcm_finset hq he Finset.univ d h
    exact ⟨i, hi⟩

/-- 【拆n簿记】lcmDiff d = p^k·m（p ∤ m）时，各块公差的 p-指数不超过 k -/
theorem factorization_p_le_of_lcmDiff {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (d : ι → ℕ) (hd : ∀ i, 0 < d i) (heq : lcmDiff d = p ^ k * m) (i : ι) :
    (d i).factorization p ≤ k := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun hc => hpm (by rw [hc]; exact dvd_zero p))
  have hdvd : d i ∣ p ^ k * m := by rw [← heq]; exact dvd_lcmDiff i
  by_contra hgt
  push Not at hgt
  have h1 : p ^ (k + 1) ∣ d i :=
    (hp.pow_dvd_iff_le_factorization (ne_of_gt (hd i))).2 (by omega)
  have h2 : p ^ (k + 1) ∣ p ^ k * m := h1.trans hdvd
  have h3 := (hp.pow_dvd_iff_le_factorization
    (Nat.mul_ne_zero (pow_ne_zero k (ne_of_gt hp.pos)) (ne_of_gt hm0))).1 h2
  rw [Nat.factorization_mul (pow_ne_zero k (ne_of_gt hp.pos)) (ne_of_gt hm0),
    Finsupp.add_apply, Nat.factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd hpm] at h3
  omega

/-- 【拆n簿记】lcmDiff d = p^k·m（p ∤ m）时，p-指数 k 被某块取到 -/
theorem exists_factorization_p_eq_of_lcmDiff {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (d : ι → ℕ) (hd : ∀ i, 0 < d i) (hne : Nonempty ι)
    (heq : lcmDiff d = p ^ k * m) : ∃ i, (d i).factorization p = k := by
  have hdvd : p ^ k ∣ lcmDiff d := by rw [heq]; exact dvd_mul_right _ _
  obtain ⟨i, hi⟩ := exists_of_prime_pow_dvd_lcmDiff hp k hne d hdvd
  refine ⟨i, le_antisymm (factorization_p_le_of_lcmDiff hp hpm d hd heq i) ?_⟩
  exact (hp.pow_dvd_iff_le_factorization (ne_of_gt (hd i))).1 hi

/-- 【拆n③极小子覆盖】有限覆盖族中取出基数最小的覆盖子族；最小性 ⇒ 子族内每块
    在子族内有私有点（即子族系统的 Essential）。稀释保持独占，故可直接套 IH。 -/
theorem exists_minimal_subcover {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (hcover : ∀ x : ℤ, ∃ i, MemAP a d i x) :
    ∃ J : Finset ι, (∀ x : ℤ, ∃ i ∈ J, MemAP a d i x) ∧
      ∀ i ∈ J, ∃ t, MemAP a d i t ∧ ∀ j ∈ J, j ≠ i → ¬ MemAP a d j t := by
  classical
  obtain ⟨J₀, hJ₀mem, hmin⟩ :=
    Finset.exists_min_image
      (Finset.univ.filter (fun J : Finset ι => ∀ x : ℤ, ∃ i ∈ J, MemAP a d i x))
      (fun J : Finset ι => J.card)
      ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => by
        obtain ⟨i, hi⟩ := hcover x
        exact ⟨i, Finset.mem_univ _, hi⟩⟩⟩
  have hcov₀ : ∀ x : ℤ, ∃ i ∈ J₀, MemAP a d i x := (Finset.mem_filter.1 hJ₀mem).2
  refine ⟨J₀, hcov₀, ?_⟩
  intro i hi
  by_contra hno
  push Not at hno
  have hcovE : ∀ x : ℤ, ∃ j ∈ J₀.erase i, MemAP a d j x := by
    intro x
    obtain ⟨i', hi'J, hi'mem⟩ := hcov₀ x
    by_cases hie : i' = i
    · subst hie
      obtain ⟨j, hjJ, hjne, hjmem⟩ := hno x hi'mem
      exact ⟨j, Finset.mem_erase.2 ⟨hjne, hjJ⟩, hjmem⟩
    · exact ⟨i', Finset.mem_erase.2 ⟨hie, hi'J⟩, hi'mem⟩
  have hmemE : (J₀.erase i) ∈
      Finset.univ.filter (fun J : Finset ι => ∀ x : ℤ, ∃ i ∈ J, MemAP a d i x) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hcovE⟩
  have hle := hmin (J₀.erase i) hmemE
  have hlt : (J₀.erase i).card < J₀.card := by
    rw [Finset.card_erase_of_mem hi]
    have hcard : 0 < J₀.card := Finset.card_pos.2 ⟨i, hi⟩
    omega
  exact absurd hlt (not_lt.2 hle)

/-- 【拆n③簿记】子族（J 上重标）的 lcm 整除原 lcm -/
theorem lcmDiff_subtype_dvd {ι : Type*} [Fintype ι] (d : ι → ℕ) (J : Finset ι) :
    lcmDiff (fun i : {x : ι // x ∈ J} => d i.val) ∣ lcmDiff d :=
  Finset.lcm_dvd (fun i _ => dvd_lcmDiff i.val)

/-- 【拆n③簿记】子族的 lcm 为正（各块公差为正） -/
theorem lcmDiff_subtype_pos {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (J : Finset ι) : 0 < lcmDiff (fun i : {x : ι // x ∈ J} => d i.val) := by
  have h1 : lcmDiff (fun i : {x : ι // x ∈ J} => d i.val) ≠ 0 := by
    rw [show lcmDiff (fun i : {x : ι // x ∈ J} => d i.val)
        = Finset.univ.lcm (fun i : {x : ι // x ∈ J} => d i.val) from rfl,
      Finset.lcm_ne_zero_iff]
    intro i' _
    exact ne_of_gt (hd i'.val)
  exact Nat.pos_of_ne_zero h1

/-- 【拆n④裂块】p 素、p ∤ d 时（CRT）：模 d 的块与模 p 的剩余类之交
    是某个模 d·p 的 AP。β=0 的块经此裂解进入每根纤维，裂块使块数变多，
    这正是复合情形可加性计数的来源之一。 -/
theorem exists_crt_block {p : ℕ} (hp : p.Prime) {d : ℕ} (hpd : ¬ p ∣ d) (a c : ℤ) :
    ∃ r : ℤ, ∀ x : ℤ, (((d : ℤ) ∣ x - a) ∧ ((p : ℤ) ∣ x - c)) ↔ (((d * p : ℕ) : ℤ) ∣ x - r) := by
  classical
  have hne : NeZero p := ⟨hp.ne_zero⟩
  have hfac : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime d p := Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpd)
  have hdvdadd : ∀ (q y₁ y₂ : ℤ), (q ∣ y₁) → (q ∣ y₂) → (q ∣ y₁ + y₂) := by
    intro q y₁ y₂ hk₁ hk₂
    obtain ⟨k₁, hk₁⟩ := hk₁
    obtain ⟨k₂, hk₂⟩ := hk₂
    exact ⟨k₁ + k₂, by rw [hk₁, hk₂]; ring⟩
  have hdvdsub : ∀ (q y₁ y₂ : ℤ), (q ∣ y₁) → (q ∣ y₂) → (q ∣ y₁ - y₂) := by
    intro q y₁ y₂ hk₁ hk₂
    obtain ⟨k₁, hk₁⟩ := hk₁
    obtain ⟨k₂, hk₂⟩ := hk₂
    exact ⟨k₁ - k₂, by rw [hk₁, hk₂]; ring⟩
  have hd0 : (d : ZMod p) ≠ 0 := by
    intro h
    exact hpd ((ZMod.natCast_eq_zero_iff d p).1 h)
  set u : ZMod p := ((c - a) : ZMod p) / (d : ZMod p) with hudef
  have hu : (d : ZMod p) * u = ((c - a : ℤ) : ZMod p) := by
    rw [hudef, Int.cast_sub]
    exact mul_div_cancel₀ ((c - a) : ZMod p) hd0
  set u₁ : ℕ := u.val with hu₁def
  have hcastu : (((u₁ : ℤ) : ZMod p)) = u := by
    rw [hu₁def, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  have hz : (((d : ℤ) * (u₁ : ℤ) : ℤ) : ZMod p) = ((c - a : ℤ) : ZMod p) := by
    simp only [Int.cast_mul, Int.cast_natCast, hcastu]
    exact hu
  have hkey : ((p : ℤ) ∣ ((d : ℤ) * (u₁ : ℤ)) - (c - a)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (c - a) ((d : ℤ) * (u₁ : ℤ)) p).1 hz.symm
  refine ⟨a + (d : ℤ) * (u₁ : ℤ), fun x => ?_⟩
  set r : ℤ := a + (d : ℤ) * (u₁ : ℤ) with hrdef
  have hdvdra : (d : ℤ) ∣ r - a := ⟨(u₁ : ℤ), by rw [hrdef]; ring⟩
  have hpdvrc : (p : ℤ) ∣ r - c := by
    have h1 : r - c = ((d : ℤ) * (u₁ : ℤ)) - (c - a) := by rw [hrdef]; ring
    rw [h1]
    exact hkey
  have hsplit : ∀ (x : ℤ), x - r = (x - c) - (r - c) := by
    intro x; ring
  constructor
  · rintro ⟨hda, hpc⟩
    have h1 : (d : ℤ) ∣ x - r := by
      have h2 : x - r = (x - a) - (r - a) := by ring
      rw [h2]
      exact hdvdsub _ _ _ hda hdvdra
    have h2 : (p : ℤ) ∣ x - r := by
      rw [hsplit x]
      exact hdvdsub _ _ _ hpc hpdvrc
    obtain ⟨w, hw⟩ := h2
    have h3 : (d : ℤ) ∣ (p : ℤ) * w := by rw [← hw]; exact h1
    have h4 : (d : ℤ) ∣ w := IsCoprime.dvd_of_dvd_mul_left hcop.isCoprime h3
    obtain ⟨w', hw'⟩ := h4
    refine ⟨w', ?_⟩
    rw [hw, hw', Nat.cast_mul]
    ring
  · rintro hdvd
    have hd1 : (d : ℤ) ∣ ((d * p : ℕ) : ℤ) := ⟨(p : ℤ), by rw [Nat.cast_mul]⟩
    have hp1 : (p : ℤ) ∣ ((d * p : ℕ) : ℤ) := ⟨(d : ℤ), by rw [Nat.cast_mul]; ring⟩
    have hda' : (d : ℤ) ∣ x - a := by
      have h2 : (d : ℤ) ∣ x - r := hd1.trans hdvd
      have h3 : x - a = (x - r) + (r - a) := by ring
      rw [h3]
      exact dvd_add h2 hdvdra
    have hpc' : (p : ℤ) ∣ x - c := by
      have h2 : (p : ℤ) ∣ x - r := hp1.trans hdvd
      have h3 : x - c = (x - r) + (r - c) := by ring
      rw [h3]
      exact dvd_add h2 hpdvrc
    exact ⟨hda', hpc'⟩

/-! ## 蓝图·拆n化归：m-投影骨架 -/

/-- 【拆n⑤a】粗化保持成员关系：公差变大（d' ∣ d）则块变大，仍含原块所有点。 -/
theorem MemAP.of_dvd {ι : Type*} {a : ι → ℤ} {d d' : ι → ℕ} (hdd : ∀ i, d' i ∣ d i)
    {i : ι} {x : ℤ} (h : MemAP a d i x) : MemAP a d' i x := by
  obtain ⟨k, hk⟩ := h
  refine ⟨((d i / d' i : ℕ) : ℤ) * k, ?_⟩
  rw [hk]
  have hdd' : (d i : ℤ) = (d' i : ℤ) * ((d i / d' i : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdd i)]
  rw [hdd']
  ring

/-- 【拆n⑤a】粗化保持覆盖。 -/
theorem cover_of_coarsen {ι : Type*} [Fintype ι] {a : ι → ℤ} {d d' : ι → ℕ}
    (hdd : ∀ i, d' i ∣ d i) (hcover : ∀ x : ℤ, ∃ i, MemAP a d i x) :
    ∀ x : ℤ, ∃ i, MemAP a d' i x := fun x => by
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨i, MemAP.of_dvd hdd hi⟩

/-- 【拆n⑤a】公差的 p/m 分解：d i = p^(β i) · μ i，其中 β i ≤ k、μ i ∣ m、p ∤ μ i。
    （β i = (d i).factorization p，μ i = d i / p^(β i)。） -/
theorem exists_mu_split {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) {d : ι → ℕ} (hd : ∀ i, 0 < d i) (heq : lcmDiff d = p ^ k * m) :
    ∃ β μ : ι → ℕ, (∀ i, β i ≤ k) ∧ (∀ i, p ^ β i * μ i = d i) ∧
      (∀ i, μ i ∣ m) ∧ (∀ i, ¬ p ∣ μ i) := by
  classical
  have hpdb : ∀ i, p ^ (d i).factorization p ∣ d i := fun i =>
    (hp.pow_dvd_iff_le_factorization (ne_of_gt (hd i))).2 (le_refl _)
  have hpmu : ∀ i, ¬ p ∣ d i / p ^ (d i).factorization p := by
    intro i hdiv
    have h1 : p ^ ((d i).factorization p + 1) ∣ d i := by
      have h2 : p ^ (d i).factorization p * p ∣
          p ^ (d i).factorization p * (d i / p ^ (d i).factorization p) :=
        mul_dvd_mul_left _ hdiv
      rw [← Nat.pow_succ, Nat.mul_div_cancel' (hpdb i)] at h2
      exact h2
    exact absurd ((hp.pow_dvd_iff_le_factorization (ne_of_gt (hd i))).1 h1) (by omega)
  refine ⟨fun i => (d i).factorization p, fun i => d i / p ^ (d i).factorization p,
    fun i => factorization_p_le_of_lcmDiff hp hpm d hd heq i,
    fun i => Nat.mul_div_cancel' (hpdb i), ?_, hpmu⟩
  intro i
  have hβk := factorization_p_le_of_lcmDiff hp hpm d hd heq i
  have hdv : d i ∣ p ^ k * m := by rw [← heq]; exact dvd_lcmDiff i
  obtain ⟨t, ht⟩ := hdv
  have key : p ^ (k - (d i).factorization p) * m =
      (d i / p ^ (d i).factorization p) * t := by
    have hcan : p ^ (d i).factorization p *
        (p ^ (k - (d i).factorization p) * m) =
        p ^ (d i).factorization p * ((d i / p ^ (d i).factorization p) * t) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hβk,
        ← Nat.mul_assoc, Nat.mul_div_cancel' (hpdb i), ht]
    exact Nat.mul_left_cancel (Nat.pow_pos hp.pos) hcan
  have hcp2 : Nat.Coprime (d i / p ^ (d i).factorization p) p :=
    Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 (hpmu i))
  have hiso : IsCoprime ((d i / p ^ (d i).factorization p : ℕ) : ℤ)
      (((p : ℕ) ^ (k - (d i).factorization p) : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact IsCoprime.pow_right (n := k - (d i).factorization p) (Nat.Coprime.isCoprime hcp2)
  have hEu : (d i / p ^ (d i).factorization p : ℕ) ∣ m := by
    have h4 : ((d i / p ^ (d i).factorization p : ℕ) : ℤ) ∣
        (((p : ℕ) ^ (k - (d i).factorization p) * m : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      have hd0 : (d i / p ^ (d i).factorization p : ℕ) ∣
          p ^ (k - (d i).factorization p) * m :=
        ⟨t, key⟩
      exact_mod_cast hd0
    exact Int.natCast_dvd_natCast.1 (IsCoprime.dvd_of_dvd_mul_left hiso h4)
  exact hEu

/-- 【拆n⑤a】m-投影系统（公差 μ i）的 lcm 恰为 m。 -/
theorem lcmDiff_mu_eq {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) {d : ι → ℕ} (hne : Nonempty ι)
    (heq : lcmDiff d = p ^ k * m) {β μ : ι → ℕ}
    (hmul : ∀ i, p ^ β i * μ i = d i) (hpmu : ∀ i, ¬ p ∣ μ i) :
    lcmDiff μ = m := by
  have hm0 : m ≠ 0 := fun h => hpm (by rw [h]; exact dvd_zero p)
  have hL0 : lcmDiff μ ≠ 0 := by
    intro h
    rw [show lcmDiff μ = Finset.univ.lcm μ from rfl, Finset.lcm_eq_zero_iff] at h
    obtain ⟨i, -, hi0⟩ := h
    exact hpmu i (by rw [hi0]; exact dvd_zero p)
  have hA : lcmDiff μ ∣ m := by
    have h1 : lcmDiff μ ∣ lcmDiff d := Finset.lcm_mono_fun (fun i _ => by
      rw [← hmul i]
      exact dvd_mul_left _ _)
    have h2 : lcmDiff μ ∣ p ^ k * m := by rwa [heq] at h1
    have h3 : ¬ p ∣ lcmDiff μ := by
      intro hpL
      obtain ⟨i, hi⟩ := exists_of_prime_pow_dvd_lcmDiff hp 1 hne μ (by rwa [Nat.pow_one])
      rw [Nat.pow_one] at hi
      exact hpmu i hi
    have hcp : Nat.Coprime p (lcmDiff μ) := hp.coprime_iff_not_dvd.2 h3
    have hiso : IsCoprime ((lcmDiff μ : ℕ) : ℤ) (((p : ℕ) ^ k : ℕ) : ℤ) := by
      rw [Nat.cast_pow]
      exact IsCoprime.pow_right (n := k) (Nat.coprime_comm.1 hcp).isCoprime
    have h5 : ((lcmDiff μ : ℕ) : ℤ) ∣ (((p : ℕ) ^ k * m : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      exact_mod_cast h2
    exact Int.natCast_dvd_natCast.1 (IsCoprime.dvd_of_dvd_mul_left hiso h5)
  have hB : m ∣ lcmDiff μ := by
    refine (Nat.factorization_le_iff_dvd hm0 hL0).mp (Finsupp.le_def.2 fun q => ?_)
    by_cases hqp : q.Prime
    · by_cases hqe : q = p
      · subst hqe
        rw [Nat.factorization_eq_zero_of_not_dvd hpm]
        exact Nat.zero_le _
      · have hγd : q ^ m.factorization q ∣ m :=
          (hqp.pow_dvd_iff_le_factorization hm0).2 (le_refl _)
        have h2 : q ^ m.factorization q ∣ lcmDiff d := by
          rw [heq]
          exact hγd.trans ⟨p ^ k, Nat.mul_comm _ _⟩
        obtain ⟨i, hi⟩ := exists_of_prime_pow_dvd_lcmDiff hqp _ hne d h2
        have hcpq : Nat.Coprime q p := by
          refine hqp.coprime_iff_not_dvd.2 ?_
          intro hqdiv
          rcases (Nat.dvd_prime hp).1 hqdiv with h1 | h1
          · exact absurd h1 hqp.ne_one
          · exact hqe h1
        have hisoq : IsCoprime ((q ^ m.factorization q : ℕ) : ℤ)
            (((p : ℕ) ^ β i : ℕ) : ℤ) := by
          rw [Nat.cast_pow]
          exact IsCoprime.pow_right (n := β i)
            (IsCoprime.pow_left (m := m.factorization q) hcpq.isCoprime)
        rw [← hmul i] at hi
        have h4 : q ^ m.factorization q ∣ μ i :=
          Int.natCast_dvd_natCast.1 (IsCoprime.dvd_of_dvd_mul_left hisoq (by exact_mod_cast hi))
        exact (hqp.pow_dvd_iff_le_factorization hL0).1 (h4.trans (dvd_lcmDiff (d := μ) i))
    · rw [Nat.factorization_eq_zero_of_not_prime m hqp]
      exact Nat.zero_le _
  exact Nat.dvd_antisymm hA hB

/-! ## 蓝图·拆n化归：记账预备 -/

/-- 【拆n⑤b】整除形式的成员关系：d i ∣ x − a i ⟹ x ∈ 块 i。 -/
theorem MemAP.of_dvd_sub {ι : Type*} {a : ι → ℤ} {d : ι → ℕ} {i : ι} {x : ℤ}
    (h : (d i : ℤ) ∣ x - a i) : MemAP a d i x := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  linear_combination hk

/-- 【拆n⑤b】独占数在 mod lcm 下两两不同：i ≠ j 时，i 的独占数与 j 的独占数
    不模 lcmDiff d 同余（否则 i 的独占数落入块 j，与独占性矛盾）。 -/
theorem private_mod_ne {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (x : ι → ℤ) (hx : ∀ i, MemAP a d i (x i) ∧ ∀ j, j ≠ i → ¬ MemAP a d j (x i))
    {i j : ι} (hij : i ≠ j) :
    ¬ ((lcmDiff d : ℤ) ∣ x i - x j) := by
  intro h
  obtain ⟨hi, hpriv⟩ := hx i
  obtain ⟨hj⟩ := hx j
  obtain ⟨k, hk⟩ := hj
  have hdj : ((d j : ℕ) : ℤ) ∣ ((lcmDiff d : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.2 (dvd_lcmDiff (d := d) j)
  have h1 : ((d j : ℕ) : ℤ) ∣ x i - x j := hdj.trans h
  have h2 : ((d j : ℕ) : ℤ) ∣ x i - a j := by
    have he : x i - a j = (x i - x j) + (x j - a j) := by ring
    rw [he]
    exact dvd_add h1 ⟨k, by rw [hk]; ring⟩
  exact hpriv j (Ne.symm hij) (MemAP.of_dvd_sub h2)

/-- 【拆n⑤b】bound 的整除单调性：m' ∣ m ⟹ bound m' ≤ bound m。 -/
theorem bound_le_of_dvd {m m' : ℕ} (hm0 : m ≠ 0) (h : m' ∣ m) : bound m' ≤ bound m := by
  have hm0' : m' ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := h
    rw [hc, Nat.zero_mul] at hk
    exact hm0 hk
  have hfle : m'.factorization ≤ m.factorization :=
    (Nat.factorization_le_iff_dvd hm0' hm0).mpr h
  have hsum : ∑ p ∈ m'.primeFactors, m'.factorization p * (p - 1)
      ≤ ∑ p ∈ m.primeFactors, m.factorization p * (p - 1) := by
    refine le_trans (Finset.sum_le_sum fun p hp => ?_) (Finset.sum_le_sum_of_subset fun p hp => ?_)
    · exact Nat.mul_le_mul (Finsupp.le_def.1 hfle p) (Nat.le_refl (p - 1))
    · obtain ⟨hpr, hdvd⟩ := (Nat.mem_primeFactors_of_ne_zero hm0').1 hp
      exact Nat.Prime.mem_primeFactors hpr (hdvd.trans h) hm0
  simp only [bound]
  linarith

/-- 【拆n⑤b】③ 的子族独占性 ⟹ 重标子族满足 Essential（可直接套 IH）。 -/
theorem essential_subtype {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (J : Finset ι)
    (hJ : ∀ i ∈ J, ∃ t, MemAP a d i t ∧ ∀ j ∈ J, j ≠ i → ¬ MemAP a d j t) :
    ∀ i : {x : ι // x ∈ J}, Essential (fun x => a x.val) (fun x => d x.val) i := by
  intro i
  obtain ⟨t, ht, hpriv⟩ := hJ i.1 i.2
  refine ⟨t, ht, ?_⟩
  intro j hj
  exact hpriv j.val j.2 (fun hc => hj (Subtype.ext hc))

/-- 【拆n⑤d】好子覆盖条款：若 m-投影存在子族 J——投影覆盖、重标后本质、
    lcm 恰为 m——则（归纳假设下）m-账闭合：bound m ≤ Fintype.card ι。
    「好子覆盖的存在性」是当前开放的数学决策点（稀释保 lcm 与本质性的张力）。 -/
theorem bound_m_le_of_good_subcover.{u} {ι : Type u} [Fintype ι] {m n : ℕ} {a : ι → ℤ}
    {μ : ι → ℕ} (hμpos : ∀ i, 0 < μ i) (hn : m < n)
    (hgood : ∃ J : Finset ι,
      (∀ x : ℤ, ∃ i ∈ J, MemAP a μ i x) ∧
      lcmDiff (fun i : {x // x ∈ J} => μ i.val) = m ∧
      ∀ i : {x // x ∈ J},
        Essential (fun y : {x // x ∈ J} => a y.val) (fun y : {x // x ∈ J} => μ y.val) i)
    (IH : ∀ m' < n, 0 < m' → ∀ (ι' : Type u) [Fintype ι'] (a' : ι' → ℤ) (d' : ι' → ℕ),
      lcmDiff d' = m' → (∀ i, 0 < d' i) → (∀ x : ℤ, ∃ i, MemAP a' d' i x) →
      (∀ i, Essential a' d' i) → Fintype.card ι' ≥ bound m') :
    bound m ≤ Fintype.card ι := by
  obtain ⟨J, hcovJ, hmJ, hessJ⟩ := hgood
  have hcov'' : ∀ x : ℤ, ∃ i : {x : ι // x ∈ J},
      MemAP (fun y => a y.val) (fun y => μ y.val) i x := by
    intro x
    obtain ⟨i, hi, him⟩ := hcovJ x
    exact ⟨⟨i, hi⟩, him⟩
  have hd'' : ∀ i : {x : ι // x ∈ J}, 0 < μ i.val := fun i => hμpos i.val
  have hm0 : 0 < m := by
    rw [← hmJ]
    exact lcmDiff_subtype_pos hμpos J
  have hIH := IH m hn hm0 {x : ι // x ∈ J} (fun y => a y.val) (fun y => μ y.val) hmJ hd'' hcov'' hessJ
  have h4 := hIH
  rw [Fintype.card_coe] at h4
  exact le_trans h4.le (Finset.card_le_univ J)

/-- 【拆n⑤e】非退化触及引理：每个 m-类都被某个 μ > 1 的块的投影触及。
    反证：若类 c 只被 μ = 1 的纯 p-幂块触及，则把任意 x 经 CRT 提升为
    x' ≡ x (mod p^k)、x' ≡ c (mod m)，纯块盖住 x' 即盖住 x（p^β ∣ p^k），
    故纯块盖住整个 ℤ，使一切 μ > 1 的块冗余，与独占性矛盾。 -/
theorem exists_hit_of_ne_one {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hm1 : 1 < m) {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i)
    (hcover : ∀ x : ℤ, ∃ i, MemAP a d i x)
    {β μ : ι → ℕ} (hmul : ∀ i, p ^ β i * μ i = d i) (hβk : ∀ i, β i ≤ k)
    (hmud : ∀ i, μ i ∣ m) (hlcm : lcmDiff μ = m) (c : ℤ) :
    ∃ i, μ i ≠ 1 ∧ (μ i : ℤ) ∣ c - a i := by
  by_contra hcon
  push Not at hcon
  -- 纯 p-幂块盖住整个 ℤ
  have hpure : ∀ x : ℤ, ∃ i, μ i = 1 ∧ MemAP a d i x := by
    intro x
    have hiso : IsCoprime ((p ^ k : ℕ) : ℤ) ((m : ℕ) : ℤ) := by
      have h3 := IsCoprime.pow_left (m := k) (hp.coprime_iff_not_dvd.2 hpm).isCoprime
      rwa [← Nat.cast_pow] at h3
    obtain ⟨u, v, huv⟩ := hiso
    obtain ⟨x', hx'eq, hx'1, hx'2⟩ :
        ∃ x' : ℤ, x' = x + ((p ^ k : ℕ) : ℤ) * (u * (c - x)) ∧
          ((p ^ k : ℕ) : ℤ) ∣ x' - x ∧ ((m : ℕ) : ℤ) ∣ x' - c := by
      refine ⟨x + ((p ^ k : ℕ) : ℤ) * (u * (c - x)), rfl, ⟨u * (c - x), by ring⟩,
        ⟨v * (x - c), ?_⟩⟩
      linear_combination (norm := ring) (c - x) * huv
    obtain ⟨i₀, hi₀⟩ := hcover x'
    have h2 : ((d i₀ : ℕ) : ℤ) ∣ x' - a i₀ := by
      obtain ⟨kk, hkk⟩ := hi₀
      exact ⟨kk, by rw [hkk]; ring⟩
    have hμc : ((μ i₀ : ℕ) : ℤ) ∣ c - a i₀ := by
      have hμdd : ((μ i₀ : ℕ) : ℤ) ∣ ((d i₀ : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.2 ⟨p ^ β i₀, by rw [← hmul i₀]; ring⟩
      have hμd' : ((μ i₀ : ℕ) : ℤ) ∣ x' - a i₀ := hμdd.trans h2
      have hμx'c : ((μ i₀ : ℕ) : ℤ) ∣ x' - c :=
        (Int.natCast_dvd_natCast.2 (hmud i₀)).trans hx'2
      obtain ⟨k1, hk1⟩ := hμd'
      obtain ⟨k2, hk2⟩ := hμx'c
      have h3 : ((μ i₀ : ℕ) : ℤ) ∣ (x' - a i₀) - (x' - c) := ⟨k1 - k2, by rw [hk1, hk2]; ring⟩
      rw [show (x' - a i₀) - (x' - c) = c - a i₀ from by ring] at h3
      exact h3
    have hμ1 : μ i₀ = 1 := by
      by_contra hμ1'
      exact hcon i₀ hμ1' hμc
    have hμ1d : d i₀ = p ^ β i₀ := by rw [← hmul i₀, hμ1, Nat.mul_one]
    refine ⟨i₀, hμ1, ?_⟩
    have hx'a : ((p ^ β i₀ : ℕ) : ℤ) ∣ x - a i₀ := by
      have hxd : ((p ^ k : ℕ) : ℤ) ∣ x - x' := ⟨-(u * (c - x)), by rw [hx'eq]; ring⟩
      have hxd2 : ((p ^ β i₀ : ℕ) : ℤ) ∣ x - x' :=
        (Int.natCast_dvd_natCast.2
          ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 (hβk i₀))).trans hxd
      have h3 : x - a i₀ = (x - x') + (x' - a i₀) := by ring
      rw [h3]
      exact dvd_add hxd2 (by rw [← hμ1d]; exact h2)
    rw [← hμ1d] at hx'a
    exact MemAP.of_dvd_sub hx'a
  -- μ > 1 的块存在
  have hex : ∃ i, μ i ≠ 1 := by
    by_contra hall
    push Not at hall
    have hlc : lcmDiff μ ∣ 1 :=
      Finset.lcm_dvd (fun i _ => by rw [hall i])
    have h1 : lcmDiff μ = 1 := Nat.dvd_one.1 hlc
    rw [hlcm] at h1
    exact absurd h1 (by omega)
  obtain ⟨i₀, hi₀ne⟩ := hex
  obtain ⟨x, hxmem, hxpriv⟩ := hess i₀
  obtain ⟨j, hjpure, hjmem⟩ := hpure x
  refine absurd hjmem (hxpriv j ?_)
  intro h
  rw [h] at hjpure
  exact hi₀ne hjpure

/-- 【拆n⑤f】非退化投影覆盖：μ > 1 的块的投影（μ-差 AP）覆盖整个 ℤ。
    ⑤-e 对每个整数逐点成立，取 c := x 即得。 -/
theorem cover_of_ne_one {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hm1 : 1 < m) {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i) (hcover : ∀ x : ℤ, ∃ i, MemAP a d i x)
    {β μ : ι → ℕ} (hmul : ∀ i, p ^ β i * μ i = d i) (hβk : ∀ i, β i ≤ k)
    (hmud : ∀ i, μ i ∣ m) (hlcm : lcmDiff μ = m) :
    ∀ x : ℤ, ∃ i, μ i ≠ 1 ∧ MemAP a μ i x := by
  intro x
  obtain ⟨i, hi1, hi2⟩ :=
    exists_hit_of_ne_one hp hpm hm1 hess hcover hmul hβk hmud hlcm x
  exact ⟨i, hi1, MemAP.of_dvd_sub hi2⟩

/-! ## 蓝图·路2：强化归纳骨架 -/

open Classical in
/-- 【拆n·路2·T″】本质块子族的 lcmDiff（T″ 的 lcm 参数：
    冗余块不贡献 lcm——{ℤ, {a mod n}} 反例的修正）。 -/
noncomputable def essLcm {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) : ℕ :=
  lcmDiff (fun i : {i : ι // Essential a d i} => d i.val)

open Classical in
/-- 【拆n·路2】冗余度 ρ：无私有点（非本质）的块数。独占族上 ρ = 0。 -/
noncomputable def rho {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) : ℕ :=
  Fintype.card {i : ι // ¬ Essential a d i}

open Classical in
/-- 【拆n·路2】独占族上 ρ = 0：强化陈述在独占情形退回原定理。 -/
theorem rho_eq_zero_of_essential {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i) : rho a d = 0 := by
  have hempty : IsEmpty {i : ι // ¬ Essential a d i} :=
    ⟨fun i => absurd (hess i.1) i.2⟩
  show Fintype.card {i : ι // ¬ Essential a d i} = 0
  exact @Fintype.card_eq_zero _ (Subtype.fintype _) hempty

/-- 【拆n·路2·T″】纯算术整除下降：p ∣ d、d ∣ N ⇒ d/p ∣ N/p。 -/
theorem div_dvd_div {p d N : ℕ} (hp0 : 0 < p) (hpd : p ∣ d) (hd : d ∣ N) :
    d / p ∣ N / p := by
  obtain ⟨t, ht⟩ := hd
  have hpdi : p * (d / p) = d := Nat.mul_div_cancel' (hpd)
  have h2 : N = p * (d / p * t) := by
    set x := d / p with hx
    have h3 : d = p * x := (Nat.mul_div_cancel' hpd).symm
    conv_lhs => rw [ht, h3]
    rw [Nat.mul_assoc]
  have h3 : N / p = d / p * t := by
    rw [h2, Nat.mul_div_cancel_left _ hp0]
  exact ⟨t, h3⟩

/-- 【拆n·路2】纤维公差整除：p ∣ d i 时 d i / p 整除 n / p（n = lcmDiff d）。 -/
theorem fibD_dvd_div {ι : Type*} [Fintype ι] {p n : ℕ} (hp0 : 0 < p)
    {d : ι → ℕ} (heq : lcmDiff d = n) (hpd : ∀ i, p ∣ d i) (i : ι) :
    d i / p ∣ n / p := by
  have hd' : d i ∣ n := by rw [← heq]; exact dvd_lcmDiff i
  obtain ⟨t, ht⟩ := hd'
  have hpdi : p * (d i / p) = d i := Nat.mul_div_cancel' (hpd i)
  have h2 : n = p * (d i / p * t) := by
    rw [ht]
    conv_lhs => rw [← hpdi]
    rw [Nat.mul_assoc]
  have h3 : n / p = d i / p * t := by
    rw [h2, Nat.mul_div_cancel_left _ hp0]
  exact ⟨t, h3⟩

/-- 【拆n·缺口1·簿记】bound(n/p) + (p−1) = bound n（p^k ∥ n，k ≥ 1）。
    两次 bound_mul_prime_pow 相减。 -/
theorem bound_div_pow_add {p k n : ℕ} (hp : p.Prime) (hn0 : n ≠ 0) (hpk : p ^ k ∣ n)
    (hk1 : 1 ≤ k) (hpm : ¬ p ∣ n / p ^ k) :
    bound (n / p) + (p - 1) = bound n := by
  have hnp0 : n / p ^ k ≠ 0 := by
    intro hc
    apply hn0
    rw [← Nat.mul_div_cancel' hpk, hc, Nat.mul_zero]
  set np' := n / p ^ k with hnp'def
  have h2' : n = p ^ k * np' := (Nat.mul_div_cancel' hpk).symm
  have h1 : p ^ k = p * p ^ (k - 1) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk', Nat.pow_succ]
    rw [mul_comm]
  have h2 : n = p * (p ^ (k - 1) * np') := by
    rw [h2', h1, Nat.mul_assoc]
  have hdiv : n / p = p ^ (k - 1) * np' := by
    rw [h2, Nat.mul_div_cancel_left _ hp.pos]
  have hA1 : bound n = bound np' + (p - 1) * k := by
    rw [h2', bound_mul_prime_pow hp k hnp0 hpm, mul_comm]
  have hA2 : bound (n / p) = bound np' + (k - 1) * (p - 1) := by
    rw [hdiv]
    exact bound_mul_prime_pow hp (k - 1) hnp0 hpm
  have hmul : (k - 1) * (p - 1) + (p - 1) = (p - 1) * k := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk']
    rw [mul_comm (p - 1) (k - 1 + 1), Nat.succ_mul]
  omega

/-- 【拆n·缺口1·超可加】bound 对 lcm 超可加：非空有限族各成员 bound 之和
    ≥ 整族 lcm 的 bound + (族大小 − 1)。证明：逐素数 q，v_q(lcm) 由某成员
    达到（②-1 的 Finset 版），故 v_q(lcm) ≤ Σ_i v_q(f i)；q ∉ pf(f i) 处
    summand 为零（f i = 0 或 q ∤ f i 两情形）。 -/
theorem bound_lcm_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hs : s.Nonempty) :
    ∑ i ∈ s, bound (f i) ≥ bound (s.lcm f) + s.card - 1 := by
  classical
  set L := s.lcm f with hLdef
  have hpos : 0 < s.card := Finset.card_pos.2 hs
  rcases Nat.eq_zero_or_pos L with hL0 | hL0
  · rw [hL0]
    have hb0 : bound (0 : ℕ) = 1 := by simp [bound]
    have h1 : ∀ i ∈ s, 1 ≤ bound (f i) := by
      intro i _
      unfold bound
      exact Nat.add_le_add_left (Finset.sum_nonneg
        fun q _ => Nat.zero_le _) 1
    have h2 : s.card ≤ ∑ i ∈ s, bound (f i) := by
      have h3 := Finset.sum_le_sum (fun i hi => h1 i hi)
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one] at h3
      exact h3
    omega
  · have hL0' : L ≠ 0 := ne_of_gt hL0
    have hqle : ∀ q ∈ L.primeFactors,
        L.factorization q ≤ ∑ i ∈ s, (f i).factorization q := by
      intro q hq
      have hqp : q.Prime := ((Nat.mem_primeFactors_of_ne_zero hL0').1 hq).1
      have hqdv : q ∣ L := ((Nat.mem_primeFactors_of_ne_zero hL0').1 hq).2
      have hdvd : q ^ L.factorization q ∣ L :=
        hqp.pow_dvd_iff_le_factorization hL0' |>.2 (le_refl (L.factorization q))
      have hpos1 : 0 < L.factorization q :=
        (hqp.pow_dvd_iff_le_factorization hL0').1 (by rwa [Nat.pow_one])
      obtain ⟨i, hi, hfi⟩ :=
        exists_of_prime_pow_dvd_lcm_finset hqp hpos1 s f hdvd
      have hfi0 : f i ≠ 0 := by
        intro hc
        exact absurd (s.lcm_eq_zero_iff.2 ⟨i, hi, hc⟩) hL0'
      have hle := (hqp.pow_dvd_iff_le_factorization hfi0).1 hfi
      refine le_trans hle ?_
      exact @Finset.single_le_sum ι ℕ _ _ (fun j => (f j).factorization q) s _
        (fun j _ => Nat.zero_le _) i hi
    have hzero : ∀ i ∈ s, ∑ q ∈ L.primeFactors \ (f i).primeFactors,
        (f i).factorization q * (q - 1) = 0 := by
      intro i _
      refine Finset.sum_eq_zero (fun q hq => ?_)
      have hqpf : q ∉ (f i).primeFactors := (Finset.mem_sdiff.1 hq).2
      rcases Nat.eq_zero_or_pos (f i) with h0 | h0
      · rw [h0]; simp
      · have hqp : q.Prime := ((Nat.mem_primeFactors_of_ne_zero hL0').1
            (Finset.mem_sdiff.1 hq).1).1
        have hnd : ¬ q ∣ f i := fun hqd =>
          hqpf ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt h0)).2 ⟨hqp, hqd⟩)
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.zero_mul]
    have hsub : ∀ i ∈ s, ∑ q ∈ L.primeFactors, (f i).factorization q * (q - 1)
        ≤ ∑ q ∈ (f i).primeFactors, (f i).factorization q * (q - 1) := by
      intro i hi
      have hdisj : Disjoint (f i).primeFactors
          (L.primeFactors \ (f i).primeFactors) := Finset.disjoint_sdiff
      have hunion : ∑ q ∈ (f i).primeFactors ∪ (L.primeFactors \ (f i).primeFactors),
          (f i).factorization q * (q - 1)
          = ∑ q ∈ (f i).primeFactors, (f i).factorization q * (q - 1)
            + ∑ q ∈ L.primeFactors \ (f i).primeFactors,
              (f i).factorization q * (q - 1) := Finset.sum_union hdisj
      have hzeroi := hzero i hi
      calc ∑ q ∈ L.primeFactors, (f i).factorization q * (q - 1)
          ≤ ∑ q ∈ (f i).primeFactors ∪ (L.primeFactors \ (f i).primeFactors),
            (f i).factorization q * (q - 1) :=
            Finset.sum_le_sum_of_subset fun q hq => by
              by_cases hmem : q ∈ (f i).primeFactors
              · exact Finset.mem_union_left _ hmem
              · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hq, hmem⟩)
        _ = ∑ q ∈ (f i).primeFactors, (f i).factorization q * (q - 1) := by
            rw [hunion, hzeroi, add_zero]
    have hsumbound : ∑ i ∈ s, bound (f i)
        = s.card + ∑ i ∈ s, ∑ q ∈ (f i).primeFactors,
          (f i).factorization q * (q - 1) := by
      have h1 : ∀ i ∈ s, bound (f i)
          = 1 + ∑ q ∈ (f i).primeFactors, (f i).factorization q * (q - 1) := by
        intro i _; rfl
      conv_lhs => rw [Finset.sum_congr rfl fun i hi => h1 i hi]
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hchain : ∑ i ∈ s, ∑ q ∈ L.primeFactors, (f i).factorization q * (q - 1)
        ≤ ∑ i ∈ s, ∑ q ∈ (f i).primeFactors, (f i).factorization q * (q - 1) :=
      Finset.sum_le_sum (fun i hi => hsub i hi)
    have h1' : bound L ≤ 1 + ∑ i ∈ s, ∑ q ∈ L.primeFactors,
        (f i).factorization q * (q - 1) := by
      have hstep1 : ∀ q ∈ L.primeFactors, L.factorization q * (q - 1)
          ≤ ∑ i ∈ s, (f i).factorization q * (q - 1) := by
        intro q hq
        rw [← Finset.sum_mul s (fun x => (f x).factorization q) (q - 1)]
        exact Nat.mul_le_mul (hqle q hq) (le_refl (q - 1))
      refine Nat.add_le_add_left (le_trans (Finset.sum_le_sum hstep1) ?_) 1
      rw [Finset.sum_comm]
    have hfinal : bound L + (s.card - 1) ≤ ∑ i ∈ s, bound (f i) := by
      rw [hsumbound]
      have hBL1 : 1 ≤ bound L := by
        unfold bound
        exact Nat.add_le_add_left (Finset.sum_nonneg
          fun q _ => Nat.zero_le _) 1
      have hXY : bound L - 1 ≤ ∑ i ∈ s,
          ∑ q ∈ (f i).primeFactors, (f i).factorization q * (q - 1) :=
        le_trans (by omega : bound L - 1 ≤
          ∑ i ∈ s, ∑ q ∈ L.primeFactors, (f i).factorization q * (q - 1)) hchain
      omega
    omega

/-- 【拆n·路2·摊派】每块居某纤维：∃ c : Fin p, i ∈ Fiber p a c
    （c 取 a i mod p 的代表）。 -/
theorem exists_fiber_mem {ι : Type*} (p : ℕ) (hp0 : 0 < p) (a : ι → ℤ) (i : ι) :
    ∃ c : Fin p, (p : ℤ) ∣ a i - ((c:ℕ):ℤ) := by
  have hp0' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.ne_of_gt hp0)
  have hp1 : (p : ℤ) > 0 := by exact_mod_cast hp0
  have hmem : 0 ≤ a i % p := Int.emod_nonneg _ hp0'
  have hlt : a i % p < p := Int.emod_lt_of_pos _ hp1
  refine ⟨⟨(a i % p).toNat, ?_⟩, ?_⟩
  · have h1 : ((a i % p).toNat : ℤ) = a i % p := Int.toNat_of_nonneg hmem
    exact Nat.cast_lt.1 (by rw [h1]; exact hlt)
  · rw [Int.toNat_of_nonneg hmem]
    exact ⟨a i / (p : ℤ), by
      linear_combination (norm := ring) -(Int.mul_ediv_add_emod (a i) (p : ℤ))⟩

/-- 【拆n·路2·摊派】整除传递：q 素 ≠ p、q^e ∣ d ⇒ q^e ∣ d / p。 -/
theorem dvd_div_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqe : q ≠ p)
    {e : ℕ} {d : ℕ} (hd : q ^ e ∣ d) (hpd : p ∣ d) :
    q ^ e ∣ d / p := by
  have hcpq : Nat.Coprime q p := by
    refine hq.coprime_iff_not_dvd.2 ?_
    intro hqdiv
    rcases (Nat.dvd_prime hp).1 hqdiv with h1 | h1
    · exact absurd h1 hq.ne_one
    · exact hqe h1
  have hiso : IsCoprime ((q ^ e : ℕ) : ℤ) ((p : ℕ) : ℤ) := by
    have h2 := IsCoprime.pow_left (m := e) hcpq.isCoprime
    rwa [← Nat.cast_pow] at h2
  have h1 : ((q ^ e : ℕ) : ℤ) ∣ ((p : ℕ) * (d / p : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hpd]
    exact Int.natCast_dvd_natCast.2 hd
  exact Int.natCast_dvd_natCast.1 (IsCoprime.dvd_of_dvd_mul_left hiso h1)

/-- 【拆n·缺口2】逐块纤维独占：单块独占点经桥引理推入其所在纤维
    （只需该块自己的独占性，无需全局独占假设）。 -/
theorem fiber_essential_of {ι : Type*} {p : ℕ} (hp : p.Prime) {a : ι → ℤ} {d : ι → ℕ}
    (hpd : ∀ i, p ∣ d i) (c : ℤ) (i : Fiber p a c) (hi : Essential a d i.1) :
    Essential (fibA p a c) (fibD p a c d) i := by
  obtain ⟨m, hm, hpriv⟩ := hi
  have hdiv_d : (p : ℤ) ∣ (d i.1 : ℤ) := by
    obtain ⟨q, hq⟩ := hpd i.1
    exact ⟨(q : ℤ), by exact_mod_cast hq⟩
  have hdiv : (p : ℤ) ∣ m - c := by
    obtain ⟨k, hk⟩ := hm
    have : m - c = (a i.1 - c) + (d i.1 : ℤ) * k := by linarith
    rw [this]
    exact dvd_add i.2 (dvd_mul_of_dvd_left hdiv_d k)
  have hkey : c + (p : ℤ) * ((m - c) / (p : ℤ)) = m := by
    rw [Int.mul_ediv_cancel' hdiv]
    ring
  refine ⟨(m - c) / (p : ℤ), ?_, ?_⟩
  · rw [fiber_memAP_iff hp hpd c i ((m - c) / (p : ℤ)), hkey]
    exact hm
  · intro j hj hmem
    rw [fiber_memAP_iff hp hpd c j ((m - c) / (p : ℤ)), hkey] at hmem
    exact hpriv j.1 (fun hje => hj (Subtype.ext hje)) hmem

/-- 【拆n·缺口2】纤维独占 ↔ 原独占（逐块）：纤维私有点与全局私有点
    通过桥引理互相转移（hpd 下块的所有点都在其纤维内）。 -/
theorem fiber_essential_iff {ι : Type*} {p : ℕ} (hp : p.Prime) {a : ι → ℤ} {d : ι → ℕ}
    (hpd : ∀ i, p ∣ d i) (c : ℤ) (i : Fiber p a c) :
    Essential (fibA p a c) (fibD p a c d) i ↔ Essential a d i.1 := by
  constructor
  · rintro ⟨t, ht, hpriv⟩
    refine ⟨c + (p : ℤ) * t, ?_, ?_⟩
    · rw [← fiber_memAP_iff hp hpd c i t]
      exact ht
    · intro j hj hmem
      have h1 : (p : ℤ) ∣ d j := by
        obtain ⟨q, hq⟩ := hpd j
        exact ⟨(q : ℤ), by exact_mod_cast hq⟩
      have h2 : (p : ℤ) ∣ (c + (p : ℤ) * t) - a j := by
        obtain ⟨k, hk⟩ := hmem
        have h3 : (p : ℤ) ∣ ↑(d j) * k := dvd_mul_of_dvd_left h1 k
        have h4 : (c + (p : ℤ) * t) - a j = ↑(d j) * k := by rw [hk]; ring
        rw [h4]
        exact h3
      have h3 : (p : ℤ) ∣ (c + (p : ℤ) * t) - c := ⟨t, by ring⟩
      have h4 := dvd_sub h3 h2
      rw [show (c + (p : ℤ) * t) - c - ((c + (p : ℤ) * t) - a j) = a j - c from by
        ring] at h4
      have h5 : MemAP (fibA p a c) (fibD p a c d) ⟨j, h4⟩ t := by
        rw [fiber_memAP_iff hp hpd c ⟨j, h4⟩ t]
        exact hmem
      exact hpriv ⟨j, h4⟩ (fun hje => hj (congrArg Subtype.val hje)) h5
  · exact fun h => fiber_essential_of hp hpd c i h

/-- 【拆n·路2·T″】p-部分降级整除：p^e ∣ d ⇒ p^{e−1} ∣ d / p（e ≥ 1）。 -/
theorem pow_pred_dvd_div_self {p e d : ℕ} (hp0 : 0 < p) (he1 : 1 ≤ e) (hd : p ^ e ∣ d) :
    p ^ (e - 1) ∣ d / p := by
  obtain ⟨u, hu⟩ := hd
  have h1 : p ^ e = p * p ^ (e - 1) := by
    conv_lhs => rw [show e = (e - 1) + 1 from (Nat.sub_add_cancel he1).symm, Nat.pow_succ']
  rw [hu, h1, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp0]
  exact dvd_mul_right _ _

/-- 【拆n·缺口1·T″·摊派】essLcm/p 整除各纤维 ess-lcm 之 lcm：
    逐素数幂——q ≠ p 时 q^δ ∥ essLcm 的载体是本质块 i（ess-lcm 定义），
    i 居纤维 c(i)，q^δ ∣ d i / p（dvd_div_of_ne），q^δ ∣ 纤维 ess-lcm
    （本质子族上的 dvd_lcmDiff），q^δ ∣ 全体 lcm；q = p 时载体指数升一级
    （p^{δ+1} ∣ essLcm ⟹ p^δ ∣ d i / p），p-部分恰降一级，与纤维账吻合。 -/
theorem essLcm_div_dvd_lcm_essLcm_fibD {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime)
    {a : ι → ℤ} {d : ι → ℕ} (hd : ∀ i, 0 < d i) (hpd : ∀ i, p ∣ d i)
    (hpdL : p ∣ essLcm a d) :
    essLcm a d / p ∣ Finset.univ.lcm (fun c : Fin p =>
      essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) := by
  classical
  have hp0 : 0 < p := hp.pos
  have h1pos : 0 < essLcm a d := by
    rw [Nat.pos_iff_ne_zero, show essLcm a d = Finset.univ.lcm
      (fun i : {x : ι // Essential a d x} => d i.val) from rfl,
      Finset.lcm_ne_zero_iff]
    intro j _
    exact (hd j.val).ne'
  have hEp0 : essLcm a d / p ≠ 0 :=
    ne_of_gt (Nat.div_pos (Nat.le_of_dvd h1pos hpdL) hp0)
  have hMne : Finset.univ.lcm (fun c : Fin p =>
      essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro c _
    rw [show essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
        = Finset.univ.lcm (fun i : {i : Fiber p a ((c:ℕ):ℤ) //
            Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i} =>
            fibD p a ((c:ℕ):ℤ) d i.val) from rfl, Finset.lcm_ne_zero_iff]
    intro j _
    exact ne_of_gt (Nat.div_pos (Nat.le_of_dvd (hd j.1.val) (hpd j.1.val)) hp0)
  have hneE : Nonempty {x : ι // Essential a d x} := by
    by_contra hne
    have hIE : IsEmpty {x : ι // Essential a d x} :=
      ⟨fun x => hne ⟨x⟩⟩
    have h1 : essLcm a d = 1 := by
      rw [show essLcm a d = Finset.univ.lcm
        (fun i : {x : ι // Essential a d x} => d i.val) from rfl,
        Finset.univ_eq_empty, Finset.lcm_empty]
    have h2 : 1 < essLcm a d := by
      have hp2 : 1 < p := hp.one_lt
      have h3 : p ≤ essLcm a d := Nat.le_of_dvd h1pos hpdL
      omega
    omega
  have hcarrierP : ∀ e : ℕ, 0 < e → p ^ e ∣ essLcm a d → ∃ c : Fin p,
      p ^ (e - 1) ∣ essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) := by
    intro e he0 hqdv
    obtain ⟨i₀, hi₀dvd⟩ := exists_of_prime_pow_dvd_lcmDiff hp e hneE
      (fun i : {x : ι // Essential a d x} => d i.val) hqdv
    have hi₀ess : Essential a d i₀ := i₀.2
    obtain ⟨c, hc⟩ := exists_fiber_mem p hp0 a i₀
    have htr : p ^ (e - 1) ∣ d i₀ / p :=
      pow_pred_dvd_div_self hp0 he0 hi₀dvd
    have hfess : Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
        ⟨i₀, hc⟩ := fiber_essential_of hp hpd ((c:ℕ):ℤ) ⟨i₀, hc⟩ hi₀ess
    have hLidx : p ^ (e - 1) ∣ essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) :=
      htr.trans (dvd_lcmDiff (d := fun j : {x : Fiber p a ((c:ℕ):ℤ) //
          Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) x} =>
          fibD p a ((c:ℕ):ℤ) d j.val) ⟨⟨i₀, hc⟩, hfess⟩)
    exact ⟨c, hLidx⟩
  have hcarrierNP : ∀ (q : ℕ), q.Prime → q ≠ p → ∀ e : ℕ, q ^ e ∣ essLcm a d →
      ∃ c : Fin p, q ^ e ∣ essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) := by
    intro q hq hqe e hqdv
    obtain ⟨i₀, hi₀dvd⟩ := exists_of_prime_pow_dvd_lcmDiff hq e hneE
      (fun i : {x : ι // Essential a d x} => d i.val) hqdv
    have hi₀ess : Essential a d i₀ := i₀.2
    obtain ⟨c, hc⟩ := exists_fiber_mem p hp0 a i₀
    have htr : q ^ e ∣ d i₀ / p :=
      dvd_div_of_ne hp hq hqe hi₀dvd (hpd i₀)
    have hfess : Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
        ⟨i₀, hc⟩ := fiber_essential_of hp hpd ((c:ℕ):ℤ) ⟨i₀, hc⟩ hi₀ess
    have hLidx : q ^ e ∣ essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) :=
      htr.trans (dvd_lcmDiff (d := fun j : {x : Fiber p a ((c:ℕ):ℤ) //
          Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) x} =>
          fibD p a ((c:ℕ):ℤ) d j.val) ⟨⟨i₀, hc⟩, hfess⟩)
    exact ⟨c, hLidx⟩
  have hqle : ∀ q ∈ (essLcm a d / p).primeFactors,
      (essLcm a d / p).factorization q
      ≤ (Finset.univ.lcm (fun c : Fin p =>
          essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d))).factorization q := by
    intro q hq
    have hqp : q.Prime := ((Nat.mem_primeFactors_of_ne_zero hEp0).1 hq).1
    by_cases hqe : q = p
    · have hqe' : p = q := hqe.symm
      subst hqe'
      have hδ1 : p ^ ((essLcm a d / p).factorization p + 1) ∣ essLcm a d := by
        have h1 : p ^ ((essLcm a d / p).factorization p) ∣ essLcm a d / p :=
          (hqp.pow_dvd_iff_le_factorization hEp0).2 (le_refl _)
        have h2 : essLcm a d = p * (essLcm a d / p) := (Nat.mul_div_cancel' hpdL).symm
        conv_rhs => rw [h2]
        rw [Nat.pow_succ, mul_comm]
        exact Nat.mul_dvd_mul_left p h1
      obtain ⟨c, hc⟩ := hcarrierP ((essLcm a d / p).factorization p + 1)
        (by omega) hδ1
      have hle : p ^ ((essLcm a d / p).factorization p) ∣
          essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) :=
        (Nat.pow_dvd_pow p (by omega)).trans hc
      exact (hqp.pow_dvd_iff_le_factorization hMne).1
        (hle.trans (Finset.dvd_lcm (Finset.mem_univ c)))
    · have hqdv : q ^ ((essLcm a d / p).factorization q) ∣ essLcm a d := by
        have h1 : q ^ ((essLcm a d / p).factorization q) ∣ essLcm a d / p :=
          (hqp.pow_dvd_iff_le_factorization hEp0).2 (le_refl _)
        have h2 : essLcm a d / p ∣ essLcm a d :=
          ⟨p, (Nat.mul_div_cancel' hpdL).symm.trans (mul_comm _ _)⟩
        exact h1.trans h2
      obtain ⟨c, hc⟩ := hcarrierNP q hqp hqe _ hqdv
      exact (hqp.pow_dvd_iff_le_factorization hMne).1
        (hc.trans (Finset.dvd_lcm (Finset.mem_univ c)))
  refine (Nat.factorization_le_iff_dvd hEp0 hMne).mp (Finsupp.le_def.2 fun q => ?_)
  by_cases hqp : q.Prime
  · by_cases hqm : q ∈ (essLcm a d / p).primeFactors
    · exact hqle q hqm
    · by_contra hz
      have hpos : 0 < (essLcm a d / p).factorization q := by omega
      have hqd : q ∣ essLcm a d / p := by
        have h2 : q ^ 1 ∣ essLcm a d / p :=
          (hqp.pow_dvd_iff_le_factorization hEp0).2 hpos
        rwa [Nat.pow_one] at h2
      exact hqm ((Nat.mem_primeFactors_of_ne_zero hEp0).2 ⟨hqp, hqd⟩)
  · rw [Nat.factorization_eq_zero_of_not_prime (essLcm a d / p) hqp]
    exact Nat.zero_le _

/-- 【拆n·缺口2】纤维冗余计数 ≤ 原冗余计数：Σ_c ρ_c ≤ ρ a d。
    单射 Σ_c {纤维非本质块} → {原非本质块}：块 i 的纤维非本质性反推其原非本质性
    （逆否：原独占 ⟹ 纤维独占，逐块版 fiber_essential_of）；
    纤维归属由 mod p 决定（模 p 相同的类唯一），故不同纤维的块映射到不同的原块。 -/
theorem sum_rho_le {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime)
    {a : ι → ℤ} {d : ι → ℕ} (hpd : ∀ i, p ∣ d i) :
    ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) ≤ rho a d := by
  classical
  have hinj : Function.Injective (fun x : (Σ c : Fin p,
      {i : Fiber p a ((c:ℕ):ℤ) // ¬ Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i}) =>
      (⟨x.2.1.1, fun hEsso =>
        x.2.2 (fiber_essential_of hp hpd ((x.1:ℕ):ℤ) x.2.1 hEsso)⟩ :
        {i : ι // ¬ Essential a d i})) := by
    rintro ⟨c₁, i₁, h₁⟩ ⟨c₂, i₂, h₂⟩ heq
    have heq' : i₁.1 = i₂.1 := congrArg Subtype.val heq
    have hc : (p : ℤ) ∣ ((c₂:ℕ):ℤ) - ((c₁:ℕ):ℤ) := by
      have h1 : (p : ℤ) ∣ (a i₁.1 - ((c₁:ℕ):ℤ)) - (a i₂.1 - ((c₂:ℕ):ℤ)) :=
        dvd_sub i₁.2 i₂.2
      rw [heq'] at h1
      have h2 : a i₂.1 - ((c₁:ℕ):ℤ) - (a i₂.1 - ((c₂:ℕ):ℤ))
          = ((c₂:ℕ):ℤ) - ((c₁:ℕ):ℤ) := by ring
      rwa [h2] at h1
    have hzeq : ((c₁:ℕ) : ZMod p) = ((c₂:ℕ) : ZMod p) := by
      have h := (ZMod.intCast_eq_intCast_iff_dvd_sub ((c₁:ℕ):ℤ) ((c₂:ℕ):ℤ) p).2 hc
      simpa using h
    have hval : (c₁:ℕ) = (c₂:ℕ) := by
      have h1 := congrArg ZMod.val hzeq
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt c₁.isLt,
        Nat.mod_eq_of_lt c₂.isLt] at h1
    have hcc : c₁ = c₂ := Fin.ext hval
    exact Sigma.ext hcc (by cases hcc; exact heq_of_eq (Subtype.ext (Subtype.ext heq')))
  calc ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
      = Fintype.card (Σ c : Fin p,
          {i : Fiber p a ((c:ℕ):ℤ) //
            ¬ Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i}) := by
        rw [Fintype.card_sigma]
        exact Finset.sum_congr rfl fun c _ => rfl
    _ ≤ Fintype.card {i : ι // ¬ Essential a d i} :=
        Fintype.card_le_of_injective _ hinj
    _ = rho a d := rfl

/-- 【拆n·缺口1·摊派】无裂块时各纤维的 bound 之和 ≥ bound n：逐素数账目——
    p 部分由 v_p(d) = k 的块贡献 k−1；每个 q ≠ p 的素数幂 γ = v_q(n) 由
    q^γ 载体块经 dvd_div_of_ne 传入其所在纤维。 -/
theorem sum_bound_fibD_ge {ι : Type*} [Fintype ι] {p k m : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k)
    (hpm : ¬ p ∣ m) {a : ι → ℤ} {d : ι → ℕ}
    (heq : lcmDiff d = p ^ k * m) (hd : ∀ i, 0 < d i) (hpd : ∀ i, p ∣ d i)
    (hne : Nonempty ι) :
    ∑ c : Fin p, bound (lcmDiff (fibD p a ((c:ℕ):ℤ) d)) ≥ bound (p ^ k * m) := by
  classical
  have hm0 : m ≠ 0 := fun hc => hpm (by rw [hc]; exact dvd_zero p)
  have hn0 : p ^ k * m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero k hp.ne_zero) hm0
  have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk1).symm
  have hpk_eq : p ^ k = p * p ^ (k - 1) := by
    conv_lhs => rw [hk', pow_succ']
  have hfkp : (p ^ k * m).factorization p = k := by
    rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm0, Finsupp.add_apply,
      Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]
  have hLne : ∀ c : Fin p, lcmDiff (fibD p a ((c:ℕ):ℤ) d) ≠ 0 := by
    intro c
    rw [show lcmDiff (fibD p a ((c:ℕ):ℤ) d)
        = Finset.univ.lcm (fibD p a ((c:ℕ):ℤ) d) from rfl, Finset.lcm_ne_zero_iff]
    intro j _
    exact ne_of_gt (Nat.div_pos (Nat.le_of_dvd (hd j.val) (hpd j.val)) hp.pos)
  have hLdvd : ∀ c : Fin p, lcmDiff (fibD p a ((c:ℕ):ℤ) d) ∣ p ^ k * m := by
    intro c
    have h1 : lcmDiff (fibD p a ((c:ℕ):ℤ) d) ∣ (p ^ k * m) / p :=
      Finset.lcm_dvd (fun i _ => fibD_dvd_div hp.pos heq hpd i.1)
    have h2 : (p ^ k * m) / p = p ^ (k - 1) * m := by
      rw [show p ^ k * m = p * (p ^ (k - 1) * m) from by rw [← Nat.mul_assoc, ← hpk_eq],
        Nat.mul_div_cancel_left _ hp.pos]
    rw [h2] at h1
    exact h1.trans ⟨p, by rw [mul_comm (p ^ (k - 1) * m) p, ← Nat.mul_assoc, ← hpk_eq]⟩
  have hstep1 : ∀ c : Fin p, bound (lcmDiff (fibD p a ((c:ℕ):ℤ) d)) =
      1 + ∑ q ∈ (p ^ k * m).primeFactors,
        (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q * (q - 1) := by
    intro c
    unfold bound
    congr 1
    refine Finset.sum_subset ?_ ?_
    · intro q hq
      obtain ⟨hqp, hqdvd⟩ := (Nat.mem_primeFactors_of_ne_zero (hLne c)).1 hq
      exact Nat.Prime.mem_primeFactors hqp (hqdvd.trans (hLdvd c)) hn0
    · intro q hq hqnot
      have hqp : q.Prime := ((Nat.mem_primeFactors_of_ne_zero hn0).1 hq).1
      have hnd : ¬ q ∣ lcmDiff (fibD p a ((c:ℕ):ℤ) d) := fun hdvd =>
        hqnot ((Nat.mem_primeFactors_of_ne_zero (hLne c)).2 ⟨hqp, hdvd⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.zero_mul]
  have hSp : k - 1 ≤ ∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization p := by
    obtain ⟨i₀, hi₀⟩ := exists_factorization_p_eq_of_lcmDiff hp hpm d hd hne heq
    obtain ⟨c₀, hc₀⟩ := exists_fiber_mem p hp.pos a i₀
    have hpk : p ^ k ∣ d i₀ :=
      (hp.pow_dvd_iff_le_factorization (ne_of_gt (hd i₀))).mpr (by omega)
    have hdiv : p ^ (k - 1) ∣ d i₀ / p := by
      have h1 : p * p ^ (k - 1) ∣ p * (d i₀ / p) := by
        rw [← hpk_eq, Nat.mul_div_cancel' (hpd i₀)]
        exact hpk
      exact (Nat.mul_dvd_mul_iff_left hp.pos).1 h1
    have hLidx : p ^ (k - 1) ∣ lcmDiff (fibD p a ((c₀:ℕ):ℤ) d) :=
      hdiv.trans (dvd_lcmDiff (d := fibD p a ((c₀:ℕ):ℤ) d) ⟨i₀, hc₀⟩)
    have h1 : (lcmDiff (fibD p a ((c₀:ℕ):ℤ) d)).factorization p ≥ k - 1 :=
      (hp.pow_dvd_iff_le_factorization (hLne c₀)).1 hLidx
    exact le_trans h1 (@Finset.single_le_sum (Fin p) ℕ _ _
      (fun c => (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization p) Finset.univ _
      (fun c _ => Nat.zero_le _) c₀ (Finset.mem_univ c₀))
  have hSq : ∀ q ∈ (p ^ k * m).primeFactors, q ≠ p →
      (p ^ k * m).factorization q ≤
        ∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q := by
    intro q hq hqpne
    have hqp : q.Prime := ((Nat.mem_primeFactors_of_ne_zero hn0).1 hq).1
    have hqdv : q ^ (p ^ k * m).factorization q ∣ p ^ k * m :=
      (hqp.pow_dvd_iff_le_factorization hn0).mpr (le_refl _)
    obtain ⟨i, hi⟩ :=
      exists_of_prime_pow_dvd_lcmDiff hqp ((p ^ k * m).factorization q) hne d (heq.symm ▸ hqdv)
    obtain ⟨c, hc⟩ := exists_fiber_mem p hp.pos a i
    have hdiv : q ^ (p ^ k * m).factorization q ∣ d i / p :=
      dvd_div_of_ne hp hqp hqpne hi (hpd i)
    have hLidx : q ^ (p ^ k * m).factorization q ∣ lcmDiff (fibD p a ((c:ℕ):ℤ) d) :=
      hdiv.trans (dvd_lcmDiff (d := fibD p a ((c:ℕ):ℤ) d) ⟨i, hc⟩)
    have h1 : (p ^ k * m).factorization q
        ≤ (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q :=
      (hqp.pow_dvd_iff_le_factorization (hLne c)).1 hLidx
    exact le_trans h1 (@Finset.single_le_sum (Fin p) ℕ _ _
      (fun c => (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q) Finset.univ _
      (fun c _ => Nat.zero_le _) c (Finset.mem_univ c))
  have hp_mem : p ∈ (p ^ k * m).primeFactors :=
    Nat.Prime.mem_primeFactors hp (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) hn0
  have hsplit : (∑ q ∈ (p ^ k * m).primeFactors,
        (∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q) * (q - 1))
      = (∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization p) * (p - 1)
        + ∑ q ∈ (p ^ k * m).primeFactors.erase p,
            (∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q) * (q - 1) := by
    rw [← Finset.sum_erase_add _ _ hp_mem, add_comm]
  have hsplit2 : (∑ q ∈ (p ^ k * m).primeFactors, (p ^ k * m).factorization q * (q - 1))
      = (p ^ k * m).factorization p * (p - 1)
        + ∑ q ∈ (p ^ k * m).primeFactors.erase p, (p ^ k * m).factorization q * (q - 1) := by
    rw [← Finset.sum_erase_add _ _ hp_mem, add_comm]
  have hkey : p + (k - 1) * (p - 1) ≥ 1 + k * (p - 1) := by
    have hppos : 0 < p := hp.pos
    conv_rhs => rw [hk', Nat.succ_mul]
    omega
  calc ∑ c : Fin p, bound (lcmDiff (fibD p a ((c:ℕ):ℤ) d))
      ≥ ∑ c : Fin p, (1 + ∑ q ∈ (p ^ k * m).primeFactors,
          (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q * (q - 1)) :=
        Finset.sum_le_sum (fun c _ => (hstep1 c).ge)
    _ = p + ∑ q ∈ (p ^ k * m).primeFactors,
          (∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q) * (q - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, Nat.mul_one]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => (Finset.sum_mul _ _ _).symm
    _ = p + ((∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization p) * (p - 1)
        + ∑ q ∈ (p ^ k * m).primeFactors.erase p,
            (∑ c : Fin p, (lcmDiff (fibD p a ((c:ℕ):ℤ) d)).factorization q) * (q - 1)) := by
        rw [hsplit]
    _ ≥ p + ((k - 1) * (p - 1)
        + ∑ q ∈ (p ^ k * m).primeFactors.erase p,
            (p ^ k * m).factorization q * (q - 1)) := by
        exact Nat.add_le_add_left (Nat.add_le_add (Nat.mul_le_mul_right (p - 1) hSp)
          (Finset.sum_le_sum (fun q hq =>
            Nat.mul_le_mul_right (q - 1)
              (hSq q (Finset.mem_erase.1 hq).2 (Finset.mem_erase.1 hq).1)))) p
    _ ≥ 1 + (k * (p - 1)
        + ∑ q ∈ (p ^ k * m).primeFactors.erase p,
            (p ^ k * m).factorization q * (q - 1)) := by
        omega
    _ = 1 + ((p ^ k * m).factorization p * (p - 1)
        + ∑ q ∈ (p ^ k * m).primeFactors.erase p,
            (p ^ k * m).factorization q * (q - 1)) := by
        rw [hfkp]
    _ = 1 + ∑ q ∈ (p ^ k * m).primeFactors, (p ^ k * m).factorization q * (q - 1) := by
        rw [hsplit2]
    _ = bound (p ^ k * m) := by
        rw [bound]

/-! 【拆n·路2·历史归纳尝试】：card + ρ ≥ bound。独占情形 ρ = 0 退回原定理。
此归纳证明未闭合，下面仅以注释保留；同名完整定理已在文件末从匹配定理推出。
    复合步按 p 分纤维、每纤维套 T(n/p)：T 的 ρ-项恰好吸收纤维限制的冗余，
    故无需稀释、无 lcm 损失。无裂块（∀ i, p ∣ d i）情形归约为两条纯账目
    【缺口 1】Σ_c bound L_c ≥ bound n（m-摊派 + p-摊派，L_c = 纤维 c 的 lcm）
    【缺口 2】Σ_c ρ_c ≤ ρ a d（hpd 下各块恰居一纤维，原独占 ⇒ 纤维独占）。
    结构性结论（纸面已核）：
    ① 复合步不能走投影——粗化使 ρ(F′) ≥ ρ(orig)，任何 ρ-单调强化在投影下方向
       相反，p-账 k(p−1) 无法从投影族恢复；复合步必须留在原层级做纤维分解。
    ② 纤维求和账目归结为 (p−1)(1 + Σe_c − N₀) − Σρ_c + ρ(orig) ≥ k(p−1)。
    ③ 无裂块时 ρ_c = 0（fiber_essential）、Σe_c ≥ k−1（β = k 块存在）、
       Σ bound(m_c) ≥ bound(m) + (p−1)（载体摊派）——账目闭合。
    ④ 裂块情形：CRT 裂块 + 裂片本质性分析 ——开放。 -/
/- 历史尝试存档（不是可引用的 Lean 定理）：
theorem main_induction_strong : ∀ n : ℕ, 0 < n → ∀ (ι : Type*) [Fintype ι] (a : ι → ℤ)
    (d : ι → ℕ), essLcm a d = n → (∀ i, 0 < d i) → (∀ m : ℤ, ∃ i, MemAP a d i m) →
    Fintype.card ι + rho a d ≥ bound n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn ι _ a d heq hd hcover
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact absurd hn (by omega)
    by_cases hn1 : n = 1
    · subst hn1
      -- 覆盖 ⇒ ι 非空 ⇒ card ≥ 1 = bound 1
      have hnE : Nonempty ι := ⟨(hcover 0).choose⟩
      have hcard : 0 < Fintype.card ι := Fintype.card_pos (α := ι)
      rw [bound_one]
      omega
    obtain ⟨p, hp, hpd₀⟩ := Nat.exists_prime_and_dvd hn1
    by_cases hpd : ∀ i, p ∣ d i
    · -- 无裂块：纤维求和
      classical
      -- 纤维 ess-lcm 下降：纤维族的本质成员 = 原本质块在此纤维的限制，
      -- 其差 d j/p 整除 (essLcm a d)/p < essLcm a d = n
      have hLc : ∀ c : Fin p, essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) < n := by
        intro c
        have h1 : essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) ∣ n / p := by
          refine Finset.lcm_dvd (fun j _ => ?_)
          have horig : Essential a d j.1 :=
            (fiber_essential_iff (p := p) (a := a) (d := d) hp hpd ((c:ℕ):ℤ) j).1 j.2
          have hdv : d j.1 ∣ essLcm a d :=
            dvd_lcmDiff (d := fun i : {x : ι // Essential a d x} => d i.val) ⟨j.1, horig⟩
          rw [heq] at hdv
          exact div_dvd_div hp.pos (hpd j.1) hdv
        have h2 : essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) ≤ n / p :=
          Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hn hpd₀) hp.pos) h1
        have h3 : n / p < n := Nat.div_lt_self hn hp.one_lt
        omega
      have hLc0 : ∀ c : Fin p, 0 < essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) := by
        intro c
        have hnz : essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) ≠ 0 := by
          rw [show essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
              = Finset.univ.lcm (fun i : {i : Fiber p a ((c:ℕ):ℤ) //
                  Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i} =>
                  fibD p a ((c:ℕ):ℤ) d i.val) from rfl,
            Finset.lcm_ne_zero_iff]
          intro j _
          exact ne_of_gt (Nat.div_pos (Nat.le_of_dvd (hd j.1.val) (hpd j.1.val)) hp.pos)
        exact Nat.pos_of_ne_zero hnz
      -- 每纤维套 T(n/p)：card Fib_c + ρ_c ≥ bound ess-lcm_c（T 的 ρ-项吸收纤维冗余）
      have hT : ∀ c : Fin p, Fintype.card (Fiber p a ((c:ℕ):ℤ))
          + rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
          ≥ bound (essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) := by
        intro c
        have hcov' : ∀ t : ℤ, ∃ i : Fiber p a ((c:ℕ):ℤ),
            MemAP (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i t :=
          fiber_cover hp hpd hcover ((c:ℕ):ℤ)
        have hd' : ∀ i : Fiber p a ((c:ℕ):ℤ), 0 < fibD p a ((c:ℕ):ℤ) d i :=
          fun i => Nat.div_pos (Nat.le_of_dvd (hd i.1) (hpd i.1)) hp.pos
        exact ih _ (hLc c) (hLc0 c) _ (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) rfl
          hd' hcov'
      have hsum : Fintype.card ι
          + ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
          ≥ ∑ c : Fin p, bound (essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) := by
        have h2 : ∑ c : Fin p, (Fintype.card (Fiber p a ((c:ℕ):ℤ))
            + rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d))
            ≥ ∑ c : Fin p, bound (essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) :=
          Finset.sum_le_sum (fun c _ => hT c)
        rw [card_eq_sum_fiber hp a, ← Finset.sum_add_distrib]
        exact h2
      -- 0 步：n = p^k·m（k = n.factorization p，p ∤ m）
      have hn0 : n ≠ 0 := hn.ne'
      have hfk1 : 1 ≤ n.factorization p :=
        (hp.pow_dvd_iff_le_factorization hn0).1 (by rwa [Nat.pow_one])
      have hpk₀ : p ^ n.factorization p ∣ n :=
        (hp.pow_dvd_iff_le_factorization hn0).mpr (le_refl _)
      obtain ⟨mm, hmdef⟩ : ∃ mm, n / p ^ n.factorization p = mm := ⟨_, rfl⟩
      have heq' : n = p ^ n.factorization p * mm := by
        rw [← hmdef]
        exact (Nat.mul_div_cancel' hpk₀).symm
      have hpm : ¬ p ∣ mm := by
        intro hc
        have h3 : p ^ n.factorization p * p ∣ p ^ n.factorization p * mm :=
          mul_dvd_mul_left _ hc
        rw [← Nat.pow_succ, ← heq'] at h3
        exact absurd ((hp.pow_dvd_iff_le_factorization hn0).1 h3) (by omega)
      have hnE : Nonempty ι := ⟨Classical.choose (hcover 0)⟩
      -- 缺口 1：ess-摊派（Σ_c bound essLcm_c ≥ bound n）
      have hgap1 : ∑ c : Fin p, bound (essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d))
          ≥ bound n := by
        have hMne : Finset.univ.lcm (fun c : Fin p =>
            essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) ≠ 0 := by
          rw [Finset.lcm_ne_zero_iff]
          intro c _
          exact Nat.pos_iff_ne_zero.mp (hLc0 c)
        have hB : essLcm a d / p ∣ Finset.univ.lcm (fun c : Fin p =>
            essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) :=
          essLcm_div_dvd_lcm_essLcm_fibD hp hd hpd (by rw [heq]; exact hpd₀)
        have hmono : bound (essLcm a d / p)
            ≤ bound (Finset.univ.lcm (fun c : Fin p =>
              essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d))) :=
          bound_le_of_dvd hMne hB
        have hcard_eq : (Finset.univ : Finset (Fin p)).card = p := by
          rw [Finset.card_univ, Fintype.card_fin]
        have hp1 : 0 < p := hp.pos
        have hz : ∑ c : Fin p, bound (essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d))
            ≥ bound (Finset.univ.lcm (fun c : Fin p =>
              essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)))
              + (Finset.univ : Finset (Fin p)).card - 1 :=
          bound_lcm_sum (ι := Fin p) Finset.univ
            (fun c : Fin p => essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d))
            ⟨⟨0, hp.pos⟩, Finset.mem_univ _⟩
        have hbook : bound (essLcm a d / p) + (p - 1) = bound n := by
          rw [heq]
          exact bound_div_pow_add hp hn0 hpk₀ hfk1 (by rwa [hmdef])
        omega
      -- 缺口 2：Σ_c ρ_c ≤ ρ a d
      have hgap2 : ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) ≤ rho a d :=
        sum_rho_le hp hpd
      -- 合并
      calc Fintype.card ι + rho a d
          ≥ Fintype.card ι
            + ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) :=
            Nat.add_le_add_left hgap2 (Fintype.card ι)
        _ ≥ ∑ c : Fin p, bound (essLcm (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)) := hsum
        _ ≥ bound n := hgap1
    · -- 裂块：∃ i, p ∤ d i。—— 本轮确立【新架构】（纸面 + explore/*.py 穷举数值验证，762k+ 实例）：
      -- 架构：对 problem7 直接归纳，测度 = lcmDiff n（全本质情形 essLcm = lcmDiff）；
      --   纤维分析一律改用**极小子覆盖**（去可约块，见 §1035 exists_minimal_subcover），这是打通的关键。
      --  A. 无裂块步（∃ 素 q | n，∀ i, q | d i）【纸面已证】：card = Σ_c card(F_c)；
      --     每根纤维的片系统 F_c 约化为极小子覆盖 F_c⁰：全本质、覆盖保持、非本质片全部清空；
      --     关键提升：本质-in-纤维 ⟹ 本质-原族（私有点提升），故 F_c⁰ 各块 t-差 ∣ n/q < n ⟹ IH；
      --     Σ_c bound(lcmDiff F_c⁰) ≥ bound(lcm_c lcmDiff F_c⁰) + (q−1) ≥ bound(n/q) + (q−1) = bound n。
      --  B. 裂块步（∃ 本质 i, q ∤ d i；此时 d_i | n/q^{v_q(n)}）：card = Σ_c card(F_c) − (q−1)#I₀
      --     ≥ Σ_c bound(L_c) + junksum − (q−1)#I₀，L_c = lcmDiff(F_c⁰)，
      --     junksum = Σ_{i∈I₀}(q − aᵢ)，aᵢ = 块 i 有私有点的纤维数（= 本质片数，≥ 1）；
      --     Σ_c bound(L_c) = bound n + Σ_p (p−1)·M_p，M_p := Σ_c v_p(L_c) − v_p(n/q) ≥ 0（载体摊派）；
      --     故归结为 **(★)：Σ_p (p−1)·M_p ≥ Σ_{i∈I₀}(aᵢ − 1)**（等价于含 junksum 的原始形式）。
      -- 数值验证结论（explore/*.py；注意：K=5 枚举会遗漏 6+ 块族，须用 K≥6 深枚举复核！）：
      --   · T⁷（card ι ≥ bound(essLcm)）0 反例，且 minCard ≡ bound(essLcm) 恒取等（紧）；
      --   · **(★)（Σ_p (p−1)M_p ≥ Σ_{I₀}(aᵢ−1)）已证伪**：n=12, q=3,
      --     F = {0%3, 0%4, 1%4, 2%4, 7%12, 11%12}（全本质、lcmDiff=12、aᵢ≡2）：
      --     Σ_p(p−1)M_p = 2 < 3 = Σ(aᵢ−1)（K=5 枚举遗漏的 6 块族）。故素幂容量不足以独立付款。
      --   · **精确恒等式（修正版）**：记 slack(F) := card(F) − bound(lcmDiff F)，裂块步（q | n、I₀ ≠ ∅）中
      --     **slack(F) = Σ_c slack(F_c⁰) + [Σ_p (p−1)M_p − Σ_{I₀}(aᵢ − 1)]**（恒等，n=12 例核验：1 = 2 − 1）。
      --     故 case (b) ⟺ Σ_c slack(F_c⁰) ≥ Σ_{I₀}(aᵢ−1) − Σ_p(p−1)M_p。
      --   · **(PFC) 成立（0 反例）**：∀c: Σ_{i∈I₀(c)}(1 − 1/aᵢ) ≤ bound(L_c) − 1。
      --     配合 Σ_c bound(L_c) = bound(n) + Σ_p(p−1)M_p（因 max_c v_p(L_c) = v_p(n/q)）得充分条件
      --     **(SLACK)：Σ_c slack(F_c⁰) ≥ bound(n) − q**（n=12 例：2 = 2 取等；a=1 例：0 = 0）。
      --   · 逐素数强化 (★★★_p)、"|F| ≥ bound(M)+(q−1)" 等候选同源失败（K=5 遗漏所致），已废弃。
      --   · 已证伪的候选：T‴（card+ρ ≥ bound(lcmDiff)，{ℤ, 0 mod 30} 反例）；
      --     L2（p∤d 本质块私有点纤维唯一，3482 反例）；R1（逐纤维 #ess ≥ bound，241046 反例）；
      --     T¹⁹（"兄弟块"强化，{0,2,4,1,3,5 mod 6}）。
      --   · 结构：非本质裂块可 WLOG 缩为 q 整除（保覆盖/计数/essLcm）；本质裂块"碎片保覆盖"变换仅 aᵢ = 1 时安全。
      --   · slack 的已观测来源：同差块组（如 {0,1,2,3 mod 4}：slack = m_ν − bound(ν) = 1；
      --     n=12 例中 F₁⁰、F₂⁰ 各为 4 块同差 4，各生 slack 1）；纤维化下似超可加。
      -- 【T²³⁺ 架构】σ(F) := Σ_ν [m_ν − bound(ν)]₊（m_ν = 差为 ν 的块数；同差块组松弛）。
      --   归纳陈述：**T²³⁺: card(F) ≥ bound(lcmDiff F) + σ(F)**（全本质族；n=1 基例：card=1, σ=0 ✓）。
      --   归纳步（q | n，F_c⁰ = 纤维极小子覆盖，L_c = lcmDiff F_c⁰，IH 用于 F_c⁰）：
      --     case (a)（I₀=∅）：card = Σ_c card(F_c) ≥ Σ_c [bound(L_c) + σ(F_c⁰)]
      --       = bound(n) + Σ_p(p−1)M_p + Σ_c σ(F_c⁰) ≥ bound(n) + σ(F)   ——需 (S4)|_{I₀=∅}。
      --     case (b)：card = Σ_c card(F_c) − (q−1)#I₀ ≥ bound(n) + Σ_p(p−1)M_p + Σ_c σ(F_c⁰) − Σ_{I₀}(aᵢ−1)
      --       ≥ bound(n) + σ(F)   ——需 (S4)。
      --   (S4)：σ(F) + Σ_{i∈I₀}(aᵢ − 1) ≤ Σ_c σ(F_c⁰) + Σ_p (p−1)M_p。
      -- 【重要更正·K=7 枚举】**朴素 σ（仅同差块组）不足以证明 (S4)**：
      --   n=24, q=3, F = {0%2, 0%3, 1%8, 3%8, 5%8, 7%24, 23%24}（全本质、lcmDiff=24）：
      --   该族 σ(F)=0、Σ(aᵢ−1)=4、Σ(p−1)M_p=3，而 Σ_c σ(F_c⁰)=0 < 1 ⇒ (S4)/(S3) 反例（K=7 共 252 例，
      --   均含 7 块，K=6 枚举不可见——**K=5/6 两次不够，候选断言必须 K≥7 复核**）。
      --   失败机制：σ 低估"共集对齐"纤维的松弛——如 F₁⁰ = {(1,2),(0,8),(6,8),(4,8),(2,8)}：
      --   σ=0 而 slack=1（4 个 d=8 块全落在偶共集内，其诱导系统 {(0,4),(3,4),(2,4),(1,4)} 有同差超额 1）。
      --   ⇒ 正确的 σ 必须**递归**捕捉共集层结构。
      -- 【σ_rec·定稿】设 q*(F) := lcmDiff(F) 的最小素因子（正则选取）。定义
      --   **σ_rec(F) := max( σ(F), Σ_c σ_rec(F_{c*}⁰) + Σ_p(p−1)M_p^{q*} − Σ_{i∈I₀}(aᵢ−1) )**（q* 的纤维分解），
      --   其中 σ(F) := Σ_ν[m_ν−bound(ν)]₊。递归良基（子族 lcmDiff ≤ n/q* < n）；n=1 时 σ_rec = 0。
      --   数值核验（n ≤ 24, K=7 全枚举 5834 个全本质族，含此前击穿朴素 σ 的 K=7 族与 n=30 九块例）：
      --     · **(C′) σ_rec(F) ≤ slack(F)：0 反例**（安全性，从不高估）；
      --     · **(S5)【唯一剩余引理】∀ 素 q | n: Σ_c σ_rec(F_c⁰) + Σ_p(p−1)M_p ≥ σ(F) + Σ_{i∈I₀}(aᵢ−1)：0 反例**
      --       （对正则 q* 的 (S5) 即足够）。
      --   **T²³⁺ 归纳（现完整）**：用精确恒等式 card(F) = bound(n) + Σ(p−1)M_p + Σ_c slack(F_c⁰) − Σ(aᵢ−1)，
      --   由 IH（slack(F_c⁰) ≥ σ_rec(F_c⁰)，即子族的 T²³⁺）与 (S5) 得
      --   card(F) ≥ bound(n) + max(σ(F), B′(q*)) = bound(n) + σ_rec(F)  ✓。
      --   （(C′) 不需要单独证明：它是 T²³⁺ 的推论。）
      -- 历史核验与已证伪候选：T⁷（card ≥ bound(essLcm)）0 反例且紧；(PFC) 0 反例；
      --   已证伪：T‴、L2、R1、T¹⁹、(★)、(★★★_p)、朴素 (S4)/(S3)（K=7 反例 252 例）。
      --   **教训：候选断言必须 K ≥ 7 深枚举复核（K=5/6 两次漏检）。**
      -- 【最终结构·本轮定稿】记 slack(F) := card − bound(n)、net(F,q) := Σ_p(p−1)M_p − Σ_{I₀}(aᵢ−1)。
      --   精确恒等式（两类情形统一）：**slack(F) = net(F,q) + Σ_c slack(F_c⁰)**（望远镜）。
      --   由此：T²³⁺(F) ⟺ slack(F) ≥ σ_rec(F)，且 σ_rec 的递归 = 沿分解树取"割值最大值"，
      --   展开即得 **[T²³⁺ ⟺ (A')]**：**(A') σ(G) ≤ slack(G)（一切全本质覆盖 G）**。
      --   归纳步的最小形式：**T²³⁺(F) ⟸ T²³⁺(子族) + (S5)(F, q*)**，其中
      --   **(S5)(F,q): σ(F) + Σ_{i∈I₀}(aᵢ−1) ≤ Σ_c σ_rec(F_c⁰) + Σ_p(p−1)M_p ⟺ B′(F,q) ≥ σ(F)**。
      --   ——(S5) 即"B′ 分支支配 σ 分支"，是整个数学侧**唯一剩余引理**。
      --   K=7 深枚举（n ≤ 24，5834 全本质族，含手工九块例）复核状态（**仅小 n 有效**，见下方陷阱记录）：
      --     (A') 直接 0 反例【n=60 已证伪】；(S2*)（无裂块，σ ≤ Σ_c σ(F_c⁰) + Σ(p−1)M_p）0 反例【n=60 已证伪】；
      --     **(S5) 0 反例（n=60 亦通过）**；(C′) σ_rec ≤ slack 0 反例；**(TGT) 0 反例（n=60 亦通过）**。
      -- 【B′ = slack·已证】给定子族 T²³⁺（即 (C′)-子族）：
      --   · B′(F,q) ≤ slack(F)：逐子族 σ_rec(F_c⁰) ≤ slack(F_c⁰)（IH）；
      --   · B′(F,q) ≥ slack(F)：由 σ_rec ≥ B′ 的定义沿树展开至叶（叶 σ_rec = σ = 0），得
      --     B′(F,q) ≥ Σ_{内部节点} net = slack(F)（望远镜）。
      --   于是 **B′(F,q) = slack(F) 对一切素 q | n**，且 σ_rec(F) = max(σ(F), slack(F))。
      --   故 **T²³⁺(F) ⟺ (A′)(F)**（在子族 IH 下），(S5) ≡ (A′) ≡ (TGT)：
      --   **(TGT): σ(F) ≤ Σ_c slack(F_c⁰) + net(F,q)**（一切素 q | n；K=7 0 反例，n=60 实例亦通过）。
      -- 【小 n 陷阱·第五次教训】以下"朴素 σ"路线族在 n=60 被一个实例整体证伪（仅小 n 成立，
      --   故废弃；保留此记录防止重蹈）：
      --   反例：F = {0..5 mod 12} ∪ {0..7 mod 20} ∪ {补类 18 块 mod 60}（card=32，cover、全本质、
      --   lcmDiff=60，q=2）。数据：σ(F)=11、slack=23、Σ(p−1)M_p=7；
      --   逐层 δ：ν=6: h=6,b=4,δ=1；ν=10: h=8,b=6,δ=1；ν=30: h=18,b=8,δ=7 ⟹ Σδ=9 > 7 ⟹
      --   **(D) 假；(S2*) 假（13 > 4+7=11）；(A′) 朴素版假（17 > 7）；(A″-p=2) 假（2 > 1）；
      --   唯一性/不交性假（ν=6 与 ν=10 两 Case-2 层并存且均跨纤维）。**
      --   但 **(S5)/(TGT) 在同实例通过**（11 ≤ Σ_c σ_rec(F_c⁰) + 7，纤维 σ_rec 经自身子层
      --   M_3=M_5=1 抬到 ≥6/根）——递归 σ_rec 是唯一承载付款的结构（再次确认）。
      --   教训重申：凡"朴素 σ/池化"断言必须经 n ≥ 60 级压力测试（explore/record_n60.py 已存）。
      -- 【σ_rec 版的证明结构（最终目标，机制已在多例验证）】：
      --   精确恒等式 slack(F) = net(F,q) + Σ_c slack(F_c⁰)（望远镜）⟹ T²³⁺(F) ⟸ IH(子族) + (S5)。
      --   (S5) 的机制：顶层 σ-超额与 Σ(aᵢ−1) 缺口由两层支付——
      --     (1) 顶层 M_p：素数载体在纤维间的多余拷贝（每一 (层 ν, 素 p) 组合可用
      --         v_p(ν)·(n₊−1) ≤ M_p 单独支付；多层共享时由跨素数再分配抵补，
      --         如 n=60 例 δ_30=7 = Σ_p(p−1)v_p(30)(n₊−1) = 1+2+4 恰配平）；
      --     (2) 子族 σ_rec 的递归内容：子层的 M-项把更深的载体余量逐级上传
      --         （n=60 例中每根纤维 σ_rec ≥ 6 全部来自其子分解）。
      --   情形 (b) 同机制：q∤ν 组（I₀ 块）的合并（μ=ν 的 I₁ 块同层）与 Σ(aᵢ−1) 由更深层回传。
      -- 已完成：架构全链、B′=slack、恒等式、base、case (a)/(b) 的归结；待证：(S5) 的递归配平
      --   （对分解树的归纳，每个节点上"顶层 M_p + 子层 σ_rec"双源覆盖本层需求）。【开放】
      sorry
-/

/-! ## 新架构·可存活部件：σ 与 (A′) 主目标

本节形式化与最终架构任何形态都兼容的部分：
- σ（同差块组超额）的定义与基本引理；
- 唯一剩余目标 T²³′ 的精确陈述（(A′)/(S5)/(TGT) 的最简等价形式，
  即一切全本质覆盖 card ≥ bound(lcmDiff) + σ；n=60 压力实例已通过此形式）；
- 基例（已证）；
- 由 T²³′ 组装 problem7（σ ≥ 0）。
-/

/-- 差为 ν 的块数 m_ν。 -/
def diffCount {ι : Type*} [Fintype ι] (d : ι → ℕ) (ν : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => d i = ν)).card

/-- 同差块组超额 σ(F) := Σ_ν [m_ν − bound(ν)]₊（Nat 截断即 ₊）。 -/
def sigma {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ :=
  (Finset.univ.image d).sum (fun ν => diffCount d ν - bound ν)

/-- bound n 恒正（下界函数正性；由此 T23prime_base 中 σ ≥ 0 的组装可行）。 -/
theorem bound_pos (n : ℕ) : 0 < bound n := by
  rw [bound]; omega

/-- σ 的核数守恒：Σ_ν m_ν = card。 -/
theorem diffCount_sum {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    (Finset.univ.image d).sum (diffCount d) = Fintype.card ι := by
  classical
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_image d Finset.univ).symm

/-- σ ≤ card：σ 只计各组超出 b-容量的部分，故不超过块数（由核数守恒 diffCount_sum 得）。 -/
theorem sigma_le_card {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    sigma d ≤ Fintype.card ι := by
  classical
  have h1 : sigma d ≤ (Finset.univ.image d).sum (diffCount d) := by
    refine Finset.sum_le_sum (fun ν _ => ?_)
    exact Nat.sub_le _ _
  rwa [diffCount_sum d] at h1

/-- 差映射单射时 σ = 0（每群大小 1 ≤ bound）。 -/
theorem sigma_eq_zero_of_injective {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hinj : Function.Injective d) : sigma d = 0 := by
  classical
  refine Finset.sum_eq_zero (fun ν hν => ?_)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hν
  have h1 : diffCount d (d i) = 1 := by
    rw [diffCount, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  rw [h1]
  have hb := bound_pos (d i)
  omega

/-! ## 保证可用部件·二期：无包含块引理 (††)、bound 乘性、(P_p)/(Rp) 目标陈述

本节的陈述与证明不依赖任何剩余路线选择（无论 (T'')/(U''-nt) 如何最终证明）：
- (††) 无包含块引理：全本质族中块之间不可能互相包含（本质性核）；
- bound 乘性：bound(mn) + 1 = bound m + bound n（m,n 互素）——全部配平恒等式的枢纽；
- (P_p)/(Rp) 的精确陈述（数学侧已证/已归约，形式化接驳留待最后）。 -/

/-- 若 d_j ∣ d_i 且 a_i ≡ a_j (mod d_j)，则块 i 的所有点都被块 j 覆盖（i 的块 ⊆ j 的块）。 -/
theorem memap_of_dvd_of_dvd_sub {ι : Type*} {a : ι → ℤ} {d : ι → ℕ} {i j : ι}
    (hdvd : d j ∣ d i) (hsub : (d j : ℤ) ∣ (a i - a j)) :
    ∀ m : ℤ, MemAP a d i m → MemAP a d j m := by
  intro m hm
  obtain ⟨k, hk⟩ := hm
  obtain ⟨t, ht⟩ := hsub
  have hdi : ((d i : ℤ)) = (d j : ℤ) * ((d i / d j : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  refine ⟨t + ((d i / d j : ℕ) : ℤ) * k, ?_⟩
  have haj : a j = a i - (d j : ℤ) * t := by linarith
  rw [hk, haj, hdi]
  ring

/-- **(††) 无包含块引理**：全本质族中，若 i ≠ j 且 d_j ∣ d_i、a_i ≡ a_j (mod d_j)，
则矛盾（块 i 被块 j 包含 ⟹ i 的独占点被他块覆盖）。 -/
theorem no_containment_of_essential {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i) {i j : ι} (hij : i ≠ j)
    (hdvd : d j ∣ d i) (hsub : (d j : ℤ) ∣ (a i - a j)) : False := by
  obtain ⟨m, hm, hpriv⟩ := hess i
  exact hpriv j hij.symm (memap_of_dvd_of_dvd_sub hdvd hsub m hm)

/-- (††) 推论（同公差同余）：全本质族中，两块公差相等且同余 ⟹ 同一块（i = j）。 -/
theorem eq_of_same_diff_congr {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i) {i j : ι}
    (hd_eq : d i = d j) (hsub : (d j : ℤ) ∣ (a i - a j)) : i = j := by
  by_contra hij
  exact no_containment_of_essential hess hij (by rw [hd_eq]) hsub

/-- **bound 乘性**：m, n 互素时 bound(m·n) + 1 = bound m + bound n。 -/
theorem bound_mul_add_one {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : m.Coprime n) :
    bound (m * n) + 1 = bound m + bound n := by
  unfold bound
  have hfac : ∀ p, (m * n).factorization p
      = m.factorization p + n.factorization p := by
    intro p
    rw [Nat.factorization_mul hm hn]
    rfl
  have hzero_m : ∀ p ∈ m.primeFactors, n.factorization p = 0 := by
    intro p hp
    have hpm : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
    have hpn : ¬ p ∣ n := by
      intro hpn
      have h1 : p ∣ m.gcd n := Nat.dvd_gcd hpm hpn
      rw [hcop.gcd_eq_one] at h1
      exact (Nat.mem_primeFactors.mp hp).1.ne_one (Nat.dvd_one.mp h1)
    exact Nat.factorization_eq_zero_of_not_dvd hpn
  have hzero_n : ∀ p ∈ n.primeFactors, m.factorization p = 0 := by
    intro p hp
    have hpn : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    have hpm : ¬ p ∣ m := by
      intro hpm1
      have h1 : p ∣ n.gcd m := Nat.dvd_gcd hpn hpm1
      rw [hcop.symm.gcd_eq_one] at h1
      exact (Nat.mem_primeFactors.mp hp).1.ne_one (Nat.dvd_one.mp h1)
    exact Nat.factorization_eq_zero_of_not_dvd hpm
  have hdisj : Disjoint m.primeFactors n.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpm hpn
    have h1 : p ∣ m.gcd n :=
      Nat.dvd_gcd (Nat.mem_primeFactors.mp hpm).2.1 (Nat.mem_primeFactors.mp hpn).2.1
    rw [hcop.gcd_eq_one] at h1
    exact (Nat.mem_primeFactors.mp hpm).1.ne_one (Nat.dvd_one.mp h1)
  rw [Nat.primeFactors_mul hm hn, Finset.sum_union hdisj]
  have hsplit : ∑ p ∈ m.primeFactors, (m * n).factorization p * (p - 1)
      = ∑ p ∈ m.primeFactors, m.factorization p * (p - 1) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hfac p, hzero_m p hp, add_zero]
  have hsplit2 : ∑ p ∈ n.primeFactors, (m * n).factorization p * (p - 1)
      = ∑ p ∈ n.primeFactors, n.factorization p * (p - 1) := by
    apply Finset.sum_congr rfl
    intro hp' hp
    rw [hfac hp', hzero_n hp' hp, zero_add]
  rw [hsplit, hsplit2]
  omega

/-- **配平枢纽恒等（算术核）**：Σ_{p|ν}((p−1)v_p(ν)+1) = bound(ν) + ω(ν) − 1。
（多素配平全部归约的枢纽；与 bound 乘性 bound_mul_add_one 配套。） -/
theorem sum_bp_eq_bound_add {ν : ℕ} (_hν : ν ≠ 0) :
    ∑ p ∈ ν.primeFactors, ((p - 1) * ν.factorization p + 1)
      = bound ν + ν.primeFactors.card - 1 := by
  unfold bound
  have h1 : ∑ p ∈ ν.primeFactors, ((p - 1) * ν.factorization p + 1)
      = (∑ p ∈ ν.primeFactors, (p - 1) * ν.factorization p)
        + ν.primeFactors.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : ∑ p ∈ ν.primeFactors, (p - 1) * ν.factorization p
      = ∑ p ∈ ν.primeFactors, ν.factorization p * (p - 1) := by
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [h1, h2]
  omega

/-- **min-平移恒等（逐组核对核）**：B ≤ S 时
min(m,S) − min(m,B) = min(m−B, S−B)（Nat 截断）。 -/
theorem min_sub_min_eq {m B S : ℕ} (hBS : B ≤ S) :
    min m S - min m B = min (m - B) (S - B) := by
  omega

/-- 真实 p-线普查：只计 p|d 的块，按 p-自由部分的同余类判断其是否在线上。
β=0 不计裂块；y 的周期为 lcmDiff 的 p-自由部分。 -/
def lineCount {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (p : ℕ) (y : ℤ) (b : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => p ∣ d i ∧ (d i).factorization p = b ∧
    (d i / p ^ (d i).factorization p : ℤ) ∣ y - a i)).card

/-- 过载层集（按层去重，与过载组计数不同）。 -/
def overfullLayers {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : Finset ℕ :=
  ((Finset.univ.image d).filter (fun ν => p ∣ ν ∧ bound ν < diffCount d ν)).image
    (fun ν => ν.factorization p)

/-- 真实线的截断普查和 F(y)。 -/
def lineScore {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (p : ℕ) (y : ℤ) : ℕ :=
  ∑ b ∈ Finset.range ((lcmDiff d).factorization p + 1),
    min (lineCount a d p y b) ((p - 1) * b + 1)

/-- 给定真实线上吃满 b(p^β) 的过载层。 -/
def saturatedLayers {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (p : ℕ) (y : ℤ) : Finset ℕ :=
  (overfullLayers d p).filter (fun b => (p - 1) * b + 1 ≤ lineCount a d p y b)

/-- **(A) 已证伪的命题存档**，不是定理：即使 M 是真实线普查，也可达标而无最深块。
文件末 `SigmaRouteAudit.not_deep_presence` 给出全本质覆盖反例。 -/
def deep_presence {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (p : ℕ) : Prop :=
  ∀ y : ℤ, (p - 1) * (lcmDiff d).factorization p + 1 ≤ lineScore a d p y →
    0 < lineCount a d p y ((lcmDiff d).factorization p)

/-- **(B)-核引理（本轮证明的新碎片，(††) 的直接推论）**：若线 y 含深块 (a, p^αμ)，
则对每个 μ' | μ 的浅层单元 (β', μ')：同线块偏移 a' 满足 a' ≡ y ≡ a (mod μ')，
而 (††)（μ' | μ ⟹ p^{β'}μ' | p^αμ）强制 a ≢ a' (mod p^{β'}μ')，即 (a'−a)/μ' ≢ 0 (mod p^{β'})；
模 p^{β'}μ' 的 y-类内共 p^{β'} 个残类，a 的类被禁 ⟹ **m_{(β',μ')}(y) ≤ p^{β'} − 1**。
实例核对（反例）：深块 (a,80)（μ=5）在线上 ⟹ 10-块 (μ'=5) 须避 a mod 10 ⟹ 同线 10-块仅
单一偏移 ⟹ M_1(y) ≤ 1 < 2 = b(p) ✓✓（与全表数据吻合：达标线 c₁=1）。
一般推论：所有浅层单元的 μ' | μ_deep 时，逐层"每单元缺一"。 -/
theorem B_core_perCell {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i) {p β' α μ' μ : ℕ}
    (hβα : β' ≤ α) (hμ' : μ' ∣ μ) {i j : ι} (hij : i ≠ j)
    (hi : d i = p ^ α * μ) (hj : d j = p ^ β' * μ')
    (hcong : (d j : ℤ) ∣ (a i - a j)) : False := by
  have hdiv : d j ∣ d i := by
    rw [hi, hj]
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p hβα) hμ'
  exact no_containment_of_essential hess hij hdiv hcong

/-- **(V-strong) 判定（本轮最强形式，0/4710 邻域 + 本体全验）**：非平凡区中，
线含深块（M_α(y) ≥ 1）⟹ **过载层零饱和**（乃至连一层都不饱和）。
配 (A)（达标⟹深块在）：达标线上过载层零饱和 ⟹ (V)（≤1 版）以全额余量成立。
历史证明素材（仅探索，不是 V-strong 的证明）：B-核给受限单元 ≤ p^{β'}−1。
2026-10-10 更正：p=2、β'=3 时 7>4，故“p=2 全闭”的旧说法也错误；
且深块存在版已被 `SigmaRouteAudit` 变体证伪。`True` 存档不证明本注释中的候选。
-/
theorem V_strong_record : True := trivial

/-- **(V-strong°) 历史探索骨架（载体私有线版，未证）**：
载体私有线 y° 上恒有深块（载体自身，故 (A) 无需用于最终链）；目标是
**y° 上过载层零饱和**（验证 0/4710+）。
证明骨架（本轮完成的分析）：
1. **(††)-封锁集**：单元 (β',μ') 的线上块偏移 a' 必须避开一切块 (a_i,d_i) 满足 d_i | p^{β'}μ' 的类
   （a' ≢ a_i mod d_i）——比 B-核（仅深块）更强：封锁来自所有除子块；
2. **载体封锁**：载体 (a*,p^αμ*) 封锁一切单元 μ' | μ*：清除 y°-类 mod μ' 内 a* 的类 ⟹
   该单元 ≤ p^{β'}−1；
3. **单单元即闭**：p=2,β'=1 等情形 p^{β'}−1 < b(p^{β'}) 直接不饱和；
4. **多单元双向封锁（新）**：设单元 (β',μ'_1)、(β',μ'_2)（μ'_i | μ*）皆欲饱和：
   取块 B_2 ∈ 第二单元：它封锁第一单元的一个类；B_1 ∈ 第一单元封锁第二单元的一个类；
   连同载体封锁，两单元各损失 ≥ 2 个类 —— p=2,β'=1 时每单元仅 2 类 ⟹ 两单元 ≤ 1+1 = 2 = b(p)
   边界，需第三重封锁（同 μ 的更深块或 (††) 跨单元链）压到 ≤ 1；
5. **边界案例**（p=2,β'=2；p≥3）：需多块联合计数（已定位，未写完）。
-/
theorem V_strong_carrier_skeleton : True := trivial

/- **(V-reverse)·机制最终综合（本轮决定性实验锚定）**：
【实验 1】n=48 定向构造：45957 个"载体线 M₁ 饱和"实例——**全部落在 α∈O 的平凡区**
（48-块补全覆盖必使 α-层过载）。
【实验 2】n=240 决定性判定：加入自由单元（6-块，μ'=3 ∤ μ*=5）后 4M 次搜索：
合法实例仅 10 个、**非平凡区 0 个**、(V) 0 违例。
⟹ **自由单元（不被任何深块整除的浅单元）只能在平凡区出现**；
非平凡区中 B-核封锁（单单元已证 + 多单元双向封锁最小情形已手工证）无自由单元可用 ⟹ (V)。
最终证明目标（逆否形式）：**载体线饱和 ⟹ Σ_Oβ ≥ α**（即 α∈O 或更深的过载被迫出现）。
机制综合：(i) 深块必需（lcm）；(ii) 深块封锁可整除单元（B-核，(††)）；(iii) 自由单元的饱和取值
迫使深块族膨胀至过载（实验 1）——(iii) 的定量证明是最后一式（待）。 -/

/- **【过载扩张现象·探索收尾】** 受控枚举（n=48，66 万合法实例）：
  ① 达标+1-层饱和共存实例 75 万个（16-块×3-4 + 线上自由 6-块×2 + 48-块补全），
    载体线普查 {1:2, 4:≥3}、F≥5：但全部落在 α∈O（48-块补全覆盖必过载）⟹ 平凡区，(V) 不适用；
  ② 全域 |O| 分布：100% 为 (|O|=1, Σ_Oβ≥α) —— **n=48 下非平凡区结构性为空**；
  ③ 单过载层达标线（|O|=1 非平凡，如 {6:5,16:1,48:7}）由 (R'') 的 |O|≤1 已证情形覆盖 ✓。
  ⟹ (V) 的"≤1"设计被证实精确：单饱和被允许（|O|=1 情形已证），双饱和仅在非平凡区被禁——
    而非平凡区的存在需 n 足够大（n=240 起现，且所有实例 0 违例）。 -/

/-- **(B) 已证伪的真实线命题存档**，不是定理。
`SigmaRouteAudit.not_one_saturation` 的变体满足非平凡、深块存在与达标，但有两饱和层。
深块在线上存在，并不表示它在该线上有独占点；原封锁机制不能忽略此区别。 -/
def one_saturation {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (p : ℕ) : Prop :=
  ∀ y : ℤ, 0 < lineCount a d p y ((lcmDiff d).factorization p) →
    (∑ b ∈ overfullLayers d p, b) < (lcmDiff d).factorization p →
    (saturatedLayers a d p y).card ≤ 1

/- ══════════ 【文献参照·非我方成果】与【我方独立成果清单】 ══════════
【文献参照（仅备查，不计入我方成果）】
原题断言即 R.J. Simpson 定理（Acta Arith. 45 (1985) 145–152）：regular（无真子覆盖 = 全本质）
覆盖的列数 ≥ Σα_i(p_i−1)+1；Korec (Acta Arith. 44 (1984)) 对互斥覆盖同款。其复证全文在
arXiv:1904.04806 附录 A（本仓库 explore/lit/ 存有该 PDF 与文本）。
【我方独立成果清单（本项目自建，含验证与形式化）】
A. 定理级：
  A1. **(PC)-一般 κ 定理**（挖点类覆盖 ℤ/p^κ 的普查下界 b(p^κ)）：投影归纳 + 静态不等式，
      5272 实例 0 反例（explore/verify_pairing_level.py 前身）。
  A2. **(P_p) 全部情形**（一切素数与指数）：链 (PC) ⟹ (L⁺) ⟹ (L) ⟹ (P_p)。
  A3. **(R'') 的 |O|≤1 情形**：由 (L⁺) 直接证明。
  A4. **(††) 无包含块引理**（Lean 带完整证明）+ 推论 + **B-核引理**（深块偏移禁区，Lean 带证明）。
  A5. **bound 乘性**（Lean 证）、**配平枢纽恒等** Σ_{p|ν}((p−1)v_p+1)=bound ν+ω(ν)−1（Lean 证）、
      min-平移恒等（Lean 证）。
B. 架构级（我方自建的 σ-强化路线，独立于文献）：
  B1. 注释中的归约：TGT ⟸ (R) ⟸ Σ_p(Rp) ⟸ (R'')；Lean 装配尚待完成，(V) 候选已证伪；
  B2. 过载层结构、δ-形、逃离计数、封锁机制（单胞已证 + 最小多胞手工证）；
  B3. (V)/(A)/(B)/deep_saturation 已以无 sorry 的真实线 Prop 定义和否定证明存档。
C. 方法论级：十次陷阱勘误档案（lcmlist 铁律、形状覆盖、(T'') 完整勘误链等）、
  47+ 验证脚本、危险形状类穷举与邻域扰动验证矩阵。
状态：原题由文献定理支撑（非我方）；我方 σ-强化版 T²³′ 的 (Rp)/(R'') 及 Lean 接驳仍开放。 ══════ -/

/-- **(V) 已证伪的真实线命题存档**，不是定理。
文件末 `SigmaRouteAudit.not_V_final`：n=720，O={1,2}，y=6 上两层同时饱和。 -/
def V_final {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (p : ℕ) : Prop :=
  ∀ y : ℤ, (p - 1) * (lcmDiff d).factorization p + 1 ≤ lineScore a d p y →
    (∑ b ∈ overfullLayers d p, b) < (lcmDiff d).factorization p →
    (saturatedLayers a d p y).card ≤ 1

/-! (P_p) 的旧开放辅助目标已从零告警副本移除；原始陈述保存在旧版本中。
最终匹配路线不依赖此目标。 -/

/-- **过载组计数 t_p**（多素配平的关键量）：差为 ν 的组过载 ⟺ m_ν > bound ν。 -/
def overfullCount {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : ℕ :=
  (((Finset.univ.image d).filter (fun ν => p ∣ ν ∧ bound ν < diffCount d ν)).card)

/-! (Rp) 的旧开放辅助目标已从零告警副本移除；原始陈述保存在旧版本中。
最终匹配路线不依赖此目标。 -/

/-- **⚠ (T'') 已证伪（记录存档，勿用）**：反例 n=240, 普查 {10:8, 12:6, 80:8}（lcm=240 ✓），
O={1,2}, Σ_Oβ=3 < v₂=4。原陈述（|O| ≥ 2 ⟹ Σ_Oβ ≥ v_p(n)）为假；
全链 TGT/Pp/Rp/(R'')/(R) 在该族上仍全真——多素配平的正确形式是 (R'')/(Rp)（下层 δ-形），
|O|≥2 情形的机制候选为「深层饱和」（α∉O ⟹ S_α 吃满 b(p^α)）。此定理仅作反例档案保留。 -/
def Tpp_levels_falsified_record {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : Prop :=
  2 ≤ (overfullLayers d p).card →
    (lcmDiff d).factorization p ≤ ∑ b ∈ overfullLayers d p, b

/-- **深层饱和候选题（2026-10-10 已证伪，只以 Prop 存档）**：若 p 的过载层至少两层、
且最深层 α := v_p(lcmDiff) 非过载（α-层所有组 m_ν ≤ bound ν），则 α-层的 p-普查吃满 b(p^α)：
Σ_{v_p(ν)=α} min(m_ν, b(p^α)) ≥ b(p^α)。
（n=240 反例 {10:8,12:6,80:8} 中 ν=80: m=8 ≥ b₂(16)=5 满足；由 S_α = b(p^α) ≥ (p−1)(α−Σ_Oβ)
立即给出 (R'') 的 |O|≥2 情形。n=24 例 {6:5,12:1,24:2}（|O|=1）不满足——故 |O|≥2 假设必需。
旧采样未找到反例；文件末 n=720 的反例满足前提，但 S₄=2<5。） -/
def deep_saturation_candidate {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : Prop :=
  2 ≤ (overfullLayers d p).card →
    (∀ ν ∈ (Finset.univ.image d), p ∣ ν → ν.factorization p = (lcmDiff d).factorization p →
      diffCount d ν ≤ bound ν) →
    (p - 1) * (lcmDiff d).factorization p + 1 ≤
      ∑ ν ∈ (Finset.univ.image d).filter (fun ν => ν.factorization p = (lcmDiff d).factorization p),
        min (diffCount d ν) ((p - 1) * (lcmDiff d).factorization p + 1)

/-! 【T²³′ 的历史探索记录；最终证明见文件末】(A′)/(S5)/(TGT) 的最简等价形式：
    一切全本质覆盖 card ≥ bound(lcmDiff) + σ。
    等价改写（代数恒等）：Σ_ν min(m_ν, bound ν) ≥ bound(lcmDiff)
    另两种等价形式：Σ_ν (bound ν − m_ν)₊ + bound(lcmDiff) ≤ Σ_ν bound ν；
    以及（用次可加工具 1+Σ(b(ν)−1) ≥ b(lcm)，由 v_p(lcm) ≤ Σv_p 立得）的充分式。
    验证：n ≤ 24 K=7 全枚举 5834 族、n=30 九块例、n=60 手工实例、
    n∈{84,96,120,180} 各 30 万随机分层族（explore/stress_T23prime.py）——全部零反例，
    最紧处 slack−σ=0 取等（纯同差族 {0..ν−1 mod ν}: ν−bound ν）。
    【LP 路线·排除性负面结果】全本质族中：私有点 x_i 模 n 两两不同（d_j ∣ n 且
    x_i ≡ x_j ⟹ d_j ∣ x_i−x_j ⟹ x_i ∈ B_j 矛盾）。于是 w := Σ_i δ_{x_i mod n} 是
    覆盖 LP 的可行对偶、质量 = s；y ≡ 1 可行原始亦然。故分数覆盖数 = 整数覆盖数 = s，
    即任何线性对偶/权重证书最多证 s ≥ s——LP 类路线原理上不可能证出 bound(n)。
    【紧例结构（explore/tight_scan.py，n≤30 K=7）】margin := (Σ_ν b(ν) − b(n)) − Σ(b(ν)−m_ν)₊ = 0
    的全部实例满足「缺陷总和 = b-超额」精确耗尽，且组构型为"素数幂链式单块群"：
    如 lcmDiff=6: ν∈{2,3,6}, m∈{1,2,1}（缺陷 1+1+3 = 9−4 = 5）；lcmDiff=12:
    ν∈{2,3,4,12}, m∈{1,2,1,1}（缺陷 1+1+2+4 = 13−5 = 8）。证明须解释此精确配平。
    【逐素数分解·新（explore/check_Pp.py，6049 实例 0 反例，紧例均取等）】
      (P_p): ∀素 p | n: Σ_{ν: p | ν} min(m_ν, (p−1)v_p(ν) + 1) ≥ (p−1)v_p(n) + 1
      (W):   Σ_ν (ω(ν)−1)·min(m_ν, b(ν)) ≥ ω(n) − 1
      （ω = 素因子个数。）(P_p) 是**单素数**命题——跨素数纠缠被拆开：由 (P_p)×(p−1)-加权求和
      得 Σ_ν ω(ν)min(m_ν, b(ν)) ≥ b(n) + ω(n) − 1，再需「多素组重叠量 Σ(ω(ν)−1)min 的配平」
      （n=60 例：Σω·min = 44 ≥ 11 而 Σg = 26，余量吸收；紧例中 Σg = ω(n)−1 取等）。
      证明 (P_p) 的抓手：p-纤维分解下 p-可除块居单纤维、每纤维的 p^j-类计数（v_p(n) = 1 时
      (P_p) 化为 Σ min(m_ν, p) ≥ p，含 p 个覆盖类所需块数）。【P_p 的证明 = 新的单素数主战场】
      【(P_p)·v_p(n)=1 情形·已证定理】n = pM（p∤M）。证：CRT 图景 ℤ/n ≅ ℤ/p × ℤ/M，
      splits（p∤d）为 over X := ∪C_i 的全 p-线，pures 为 {c_j}×C_j。
      (1) y* ∈ ℤ/M∖X 非空：若 X = ℤ/M 则 splits 全覆盖 ⟹ pures 全非本质，矛盾；
      (2) 对每类 c mod p，CRT 点 (c,y*) 不被任何 split 覆盖（y*∉X），故被该类纯块覆盖；
      (3) 各类互异 ⟹ **≥ p 个互异纯块满足 y* ∈ 其 μ-陪集**（记 m⁺_μ 为其 μ-分组计数）；
      (4) Σ_μ min(m_{pμ}, p) ≥ Σ_μ min(m⁺_μ, p) ≥ min(Σ_μ m⁺_μ, p) = p（末步用
          Σmin(a_i,p) ≥ min(Σa_i,p)）。∎
      数值核验（explore/verify_Pp_proof.py）：6380 个 (实例,p,v_p=1) 样本中
      y* 总存在、m⁺-计数总是 ≥ p——零反例。
      一般 v_p(n)=κ 的状态（explore/verify_yline.py，注意陪集条件用 p-free 部分 μ = d/p^{v_p(d)}）：
      · y*-线（y*∉X）上：纯块 A_j (=a mod p^{β_j}) 覆盖 ℤ/p^κ ✓（每线点被该类纯块覆盖）。
      · 但**单线 min-形式不足**（κ≥2 时 518 反例）：最小例 n=12,p=2,κ=2,
        F={0%2,0%3,1%6,5%12,11%12}, y*=1: P*={0%2,1%6}(均 β=1): Σmin=2 < b(4)=3。
      · 补偿在**其他线**：y=2 线 P*_2={0%2(β1),5%12,11%12(β2)}: Σmin=min(1,2)+min(2,3)=3=b(4) 恰等。
        （y∈X 的线由 split 全覆盖、免费。）
      · **(L)·最优线引理（explore/verify_L.py，5658 个 κ≥2 实例 0 反例）**：
        max_{y ∉ X} Σ_β min(M_β(y), b(p^β)) ≥ b(p^κ)（M_β(y) = 该线上 β-级纯块数）。
        归约链：每纯块 (β,μ) 组在线上按 β 供容量、min 截断后求和 ≥ 最优线形式 ≥ b(p^κ)，
        故 **(L) ⟹ (P_p)-一般情形**。（注意：逐线平均不成立（例中 5 < 6），但最优线成立（3=3）；
        平均失败正是因线-覆盖可"廉价"如 {0 mod 2, 1 mod 2}（2 < b(4)=3）——β=κ 载体的
        线才是锚点。）
      · v_p=1：单线即够且完整得证 ✓；κ≥2：(L) 为唯一剩余目标。
      · **(L⁺)·载体私有线（explore/verify_carrier_line.py，5658 实例 0 反例）**：
        存在 β=κ 载体块 j* 与私有点 x（(x, y°) 私于 j*），使 y°=x mod M 满足
        F(y°) ≥ b(p^κ)。(L⁺) ⟹ (L) ⟹ (P_p)-一般情形。
        证明骨架：(PRIV) 私有点 (x*,y°) 不被任何其他块覆盖 ⟹ 线上覆盖 ℤ/p^κ 的类族中
        **x* 仅被自己的类 A*={x*}（β=κ 单点类）覆盖**。由此化归子引理
        **(PC)**：ℤ/p^κ 的类覆盖（β_j ≤ κ）若含 β=κ 单点类 A*={x*} 且 x* ∉ A_j (j≠*)，
        则 Σ_β min(M_β, b(p^β)) ≥ b(p^κ)。——这正是"廉价覆盖"反例（{0,1 mod 2} 盖 ℤ/4：
        2<3）被本质性排除的机制：其 β=κ 级为空/点被他类覆盖。κ=1 时 (PC) 平凡成立
        （点族覆盖，M_1 ≥ p）；**κ=2 已手证**：按 M_1（β=1 类，每类盖满一根 p-纤维）分情形：
        M_1 ≥ 2 ⟹ Σ ≥ 2+1（A* 在）；M_1 = 1 ⟹ 其余 p−1 纤维各需 ≥ p 个点类 ⟹ M_2 ≥ p(p−1) ≥ 2
        ⟹ Σ ≥ 1+min(M_2,3) ≥ 3；M_1 = 0 ⟹ 全部点覆盖 ⟹ M_2 ≥ p² ⟹ Σ ≥ 3。∎（κ=2）
        **κ=3 已手证（一切 p）**：记 m₁ = 含 β=1 整类的纤维数（**m₁ ≤ p−1**：(PRIV) 强制挖点
        纤维 c₁ 无 β=1 类，否则 x* 被他类覆盖）。逐纤维账目：β=1 类盖满该纤维；无 β=1 的纤维 c：
        M_3^{(c)} ≥ p·(p − M_2^{(c)})（每条未被 β=2 半线盖的 p-半线需全部 p 点）；特别地
        **M_2^{(c₁)} ≤ p−1**（β=2 类避开 x* 半线）且 M_3 ≥ p(p − M_2^{(c₁)}) + 1（含 A*）。
        分情形：(a) M_3 ≥ 3p−2 ⟹ Σ ≥ 3p−2；(b) M_3 < 3p−2 ⟹ Σ_c(p−M_2^{(c)}) ≤ 2 ⟹
        M_2 ≥ (p−m₁)p − 2 ⟹ Σ ≥ m₁ + min((p−m₁)p−2, 2p−1) + p ≥ 3p−2（m₁ ≤ p−2 时）；
        m₁ = p−1（仅 c₁ 需覆盖）时 Σ ≥ (p−1) + min(M_2,2p−1) + min(p(p−M_2)+1, 3p−2) ≥ 3p−2
        （对 M_2 = 0..p−1 逐点核对，p=2,3 单独验证）。∎（κ=3）
        一般 κ 归纳·机制与最后一个技术核心（本轮定位）：
        (i) 逐纤维递归：挖点纤维 c₁ 的在纤维覆盖满足 (PC)-κ−1（同样带挖点）⟹ 由 IH
            其局域形式 ≥ b(p^{κ−1})；其余纤维为普通覆盖。
        (ii) 截断核心：全局容量 b(p^β) 与局域容量 b(p^{β−1}) 的失配
            p·b(p^{β−1}) − b(p^β) = (p−1)²(β−1)（逐 β），且**只在 M_β ≥ b(p^β)（组饱和）时咬合**。
            饱和恰意味着该层点/类极多——正是"挖点强制"逐层版本的用武之地
            （t-层半线回避 ⟹ M_{t+1} ≥ p^t·(需要量)）：即截断损失与挖点盈余在同层配对。
        (iii) 故一般 κ 的归纳 = "(i) 递归 + (ii) 饱和层配对"：两者都在已证的 κ≤3 中完整现身
            （κ=3 的 M_3 ≥ p(p−M_2)+1 即 (ii) 在 t=2 层的实例；m₁ ≤ p−1 即 (i)）。
        **精确递归恒等式（本轮核心结构发现）**：记 E_κ := F_κ − b(p^κ)（(PC) 的盈余）、
        f^{(c)} := 纤维 c 的局域 F、D_β := Σ_c min(M'_{β−1}(c), b(p^{β−1})) − min(M_β, b(p^β))（复制损失，
        双号），excess := Σ_c f^{(c)} − [b(p^{κ−1}) + (|T|−1)p]，则**恒等**：
          **E_κ = [(|T|−1)p + min(M_1,p) − (p−1)] + excess − Σ_{β≥2}D_β.**
        又 excess = Σ_c E^{(c)}（子层盈余：c₁ 的 E^{(κ−1)} ≥ 0 由 IH、其余由 (Q) ≥ 0）。故
        **(PC)-κ ⟺ [(|T|−1)p + min(M_1,p) − (p−1)] + Σ_c E^{(c)} ≥ Σ_{β≥2}D_β**：
        即"各层复制损失由 β=1 供给 + 全部子层盈余支付"。基例 κ=1: E_1 = min(M_1,p) − p ≥ 0 ⟸ M_1 ≥ p ✓。
        数值（explore/verify_identity.py 修正版思路）：208 个 (PC)-κ 实例中 E ∈ {0,1}，
        **192/208 取 E=0（精确等号）**——递归账目在紧例处逐层精确耗尽（与缺陷耗尽现象统一）。
        **链式不等式的结构分析（最终证明义务）**：
        · **饱和判据**：D_β ≥ 1 ⟹ M_β > b(p^β)（该层组饱和；因 loc_β ≤ M_β 且 glob_β < loc_β）。
        · **配对对象**：D_β 对应的子层盈余是各纤维 c 在 in-fibre 层 β−1 的盈余
          （E^{(c)} 的展开式 E^{(c)} = provision^{(c)} + ΣE^{(cc')} − ΣD^{(c)} 中同层项）。
        · **全树望远镜**：由恒等式递归展开，E_κ ≥ 0 ⟺ Σ_{全树节点}(provision + 饱和层配对) ≥ 0；
          因 92% 实例 E_κ = 0，**配对必须逐层精确**（无松弛可用）：每个饱和层的 D_β 由
          "β=1 供给 + 该层挖点强制盈余"恰好支付。
        · 已在 κ≤3 逐例核对（κ=3 的 M_3 ≥ p(p−M_2)+1 即层配对在 t=2 的实例）。
        结论：**(PC)-一般 κ = 恒等式(已证) + 逐层精确配对(最后一步，全树望远镜)**。
        【全树望远镜·精确恒等】递归展开所有节点（每节点 = 一次 (PC)+挖点实例）：
          **E_root = Σ_节点 prov − Σ_节点 Σ_{β≥2}D^node_β + Σ_叶 E_leaf**，E_leaf = min(M_1,p) − p ≥ 0。
        故 E_root ≥ 0 ⟺ "全树供给 + 叶盈余 ≥ 全树饱和损失"（精确恒等，无松弛）。
        饱和损失 D_β ≥ 1 ⟺ M_β > b(p^β)（该节点该层饱和）；供给 prov = (|T|−1)p + min(M_1,p) − (p−1)
        计的是"分散度"（纤维数 T 与 β=1 整类数）。**配对语义：分散度供给支付饱和损失**——
        这正是 (P_p) 各证明中"挖点强制盈余"的全树版本，也是 92% 紧例取等的机制。
        最后一步的证明义务：在全树逐层核对 prov ≥ D 的配对（含叶盈余的吸收）。
        ══════════ (PC)-一般 κ：已完整证明（投影归纳 + 静态不等式）══════════
        **定理 (PC)**：ℤ/p^κ 的类覆盖（类 = 模 p^β 陪集，β ≤ κ）含点类 A*={x*}（β*=κ），
        且 x* 不被其它类覆盖 ⟹ F := Σ_{β=1}^κ min(M_β, b(p^β)) ≥ b(p^κ)。
        证明（对 κ 归纳；explore/verify_pairing_level.py 前身 verify_projection.py 全验）：
        · κ=1：层 1 类 = 点 ⟹ 覆盖 ⟹ M_1 ≥ p = b(p) ✓。
        · κ ≥ 2：设 π: ℤ/p^κ → ℤ/p^{κ−1}。像族 fam̄ := {π(A)}（去重）是 (PC)-(κ−1) 实例：
          覆盖 ✓（y 取代表元 x：其覆盖类的 π 像覆盖 y）；挖点保持 ✓（模 p^β (β≤κ−1) 陪集
          的 π 像含 y ⟺ 原类含 y 的全部原像（p^{κ−1}≡0 mod p^β）⟹ 若像类覆盖 π(x*) 则
          源类覆盖 x*，唯 A* 例外；π({z}) 与 π(A*) 在 π(z)=π(x*) 时为同一像类，去重）。
          层计数：M̄_β = M_β (β ≤ κ−2)，M̄_{κ−1} = |Y_1 ∪ Y_2| = m + d，其中 Y_1 = 层 κ−1
          类的基集（|Y_1| = m），Y_2 = 点类的基集，d = |Y_2 ∖ Y_1|。
        · **静态不等式**：B := b(p^{κ−1})，M := M_κ：F_κ − F̄ = min(m,B) + min(M, B+p−1)
          − min(m+d, B) ≥ p−1。证明：称基 y 被底层触及若某层 ≤ κ−1 类覆盖 y 的某一原像；
          因层 ≤ κ−1 类 = 模 p^β 陪集而 y 的 p 个原像 mod p^β 全同，"全有或全无"。
          记 W := {y : 原像全不被底层触及}：y ∈ W ⟹ p 个原像全为点类 ⟹ c_y = p；
          y ∈ Y_1 ⟹ y ∉ W。记 h := |Y_2 ∖ (W ∪ Y_1)|：则 d = |W| + h，
          M ≥ p|W| + h = d + (p−1)|W|。挖点 ⟹ π(x*) ∈ W ⟹ |W| ≥ 1 ⟹ M ≥ d + p − 1。
          分情形（B ≥ p）：
          (i) m+d ≤ B：F_κ−F̄ = min(M, B+p−1) − d ≥ min(d+p−1, B+p−1) − d = p−1 ✓
              （M ≥ d+p−1；B ≥ d）；
          (ii) m+d > B 且 m ≥ B：F_κ−F̄ = min(M, B+p−1) ≥ min(p|W|, B+p−1) ≥ p > p−1 ✓；
          (iii) m+d > B 且 m < B：B−m ≤ d ⟹ B−m+p−1 ≤ d+p−1 ≤ M；若 M ≥ B+p−1 则
              min = B+p−1 ≥ B−m+p−1；否则 min = M ≥ d+p−1 ≥ B−m+p−1 ⟹
              F_κ−F̄ = min(M,B+p−1) − (B−m) ≥ p−1 ✓。∎（静态不等式）
        · 归纳：F_κ ≥ F̄ + (p−1) ≥ b(p^{κ−1}) + (p−1) = b(p^κ) ✓。∎（(PC)-一般 κ）
        · **验证**：5272 个 (PC) 实例（(p,κ)=(2,2),(2,3),(2,4),(3,2),(3,3),(2,5)）：
          像恒为合法 (PC)-(κ−1) 实例（0 例外），静态不等式 0 反例。
          方法论注：单层配对 (PL-ℓ) 与逐节点 prov≥ΣD 均失败（75/2647 处），唯投影静态不减
          F_κ ≥ F̄+(p−1) 成立——这是正确的不变量。
        推论链：(PC)-一般 κ ⟹ (L⁺) ⟹ (L) ⟹ **(P_p) 全部情形已证**（一切素数与一切 v_p）。
        ══════════════════════════════════════════════════════════════════════
        ══════════ 多素重组：投影归纳 + 配平式 (R)（本轮）══════════
        **投影（灭一个 p）**：π: ℤ/n → ℤ/n'（n' = n/p）。块 B = AP(a,d)：p∤d ⟹ π(B) = AP(a mod d, d)
        （完整 AP，d | n'）；p | d ⟹ π(B) = AP(a mod d', d')（d' = d/p | n'，因 gcd(pd',n')=d'，
        像是完整 AP）。族 F' := {π(B)} 覆盖 ℤ/n' ✓（π 满射 + F 覆盖）。层计数小定理：**S(n) ≥ S(F')**，
        其中 S(X) := Σ_{ν}min(m_ν, b(ν))（因 m'_{ν'} ≤ m_{ν'} + m_{pν'} 且 b(ν') ≤ b(pν')）。
        取 F' 的极小覆盖 F''（仍覆盖 ⟹ 全本质）⟹ T²³′(n') ⟹ **S(n) ≥ b(n/p)（一切素 p | n）**。
        但缺口 (p−1)（b(n) = b(n/p) + (p−1)）无法由投影单独补足——**S(n) ≥ S(F')+(p−1) 被枚举证伪**
        （explore/verify_PQ.py：n=12 例 [(0,2),(0,3),(1,3),(1,4),(11,12)]：S=S'=5，违 +1）。
        同理 (T2) Σ_pL_p ≥ b(n)+g（L_p := Σ_{ν∋p}min(m_ν,(p−1)v_p(ν)+1)，g := Σ(ω(ν)−1)min(m_ν,b(ν))）
        亦被证伪（n=12 例 [(0,2),(0,3),(1,12),(5,12),(7,12),(11,12)]：ΣL=8 < b+g=9）。
        **正确的充要重组式 (R)（explore/verify_R.py，0 反例，紧例取等）**：
        恒等式 **b(ν) = Σ_{p|ν}b_p(ν) − (ω(ν)−1)**（b_p(ν) := (p−1)v_p(ν)+1）给出
        min(m_ν, Σ_{p|ν}b_p(ν)) − min(m_ν, b(ν)) = min((m_ν−b(ν))₊, ω(ν)−1)。
        记 A := Σ_ν min(m_ν, Σ_{p|ν}b_p(ν))，D := Σ_ν min((m_ν−b(ν))₊, ω(ν)−1)：
        TGT ⟺ A ≥ b(n) + D；而 (P_p) ⟹ A ≥ Σ_ν Σ_{p|ν}min(m_ν,b_p(ν)) ≥ Σ_p b_p(n) = b(n)+ω(n)−1。
        故 **TGT ⟸ (R)：Σ_p E_p ≥ D − (ω(n)−1)**，E_p := L_p − b_p(n) ≥ 0（(P_p) 的过剩）。
        验证：n∈{12,18,24} 全枚举 5834 全本质族 + n∈{30,42,60,66,70,84,…,420} 各 ~6k 随机族：
        (R) 0 反例（枚举部分最小缺口 1）；单群紧例 census={(n,n)}（n 个点块）中 TGT 与 (R) 同时取等 0。
        **E_p = spread_p + main_p 分解（均 ≥0，为 (R) 证明的抓手）**：按 v_p(ν) = β 分层、μ = ν/p^β：
        L_p = Σ_βΣ_μ min(m_{p^βμ}, b(p^β))；spread_p := Σ_β[Σ_μ min(...) − min(Σ_μ(...), b(p^β))]
        （**μ-散布超额**——同一 β 层内多个 p-自由 μ 组各自吃满容量：这正是"跨素数联结"的几何来源，
        μ 的素因子 = 其余素数）；main_p := Σ_β min(M[p,β], b(p^β)) − b_p(n) ≥ 0 由 (L)-最优线保证
        （M[p,β] := Σ_μ m_{p^βμ} = 第 β 层总块数；Σ_βmin(M[p,β],b(p^β)) ≥ Σ_βmin(M_β(y),b(p^β)) ≥ b(p^β)）。
        待证：**Σ_p(spread_p + main_p) ≥ D − (ω(n)−1)**——(R) 的最后一步（多素配平的唯一剩余义务）。
        **(Rp) 逐素数形式（explore/verify_R_stress.py 各族 + 验证 0 反例，全本质族 ~24 万 (实例,p) 对）**：
        记 t_p := #{ν ∋ p: m_ν > b(ν)}（过载组数）。则
          **(Rp): L_p + 1 ≥ b_p(n) + t_p** ⟺ **Q_p: Σ_{非过载 ν∋p} min(m_ν, b_p(ν)) ≥ (p−1)(α_p − Σ_{过载 ∋p} v_p(ν))**，
        且 **Σ_p (Rp) ⟹ (R)**：由 L_p ≥ Σ_{过载∋p} min(m_ν,b_p(ν)) = Σ_i[(p−1)β_i + 1]（过载 ⟹ m_ν ≥ b_p(ν) 吃满）
        得 E_p + 1 − t_p ≥ (p−1)(Σ_iβ_i − α_p)：当 Σ_iβ_i ≥ α_p 时 (Rp) 自明；否则盈余由非过载组补足（Q_p）。
        · (SQ-p)（Σ_{过载∋p}v_p(ν) ≥ α_p）**被 107 例证伪**（n=12,p=2: {4:1,6:5,12:1}），(Rp) 仍成立——
          靠非过载组贡献（Q_p 形式），(Q_p) 0 反例（21909 族）。
        · **(C-strong)（单线够付：F(y°) ≥ (p−1)κ + t_p）在大 n 被证伪**（4260/28828；(n=60,p=2,{30:12,60:36}):
          线只有 3 而需 4）——线之外的全组贡献不可省。线性路线到此为止。
        最终剩余义务：**(Rp)/Q_p 的证明**（单素数形式，0 反例）：过载组（m_ν > b(ν)=1+Σ_q(q−1)v_q(ν)）
        的 p-深度 Σβ_i 与 α_p 的关系 + 非过载组在其余层的补齐。这是多素配平的最后一跳。
        ══ **(R'')·层次分解（最终形式，explore 验证 64489 全本质族 0 反例，恒有余量）** ══
        按 p-层分组：S_β := Σ_μ min(m_{(β,μ)}, b(p^β))，L_p = Σ_{β=1}^α S_β。
        过载层集 O := {β: ∃ν = p^βμ 过载}：**每个过载组必吃满 b(p^β)**（过载 ⟹ m_ν ≥ b(ν)+1 ≥ b(p^β)），
        故 β ∈ O 时 S_β ≥ t^(β)·b(p^β) ≥ (p−1)β + t^(β)（t^(β) := 该层过载组数）。
        于是：**(R'') Σ_{β∉O} S_β ≥ (p−1)(α − Σ_{β∈O}β)** ⟹ (Rp) ⟹ (R) ⟹ TGT。链上各级验证：
        (R'') 0/64489（恒有余量）；O=∅ 时 (R'') = (p−1)α，由 (L⁺)（L_p ≥ (p−1)α+1）已证 ✓。
        即：**多素配平 = 单素数最后一跳 (R'')**：过载层未及的 p-深度由其余层的产能补齐。
        至此全部归约链已定型、全链数值验证通过；剩余即 (R'') 的证明（研究级单素数引理）。
        【(R'') 变体证伪记录】V-b: Σ_{β∉O}S_β ≥ (p−1)(α−|O|) 被证伪（17631 例；O={α} 时
        RHS 应 0 而非 p−1）；V-c（每个非过载层 S_β ≥ p−1）被证伪。**(R'') 的 Σ_Oβ 深度修正不可省**。
        注：O≠∅ 且 Σ_Oβ ≥ α 时 (R'') 自动成立；故 (R'') 的实质内容 = "过载层深度不足 α 时，
        其余层以每缺失深度 (p−1) 的产能补齐"。
        ══ **(R'') 的最终分解：只剩 (T'')（本轮定型）** ══
        · **|O| ≤ 1 情形：由 (L⁺) 直接得证**（新）：|O|=1（O={β₀}）时
          Σ_{β∉O}S_β ≥ Σ_{β∉O}min(M_β(y°),b^β) ≥ F(y°) − min(M_{β₀}(y°),b^{β₀})
          ≥ (p−1)α+1 − b(p^{β₀}) = (p−1)(α−β₀) ✓（用 c_{β₀} ≤ b(p^{β₀})，对单层恒真）。
        · **|O| ≥ 2：需 (T'')**。由 Σ_Oβ ≥ α（此时 (R'') 平凡）。**(T'') 验证（explore/verify_T2pp.py）：
          16915 个 |O|≥2 的 (实例,p) 全部 Σ_Oβ ≥ α（最小差 0，仅 α=3,O={1,2} 取等；余者 ≥ 1）**；
          (α,O) 分布：几乎全部 α ∈ O（例外仅 α=3 的 O={1,2}）。紧例形状：**O={1,α}**
          （如 n=48: census {6:5, 48:8}，p=2: m₆=5>b(6)=4、m₄₈=8>b(48)=7，Σ=1+4=5=α+1）。
        · **(††)·无包含块引理（由本质性新导出）**：若族中块 B(差 d)、B'(差 d') 满足 d' | d 且
          off(B') ≡ off(B) mod d'，则 B ⊆ B' ⟹ B 无私有元 ⟹ 矛盾。故对一切真因子 d' | d：
          **m_d ≤ (d' − m_{d'})·(d/d')**（d-块必居非 d'-块的 d'-陪集，每陪集至多 d/d' 个）。
          紧例中取等（n=48: m₄₈ = 8 = (6−5)·8 ✓）。此为 (T'') 证明的候选抓手。
        · 尚缺：**(T'') 的证明**（两过载层 ⟹ Σ_Oβ ≥ α；机制似为"浅层过载组的陪集消耗迫使深层"）。(T'') 有证
          ⟹ (R'') ⟹ (R) ⟹ T²³′ 全链闭合。
        · **(T'') 机制·回避计数（本轮定位）**：过载组 ν₁=p^{β₁}μ₁、ν₂=p^{β₂}μ₂ 的块回避计数下界
          （CRT 相容对计数，紧例取等）：
          **#{x: x mod ν₁ ∉ S₁ 且 x mod ν₂ ∉ S₂} ≥ (n/ν₁)(n/ν₂)(ν₁−m₁)(ν₂−m₂)/n**
          （S_i = 该组选中偏移集；n=120 紧例恰为 6 ✓）。这些点须由 v_p > γ := max O 的深层块覆盖，
          而深层块预算 m_d ≤ b(d)：**α 越大回避量按 p^{α−γ} 增长而深层预算线性 ⟹ 矛盾**
          （n=240 假设构型：回避 12 > b(240)=11 ⟹ 无处可容 ✓；200 万次定向搜索 0 实例 ✓）。
          同 μ 情形已由 (††) 直接矛盾；异 μ 情形即此回避计数（尚待精细写出）。
        ══ **⚠ 第七次陷阱：模数≠lcm 的假证伪（本轮已修正）** ══
        "危险形状"族（8 个 10-块 + 9 个 12-块 + 6 个 120-块，如
        off10=[7,2,4,3,9,8,5,6], off12=[11,7,2,9,5,1,4,0,10], off120=[20,30,51,80,90,111]）
        其 **lcm(10,12,120) = 120 ≠ 240**（我一度以模数 N=240 计算 α=4 而误判"违反 (T'')"）。
        以正确 n=120（α=3）复核：O={1,2}，Σ_Oβ=3 = α **不违反 (T'')**（恰取等！）；
        (U''-nt) 亦落回平凡区。全 4500 族（45×220 穷举）在正确 lcm=120 下：
        **链 TGT/(P_p)/(Rp)/(R)/(R'') 0 违例、(T'') 0 违例** ✓。**故 (T'') 与 (U''-nt) 均未被证伪、仍存活**。
        真·n=240（lcm=240 需 v₂=4 的深层块）定向搜索 150 万次 0 实例——支持 (T'')。
        ══ **后续：真反例已找到（(T'') 确实为假）** ══
        定向搜索（hunt_true_danger.py，浅层1,2 过载 + 深层 v₂≥4 补全 + lcm 检查）在 n=240 找到
        **普查 {10:8, 12:6, 80:8}**（lcm(10,12,80)=240 ✓）：覆盖✓全本质✓，O={1,2}，Σ_Oβ=3 < α=4
        **真违 (T'')**（3 个实例）。**且全链 TGT/Pp/Rp/(R'')/(R) 在其上全真** ✓。
        (R'') 存活机制：**深层 α=4 的组 ν=80 饱和**（m=8 ≥ b₂(16)=5 ⟹ S₄ = b(2⁴) = 5 ≥ (p−1)(α−Σ_Oβ)=1）。
        故 |O|≥2 情形的 (R'') 证明应转向**深层饱和机制**（而非 (T'')）：hmm 候选形如
        "α∉O 且 |O|≥2 ⟹ S_α ≥ b(p^α) 或 (R'') 直接成立"。
        ══ **(V)·最终锐化形式（本轮定型；(U''-nt) 的强化）** ══
        非平凡区（Σ_Oβ < α）的达标线 y（F(y) ≥ (p−1)α+1）满足
          **(V) Σ_{β∈O} max(0, c_β − (p−1)β) ≤ 1**，c_β := min(M_β(y), b(p^β))。
        因 c_β ≤ (p−1)β+1，(V) ⟹ (U''-nt) ⟹ (R'')（配 (L⁺)）。
        语义：**每条达标线上，各过载层合计至多"吃满一次" b(p^β) 中超出 (p−1)β 的那 1 单位**
        （与 (PC) 结构中唯一的"+1"（挖点/基线）相呼应）。定向检验：非平凡区 714 条达标线 0 违例 ✓。
        这提示 (V) 的证明可直接嫁接 (PC)-投影链的"+1 单点"记账。
        ══ **(V) 的机制已完全显形（本质性驱动的反关联）** ══
        对真反例 {10:8,12:6,80:8}（n=240, p=2, α=4, O={1,2}, μ₁=μ₃=5, μ₂=3）逐线全表显示：
        · 达标线（F=7）恰为 y ≡ 2,4 (mod 5)——即 **80-块（α-层）所在的 μ-类 {2,4}**；
          且这些线上浅层**均未饱和**（c₁=1<2=c₁上界, c₂=2<3）；
        · 非达标线（F=4）上 c₁=2（1-层饱和）但 **M₄=0**（深层块缺席）。
        关键：10-块的 μ-类分布为 {0,1,2,3}∪{0,1,3,4}（类 2、4 各仅 1 块，其余各 2 块）——
        **80-块恰好全部选在"浅层最稀疏"的 μ-类上**：这是本质性（deep 块需私有点避开浅层覆盖）
        强制的反关联。**故 (V) 的证明路线 = 本质性 ⟹ 深层块居浅层间隙 ⟹ 达标线上浅层普查低于帽**
        （对每个过载层：M_β(y) 饱和要求浅层密铺该 μ-类，与深层块的私有间隙矛盾；
        累计"至多一次超 (p−1)β"即 (V)）。
        ══ **(V) 机制的定理形式（本轮锁定：本质性 (††) ⟹ 偏移互补）** ══
        逐例验证的关键：深层块 (a, 80) 的每个点 x 满足 x ≡ a (mod 10)（因 10 | 80）；
        若 a mod 10 ∈ off₁₀（存在 10-块 (a mod 10, 10)），则由 (††)（10 | 80 且同余）
        **该 10-块包含整块 (a,80) ⟹ 無私有元 ⟹ 矛盾**。
        故本质性强制 **a mod 10 ∉ off₁₀**——检验反例：80-块偏移 mod 10 = {4,7}，
        **恰为 off₁₀ 的补集**（off₁₀ 缺 {4,7}）✓✓。
        一般原理：**深层块 v_p(d)=β 的偏移 a 必须避开一切更浅块 (a', d') 满足 d' | d ∧ a ≡ a' (mod d')
        的投影**（(††) 逐对施加）——深层块只能落在浅层投影的补集上（μ-类互补）。
        证明 (V) 的最后一步：过载层 β 的线饱和 M_β(y) ≥ (p−1)β+1 意味着浅层在 y 的 μ-类上密铺；
        而 α-层块（lcm 必需）被迫落在投影补集上，其所在线的浅层普查必低于帽；
        累计即 Σ_{β∈O}max(0,c_β−(p−1)β) ≤ 1。
        **最终验证矩阵（(V) 全项 0 违例）**：非平凡区随机采样 714 条达标线 + 真反例本体 +
        **邻域扰动 4710 个合法实例**（从 {10:[0,1,2,3,5,6,8,9], 12:[0,1,4,5,8,9],
        80:[7,14,27,34,47,54,67,74]} 出发 1–6 步扰动，全部覆盖/本质/lcm=240 合法）——
        (V)、(U''-nt)、全链（TGT/Pp/Rp）均 0 违例。**危险区已被彻底覆盖，(V) 目标坚实**。
        ══ **闭合最后一段的两条子断言（本轮定位）** ══
        **(A) 达标 ⟹ 深层存在**：F(y) ≥ (p−1)α+1 ⟹ M_α(y) ≥ 1。
        · α=2 时**普查证明**：无 α-块 ⟹ F ≤ min(M_1,b(p)) ≤ p < 2p−1 ✓；
        · α≥3：普查不排除（Σ_{β<α}b(p^β) ≥ (p−1)α+1），需结构；**验证 0/4710+0/714 无例外**；
        · 反例机制：F(y) ≥ (p−1)α+1 且 M_α(y)=0 时静态不等式给 F_α ≤ F̄_{α−1}（干净投影），
          但 F̄ 无上界，故 (A) 的真证需覆盖/本质性论证（待）。
        **(B) 深层 + 非平凡 ⟹ 过载层至多一饱和**（(V) 的深层版，0 违例）。
        **闭合缺口（如实记录）**：(A)+(B) 的证明尚未写出；(B) 的机制 = (††) 偏移互补（已证）；
        (A) 的 α=2 情形已证，α≥3 情形为唯一未闭合点。全链其余环节（(V)⟹(U''-nt)⟹(R'')⟹(R)⟹TGT⟹T²³′
        ⟹原题）已证并已形式化。**数学侧完成度：除 (A)-α≥3 与 (B) 的证明外全部闭合。**
        两条存活路线的验证更新：(1) deep_saturation_candidate（见下方定理）：该反例上成立
        （ν=80: min(8,5)=5=b(16)）；定向检验 0 反例。(2) **(U''-nt)**（达标线在过载层的普查上界
        Σ_{β∈O}c_β ≤ (p−1)Σ_Oβ+1，非平凡区）：在该真反例上 **6 条达标线 0 违例** ✓，
        且在补类采样非平凡区 0/120 ✓——**(U''-nt) + (L⁺) ⟹ (R'') 于全部情形**（含 |O|≥2），
        故 (U''-nt) 与 deep_saturation 均为可闭合 (R'') 的候选，择一证明即可完成 T²³′ 数学侧。
        **教训（第七次）**：所有验证脚本必须用 **lcmlist 计算真实 n**（而非模数）驱动 α 与 b(n)；
        本轮相关脚本已修（verify_all_rich.py、植入采样、跨 n 危险构造均含 lcmlist 检查）。
        仍真被证伪者（lcm 正确）：**(K-t)（17 例）** 与 **(D3'-正部版)（14461 例）**——均为中间候选，
        不影响 (Rp)/(R'') 本身。
        ══ **多素配平·最终重构（δ-缺陷耗尽形，与 (Rp) 等价且紧）** ══
        对素 p：δ_β := b(p^β) − S_β（可负）。恒等 L_p = Σ_{非空β}[b(p^β) − δ_β] =
        (p−1)Σ_{非空β}β + k − Σδ_β（k := 非空层数）给出：
          **(Rp) ⟺ Σ_{δ_β>0}δ_β ≤ (p−1)(Σ_{非空β}β − α) + (k−1) − t_p**
        （n=24 例 {6:5,12:1,24:2}：Σδ₊ = 2+2 = 4 = 1·(6−3) + 2 − 1 取等 ✓）。
        语义：深层"深度超额"(p−1)(Σβ−α) 与层数余量 (k−1) 覆盖各层的 b-帽亏损。唯一剩余义务。
        【修正】正确组合为 **+ k − t_p**（k = 非空层数；t_p = 过载组数，可 > k，如 t=2,k=1 时
        S_β 溢出使 δ_β < 0 抵消）：**(Rp) ⟺ Σ_β δ_β（有符号!）≤ (p−1)(Σ_{非空}β − α) + k − t_p**。
        修正后的关键形式：记 Σ*_Oβ = Σ_{过载单元}β（**带重数**）：**(Rp) ⟺ (Q_p):
        Σ_{非过载单元}min(m_ν, b_p(ν)) ≥ (p−1)(α − Σ*_Oβ)_+** —— Σ*_Oβ ≥ α 时平凡（多数实例，
        含 t_p=2,k=1 型）；真正非平凡的是 Σ*_Oβ < α（过载单元深度不足）。候选 K-t、D3'-正部版
        均被 lcm-正确反例证伪（见上），但 (Q_p) 本身在所有采样上成立。
        ══ **最终验证矩阵（本轮扩样）** ══
        全链 TGT/(P_p)/(Rp)/(R)/(R'') 验证器（explore/verify_all_rich.py、verify_planted.py、
        危险类穷举、跨 n 危险构造）：
        · 小 n 全枚举 565+922+3962 族（n≤24, 含 lcm 检查）——0 违例；
        · **危险形状类穷举 4500 族（n=240, O={1,2}, Σ=3<α=4）——0 违例**（虽全违 (T'')）；
        · 植入私有点采样 3189 族（n≤1680）——0 违例；
        · **跨 n 危险构造 221 族（n=240/336/480/720）——0 违例**；
        · 补类型大 n 压力 ~250k 族（n≤840）——0 违例。
        **唯一剩余义务 = (Rp)（或其等价 (Def)/(R'')) 的证明**：t_p ≤ 1 时由 (P_p) 立得；
        t_p ≥ 2 需要新机制（浅层过载组的"陪集消耗"+深层溢出抵消——无包含块引理 (††) 与
        回避计数是已备工具，但完整论证尚未写出）。
        ══════════════════════════════════════════════════════════════════
        **(Q) 普通覆盖最小值 = p（explore/check_Qm.py 已验: p=2,3,5; m=1,2,3）**：
        Q_m := min_{普通类覆盖 of ℤ/p^m} F = p（取 {0..p−1 mod p} 达等）。
        配 (PC)-框架：Q'_κ = b(p^κ)（带挖点）；归纳 = c₁ 在纤维用 Q'_{κ−1} = b(p^{κ−1})、
        其余 needy 纤维用 Q_{κ−1} = p、m₁ 个 β=1 纤维免费，再以"饱和层配对"处理
        p·b(p^{β−1}) − b(p^β) = (p−1)²(β−1) 的截断失配（饱和 ⟹ M_β ≥ p·b^{β−1} ⟹
        挖点强制在该层提供的盈余 >> 失配）。
      【重组缺口·恒等回环（explore/check_pp_gap.py，0 违例且紧例取等）】由 (P_p) 加权求和得
      Σ_ν ω(ν)min ≥ b(n) + ω(n) − 1；因恒等式 Σmin = Σω·min − Σg（g := Σ(ω(ν)−1)min），
      推 T²³′ 需 Σg ≤ Σω·min − b(n)——该式与原目标**恒等**。即 (P_p)/(W) 分解真实、紧、可证，
      但它们的重组恰好复现原不等式：T²³′ 是关于"多素组重叠量 g 的配平"的不可约陈述。
      结论：**唯一攻坚点 = 在 (P_p) 证明（p-纤维类分析）中同产 g 的配平**（类系统间由
      split 块的跨类同差联结——这是 g 的几何来源，也是最后未被开采的结构）。
T23prime 的完整证明置于文件末，全局匹配路线之后。 -/

/-- 基例 n = 1：lcmDiff = 1 ⟹ 全 d = 1 ⟹ σ = card − 1，两边相等。已证。 -/
theorem T23prime_base {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (heq : lcmDiff d = 1) (_hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (_hess : ∀ i, Essential a d i) :
    Fintype.card ι ≥ bound 1 + sigma d := by
  classical
  have hd1 : ∀ i, d i = 1 := fun i => Nat.dvd_one.1 (heq ▸ dvd_lcmDiff i)
  have hne : Nonempty ι := ⟨(hcover 0).choose⟩
  have himg : Finset.univ.image d = {1} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro ν hν
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hν
      simp [hd1 i]
    · intro ν hν
      have : ν = 1 := Finset.mem_singleton.1 hν
      subst this
      exact Finset.mem_image.2 ⟨hne.some, Finset.mem_univ _, hd1 _⟩
  have hσ : sigma d = Fintype.card ι - 1 := by
    rw [sigma, himg, Finset.sum_singleton, bound_one, diffCount]
    congr 1
    rw [show (Finset.univ.filter (fun i => d i = 1)) = Finset.univ from
      Finset.filter_true_of_mem (fun i _ => hd1 i)]
    simp
  rw [hσ, bound_one]
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  omega

-- card_ge_bound_of_allEssential 与 problem7 在文件末由 T23prime 组装。

/-! ## 主定理 -/

/-- 【拆n·路2·T″】独占族上 essLcm = lcmDiff（本质子族即全族）。 -/
theorem essLcm_eq_of_essential {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hess : ∀ i, Essential a d i) : essLcm a d = lcmDiff d := by
  classical
  refine Nat.dvd_antisymm ?_ ?_
  · refine Finset.lcm_dvd (fun j _ => dvd_lcmDiff j.val)
  · refine Finset.lcm_dvd (fun i _ =>
      dvd_lcmDiff (d := fun j : {x : ι // Essential a d x} => d j.val) ⟨i, hess i⟩)

-- 原题的最终定理 problem7 已改接全局匹配路线，见文件末。


/-! ## 2026-10-10 · 第十一次勘误：原 σ-闭合候选的真反例

构造：原 120-覆盖 F（8 个 10-块、9 个 12-块、6 个 120-块）分别提升至
模 3 的 0、1 纤维：每块 (a,d) 变成 (3a+c,3d)。第三纤维放入
(2,6),(5,12),(11,24),(23,48),(47,48)，即深度 4 的二进制精确覆盖。
族有 51 块，真实 lcm=720；普查为 {6:1,12:1,24:1,30:16,36:18,48:2,360:12}。
对 p=2，只有 30、36 组过载，故 O={1,2}，ΣO=3<α=4。
y=6 的 M={1:2,2:3}，F=5，双饱和且无深块：否定 (A)/(V)/(U''-nt)。
最深层只有两个 48-块，S4=2<5：否定 deep_saturation_candidate。
变体把最后一块 (47,48) 扩为 (15,16)，原块全部仍本质（独占证书见 witnessB）；
y=6 的 M={1:2,2:3,4:1}，F=6，否定 (B) 与深块存在版 V-strong。
这些线上深块没有私有点；载体私有线版本的状态不能由这些反例直接判定。

以下所有有限证书用 decide +kernel 在 Lean 内核归约；整数覆盖由周期提升，
本质性由逐块独占点证书提升。因此不是单纯数值采样，也不引用任何 sorry 定理。
#print axioms 两个 legal_counterexample 应仅含 propext/Classical.choice/Quot.sound，
不得含 sorryAx 或 Lean.ofReduceBool。原题与 T23prime 的开放状态见文件头。
-/

namespace SigmaRouteAudit

def data : Fin 51 → ℕ × ℕ := ![
  (21,30), (6,30), (12,30), (9,30), (27,30), (24,30), (15,30), (18,30),
  (33,36), (21,36), (6,36), (27,36), (15,36), (3,36), (12,36), (0,36), (30,36),
  (60,360), (90,360), (153,360), (240,360), (270,360), (333,360),
  (22,30), (7,30), (13,30), (10,30), (28,30), (25,30), (16,30), (19,30),
  (34,36), (22,36), (7,36), (28,36), (16,36), (4,36), (13,36), (1,36), (31,36),
  (61,360), (91,360), (154,360), (241,360), (271,360), (334,360),
  (2,6), (5,12), (11,24), (23,48), (47,48)]

def a (i : Fin 51) : ℤ := (data i).1
def d (i : Fin 51) : ℕ := (data i).2
def witness : Fin 51 → ℕ := ![
  81,96,132,9,117,24,45,18,33,93,150,63,123,3,120,0,30,60,90,153,240,270,333,
  82,97,133,10,118,25,46,19,34,94,151,64,124,4,121,1,31,61,91,154,241,271,334,
  2,5,11,23,47]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_certificate :
    (∀ i, 0 < d i ∧ d i ∣ 720) ∧
    (∀ r : Fin 720, ∃ i : Fin 51, r.val % d i = (data i).1) ∧
    (∀ i : Fin 51, (witness i : ℤ) % (d i : ℤ) = a i % (d i : ℤ) ∧
      ∀ j : Fin 51, j ≠ i → (witness i : ℤ) % (d j : ℤ) ≠ a j % (d j : ℤ)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem numeric_certificate :
    lcmDiff d = 720 ∧ (lcmDiff d).factorization 2 = 4 ∧
    overfullLayers d 2 = {1, 2} ∧
    lineCount a d 2 6 1 = 2 ∧ lineCount a d 2 6 2 = 3 ∧
    lineCount a d 2 6 4 = 0 ∧ lineScore a d 2 6 = 5 ∧
    (saturatedLayers a d 2 6).card = 2 ∧
    (∑ ν ∈ (Finset.univ.image d).filter
      (fun ν => ν.factorization 2 = (lcmDiff d).factorization 2),
      min (diffCount d ν) ((2 - 1) * (lcmDiff d).factorization 2 + 1)) = 2 := by
  decide +kernel

theorem mem_iff_mod (i : Fin 51) (m : ℤ) :
    MemAP a d i m ↔ m % (d i : ℤ) = a i % (d i : ℤ) := by
  constructor
  · rintro ⟨k, rfl⟩
    simp
  · intro h
    obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd).mp (show a i ≡ m [ZMOD (d i : ℤ)] from h.symm)
    exact ⟨k, by linarith⟩

theorem cover : ∀ m : ℤ, ∃ i, MemAP a d i m := by
  intro m
  let r : Fin 720 := ⟨(m % 720).toNat, by
    have h0 := Int.emod_nonneg m (by norm_num : (720 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 720)
    omega⟩
  obtain ⟨i, hi⟩ := finite_certificate.2.1 r
  have hr : (r.val : ℤ) = m % 720 := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
  have hcong : (r.val : ℤ) ≡ a i [ZMOD (d i : ℤ)] := by
    have hi' : (r.val : ℤ) % (d i : ℤ) = a i := by
      dsimp [a]
      exact_mod_cast hi
    change _ = _
    rw [← hi', Int.emod_emod]
  have hdvd : (d i : ℤ) ∣ 720 := by exact_mod_cast (finite_certificate.1 i).2
  have hperiod : (r.val : ℤ) ≡ m [ZMOD (d i : ℤ)] := by
    rw [hr]
    exact (Int.mod_modEq m 720).of_dvd hdvd
  exact ⟨i, (mem_iff_mod i m).2 (hperiod.symm.trans hcong)⟩

theorem essential : ∀ i, Essential a d i := by
  intro i
  refine ⟨witness i, (mem_iff_mod i _).2 (finite_certificate.2.2 i).1, ?_⟩
  intro j hji hmem
  exact (finite_certificate.2.2 i).2 j hji ((mem_iff_mod j _).1 hmem)

theorem not_deep_presence : ¬ deep_presence a d 2 := by
  intro h
  rcases numeric_certificate with ⟨_, hα, _, _, _, h4, hF, _, _⟩
  have hach : (2 - 1) * (lcmDiff d).factorization 2 + 1 ≤ lineScore a d 2 6 := by
    rw [hα, hF]
  have hdeep := h 6 hach
  rw [hα, h4] at hdeep
  omega

theorem not_V_final : ¬ V_final a d 2 := by
  intro h
  rcases numeric_certificate with ⟨_, hα, hO, _, _, _, hF, hsat, _⟩
  have hach : (2 - 1) * (lcmDiff d).factorization 2 + 1 ≤ lineScore a d 2 6 := by
    rw [hα, hF]
  have hnt : (∑ b ∈ overfullLayers d 2, b) < (lcmDiff d).factorization 2 := by
    rw [hO, hα]
    decide
  have hsat' := h 6 hach hnt
  rw [hsat] at hsat'
  omega

/-- (U''-nt) 的过载层总量上界同样失败：左边 5，右边 4。 -/
theorem not_U_nt_bound :
    ¬ (∑ b ∈ overfullLayers d 2, min (lineCount a d 2 6 b) ((2 - 1) * b + 1)) ≤
      (2 - 1) * (∑ b ∈ overfullLayers d 2, b) + 1 := by
  rcases numeric_certificate with ⟨_, _, hO, h1, h2, _⟩
  simp [hO, h1, h2]

theorem not_Tpp_levels : ¬ Tpp_levels_falsified_record d 2 := by
  intro h
  rcases numeric_certificate with ⟨_, hα, hO, _⟩
  have hmany : 2 ≤ (overfullLayers d 2).card := by rw [hO]; decide
  have hsum := h hmany
  rw [hα, hO] at hsum
  norm_num at hsum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem deep_not_overfull :
    ∀ ν ∈ (Finset.univ.image d), 2 ∣ ν → ν.factorization 2 = (lcmDiff d).factorization 2 →
      diffCount d ν ≤ bound ν := by
  decide +kernel

theorem not_deep_saturation : ¬ deep_saturation_candidate d 2 := by
  intro h
  rcases numeric_certificate with ⟨_, hα, hO, _, _, _, _, _, hS⟩
  have hmany : 2 ≤ (overfullLayers d 2).card := by rw [hO]; decide
  have hbound := h hmany deep_not_overfull
  rw [hS, hα] at hbound
  norm_num at hbound

/-- 真反例满足原题的全部前提；以上反驳均无 sorry 依赖。 -/
theorem legal_counterexample :
    (∀ i, 0 < d i) ∧ (∀ m : ℤ, ∃ i, MemAP a d i m) ∧
    (∀ i, Essential a d i) ∧ lcmDiff d = 720 ∧
    ¬ deep_presence a d 2 ∧ ¬ V_final a d 2 ∧ ¬ deep_saturation_candidate d 2 :=
  ⟨fun i => (finite_certificate.1 i).1, cover, essential, numeric_certificate.1,
    not_deep_presence, not_V_final, not_deep_saturation⟩

#print axioms legal_counterexample

/-- 将最后一个 47 mod 48 块扩成 15 mod 16；其独占点 47 仍存在。 -/
def dataB (i : Fin 51) : ℕ × ℕ := if i = 50 then (15, 16) else data i
def aB (i : Fin 51) : ℤ := (dataB i).1
def dB (i : Fin 51) : ℕ := (dataB i).2
def witnessB (i : Fin 51) : ℕ :=
  if i = 11 then 243 else if i = 39 then 211 else if i = 44 then 631 else witness i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_certificate_B :
    (∀ i, 0 < dB i ∧ dB i ∣ 720) ∧
    (∀ r : Fin 720, ∃ i : Fin 51, r.val % dB i = (dataB i).1) ∧
    (∀ i : Fin 51, (witnessB i : ℤ) % (dB i : ℤ) = aB i % (dB i : ℤ) ∧
      ∀ j : Fin 51, j ≠ i → (witnessB i : ℤ) % (dB j : ℤ) ≠ aB j % (dB j : ℤ)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem numeric_certificate_B :
    lcmDiff dB = 720 ∧ (lcmDiff dB).factorization 2 = 4 ∧
    overfullLayers dB 2 = {1, 2} ∧
    lineCount aB dB 2 6 4 = 1 ∧ lineScore aB dB 2 6 = 6 ∧
    (saturatedLayers aB dB 2 6).card = 2 := by
  decide +kernel

theorem memB_iff_mod (i : Fin 51) (m : ℤ) :
    MemAP aB dB i m ↔ m % (dB i : ℤ) = aB i % (dB i : ℤ) := by
  constructor
  · rintro ⟨k, rfl⟩
    simp
  · intro h
    obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd).mp (show aB i ≡ m [ZMOD (dB i : ℤ)] from h.symm)
    exact ⟨k, by linarith⟩

theorem coverB : ∀ m : ℤ, ∃ i, MemAP aB dB i m := by
  intro m
  let r : Fin 720 := ⟨(m % 720).toNat, by
    have h0 := Int.emod_nonneg m (by norm_num : (720 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 720)
    omega⟩
  obtain ⟨i, hi⟩ := finite_certificate_B.2.1 r
  have hr : (r.val : ℤ) = m % 720 := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
  have hcong : (r.val : ℤ) ≡ aB i [ZMOD (dB i : ℤ)] := by
    have hi' : (r.val : ℤ) % (dB i : ℤ) = aB i := by
      dsimp [aB]
      exact_mod_cast hi
    change _ = _
    rw [← hi', Int.emod_emod]
  have hdvd : (dB i : ℤ) ∣ 720 := by exact_mod_cast (finite_certificate_B.1 i).2
  have hperiod : (r.val : ℤ) ≡ m [ZMOD (dB i : ℤ)] := by
    rw [hr]
    exact (Int.mod_modEq m 720).of_dvd hdvd
  exact ⟨i, (memB_iff_mod i m).2 (hperiod.symm.trans hcong)⟩

theorem essentialB : ∀ i, Essential aB dB i := by
  intro i
  refine ⟨witnessB i, (memB_iff_mod i _).2 (finite_certificate_B.2.2 i).1, ?_⟩
  intro j hji hmem
  exact (finite_certificate_B.2.2 i).2 j hji ((memB_iff_mod j _).1 hmem)

theorem not_one_saturation : ¬ one_saturation aB dB 2 := by
  intro h
  rcases numeric_certificate_B with ⟨_, hα, hO, h4, _, hsat⟩
  have hdeep : 0 < lineCount aB dB 2 6 ((lcmDiff dB).factorization 2) := by
    rw [hα, h4]
    decide
  have hnt : (∑ b ∈ overfullLayers dB 2, b) < (lcmDiff dB).factorization 2 := by
    rw [hO, hα]
    decide
  have hsat' := h 6 hdeep hnt
  rw [hsat] at hsat'
  omega

/-- (B) 即使补上真实普查关联与达标前提，仍有合法反例。 -/
theorem legal_counterexample_B :
    (∀ i, 0 < dB i) ∧ (∀ m : ℤ, ∃ i, MemAP aB dB i m) ∧
    (∀ i, Essential aB dB i) ∧ lcmDiff dB = 720 ∧
    ¬ one_saturation aB dB 2 ∧
    (2 - 1) * (lcmDiff dB).factorization 2 + 1 ≤ lineScore aB dB 2 6 := by
  refine ⟨fun i => (finite_certificate_B.1 i).1, coverB, essentialB,
    numeric_certificate_B.1, not_one_saturation, ?_⟩
  rw [numeric_certificate_B.2.1, numeric_certificate_B.2.2.2.2.1]
  decide

#print axioms legal_counterexample_B

end SigmaRouteAudit

/-! ## 2026-10-10 · 宏观选路后的首个形式化部件

已比较三路：修复 D+H 的单素配平、纤维递归势函数、有限值域坐标槽匹配。
选定坐标槽匹配，完整设计见 explore/proof_paths_2026-10-10.md。
把每个 p 进位坐标复制 p−1 个槽。等差数列块固定相应前缀位，补条件为负单值子句；
覆盖+独占对应极小不可满足。一般加权亏格稳定性（Kullmann，非我方文献工具）
可用 Hall 重建，纸面上给出“全部槽匹配到不同块，且存在一个未使用块”。
槽总数=b(n)−1，同差 ν 组的支持槽数=b(ν)−1。
取全部匹配块加一个余块，其组选中数≤min(mν,bν)，直接推出 TGT/T23prime/原题。
选出的块只是计数证书，不主张它们仍覆盖。

首轮检查：K=7，模数 6/12/18/24 的 4655 个合法覆盖；1280 个随机精确分割或
混合差极小覆盖，真实 lcm 最大 1680；另含 n=60/240/720A/720B 的旧反例。
全部得到可独立检查的匹配证书。数据见 explore/matching_path_report.json 与
explore/matching_path_certificates.json。样本验证不是一般匹配存在定理的证明。
以下 matching_capacity_bound 已证（无 sorry）：假设给定全槽匹配及余块，得到截断下界。
本段写于组装前；后续已完成一般匹配存在性、CRT/位坐标精确桥接与主定理装配，见文件末。
主文件原有 4 个开放目标并未被此条件引理填上；不得宣称主定理已完成。
-/

/-! 通用计数末步：全槽匹配加一个余块，推出逐组截断容量下界。
这不假设选出的块覆盖；所有假设是可检查的匹配证书。
-/

theorem matching_capacity_bound
    {Slot Block Group : Type*} [Fintype Slot] [Fintype Block] [DecidableEq Group]
    (group : Block → Group) (support : Group → Finset Slot)
    (matchBlock : Slot → Block) (hinj : Function.Injective matchBlock)
    (hincident : ∀ slot, slot ∈ support (group (matchBlock slot)))
    (anchor : Block) (hanchor : ∀ slot, matchBlock slot ≠ anchor) :
    Fintype.card Slot + 1 ≤
      ∑ ν ∈ Finset.univ.image group,
        min ((Finset.univ.filter (fun i => group i = ν)).card) ((support ν).card + 1) := by
  classical
  let matched : Finset Block := Finset.univ.image matchBlock
  let selected : Finset Block := insert anchor matched
  have hnot : anchor ∉ matched := by
    intro h
    obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp h
    exact hanchor slot heq
  have hcard : selected.card = Fintype.card Slot + 1 := by
    rw [show selected = insert anchor matched from rfl, Finset.card_insert_of_notMem hnot]
    rw [show matched = Finset.univ.image matchBlock from rfl,
      Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hmatched : ∀ ν,
      (matched.filter (fun i => group i = ν)).card ≤ (support ν).card := by
    intro ν
    have heq : matched.filter (fun i => group i = ν) =
        (Finset.univ.filter (fun slot => group (matchBlock slot) = ν)).image matchBlock := by
      ext i
      constructor
      · intro hi
        obtain ⟨him, hν⟩ := Finset.mem_filter.mp hi
        obtain ⟨slot, _, hsi⟩ := Finset.mem_image.mp him
        exact Finset.mem_image.mpr ⟨slot,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hsi] using hν⟩, hsi⟩
      · intro hi
        obtain ⟨slot, hs, hsi⟩ := Finset.mem_image.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, hsi⟩,
          by simpa only [hsi] using (Finset.mem_filter.mp hs).2⟩
    rw [heq, Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro slot hslot
    have hν := (Finset.mem_filter.mp hslot).2
    simpa only [hν] using hincident slot
  have hselected : ∀ ν,
      (selected.filter (fun i => group i = ν)).card ≤ (support ν).card + 1 := by
    intro ν
    have hsub : selected.filter (fun i => group i = ν) ⊆
        insert anchor (matched.filter (fun i => group i = ν)) := by
      intro i hi
      obtain ⟨hi, hν⟩ := Finset.mem_filter.mp hi
      rcases Finset.mem_insert.mp hi with hia | him
      · exact Finset.mem_insert.mpr (Or.inl hia)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨him, hν⟩))
    calc (selected.filter (fun i => group i = ν)).card
        ≤ (insert anchor (matched.filter (fun i => group i = ν))).card :=
          Finset.card_le_card hsub
      _ ≤ (matched.filter (fun i => group i = ν)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (support ν).card + 1 := Nat.add_le_add_right (hmatched ν) 1
  calc Fintype.card Slot + 1 = selected.card := hcard.symm
    _ = ∑ ν ∈ Finset.univ.image group,
        (selected.filter (fun i => group i = ν)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun i _ =>
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    _ ≤ ∑ ν ∈ Finset.univ.image group,
        min ((Finset.univ.filter (fun i => group i = ν)).card) ((support ν).card + 1) := by
      apply Finset.sum_le_sum
      intro ν _
      apply le_min
      · exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      · exact hselected ν

#print axioms matching_capacity_bound



/-! 有限值域极小盒覆盖的匹配核心。一般理论来源见
lit/kullmann-1103.3693-note.md；这里从 Mathlib 的 Hall 定理重建证明。
本文件不使用原题或 T23prime，也不预设匹配存在性。 -/

namespace MinimalCoverMatching

variable {Block Slot : Type*} [Fintype Block] [Fintype Slot]

noncomputable def active (support : Block → Finset Slot) (G : Finset Block) : Finset Slot :=
  by classical exact G.biUnion support

noncomputable def deficiency (support : Block → Finset Slot) (G : Finset Block) : ℤ :=
  G.card - (active support G).card

omit [Fintype Slot] in
theorem maximal_complement_matching (support : Block → Finset Slot) (H : Finset Block)
    (hmax : ∀ G, deficiency support G ≤ deficiency support H) :
    ∃ f : {i : Block // i ∉ H} → Slot, Function.Injective f ∧
      ∀ i, f i ∈ support i.val ∧ f i ∉ active support H := by
  classical
  let neigh : {i : Block // i ∉ H} → Finset Slot :=
    fun i => support i.val \ active support H
  have hall : ∀ J : Finset {i : Block // i ∉ H}, J.card ≤ (J.biUnion neigh).card := by
    intro J
    let K := J.image Subtype.val
    have hdisj : Disjoint H K := by
      apply Finset.disjoint_left.mpr
      intro i hi hik
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hik
      exact j.property hi
    have hK : K.card = J.card := Finset.card_image_of_injective _ Subtype.val_injective
    have heq : active support (H ∪ K) = active support H ∪ J.biUnion neigh := by
      ext s
      simp only [active, Finset.mem_biUnion, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_image, neigh, K]
      constructor
      · rintro ⟨i, hi, hs⟩
        rcases hi with hi | ⟨j, hj, rfl⟩
        · exact Or.inl ⟨i, hi, hs⟩
        · by_cases h : ∃ k ∈ H, s ∈ support k
          · exact Or.inl h
          · exact Or.inr ⟨j, hj, hs, h⟩
      · rintro (⟨i, hi, hs⟩ | ⟨j, hj, hs, _⟩)
        · exact ⟨i, Or.inl hi, hs⟩
        · exact ⟨j.val, Or.inr ⟨j, hj, rfl⟩, hs⟩
    have hdisjS : Disjoint (active support H) (J.biUnion neigh) := by
      apply Finset.disjoint_left.mpr
      intro s hs ht
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
      exact (Finset.mem_sdiff.mp hi).2 hs
    have hc := Finset.card_union_of_disjoint hdisj
    have hs := Finset.card_union_of_disjoint hdisjS
    have hm := hmax (H ∪ K)
    unfold deficiency at hm
    rw [heq, hc, hs, hK] at hm
    omega
  obtain ⟨f, hf, hn⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' neigh).mp hall
  exact ⟨f, hf, fun i => Finset.mem_sdiff.mp (hn i)⟩

variable {Var : Type*} [DecidableEq Var]

noncomputable def slotSupport (owner : Slot → Var) (uses : Block → Finset Var)
    (i : Block) : Finset Slot := by
  classical exact Finset.univ.filter (fun s => owner s ∈ uses i)

/-- 剩余子句若能匹配到未被 H 使用的槽，就能用这些变量满足全部剩余子句。
每个变量的槽数严格小于值域大小，故至少剩下一个未被禁止的值。 -/
theorem proper_complement_matching_impossible
    (q : Var → ℕ) (owner : Slot → Var) (uses : Block → Finset Var)
    (value : (i : Block) → (v : Var) → Fin (q v))
    (hcapacity : ∀ v, (Finset.univ.filter (fun s => owner s = v)).card < q v)
    (hcover : ∀ x : (v : Var) → Fin (q v),
      ∃ i, ∀ v ∈ uses i, x v = value i v)
    (hprivate : ∀ i, ∃ x : (v : Var) → Fin (q v),
      ∀ j, j ≠ i → ∃ v ∈ uses j, x v ≠ value j v)
    (H : Finset Block) (hproper : H ≠ Finset.univ)
    (f : {i : Block // i ∉ H} → Slot) (hinj : Function.Injective f)
    (hincident : ∀ i, f i ∈ slotSupport owner uses i.val ∧
      f i ∉ active (slotSupport owner uses) H) : False := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Block, c ∉ H := by
    by_contra h
    apply hproper
    ext c
    simp only [Finset.mem_univ, iff_true]
    exact not_not.mp (fun hc => h ⟨c, hc⟩)
  obtain ⟨x₀, hx₀⟩ := hprivate c
  let assigned (v : Var) : Finset {i : Block // i ∉ H} :=
    Finset.univ.filter (fun i => owner (f i) = v)
  let forbidden (v : Var) : Finset (Fin (q v)) :=
    (assigned v).image (fun i => value i.val v)
  have hfcard (v : Var) : (forbidden v).card < q v := by
    have hsub : (assigned v).image f ⊆ Finset.univ.filter (fun s => owner s = v) := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    calc (forbidden v).card ≤ (assigned v).card := Finset.card_image_le
      _ = ((assigned v).image f).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.univ.filter (fun s => owner s = v)).card := Finset.card_le_card hsub
      _ < q v := hcapacity v
  have hex (v : Var) : ∃ z : Fin (q v), z ∉ forbidden v := by
    have hh : (forbidden v).card < (Finset.univ : Finset (Fin (q v))).card := by
      simpa using hfcard v
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
    exact ⟨z, hz⟩
  let fresh (v : Var) : Fin (q v) := Classical.choose (hex v)
  have hfresh (v : Var) : fresh v ∉ forbidden v := Classical.choose_spec (hex v)
  let oldVars : Finset Var := H.biUnion uses
  let x (v : Var) : Fin (q v) := if v ∈ oldVars then x₀ v else fresh v
  have hsat : ∀ j, ∃ v ∈ uses j, x v ≠ value j v := by
    intro j
    by_cases hj : j ∈ H
    · have hjc : j ≠ c := by intro he; subst j; exact hc hj
      obtain ⟨v, hv, hneq⟩ := hx₀ j hjc
      have hold : v ∈ oldVars := Finset.mem_biUnion.mpr ⟨j, hj, hv⟩
      exact ⟨v, hv, by simpa only [x, ite_eq_left hold] using hneq⟩
    · let i : {i : Block // i ∉ H} := ⟨j, hj⟩
      let v := owner (f i)
      have hv : v ∈ uses j := (Finset.mem_filter.mp (hincident i).1).2
      have hnew : v ∉ oldVars := by
        intro hold
        obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hold
        apply (hincident i).2
        exact Finset.mem_biUnion.mpr ⟨k, hk,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvk⟩⟩
      refine ⟨v, hv, ?_⟩
      simp only [x, ite_eq_right hnew]
      intro he
      apply hfresh v
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, he.symm⟩
  obtain ⟨j, hj⟩ := hcover x
  obtain ⟨v, hv, hneq⟩ := hsat j
  exact hneq (hj v hv)

/-- 极小不可满足族的亏格在任意真子族上严格下降。 -/
theorem strict_deficiency
    (q : Var → ℕ) (owner : Slot → Var) (uses : Block → Finset Var)
    (value : (i : Block) → (v : Var) → Fin (q v))
    (hcapacity : ∀ v, (Finset.univ.filter (fun s => owner s = v)).card < q v)
    (hcover : ∀ x : (v : Var) → Fin (q v),
      ∃ i, ∀ v ∈ uses i, x v = value i v)
    (hprivate : ∀ i, ∃ x : (v : Var) → Fin (q v),
      ∀ j, j ≠ i → ∃ v ∈ uses j, x v ≠ value j v) :
    ∀ G : Finset Block, G ≠ Finset.univ →
      deficiency (slotSupport owner uses) G <
        deficiency (slotSupport owner uses) Finset.univ := by
  classical
  let support := slotSupport owner uses
  intro G hG
  by_contra hn
  have hge : deficiency support Finset.univ ≤ deficiency support G := le_of_not_gt hn
  obtain ⟨M, _, hM⟩ := (Finset.univ : Finset (Finset Block)).exists_max_image
    (deficiency support) (Finset.univ_nonempty)
  have hmaxM : ∀ J, deficiency support J ≤ deficiency support M :=
    fun J => hM J (Finset.mem_univ _)
  have hex : ∃ H : Finset Block, H ≠ Finset.univ ∧
      ∀ J, deficiency support J ≤ deficiency support H := by
    by_cases hm : M = Finset.univ
    · refine ⟨G, hG, fun J => ?_⟩
      have hJM : deficiency support J ≤ deficiency support Finset.univ := by
        simpa only [hm] using hmaxM J
      exact hJM.trans hge
    · exact ⟨M, hm, hmaxM⟩
  obtain ⟨H, hH, hmax⟩ := hex
  obtain ⟨f, hf, hi⟩ := maximal_complement_matching support H hmax
  exact proper_complement_matching_impossible q owner uses value hcapacity hcover
    hprivate H hH f hf hi

/-- 纯组合层：全族的亏格最大且所有槽被使用，则全部槽可匹配到不同块。 -/
theorem matching_of_deficiency_maximum (support : Block → Finset Slot)
    (hfull : active support Finset.univ = Finset.univ)
    (hmax : ∀ G, deficiency support G ≤ deficiency support Finset.univ) :
    ∃ f : Slot → Block, Function.Injective f ∧ ∀ s, s ∈ support (f s) := by
  classical
  let neigh (s : Slot) : Finset Block := Finset.univ.filter (fun i => s ∈ support i)
  have hall : ∀ T : Finset Slot, T.card ≤ (T.biUnion neigh).card := by
    intro T
    let N := T.biUnion neigh
    let G := Finset.univ \ N
    have hd : Disjoint (active support G) T := by
      apply Finset.disjoint_left.mpr
      intro s hs ht
      obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp hs
      apply (Finset.mem_sdiff.mp hi).2
      exact Finset.mem_biUnion.mpr ⟨s, ht,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsi⟩⟩
    have hcs : (active support G).card + T.card ≤ Fintype.card Slot := by
      rw [← Finset.card_union_of_disjoint hd]
      exact Finset.card_le_univ _
    have hcg : G.card + N.card = Fintype.card Block := by
      simpa only [Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    have hm := hmax G
    unfold deficiency at hm
    rw [hfull, Finset.card_univ, Finset.card_univ] at hm
    change T.card ≤ N.card
    omega
  obtain ⟨f, hf, hi⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' neigh).mp hall
  exact ⟨f, hf, fun s => (Finset.mem_filter.mp (hi s)).2⟩

/-- 极小盒覆盖给出全槽匹配和一个未被匹配使用的余块。 -/
theorem minimal_cover_matching
    (q : Var → ℕ) (owner : Slot → Var) (uses : Block → Finset Var)
    (value : (i : Block) → (v : Var) → Fin (q v))
    (hcapacity : ∀ v, (Finset.univ.filter (fun s => owner s = v)).card < q v)
    (hcover : ∀ x : (v : Var) → Fin (q v),
      ∃ i, ∀ v ∈ uses i, x v = value i v)
    (hprivate : ∀ i, ∃ x : (v : Var) → Fin (q v),
      ∀ j, j ≠ i → ∃ v ∈ uses j, x v ≠ value j v)
    (hfull : active (slotSupport owner uses) Finset.univ = Finset.univ) :
    ∃ f : Slot → Block, Function.Injective f ∧
      (∀ s, owner s ∈ uses (f s)) ∧ ∃ anchor, ∀ s, f s ≠ anchor := by
  classical
  have hstrict := strict_deficiency q owner uses value hcapacity hcover hprivate
  have hmax : ∀ G, deficiency (slotSupport owner uses) G ≤
      deficiency (slotSupport owner uses) Finset.univ := by
    intro G
    by_cases hG : G = Finset.univ
    · rw [hG]
    · exact (hstrict G hG).le
  obtain ⟨f, hf, hi⟩ := matching_of_deficiency_maximum _ hfull hmax
  have hempty : (∅ : Finset Block) ≠ Finset.univ := by
    obtain ⟨i, _⟩ := hcover (fun v => ⟨0, lt_of_le_of_lt (Nat.zero_le _) (hcapacity v)⟩)
    intro he
    have : i ∈ (∅ : Finset Block) := he.symm ▸ Finset.mem_univ i
    simp at this
  have hc : Fintype.card Slot < Fintype.card Block := by
    have hh := hstrict ∅ hempty
    unfold deficiency at hh
    rw [hfull] at hh
    simp only [active, Finset.biUnion_empty, Finset.card_empty,
      Nat.cast_zero, sub_self, Finset.card_univ] at hh
    omega
  have himage : (Finset.univ.image f).card < (Finset.univ : Finset Block).card := by
    simpa only [Finset.card_image_of_injective _ hf, Finset.card_univ] using hc
  obtain ⟨anchor, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card himage
  refine ⟨f, hf, fun s => (Finset.mem_filter.mp (hi s)).2, anchor, ?_⟩
  intro s he
  exact ha (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, he⟩)


end MinimalCoverMatching

/-- 有限盒覆盖的逐组截断下界：核心匹配存在性与组选中容量已完整连接。
各块的坐标支持只依赖组别；选出的块仅作为计数证书，不宣称仍然覆盖。 -/
theorem finite_box_capacity_bound
    {B S V G : Type*} [Fintype B] [Fintype S] [DecidableEq V] [DecidableEq G]
    (q : V → ℕ) (owner : S → V) (group : B → G) (groupUses : G → Finset V)
    (value : (i : B) → (v : V) → Fin (q v))
    (hcapacity : ∀ v, (Finset.univ.filter (fun s => owner s = v)).card < q v)
    (hcover : ∀ x : (v : V) → Fin (q v),
      ∃ i, ∀ v ∈ groupUses (group i), x v = value i v)
    (hprivate : ∀ i, ∃ x : (v : V) → Fin (q v),
      ∀ j, j ≠ i → ∃ v ∈ groupUses (group j), x v ≠ value j v)
    (hfull : MinimalCoverMatching.active
      (MinimalCoverMatching.slotSupport owner (fun i => groupUses (group i)))
      Finset.univ = Finset.univ) :
    Fintype.card S + 1 ≤ ∑ ν ∈ Finset.univ.image group,
      min ((Finset.univ.filter (fun i => group i = ν)).card)
        ((MinimalCoverMatching.slotSupport owner groupUses ν).card + 1) := by
  classical
  obtain ⟨f, hf, hi, anchor, ha⟩ := MinimalCoverMatching.minimal_cover_matching
    q owner (fun i => groupUses (group i)) value hcapacity hcover hprivate hfull
  exact matching_capacity_bound group (MinimalCoverMatching.slotSupport owner groupUses)
    f hf (fun s => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi s⟩) anchor ha


/-! CRT 桥接的第一层：定长 p 进位坐标。
不使用原题的开放定理；以 ofDigits 的一般性质证明。 -/
namespace DigitCoordinates

def encode {p k : ℕ} (hp : 1 < p) (x : Fin k → Fin p) : Fin (p ^ k) :=
  ⟨Nat.ofDigits p (List.ofFn (fun t => (x t).val)), by
    simpa only [List.length_ofFn] using Nat.ofDigits_lt_base_pow_length
      (l := List.ofFn (fun t : Fin k => (x t).val)) hp (by
      intro a ha
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp ha
      exact (x t).isLt)⟩

def decode {p k : ℕ} (hp : 0 < p) (m : ℕ) (t : Fin k) : Fin p :=
  ⟨m / p ^ t.val % p, Nat.mod_lt _ hp⟩

theorem decode_encode {p k : ℕ} (hp : 1 < p) (x : Fin k → Fin p) :
    decode (Nat.zero_lt_of_lt hp) (encode hp x).val = x := by
  funext t
  apply Fin.ext
  change Nat.ofDigits p (List.ofFn (fun s => (x s).val)) / p ^ t.val % p = (x t).val
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop t.val (Nat.zero_lt_of_lt hp) _ (by
    intro a ha
    obtain ⟨s, rfl⟩ := List.mem_ofFn.mp ha
    exact (x s).isLt), Nat.ofDigits_mod_eq_head!]
  simp [List.head!_eq_head?_getD, t.isLt, Nat.mod_eq_of_lt (x t).isLt]

theorem encode_bijective {p k : ℕ} (hp : 1 < p) : Function.Bijective (@encode p k hp) := by
  have hinj : Function.Injective (@encode p k hp) := by
    intro x y h
    have hh := congrArg (fun z : Fin (p ^ k) => @decode p k (Nat.zero_lt_of_lt hp) z.val) h
    simpa only [decode_encode] using hh
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩

theorem encode_decode {p k : ℕ} (hp : 1 < p) (m : Fin (p ^ k)) :
    encode hp (decode (Nat.zero_lt_of_lt hp) m.val) = m := by
  obtain ⟨x, rfl⟩ := (encode_bijective hp).surjective m
  rw [decode_encode]

/-- 两整数（自然数部分）模 p^k 同余，恰好意味着前 k 个位坐标相同。 -/
theorem mod_pow_eq_iff_digits {p k m a : ℕ} (_hp : 0 < p) :
    m % p ^ k = a % p ^ k ↔ ∀ t < k, m / p ^ t % p = a / p ^ t % p := by
  constructor
  · intro h t ht
    have hd : p ^ (t + 1) ∣ p ^ k := Nat.pow_dvd_pow p (by omega)
    have he : m % p ^ (t + 1) = a % p ^ (t + 1) := by
      rw [← Nat.mod_mod_of_dvd m hd, ← Nat.mod_mod_of_dvd a hd, h]
    have he' := congrArg (fun z => z / p ^ t) he
    simpa only [Nat.pow_succ, Nat.mod_mul_right_div_self] using he'
  · intro h
    induction k with
    | zero => simp only [Nat.pow_zero, Nat.mod_one]
    | succ k ih =>
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (fun t ht => h t (by omega)), h k (by omega)]

def modValue {p : ℕ} (hp : 0 < p) (k : ℕ) (m : ℤ) : Fin (p ^ k) :=
  ⟨(m % (p ^ k : ℕ)).toNat, (Int.toNat_lt (Int.emod_nonneg _ (by positivity))).mpr
    (Int.emod_lt_of_pos _ (by positivity))⟩

theorem modValue_natCast {p : ℕ} (hp : 0 < p) (k m : ℕ) :
    (modValue hp k (m : ℤ)).val = m % p ^ k := by
  simp only [modValue, ← Int.natCast_emod, Int.toNat_natCast]

theorem modValue_mod_pow {p α β : ℕ} (hp : 0 < p) (hβ : β ≤ α) (m : ℤ) :
    (((modValue hp α m).val % p ^ β : ℕ) : ℤ) = m % (p ^ β : ℕ) := by
  rw [Int.natCast_emod]
  change (((m % (p ^ α : ℕ)).toNat : ℤ) % (p ^ β : ℕ)) = _
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  exact Int.emod_emod_of_dvd m (by exact_mod_cast Nat.pow_dvd_pow p hβ)

/-- 整数版本：公差 p^β 固定的正是 p 进位前 β 个坐标，负整数同样适用。 -/
theorem int_modEq_iff_prefix {p α β : ℕ} (hp : 0 < p) (hβ : β ≤ α) (m a : ℤ) :
    Int.ModEq (p ^ β : ℕ) m a ↔
      ∀ t : Fin α, t.val < β →
        decode hp (modValue hp α m).val t = decode hp (modValue hp α a).val t := by
  have he : Int.ModEq (p ^ β : ℕ) m a ↔
      (modValue hp α m).val % p ^ β = (modValue hp α a).val % p ^ β := by
    rw [Int.ModEq, ← modValue_mod_pow hp hβ m, ← modValue_mod_pow hp hβ a]
    exact Int.natCast_inj
  rw [he, mod_pow_eq_iff_digits hp]
  constructor
  · intro h t ht
    exact Fin.ext (h t.val ht)
  · intro h t ht
    exact congrArg Fin.val (h ⟨t, lt_of_lt_of_le ht hβ⟩ ht)

/-- 任意各素数幂的位向量都能由同一个整数实现（有限 CRT）。 -/
theorem realize_coordinates {P : Type*} [Fintype P] [DecidableEq P]
    (base α : P → ℕ) (hbase : ∀ p, 1 < base p)
    (hcop : Pairwise (fun p q => (base p ^ α p).Coprime (base q ^ α q)))
    (x : (p : P) → Fin (α p) → Fin (base p)) :
    ∃ m : ℤ, ∀ p, decode (Nat.zero_lt_of_lt (hbase p))
      (modValue (Nat.zero_lt_of_lt (hbase p)) (α p) m).val = x p := by
  classical
  let residues (p : P) := (encode (hbase p) (x p)).val
  let moduli (p : P) := base p ^ α p
  let r := Nat.chineseRemainderOfFinset residues moduli Finset.univ
    (fun p _ => pow_ne_zero _ (ne_of_gt (Nat.zero_lt_of_lt (hbase p))))
    (by intro p _ q _ hpq; exact hcop hpq)
  refine ⟨(r.val : ℤ), fun p => ?_⟩
  have he : r.val % base p ^ α p = (encode (hbase p) (x p)).val := by
    simpa only [Nat.ModEq, residues, moduli,
      Nat.mod_eq_of_lt (encode (hbase p) (x p)).isLt] using
      r.property p (Finset.mem_univ p)
  rw [modValue_natCast, he, decode_encode]


end DigitCoordinates

namespace APDigitMatching

abbrev Prime (n : ℕ) := ↥n.primeFactors
abbrev Coord (n : ℕ) := (p : Prime n) × Fin (n.factorization p.val)
abbrev Slots (n : ℕ) := (v : Coord n) × Fin (v.fst.val - 1)

theorem prime {n : ℕ} (p : Prime n) : p.val.Prime :=
  Nat.prime_of_mem_primeFactors p.property

def uses (n ν : ℕ) : Finset (Coord n) :=
  Finset.univ.filter (fun v => v.snd.val < ν.factorization v.fst.val)

def digit (n : ℕ) (m : ℤ) (v : Coord n) : Fin v.fst.val :=
  DigitCoordinates.decode (prime v.fst).pos
    (DigitCoordinates.modValue (prime v.fst).pos (n.factorization v.fst.val) m).val v.snd

theorem owner_capacity (n : ℕ) (v : Coord n) :
    (Finset.univ.filter (fun s : Slots n => s.fst = v)).card < v.fst.val := by
  classical
  have he : Finset.univ.filter (fun s : Slots n => s.fst = v) =
      Finset.univ.image (fun t : Fin (v.fst.val - 1) => (⟨v, t⟩ : Slots n)) := by
    ext s
    rcases s with ⟨w, t⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      subst w
      exact ⟨t, rfl⟩
    · rintro ⟨t', h⟩
      exact congrArg Sigma.fst h.symm
  rw [he, Finset.card_image_of_injective _ (by
    intro t u h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h), Finset.card_univ,
    Fintype.card_fin]
  have hp := (prime v.fst).pos
  omega

theorem slots_card (n : ℕ) : Fintype.card (Slots n) + 1 = bound n := by
  classical
  simp only [Slots, Fintype.card_sigma, Fintype.card_fin, Coord, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.sum_coe_sort n.primeFactors (fun p : ℕ => n.factorization p * (p - 1))]
  unfold bound
  omega

theorem realize (n : ℕ) (x : (v : Coord n) → Fin v.fst.val) :
    ∃ m : ℤ, ∀ v, digit n m v = x v := by
  classical
  obtain ⟨m, hm⟩ := DigitCoordinates.realize_coordinates
    (fun p : Prime n => p.val) (fun p => n.factorization p.val)
    (fun p => (prime p).one_lt)
    (by
      intro p q hpq
      apply Nat.Coprime.pow
      exact (prime p).coprime_iff_not_dvd.mpr (by
        intro h
        have he := (Nat.dvd_prime (prime q)).mp h
        have he : p.val = q.val := he.resolve_left (prime p).ne_one
        exact hpq (Subtype.ext he)))
    (fun p t => x ⟨p, t⟩)
  refine ⟨m, fun ⟨p, t⟩ => ?_⟩
  exact congrFun (hm p) t

/-- d|n 的 AP 同余条件，精确等价于其前缀位坐标全部相等。 -/
theorem memAP_iff_digits {B : Type*} (n : ℕ) (a : B → ℤ) (d : B → ℕ)
    (hn : n ≠ 0) (hd : ∀ i, 0 < d i) (hdiv : ∀ i, d i ∣ n) (i : B) (m : ℤ) :
    MemAP a d i m ↔ ∀ v ∈ uses n (d i), digit n m v = digit n (a i) v := by
  classical
  have hle := (Nat.factorization_le_iff_dvd (hd i).ne' hn).mpr (hdiv i)
  have hap : MemAP a d i m ↔ (d i : ℤ) ∣ m - a i := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by linarith⟩
  rw [hap]
  constructor
  · intro h v hv
    have ht := (Finset.mem_filter.mp hv).2
    have hpow := Nat.ordProj_dvd (d i) v.fst.val
    have hpow' : ((v.fst.val ^ (d i).factorization v.fst.val : ℕ) : ℤ) ∣ (d i : ℤ) := by
      exact_mod_cast hpow
    have hdm : ((v.fst.val ^ (d i).factorization v.fst.val : ℕ) : ℤ) ∣ m - a i :=
      hpow'.trans h
    have he : Int.ModEq (v.fst.val ^ (d i).factorization v.fst.val : ℕ) m (a i) :=
      (Int.modEq_iff_dvd).mpr (by
        have hh := dvd_neg.mpr hdm
        rwa [neg_sub] at hh)
    exact (DigitCoordinates.int_modEq_iff_prefix (prime v.fst).pos
      (hle v.fst.val) m (a i)).mp he v.snd ht
  · intro h
    rw [Int.natCast_dvd]
    by_cases hz : (m - a i).natAbs = 0
    · rw [hz]; exact dvd_zero _
    apply (Nat.factorization_le_iff_dvd (hd i).ne' hz).mp
    intro p
    by_cases hp : p ∈ (d i).primeFactors
    · let pp : Prime n := ⟨p, Nat.primeFactors_mono (hdiv i) hn hp⟩
      have hprefix : ∀ t : Fin (n.factorization p), t.val < (d i).factorization p →
          digit n m ⟨pp, t⟩ = digit n (a i) ⟨pp, t⟩ := by
        intro t ht
        exact h ⟨pp, t⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
      have he := (DigitCoordinates.int_modEq_iff_prefix (prime pp).pos (hle p) m (a i)).mpr
        hprefix
      have hpd : (p ^ (d i).factorization p : ℕ) ∣ (m - a i).natAbs := by
        apply Int.natCast_dvd.mp
        have hh := Int.modEq_iff_dvd.mp he
        have hh' := dvd_neg.mpr hh
        rwa [neg_sub] at hh'
      exact ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hz).mp hpd
    · have hzero : (d i).factorization p = 0 := by
        simpa only [Nat.support_factorization] using Finsupp.notMem_support_iff.mp hp
      rw [hzero]
      exact Nat.zero_le _

theorem group_slots_card {n ν : ℕ} (hn : n ≠ 0) (hν : ν ≠ 0) (hdiv : ν ∣ n) :
    (MinimalCoverMatching.slotSupport (fun s : Slots n => s.fst) (uses n) ν).card + 1 =
      bound ν := by
  classical
  have hle := (Nat.factorization_le_iff_dvd hν hn).mpr hdiv
  have hf (v : Coord n) :
      ((Finset.univ : Finset (Fin (v.fst.val - 1))).filter
        (fun _ => v ∈ uses n ν)).card = if v ∈ uses n ν then v.fst.val - 1 else 0 := by
    by_cases hv : v ∈ uses n ν <;> simp [hv]
  change ((Finset.univ : Finset (Slots n)).filter (fun s => s.fst ∈ uses n ν)).card + 1 = _
  rw [← Finset.univ_sigma_univ, Finset.filter_sigma, Finset.card_sigma]
  simp_rw [hf]
  rw [Fintype.sum_sigma]
  have hp (p : Prime n) :
      (∑ t : Fin (n.factorization p.val),
        if (⟨p, t⟩ : Coord n) ∈ uses n ν then p.val - 1 else 0) =
        ν.factorization p.val * (p.val - 1) := by
    simp only [uses, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, Fin.card_filter_val_lt,
      min_eq_right (hle p.val)]
  simp_rw [hp]
  rw [Finset.sum_coe_sort n.primeFactors (fun p : ℕ => ν.factorization p * (p - 1))]
  have hs : ∑ p ∈ n.primeFactors, ν.factorization p * (p - 1) =
      ∑ p ∈ ν.primeFactors, ν.factorization p * (p - 1) := by
    symm
    apply Finset.sum_subset (Nat.primeFactors_mono hdiv hn)
    intro p _ hp
    have hz : ν.factorization p = 0 := by
      simpa only [Nat.support_factorization] using Finsupp.notMem_support_iff.mp hp
    rw [hz, zero_mul]
  rw [hs]
  unfold bound
  omega

end APDigitMatching

/-- 全局匹配路线的截断目标 TGT；不依赖旧归纳、Pp/Rp 或 T23prime。 -/
theorem truncated_cover_bound {B : Type*} [Fintype B] (a : B → ℤ) (d : B → ℕ)
    (hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, Essential a d i) :
    bound (lcmDiff d) ≤ ∑ ν ∈ Finset.univ.image d, min (diffCount d ν) (bound ν) := by
  classical
  let n := lcmDiff d
  have hn : n ≠ 0 := (lcmDiff_pos hd).ne'
  have hdiv : ∀ i, d i ∣ n := fun i => dvd_lcmDiff i
  have hap := APDigitMatching.memAP_iff_digits n a d hn hd hdiv
  have hboxcover : ∀ x : (v : APDigitMatching.Coord n) → Fin v.fst.val,
      ∃ i, ∀ v ∈ APDigitMatching.uses n (d i), x v = APDigitMatching.digit n (a i) v := by
    intro x
    obtain ⟨m, hm⟩ := APDigitMatching.realize n x
    obtain ⟨i, hi⟩ := hcover m
    refine ⟨i, fun v hv => ?_⟩
    rw [← hm v]
    exact (hap i m).mp hi v hv
  have hboxprivate : ∀ i, ∃ x : (v : APDigitMatching.Coord n) → Fin v.fst.val,
      ∀ j, j ≠ i → ∃ v ∈ APDigitMatching.uses n (d j),
        x v ≠ APDigitMatching.digit n (a j) v := by
    intro i
    obtain ⟨m, _, hm⟩ := hess i
    refine ⟨APDigitMatching.digit n m, fun j hji => ?_⟩
    have hh : ¬ ∀ v ∈ APDigitMatching.uses n (d j),
        APDigitMatching.digit n m v = APDigitMatching.digit n (a j) v := by
      intro hh
      exact hm j hji ((hap j m).mpr hh)
    push Not at hh
    exact hh
  have hfull : MinimalCoverMatching.active
      (MinimalCoverMatching.slotSupport (fun s : APDigitMatching.Slots n => s.fst)
        (fun i => APDigitMatching.uses n (d i))) Finset.univ = Finset.univ := by
    ext s
    simp only [MinimalCoverMatching.active, MinimalCoverMatching.slotSupport,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    let p := s.fst.fst
    have hp := APDigitMatching.prime p
    have hpd : p.val ^ n.factorization p.val ∣ lcmDiff d := Nat.ordProj_dvd n p.val
    obtain ⟨i, hi⟩ := exists_of_prime_pow_dvd_lcmDiff hp (n.factorization p.val)
      ⟨(hcover 0).choose⟩ d hpd
    have hle := (hp.pow_dvd_iff_le_factorization (hd i).ne').mp hi
    refine ⟨i, ?_⟩
    simpa only [APDigitMatching.uses, Finset.mem_filter, Finset.mem_univ, true_and] using
      lt_of_lt_of_le s.fst.snd.isLt hle
  have hcount := finite_box_capacity_bound
    (fun v : APDigitMatching.Coord n => v.fst.val)
    (fun s : APDigitMatching.Slots n => s.fst) d (APDigitMatching.uses n)
    (fun i => APDigitMatching.digit n (a i)) (APDigitMatching.owner_capacity n)
    hboxcover hboxprivate hfull
  rw [APDigitMatching.slots_card] at hcount
  change bound n ≤ _
  convert hcount using 1
  apply Finset.sum_congr rfl
  intro ν hν
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hν
  rw [APDigitMatching.group_slots_card hn (hd i).ne' (hdiv i)]
  rfl

#print axioms truncated_cover_bound

/-- 每组 min(m,b)+(m-b)=m，把截断目标与 σ 强化精确互换。 -/
theorem truncated_sum_add_sigma {B : Type*} [Fintype B] (d : B → ℕ) :
    (∑ ν ∈ Finset.univ.image d, min (diffCount d ν) (bound ν)) + sigma d =
      Fintype.card B := by
  classical
  rw [sigma, ← Finset.sum_add_distrib, ← diffCount_sum d]
  apply Finset.sum_congr rfl
  intro ν _
  omega

/-- σ 强化版：由 CRT 位坐标、极小不可满足亏格稳定性、Hall 匹配和组容量计数证明。 -/
theorem T23prime : ∀ n : ℕ, 0 < n → ∀ (ι : Type*) [Fintype ι] (a : ι → ℤ) (d : ι → ℕ),
    lcmDiff d = n → (∀ i, 0 < d i) → (∀ m : ℤ, ∃ i, MemAP a d i m) →
    (∀ i, Essential a d i) → Fintype.card ι ≥ bound n + sigma d := by
  intro n _ ι _ a d heq hd hcover hess
  have h := truncated_cover_bound a d hd hcover hess
  rw [heq] at h
  have hid := truncated_sum_add_sigma d
  omega

/-- 由 T23prime 丢掉非负 σ，得到原题的基数下界。 -/
theorem card_ge_bound_of_allEssential {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, Essential a d i) :
    Fintype.card ι ≥ bound (lcmDiff d) := by
  have h := T23prime (lcmDiff d) (lcmDiff_pos hd) ι a d rfl hd hcover hess
  omega

/-- **主定理（原题）**：s 个正公差 AP 覆盖 ℤ、每列含独占元，则 s ≥ bound(lcm d)。
完整证明使用文件末全局匹配路线，不依赖旧归纳的开放裂块分支。 -/
theorem problem7 {s : ℕ} (a : Fin s → ℤ) (d : Fin s → ℕ)
    (hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m) :
    s ≥ bound (lcmDiff d) := by
  simpa only [Fintype.card_fin] using card_ge_bound_of_allEssential hd hcover hess

#print axioms T23prime
#print axioms problem7

/-- 旧强化归纳目标现由极小子覆盖与已完成的匹配定理直接推出。
任何原本质块都必须在每个子覆盖中，因此 essLcm 整除极小子覆盖的真实 lcm。 -/
theorem main_induction_strong : ∀ n : ℕ, 0 < n → ∀ (ι : Type*) [Fintype ι] (a : ι → ℤ)
    (d : ι → ℕ), essLcm a d = n → (∀ i, 0 < d i) → (∀ m : ℤ, ∃ i, MemAP a d i m) →
    Fintype.card ι + rho a d ≥ bound n := by
  intro n _ ι _ a d heq hd hcover
  classical
  obtain ⟨J, hJcover, hJess⟩ := exists_minimal_subcover a d hcover
  have hcontains : ∀ i, Essential a d i → i ∈ J := by
    intro i hi
    obtain ⟨m, _, hm⟩ := hi
    obtain ⟨j, hj, hjm⟩ := hJcover m
    have hji : j = i := by
      by_contra hne
      exact hm j hne hjm
    exact hji ▸ hj
  let aJ : J → ℤ := fun i => a i.val
  let dJ : J → ℕ := fun i => d i.val
  have hdJ : ∀ i, 0 < dJ i := fun i => hd i.val
  have hcJ : ∀ m : ℤ, ∃ i, MemAP aJ dJ i m := by
    intro m
    obtain ⟨i, hi, hm⟩ := hJcover m
    exact ⟨⟨i, hi⟩, hm⟩
  have heJ : ∀ i, Essential aJ dJ i := by
    intro i
    obtain ⟨m, him, hm⟩ := hJess i.val i.property
    refine ⟨m, him, fun j hji => ?_⟩
    exact hm j.val j.property (fun h => hji (Subtype.ext h))
  have hndvd : n ∣ lcmDiff dJ := by
    rw [← heq]
    unfold essLcm lcmDiff
    apply Finset.lcm_dvd
    intro i _
    exact dvd_lcmDiff (d := dJ) ⟨i.val, hcontains i.val i.property⟩
  have hb := bound_le_of_dvd (lcmDiff_pos hdJ).ne' hndvd
  have hc := card_ge_bound_of_allEssential hdJ hcJ heJ
  have hcard : Fintype.card J ≤ Fintype.card ι := Fintype.card_subtype_le _
  omega

#print axioms main_induction_strong

/-! ## 2026-10-10 · 全局匹配路线完成记录（优先于历史开放状态）

本轮新增并完整证明的链条：
1. MinimalCoverMatching.maximal_complement_matching：最大亏格子族的剩余子句可匹配到新槽。
2. proper_complement_matching_impossible：每变量至多 q−1 个禁止值，选未禁值并与旧赋值合并；
   极小性与覆盖性使这种真子族匹配不可能。
3. strict_deficiency：真子族亏格严格小于全族；matching_of_deficiency_maximum 用槽侧 Hall
   给出全槽匹配，minimal_cover_matching 再给出未匹配余块。
4. finite_box_capacity_bound：接驳 matching_capacity_bound 得有限盒覆盖的逐组截断下界。
5. DigitCoordinates：定长 p 进位 encode/decode 互逆、前缀等价于模 p^β 同余；
   int_modEq_iff_prefix 包含负整数；realize_coordinates 用有限 CRT 实现任意数字向量。
6. APDigitMatching：MemAP ↔ 前缀位固定；真实 lcm 确保每个槽被使用；
   总槽数+1=b(n)，公差 ν 的支持槽数+1=b(ν)。
7. truncated_cover_bound：Σν min(mν,bν) ≥ b(n)；
   truncated_sum_add_sigma：Σν min(mν,bν)+σ=card；由此得到 T23prime，再得到 problem7。
8. main_induction_strong：原本质块必须出现在任意子覆盖中，因此 essLcm 整除极小子覆盖的 lcm；
   用整除单调性和 problem7 的一般指标版本直接得到旧强化目标，旧裂块归纳尝试仅注释存档。

成果归属：一般亏格稳定性/极小不可满足理论是 Kullmann 文献中的已有理论，非我方独立成果；
上述 Lean 从 Mathlib Hall 重建证明。CRT、数字展开采用库的一般结论。这里记录本项目的
形式化与“按公差组选中容量→σ强化”接驳，不把已有一般理论列为我方发现。

核验：lake env lean "IMO组合预选题.lean"；核心最终定理的 #print axioms 均只含
propext、Classical.choice、Quot.sound，无 sorryAx、Lean.ofReduceBool 或新公理。
旧版本仍保留 Pp_bound/Rp_bound 两个旧路线开放辅助目标；本零告警副本已移除它们。
最终依赖链不使用这两个目标，本副本无有效的占位证明声明。
所选 b(n) 个块是计数证书，不声称构成子覆盖；不存在用开放目标反证新引理的循环。
独立开发模块：explore/MinimalCoverMatching.lean、DigitCoordinates.lean、MatchingCapacity.lean。
-/
