# IMO 组合预选题：最终证明逻辑图

最新版的全局分层图见 [IMO组合预选题_全局证明逻辑图.md](C:/Users/18746/Desktop/数竞屠宰场/IMO组合预选题_全局证明逻辑图.md)，按从左到右展开，补齐题目定义、基础引理、已有工具和最终结论。本文件保留为先前阶段图。

本图对应 [IMO组合预选题.lean](C:/Users/18746/Desktop/数竞屠宰场/IMO组合预选题.lean:3408) 中已完成的全局匹配证明。图中的箭头表示推导或必要输入；最后的旁支给出旧强化目标的完整证明。

另有 [零告警交付副本](C:/Users/18746/Desktop/数竞屠宰场/IMO组合预选题_零告警.lean)，最终证明链完全一致；它移除了图外未使用的 `Pp_bound` / `Rp_bound` 开放目标，旧 Lean 文件原样保留。

记号：原覆盖族为 F，块数为 s，真实公差最小公倍数为 n。设 αₚ = vₚ(n)，βₚ(ν) = vₚ(ν)，mν 为公差恰好等于 ν 的块数。

- b(r) = 1 + Σₚ vₚ(r)(p − 1)，对应 Lean 的 `bound`。
- σ = Σν max(mν − b(ν), 0)，对应 Lean 的 `sigma`。
- 每个位变量 v 的值域大小为 qᵥ；将它复制成 qᵥ − 1 个槽。在本题中 qᵥ = p。
- S(G) 是子句子族 G 使用的槽的并集，δ(G) = |G| − |S(G)|；亏格在整数 ℤ 中计算。

```mermaid
flowchart TD
  subgraph MODEL["一、整数 AP 覆盖转为有限坐标模型"]
    A["前提：正公差 AP 覆盖全部整数<br/>每块都有独占点；n = lcm(dᵢ)"]
    B["CRT 分解模 n；每个模 p^αₚ 余数作定长 p 进位展开<br/>变量为 (p,t)，0 ≤ t ＜ αₚ；值域为 Fin p"]
    C["encode / decode 互逆<br/>任意完整位向量都能由一个整数实现<br/>DigitCoordinates.realize_coordinates"]
    D["公差 ν 的 AP 固定各 p 的前 βₚ(ν) 位<br/>m 属于块 i ⇔ 所有被固定的位等于 aᵢ 的对应位<br/>APDigitMatching.memAP_iff_digits；适用于负整数"]
    E["取每个盒子的补条件作为子句 Cᵢ<br/>Cᵢ：至少一个被固定的位与指定值不同"]
    F["覆盖性 ⇒ 全部子句同时满足不可能<br/>独占点 ⇒ 删除任意子句后其余子句可同时满足<br/>得到极小不可满足系统"]
    A --> B
    B --> C
    B --> D
    D --> E
    A --> F
    C --> F
    E --> F
  end

  subgraph STABILITY["二、严格亏格稳定性：第一次 Hall 与赋值反证"]
    G["反设：存在真子族 G，δ(G) ≥ δ(F)<br/>可选真子族 H，使 δ(H) 在所有子族中最大"]
    H["对任意 J ⊆ F ∖ H，由最大性得到<br/>|J| ≤ |S(J) ∖ S(H)|<br/>这是剩余子句到新槽的 Hall 条件"]
    I["第一次 Hall：F ∖ H 的每条子句匹配到不同新槽<br/>槽属于该子句的变量，且不被 H 使用<br/>maximal_complement_matching"]
    J["每个新变量至多负责 qᵥ − 1 条子句<br/>每条只禁止一个值，因此可选一个未禁值<br/>满足该变量负责的所有子句"]
    K["H 是真子族，由极小性取得满足 H 的赋值<br/>新变量不出现在 H 中，故可合并两部分赋值"]
    L["合并赋值满足 F 的全部子句，矛盾<br/>proper_complement_matching_impossible"]
    M["结论：每个真子族 G 都满足 δ(G) ＜ δ(F)<br/>strict_deficiency"]
    F --> G
    G --> H
    H --> I
    I --> J
    F --> K
    G --> K
    J --> L
    K --> L
    L --> M
  end

  subgraph MATCH["三、全槽匹配与余块：第二次 Hall"]
    N["将 (p,t) 复制成 p − 1 个槽<br/>真实 lcm 保证每个槽被至少一个块使用<br/>总槽数 W = b(n) − 1"]
    O["任取槽集 T；令 N(T) 为碰到 T 的子句<br/>令 G = F ∖ N(T)，则 S(G) 与 T 不交<br/>δ(G) ≥ δ(F) + |T| − |N(T)|"]
    P["若 |N(T)| ＜ |T|，则 δ(G) ＞ δ(F)，矛盾<br/>故所有 T 都满足槽侧 Hall 条件"]
    Q["第二次 Hall：全部 W 个槽单射匹配到不同块<br/>且每个被匹配块使用相应槽<br/>matching_of_deficiency_maximum"]
    R["取空子族：δ(F) ≥ 1，故 s ≥ W + 1<br/>存在一个未被全槽匹配使用的块 anchor"]
    S["获得：全槽匹配 f ＋ 余块 anchor<br/>minimal_cover_matching"]
    A --> N
    D --> N
    N --> O
    O --> P
    M --> P
    P --> Q
    M --> R
    N --> R
    A --> R
    Q --> S
    R --> S
  end

  subgraph COUNT["四、按公差分组计数，闭合 σ 强化和原题"]
    U["同差 ν 的全部块使用相同的前缀槽集 Sν<br/>|Sν| = b(ν) − 1<br/>APDigitMatching.group_slots_card"]
    V["选中全部匹配块，再加入 anchor，得到指标集合 K<br/>|K| = W + 1 = b(n)<br/>K 仅为计数证书，不声称仍是子覆盖"]
    X["每组的匹配块对应不同槽，且都落在 Sν<br/>加 anchor 后该组选中数至多 b(ν)，也至多 mν<br/>所以 |K ∩ 公差ν组| ≤ min(mν,b(ν))"]
    Y["对公差组求和：b(n) ≤ Σν min(mν,b(ν))<br/>matching_capacity_bound → finite_box_capacity_bound<br/>→ truncated_cover_bound（TGT）"]
    Z["逐组恒等式：min(mν,b(ν)) + max(mν − b(ν),0) = mν<br/>求和：Σν min(mν,b(ν)) + σ = s<br/>truncated_sum_add_sigma"]
    AA["σ 强化版：s ≥ b(n) + σ<br/>T23prime"]
    AB["σ ≥ 0，丢掉非负项<br/>原题：s ≥ b(n)<br/>card_ge_bound_of_allEssential → problem7"]
    D --> U
    S --> V
    N --> V
    U --> X
    V --> X
    X --> Y
    Y --> AA
    Z --> AA
    AA --> AB
  end

  subgraph LEGACY["五、旁支：从最终定理证明旧强化目标"]
    AC["对任意覆盖取极小子覆盖 J<br/>exists_minimal_subcover"]
    AD["每个原本质块必须保留在 J 中<br/>故 essLcm(F) 整除 lcm(J)"]
    AE["J 本质且覆盖：|J| ≥ b(lcm(J))<br/>bound 的整除单调性给出<br/>b(essLcm(F)) ≤ b(lcm(J)) ≤ |J| ≤ s"]
    AF["ρ ≥ 0，因此 s + ρ ≥ b(essLcm(F))<br/>main_induction_strong"]
    AC --> AD
    AC --> AE
    AD --> AE
    AB --> AE
    AE --> AF
  end

  classDef result fill:#dcfce7,stroke:#15803d,stroke-width:2px,color:#14532d;
  classDef core fill:#dbeafe,stroke:#2563eb,stroke-width:2px,color:#1e3a8a;
  classDef certificate fill:#fef3c7,stroke:#d97706,color:#78350f;
  class M,S core;
  class V,X certificate;
  class Y,AA,AB,AF result;
```

两次 Hall 的方向不同：第一次将“剩余子句”匹配到“新槽”，用于构造满足赋值并反证；第二次将“全部槽”匹配到“不同块”，用于最终计数。独占点在第一阶段提供极小不可满足性；真实 lcm 在第三阶段确保全部槽确实被使用。

一般亏格稳定性与极小不可满足理论属于已有文献工具（Kullmann，2011），这里用 Mathlib 的 Hall 定理在 Lean 中重新证明，未加入文献公理。CRT 和数字展开使用库的一般结论。

全文件已通过 Lean 验证；`truncated_cover_bound`、`T23prime`、`problem7`、`main_induction_strong` 的公理检查仅含 `propext`、`Classical.choice`、`Quot.sound`，不含 `sorryAx`。旧路线的 `Pp_bound`、`Rp_bound` 仍是开放辅助目标，**不在本图的最终证明依赖链中**。
