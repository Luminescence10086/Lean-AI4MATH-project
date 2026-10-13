# t23prime-math-state · 2026-10-10

## 2026-10-13：最早路线的修补评估

用户问最早被否决路径能否修补，按 PC/最优线/Pp/Rp/逐素纤维配平与 A/B/V 理解。
新增 `IMO组合预选题_旧路线修补评估.md`，明确区分完整重组修补与纯旧路线尚未闭合。
新发现私有点星形纸面证明：改变私有块固定的一个位，其余不变；覆盖它的其他块必须
固定该位为新值，不同改变对应不同块。取最高 p 指数载体得到 Wp 个星形块，加载体
得 Pp；每个过载组另取未使用块，得到 Rp。PC 的单树私有叶版本也同样证明。
这些是本轮独立展开的推导，未声称为原创一般理论，尚未完成 Pp/Rp 的新 Lean 形式化。

Pp/Rp 不足以在算术上推出 TGT：非合法覆盖的 census={6:3} 满足两者却 S=3<b(6)=4，
D=0,H=2,ΣE=0。正确全局预算为 ΣE≥D+H−(ω(n)−1)。
若使用已形式化初等配置核心先取得 K、|K|=b(n)、cν≤min(mν,bν)，则预算余量精确为
Σν(min(mν,bν)−cν)≥0，构成完整而非循环的修补版本；它共享现有交换核心，不是独立第三路。
若要求最后一步完全不用全局配置，仅靠旧纤维／逐线归纳，目前仍未闭合。

合法 n80 精确分割：8个偶数模16块+5个奇数模10块，无 d=n；b(80)=9。
单载体星形+每个未用组一个代表的最大预算仅7（16载体6、10载体7），否定这种简单修补。
私有星形证书通过4655小覆盖、320随机族、4旧案例及n80；307随机族真lcm≥60且≥7块。
脚本 verify_old_route_private_stars.py，报告 old_route_star_report.json。既有 Lean 版本未修改。

## 2026-10-13：初等交替搜索路线已完整 Lean 形式化

用户要求新文件开始 Lean 证明，可复制所需基础引理和叙述。
已完成根目录 `IMO组合预选题_初等证明.lean`（独立 import Mathlib，namespace ElementaryAPProof）。
没有导入原版、零告警版或其主定理；只复制 AP/lcm/素因子基础、CRT/位坐标与计数末步。
新核心：Matched 的最大基数子族；extend_matching 加块；swap_to_free 单步改派；
Searchable 携带释放槽的重排证书；search_closed 由有限最大化证明搜索集封闭；
full_matching_of_no_local_assignment 取得全槽匹配，结合初等赋值矛盾再推出余块。
这是一条交替搜索的证书式实现，不是显式 BFS / 路径列表；不引用增广路径定理。
完整链：新图论核心 → ElementaryMatching.minimal_cover_matching → finite_box_capacity_bound
→ CRT / APDigitMatching → truncated_cover_bound → T23prime → problem7。

整份新文件已编译 exit 0、源码无警告；最终定理的公理仅 propext、Classical.choice、Quot.sound。
内置 run_cmd 审计递归展开最终证明的类型和 theorem/opaque 证明体，共9649个常量；
不存在 HallMarriageTheorem、all_card_le_biUnion_card、strict_deficiency、sorryAx、
Lean.ofReduceBool 或 Simpson 的实际依赖。审计遇到禁用依赖会使编译报错，不只检查源码文本。
开发组件：ElementaryAlternating.lean、ElementaryBoxTail.lean.txt、ElementaryDependencyAudit.lean.txt；
assemble_elementary_lean.py 可重新组装独立交付文件。核验输出 elementary_lean_output.txt。
第一条初等路线已形式化；第二条有限代表元归纳路线仍是纸面证明。原版与零告警版未修改。
最终严格检查 `lean --error=warning` 已完成：exit 0、零警告、零错误。
日志 `elementary_strict_lean_output.txt`，交付文件925行；最终定理位于870行与888行。

## 2026-10-13：用户要求尝试不使用已有强结论的更多证明

新增根目录 `IMO组合预选题_初等证明补充.md`，两条完整纸面路线均得 σ 强化：
1. 最大匹配：未匹配槽的交替可达子图若不能增广，可将其全部邻居子句交给不同可达槽；
   每变量至多 q−1 个禁值，构造局部满足赋值，与真子族赋值合并，违背极小不可满足。
   从而全槽匹配；若所有子句也都被匹配，未禁值选择使全族可满足，所以有余块。
2. 最大槽差额 η(T)=|T|−|N(T)|：若有正差额，选全局最大者；删去 J 子句在 T 内的
   邻居槽后，由最大性得到 |J|≤其邻居槽数，从头证明的有限代表元归纳匹配 N(T) 到 T，
   得到同一局部赋值矛盾。再匹配全槽并取余块。
两路线无需引用亏格稳定性或 Hall 黑箱；第二条的代表元引理内容等于有限 Hall，
但其全部归纳证明已写出。两路线共享匹配机制，不称为完全无关的证明或原创一般定理。
纯纤维计数仍是待研究第三方向，裂块跨纤维预算尚未闭合，不算第三份证明。

`verify_elementary_matching.py` 通过 4655 个 K≤7 小模数合法覆盖、320 个不同形状压力族、
四个 n=60/240/720A/720B 案例和三个失败搜索赋值案例；307 个压力族实际 lcm≥60 且≥7块。
第二条路线的有限代表元归纳在全部512个3×3二部图上检查：247个全槽可匹配图、
96个无孤立槽而正差额的图都取得相应证书；其他图有孤立槽，不满足本题前提。
报告为 `elementary_matching_report.json`。有限检查不代替纸面证明或 Lean 核验。
`IMO组合预选题_初等路线研究.lean` 只独立抽取初等赋值矛盾步骤；两份新路线整体 Lean
形式化尚未完成。原版及零告警版 Lean 均保持不变。本轮未搜索原题解答。
研究模块已编译 exit 0、源码无警告；赋值矛盾引理公理仅为 propext、Classical.choice、Quot.sound。

## 全局图交付（2026-10-10 后续）

用户明确要求全局证明逻辑、从左到右展开、层次清晰。
已创建 `IMO组合预选题_全局证明逻辑图.md`：一个 flowchart LR，八个主阶段内部 direction TB，
覆盖题目定义、先前基础引理、CRT 位坐标、极小性、两次 Hall、组容量和最终装配。
附有旧强化目标、已有特殊情形/工具及历史反例的独立旁支；虚线区分旁支，
不把未参与最终证明的历史引理画成必要依赖。独立前提仅排列，不暗示互相推出。
原先 `IMO组合预选题_证明逻辑图.md` 保留，并在顶部指向全局新版。Lean 文件未修改。

## 零告警交付副本（2026-10-10 后续）

用户要求修复三条警告；若需删除引理，必须复制新文件并保留旧版。
已创建工作区根目录 `IMO组合预选题_零告警.lean`；`IMO组合预选题.lean` 未修改。
新副本将 `sum_bp_eq_bound_add` 的未引用参数 `hν` 改为 `_hν`，保留参数类型与定理接口；
移除两个不参与最终证明、且含 sorry 的旧辅助目标 `Pp_bound` / `Rp_bound`。
原始目标与研究记录仍在旧版；所有最终定理、反例证明均保留。
未关闭 linter，未屏蔽占位证明诊断；历史注释中的归纳尝试不属于有效声明。
`lake env lean "IMO组合预选题_零告警.lean"` 已通过，源码零警告、零错误。
Lake 在此中文目录有独立的 canonicalize path 环境提示，与三条源码警告不同；
另使用同一 Lake 的 LEAN_PATH 和工具链直接进行 `lean --error=warning` 严格核验，
最终 exit 0，零警告、零错误；全部最终定理的公理检查仍不含 sorryAx。
验证输出分别存于 `zero_warning_lean_output.txt` 和 `zero_warning_strict_lean_output.txt`。
旧文件 SHA256：739A051F24364A0A49EF043779570BD5D63CE9A6933AE532E7A1DAA5CFF9D1E5。

下文“两个开放辅助定理仍保留”的状态指旧版；新副本不含这两个声明。

## 最新状态：全局匹配路线已完成（本节优先于下文历史记录）

用户在宏观选路后说“ok你继续”；本轮已完成全部匹配核心、CRT 位坐标桥和最终装配。
`truncated_cover_bound`、`T23prime`、`problem7`、`main_induction_strong` 均有完整 Lean 证明。
全文件编译 exit 0；这些定理的 #print axioms 仅 propext、Classical.choice、Quot.sound，
无 sorryAx、Lean.ofReduceBool 或新增公理。原题与 σ 强化版已正式证明。

最终依赖链：
- 极小盒覆盖 → strict_deficiency → 全槽 Hall 匹配及未使用余块；
- matching_capacity_bound → finite_box_capacity_bound；
- DigitCoordinates 的 encode/decode、整数前缀同余、任意向量的 CRT 实现；
- APDigitMatching.memAP_iff_digits、slots_card、group_slots_card 与真实 lcm 的全槽使用；
- truncated_cover_bound（TGT）→ truncated_sum_add_sigma → T23prime → problem7；
- 极小子覆盖必须保留每个原本质块 → essLcm 整除其 lcm → main_induction_strong。

主文件实际仍有两个开放辅助定理 Pp_bound/Rp_bound（sorry），属于旧研究路线，
不参与以上证明。旧 main_induction_strong 的未完成归纳已注释存档；同名定理在末尾完整证明。
不要再把这些开放状态误写成原题未证，也不要宣称所有历史辅助命题都已证。

一般亏格稳定性/极小不可满足理论是 Kullmann 2011 文献工具，非我方独立成果；
本轮用 Mathlib Hall 重新证明它，未把文献工具作为公理。项目接驳的组容量计数另行记录。
选择的 b(n) 个块仅为计数证书，绝不声称它们还构成子覆盖。

独立无 sorry 开发模块：MinimalCoverMatching.lean、DigitCoordinates.lean、MatchingCapacity.lean。
matching_bridge_probe.lean 是一般模块及 AP 桥的开发核验副本，不作为主定理依赖。
具体证书测试仍为 4655 个小模数极小覆盖、1280 个压力样本、4 个命名案例；
1255 个压力案例真实 lcm≥60 且至少7块。一般结论的最终依据是 Lean 证明，不是样本。

以下为先前阶段的历史快照，遇到状态冲突以本节及主文件末 #print axioms 为准。

用户要求：查看 `IMO组合预选题.lean` 的注释，按照原方案解决剩余问题。
本轮沿原 σ 路线发现硬错误，故没有擅自改走文献证明路线，也没有声称原题已经完成。

## 最新宏观选路（后于以下勘误，优先读取）

用户要求先宏观设计多条可能路径，再选最可能者开始组装验证。
已比较 A：正确 D+H 配平，B：纤维递归势函数，C：位坐标/极小不可满足/Hall 匹配。
选 C。完整纸面链条与证明在 proof_paths_2026-10-10.md。

将模 n 用 CRT 和 p 进位展开成坐标积；块固定各 p 的前 vp(d) 位，其补为负单值子句。
原题前提等价于极小不可满足系统。一般加权亏格稳定性是已知文献工具（非我方成果），
来源 Kullmann arXiv:1103.3693，Lemma 1.9.4 与 Corollary 1.9.9；注记在 lit/ 下。
已给出从 Hall 重建它的纸面论证，因此 Lean 后续可重新证明，不需加入公理。

核心证书：将全部 W=b(n)−1 个槽匹配到不同块，另有一个未使用块。
同差 ν 组被匹配块数≤其支持槽数=b(ν)−1；加余块后组选中数≤min(mν,bν)。
所选 b(n) 个块不是子覆盖，而是计数证书；对组求和得到 TGT，再得到 T23prime 和原题。

第一阶段验证完成：4655 个 K=7 小模数合法覆盖、1280 个不同形状压力族，以及
n=60/240/720A/720B 四个已知案例。1255 个随机案例的真实 lcm≥60 且至少7块，最大1680。
完整报告和具体匹配数据在 matching_path_report.json 与 matching_path_certificates.json。
验证一般定理不是抽样推断；宏观数学依据是一般亏格稳定性/Hall 的纸面证明。

已形式化首个通用末步 matching_capacity_bound（主文件末和 MatchingCapacity.lean）：
给定匹配及余块，直接推出分组截断容量下界。axioms 仅 propext/Classical.choice/Quot.sound。
尚待形式化：极小不可满足→全槽匹配的存在定理；CRT 位坐标桥；最后装配主目标。
当前主 Lean 仍有 4 处开放 sorry；不能声称主定理已形式化完成。

## 同日后续核对：原重组链的额外错误（优先于下文先前记录）

用户询问当前证明链时，发现旧注释 `A ≥ Σp Lp` 的算术方向错误：
min(m,Σbp) ≤ Σmin(m,bp)。所以原 R→TGT 的证明不成立。
在 n>1 且无 d=1 块时，定义
H=Σν(Σp|ν min(mν,bp(ν))−min(mν,Σp|ν bp(ν)))≥0，
则目标精确等价于 Σp Ep ≥ D+H−(ω(n)−1)，旧 R 遗漏 H。
这是旧归约证明的错误，不是 R 在全本质覆盖上为假的证明。
下一步应先形式化此精确恒等式，再研究 H+D 的补偿；只证明旧 Rp/Rpp 不能按旧链闭合。

## 决定性新结论

- (A)、(B)、(V)、(U''-nt)、deep_saturation_candidate 均为假。
- 第一个反例：51 块全本质整数覆盖，真实 lcm=720，p=2，α=4，O={1,2}。
  y=6 上 M={1:2,2:3}，F=5≥5，M4=0，饱和过载层有两层；全局 S4=2<5。
- 第二个反例：将第一个反例最后的 (47,48) 扩为 (15,16)。仍有 51 块、全本质覆盖、
  真实 lcm=720、O={1,2}；y=6 上 M={1:2,2:3,4:1}，F=6≥5，仍有两饱和层。
  深块确实在线上，但没有在这条线上的独占点；这是旧 (B) 混淆的条件。
- 两个反例及其合法性已由主文件 `SigmaRouteAudit` 中的 Lean 证明核验。
  使用 `decide +kernel`，不使用 native_decide、sorry、文献定理。
  `#print axioms legal_counterexample` 和 `legal_counterexample_B` 应输出且只输出
  propext、Classical.choice、Quot.sound；无 sorryAx/Lean.ofReduceBool。
- 两反例上的 Pp、Rp、Rpp、R、TGT 都通过 Python 精确检查。这不是这些一般命题的证明。
- 当前反例不能直接判定载体私有线版 V-strong°，该版本仍未证。

## Lean 文件状态

- 引入实际线定义：lineCount、lineScore、overfullLayers、saturatedLayers。
- 原 A/B/V 中任意 M 的陈述没有真实线关联，是形式化错误。
- 将已证伪的 A/B/V/deep_saturation 及旧 Tpp 改成 Prop 定义，避免作为假定理引用。
- 保留的开放目标共 4 处 sorry：main_induction_strong、Pp_bound、Rp_bound、T23prime。
- problem7 仍依赖 main_induction_strong 的 sorry；原题及 σ 强化版尚未形式化完成。
- 历史交接声称“全链已形式化”“唯一 V 缺口”等不准确，已在文件头和成果清单勘误。
- 原 (V) 闭合方案被真实反例阻断；旧 TGT ← R ← ΣRp ← Rpp 链的 R→TGT 也有方向错误。
  后续需要先修复带 H 的重组关系，再证明足够的结构配平，最后完成 Lean 装配。

## 可复现文件

- `python explore/audit_sigma_route.py`：从实际公差计算 lcmlist，检查每个剩余类的覆盖、
  每个块的独占点，复核所有数值；固定显式构造，无随机性。
- `explore/sigma_route_counterexample.json`：第一个反例的全部块、独占点和逐线数据。
- `explore/sigma_route_counterexample_B.json`：第二个反例的全部块、独占点和逐线数据。
- `explore/sigma_route_audit_output.txt`：简洁复核输出。
- `explore/sigma_audit_probe.lean`：同一证书的自包含开发存档。
- `lake env lean "IMO组合预选题.lean"`：全文件检查；0 错误不表示 4 处开放目标已证明。

下次不要再尝试证明已证伪的 A/B/V/U''/deep_saturation，也不要把旧“小样本 0 反例”当成定理。
