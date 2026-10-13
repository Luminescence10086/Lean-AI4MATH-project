import Mathlib

/-! 2026-10-13：不直接引用强组合结论的初等路线研究。
两份完整纸面证明在 IMO组合预选题_初等证明补充.md：
(1) 最大匹配与交替路径；(2) 最大槽差额与从头证明的有限代表元归纳。
两份证明均取得全槽匹配和余块，再用同差组容量得到 TGT、σ 强化及原题。
本模块仅将两路线共享的初等赋值矛盾步骤独立编译，未宣称图论步骤已 Lean 形式化。
该步骤从既有开发模块中抽取，不调用 Hall、严格亏格稳定性或原题定理。
既有两个主 Lean 文件保持不变。
-/

namespace ElementaryMatching

variable {Block Slot : Type*} [Fintype Block] [Fintype Slot]
variable {Var : Type*} [DecidableEq Var]

noncomputable def active (support : Block → Finset Slot) (G : Finset Block) : Finset Slot :=
  by classical exact G.biUnion support

noncomputable def slotSupport (owner : Slot → Var) (uses : Block → Finset Var)
    (i : Block) : Finset Slot := by
  classical exact Finset.univ.filter (fun s => owner s ∈ uses i)
/-- 剩余子句若能匹配到未被 H 使用的槽，就能用这些变量满足全部剩余子句。
每个变量的槽数严格小于值域大小，故至少剩下一个未被禁止的值。 -/
theorem local_assignment_contradiction
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

#print axioms local_assignment_contradiction
end ElementaryMatching
