import Mathlib

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

#print axioms minimal_cover_matching

end MinimalCoverMatching
