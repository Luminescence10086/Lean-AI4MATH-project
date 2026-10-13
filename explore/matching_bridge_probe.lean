import Mathlib

def MemAP {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) (m : ℤ) : Prop :=
  ∃ k : ℤ, m = a i + (d i : ℤ) * k

def bound (n : ℕ) : ℕ := 1 + ∑ p ∈ n.primeFactors, n.factorization p * (p - 1)
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


