import Mathlib

/-! 初等交替搜索：以有限最大化和单步改派证明全槽匹配。
Searchable 的证书记录：到达槽可被释放，改派仅涉及已到达的原匹配槽。
因此扩展搜索集不需要引用 Hall、增广路径定理或亏格稳定性。 -/

namespace ElementaryAlternating

variable {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]

def Matched (support : B → Finset S) (D : Finset B) : Prop :=
  ∃ f : D → S, Function.Injective f ∧ ∀ i, f i ∈ support i.val

omit [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] in
theorem matched_empty (support : B → Finset S) : Matched support ∅ := by
  classical
  exact ⟨fun i => False.elim (Finset.notMem_empty i.val i.property),
    fun i => False.elim (Finset.notMem_empty i.val i.property),
    fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

/- 向一个有空槽的匹配加入新块，基数增加一。 -/
omit [Fintype B] [Fintype S] [DecidableEq S] in
theorem extend_matching (support : B → Finset S) (D : Finset B)
    (f : D → S) (hf : Function.Injective f) (hi : ∀ i, f i ∈ support i.val)
    (b : B) (_hb : b ∉ D) (s : S) (hs : s ∈ support b) (hfree : ∀ i, f i ≠ s) :
    Matched support (insert b D) := by
  classical
  let g : ↥(insert b D : Finset B) → S := fun j =>
    if h : j.val = b then s else f ⟨j.val, (Finset.mem_insert.mp j.property).resolve_left h⟩
  refine ⟨g, ?_, ?_⟩
  · intro j k he
    by_cases hj : j.val = b
    · by_cases hk : k.val = b
      · exact Subtype.ext (hj.trans hk.symm)
      · simp only [g, dite_eq_left hj, dite_eq_right hk] at he
        exact False.elim (hfree _ he.symm)
    · by_cases hk : k.val = b
      · simp only [g, dite_eq_right hj, dite_eq_left hk] at he
        exact False.elim (hfree _ he)
      · simp only [g, dite_eq_right hj, dite_eq_right hk] at he
        have he' : (⟨j.val, (Finset.mem_insert.mp j.property).resolve_left hj⟩ : D) =
            ⟨k.val, (Finset.mem_insert.mp k.property).resolve_left hk⟩ := hf he
        exact Subtype.ext (congrArg (fun t : D => t.val) he')
  · intro j
    by_cases hj : j.val = b
    · simpa only [g, dite_eq_left hj, hj] using hs
    · simpa only [g, dite_eq_right hj] using hi ⟨j.val, _⟩

/- 把一个块改派到空槽：仍是单射，且释放原来的槽。 -/
omit [Fintype S] [DecidableEq S] in
theorem swap_to_free {I : Type*} [DecidableEq I]
    (f : I → S) (hf : Function.Injective f) (i : I) (s : S) (hfree : ∀ j, f j ≠ s) :
    Function.Injective (Function.update f i s) ∧
      ∀ j, Function.update f i s j ≠ f i := by
  classical
  constructor
  · intro j k he
    by_cases hj : j = i
    · subst j
      by_cases hk : k = i
      · exact hk.symm
      · simp only [Function.update_self, Function.update_of_ne hk] at he
        exact False.elim (hfree k he.symm)
    · by_cases hk : k = i
      · subst k
        simp only [Function.update_of_ne hj, Function.update_self] at he
        exact False.elim (hfree j he)
      · simp only [Function.update_of_ne hj, Function.update_of_ne hk] at he
        exact hf he
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (hfree i).symm
    · simp only [Function.update_of_ne hj]
      exact fun he => hj (hf he)

def Searchable (support : B → Finset S) (D : Finset B) (f : D → S)
    (root : S) (T : Finset S) : Prop :=
  root ∈ T ∧ ∀ s ∈ T, ∃ g : D → S,
    Function.Injective g ∧ (∀ i, g i ∈ support i.val) ∧ (∀ i, g i ≠ s) ∧
      ∀ i, f i ∉ T → g i = f i

/- 最大可搜索集对交替搜索的一步转移封闭。 -/
omit [Fintype B] [Fintype S] in
theorem search_closed (support : B → Finset S) (D : Finset B) (f : D → S)
    (root : S) (T : Finset S) (hT : Searchable support D f root T)
    (hmax : ∀ U, Searchable support D f root U → U.card ≤ T.card)
    (s : S) (hs : s ∈ T) (i : D) (hsi : s ∈ support i.val) : f i ∈ T := by
  classical
  by_contra hnot
  obtain ⟨g, hg, hgi, hfree, hfix⟩ := hT.2 s hs
  have hgi_eq : g i = f i := hfix i hnot
  let U := insert (f i) T
  have hU : Searchable support D f root U := by
    refine ⟨Finset.mem_insert_of_mem hT.1, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with he | ht
    · subst t
      let g' := Function.update g i s
      obtain ⟨hginj, hgfree⟩ := swap_to_free g hg i s hfree
      refine ⟨g', hginj, ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst j; simpa only [g', Function.update_self] using hsi
        · simpa only [g', Function.update_of_ne hj] using hgi j
      · intro j
        simpa only [hgi_eq] using hgfree j
      · intro j hj
        have hjT : f j ∉ T := fun h => hj (Finset.mem_insert_of_mem h)
        have hji : j ≠ i := by
          intro he
          subst j
          exact hj (Finset.mem_insert_self _ _)
        simpa only [g', Function.update_of_ne hji] using hfix j hjT
    · obtain ⟨k, hk, hki, hkfree, hkfix⟩ := hT.2 t ht
      exact ⟨k, hk, hki, hkfree, fun j hj => hkfix j
        (fun h => hj (Finset.mem_insert_of_mem h))⟩
  have hc := hmax U hU
  have he : U.card = T.card + 1 := Finset.card_insert_of_notMem hnot
  omega

/-- 极小系统禁止的局部匹配是唯一语义输入；其余是初等图论。 -/
theorem full_matching_of_no_local_assignment
    (support : B → Finset S)
    (hfull : ∀ s, ∃ i, s ∈ support i)
    (hno : ∀ H : Finset B, H ≠ Finset.univ →
      ¬ ∃ g : {i : B // i ∉ H} → S, Function.Injective g ∧
        ∀ i, g i ∈ support i.val ∧ g i ∉ H.biUnion support) :
    ∃ f : S → B, Function.Injective f ∧ ∀ s, s ∈ support (f s) := by
  classical
  let candidates := (Finset.univ : Finset (Finset B)).filter (Matched support)
  have hne : candidates.Nonempty := ⟨∅,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, matched_empty support⟩⟩
  obtain ⟨D, hD, hmax⟩ := candidates.exists_max_image Finset.card hne
  obtain ⟨f, hf, hi⟩ := (Finset.mem_filter.mp hD).2
  have hmaxD : ∀ E, Matched support E → E.card ≤ D.card :=
    fun E hE => hmax E (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩)
  have hsurj : Function.Surjective f := by
    by_contra hn
    obtain ⟨root, hroot⟩ : ∃ root, ∀ i, f i ≠ root := by
      simpa only [Function.Surjective, not_forall, not_exists] using hn
    let searches := (Finset.univ : Finset (Finset S)).filter (Searchable support D f root)
    have hstart : Searchable support D f root {root} :=
      ⟨Finset.mem_singleton_self _, fun s hs => by
        have he := Finset.mem_singleton.mp hs
        subst s
        exact ⟨f, hf, hi, hroot, fun _ _ => rfl⟩⟩
    obtain ⟨T, hTmem, hTmax⟩ := searches.exists_max_image Finset.card
      ⟨{root}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstart⟩⟩
    have hT := (Finset.mem_filter.mp hTmem).2
    have hTmax' : ∀ U, Searchable support D f root U → U.card ≤ T.card :=
      fun U hU => hTmax U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)
    let N : Finset B := Finset.univ.filter (fun i => ∃ s ∈ T, s ∈ support i)
    have hND : N ⊆ D := by
      intro i hNi
      obtain ⟨s, hsT, hsi⟩ := (Finset.mem_filter.mp hNi).2
      by_contra hiD
      obtain ⟨g, hg, hgi, hgfree, _⟩ := hT.2 s hsT
      have hm := hmaxD (insert i D) (extend_matching support D g hg hgi i hiD s hsi hgfree)
      rw [Finset.card_insert_of_notMem hiD] at hm
      omega
    have hNF : ∀ i : N, f ⟨i.val, hND i.property⟩ ∈ T := by
      intro i
      obtain ⟨s, hsT, hsi⟩ := (Finset.mem_filter.mp i.property).2
      exact search_closed support D f root T hT hTmax' s hsT ⟨i.val, hND i.property⟩ hsi
    let H := Finset.univ \ N
    have hproper : H ≠ Finset.univ := by
      obtain ⟨i, hir⟩ := hfull root
      have hiN : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, root, hT.1, hir⟩
      intro he
      have hiH : i ∈ H := he.symm ▸ Finset.mem_univ i
      exact (Finset.mem_sdiff.mp hiH).2 hiN
    have hnN : ∀ i : {i : B // i ∉ H}, i.val ∈ N := by
      intro i
      by_contra hiN
      exact i.property (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiN⟩)
    let g : {i : B // i ∉ H} → S := fun i => f ⟨i.val, hND (hnN i)⟩
    apply hno H hproper
    refine ⟨g, ?_, ?_⟩
    · intro i j he
      have he' : (⟨i.val, hND (hnN i)⟩ : D) = ⟨j.val, hND (hnN j)⟩ := hf he
      exact Subtype.ext (congrArg (fun k : D => k.val) he')
    · intro i
      refine ⟨hi _, ?_⟩
      intro hs
      obtain ⟨j, hjH, hsj⟩ := Finset.mem_biUnion.mp hs
      have hjN : j ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        g i, hNF ⟨i.val, hnN i⟩, hsj⟩
      exact (Finset.mem_sdiff.mp hjH).2 hjN
  let e := Equiv.ofBijective f ⟨hf, hsurj⟩
  refine ⟨fun s => (e.symm s).val, ?_, ?_⟩
  · intro s t he
    exact e.symm.injective (Subtype.ext he)
  · intro s
    have hh := hi (e.symm s)
    simpa only [show f (e.symm s) = s from e.apply_symm_apply s] using hh

#print axioms full_matching_of_no_local_assignment
end ElementaryAlternating

