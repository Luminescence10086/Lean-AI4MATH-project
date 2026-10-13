import Mathlib

/-! # 极小整数 AP 覆盖的初等证明（2026-10-13）
独立新文件；原版和零告警版保持不变。
只复制 AP/lcm/素因子基础、CRT 位坐标桥与末步计数；
匹配存在性以有限最大化、单步改派、带证书的交替搜索和赋值反证证明。
不调用 Hall、严格亏格稳定性、Simpson 定理或旧主定理。
Searchable 记录可达槽的重排证书；最大 Searchable 集的封闭性替代显式路径列表。
它展开了增广的具体机制，没有引用增广路径存在性定理。
-/

namespace ElementaryAPProof


def MemAP {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) (m : ℤ) : Prop :=
  ∃ k : ℤ, m = a i + (d i : ℤ) * k


def lcmDiff {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ :=
  Finset.univ.lcm d


def bound (n : ℕ) : ℕ := 1 + ∑ p ∈ n.primeFactors, n.factorization p * (p - 1)


def Essential {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) : Prop :=
  ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m


theorem dvd_lcmDiff {ι : Type*} [Fintype ι] {d : ι → ℕ} (i : ι) : d i ∣ lcmDiff d :=
  Finset.dvd_lcm (Finset.mem_univ i)


theorem lcmDiff_pos {ι : Type*} [Fintype ι] {d : ι → ℕ} (hd : ∀ i, 0 < d i) :
    0 < lcmDiff d := by
  by_contra h0
  have h0' : lcmDiff d = 0 := Nat.le_zero.mp (Nat.not_lt.1 h0)
  obtain ⟨i, -, hi0⟩ := Finset.lcm_eq_zero_iff.1 h0'
  exact absurd hi0 (ne_of_gt (hd i))


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


theorem exists_of_prime_pow_dvd_lcmDiff {ι : Type*} [Fintype ι] {q : ℕ} (hq : q.Prime)
    (e : ℕ) (hne : Nonempty ι) (d : ι → ℕ) (h : q ^ e ∣ lcmDiff d) : ∃ i, q ^ e ∣ d i := by
  classical
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨Classical.arbitrary ι, Nat.one_dvd _⟩
  · obtain ⟨i, _, hi⟩ := exists_of_prime_pow_dvd_lcm_finset hq he Finset.univ d h
    exact ⟨i, hi⟩


def diffCount {ι : Type*} [Fintype ι] (d : ι → ℕ) (ν : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => d i = ν)).card


def sigma {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ :=
  (Finset.univ.image d).sum (fun ν => diffCount d ν - bound ν)


theorem diffCount_sum {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    (Finset.univ.image d).sum (diffCount d) = Fintype.card ι := by
  classical
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_image d Finset.univ).symm


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


namespace ElementaryMatching

variable {B S V : Type*} [Fintype B] [Fintype S] [DecidableEq V]

/-- 初等图论核心接入极小盒覆盖；余块也由未禁值赋值反证得到。 -/
theorem minimal_cover_matching
    (q : V → ℕ) (owner : S → V) (uses : B → Finset V)
    (value : (i : B) → (v : V) → Fin (q v))
    (hcapacity : ∀ v, (Finset.univ.filter (fun s => owner s = v)).card < q v)
    (hcover : ∀ x : (v : V) → Fin (q v), ∃ i, ∀ v ∈ uses i, x v = value i v)
    (hprivate : ∀ i, ∃ x : (v : V) → Fin (q v),
      ∀ j, j ≠ i → ∃ v ∈ uses j, x v ≠ value j v)
    (hfull : active (slotSupport owner uses) Finset.univ = Finset.univ) :
    ∃ f : S → B, Function.Injective f ∧
      (∀ s, owner s ∈ uses (f s)) ∧ ∃ anchor, ∀ s, f s ≠ anchor := by
  classical
  let support := slotSupport owner uses
  have allSlotsUsed : ∀ s, ∃ i, s ∈ support i := by
    intro s
    have hs : s ∈ active support Finset.univ := hfull.symm ▸ Finset.mem_univ s
    simpa only [active, Finset.mem_biUnion, Finset.mem_univ, true_and] using hs
  have hno : ∀ H : Finset B, H ≠ Finset.univ →
      ¬ ∃ g : {i : B // i ∉ H} → S, Function.Injective g ∧
        ∀ i, g i ∈ support i.val ∧ g i ∉ H.biUnion support := by
    intro H hH
    rintro ⟨g, hg, hi⟩
    exact local_assignment_contradiction q owner uses value hcapacity hcover hprivate H hH
      g hg hi
  obtain ⟨f, hf, hi⟩ := ElementaryAlternating.full_matching_of_no_local_assignment
    support allSlotsUsed hno
  have hempty : (∅ : Finset B) ≠ Finset.univ := by
    obtain ⟨i, _⟩ := hcover (fun v => ⟨0, lt_of_le_of_lt (Nat.zero_le _) (hcapacity v)⟩)
    intro he
    have : i ∈ (∅ : Finset B) := he.symm ▸ Finset.mem_univ i
    simp at this
  have hanchor : ∃ anchor, ∀ s, f s ≠ anchor := by
    by_contra hn
    have hsurj : Function.Surjective f := by
      simpa only [Function.Surjective, not_exists, not_forall, not_not] using hn
    let e := Equiv.ofBijective f ⟨hf, hsurj⟩
    apply hno ∅ hempty
    refine ⟨fun i => e.symm i.val, ?_, ?_⟩
    · intro i j he
      exact Subtype.ext (e.symm.injective he)
    · intro i
      refine ⟨?_, ?_⟩
      · have hh := hi (e.symm i.val)
        simpa only [show f (e.symm i.val) = i.val from e.apply_symm_apply i.val] using hh
      · rw [Finset.biUnion_empty]
        exact Finset.notMem_empty _
  exact ⟨f, hf, fun s => (Finset.mem_filter.mp (hi s)).2, hanchor⟩

#print axioms minimal_cover_matching
end ElementaryMatching


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


theorem finite_box_capacity_bound
    {B S V G : Type*} [Fintype B] [Fintype S] [DecidableEq V] [DecidableEq G]
    (q : V → ℕ) (owner : S → V) (group : B → G) (groupUses : G → Finset V)
    (value : (i : B) → (v : V) → Fin (q v))
    (hcapacity : ∀ v, (Finset.univ.filter (fun s => owner s = v)).card < q v)
    (hcover : ∀ x : (v : V) → Fin (q v),
      ∃ i, ∀ v ∈ groupUses (group i), x v = value i v)
    (hprivate : ∀ i, ∃ x : (v : V) → Fin (q v),
      ∀ j, j ≠ i → ∃ v ∈ groupUses (group j), x v ≠ value j v)
    (hfull : ElementaryMatching.active
      (ElementaryMatching.slotSupport owner (fun i => groupUses (group i)))
      Finset.univ = Finset.univ) :
    Fintype.card S + 1 ≤ ∑ ν ∈ Finset.univ.image group,
      min ((Finset.univ.filter (fun i => group i = ν)).card)
        ((ElementaryMatching.slotSupport owner groupUses ν).card + 1) := by
  classical
  obtain ⟨f, hf, hi, anchor, ha⟩ := ElementaryMatching.minimal_cover_matching
    q owner (fun i => groupUses (group i)) value hcapacity hcover hprivate hfull
  exact matching_capacity_bound group (ElementaryMatching.slotSupport owner groupUses)
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

#print axioms int_modEq_iff_prefix
#print axioms realize_coordinates

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
    (ElementaryMatching.slotSupport (fun s : Slots n => s.fst) (uses n) ν).card + 1 =
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
  have hfull : ElementaryMatching.active
      (ElementaryMatching.slotSupport (fun s : APDigitMatching.Slots n => s.fst)
        (fun i => APDigitMatching.uses n (d i))) Finset.univ = Finset.univ := by
    ext s
    simp only [ElementaryMatching.active, ElementaryMatching.slotSupport,
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


theorem truncated_sum_add_sigma {B : Type*} [Fintype B] (d : B → ℕ) :
    (∑ ν ∈ Finset.univ.image d, min (diffCount d ν) (bound ν)) + sigma d =
      Fintype.card B := by
  classical
  rw [sigma, ← Finset.sum_add_distrib, ← diffCount_sum d]
  apply Finset.sum_congr rfl
  intro ν _
  omega


theorem T23prime : ∀ n : ℕ, 0 < n → ∀ (ι : Type*) [Fintype ι] (a : ι → ℤ) (d : ι → ℕ),
    lcmDiff d = n → (∀ i, 0 < d i) → (∀ m : ℤ, ∃ i, MemAP a d i m) →
    (∀ i, Essential a d i) → Fintype.card ι ≥ bound n + sigma d := by
  intro n _ ι _ a d heq hd hcover hess
  have h := truncated_cover_bound a d hd hcover hess
  rw [heq] at h
  have hid := truncated_sum_add_sigma d
  omega


theorem card_ge_bound_of_allEssential {ι : Type*} [Fintype ι] {a : ι → ℤ} {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, Essential a d i) :
    Fintype.card ι ≥ bound (lcmDiff d) := by
  have h := T23prime (lcmDiff d) (lcmDiff_pos hd) ι a d rfl hd hcover hess
  omega


theorem problem7 {s : ℕ} (a : Fin s → ℤ) (d : Fin s → ℕ)
    (hd : ∀ i, 0 < d i) (hcover : ∀ m : ℤ, ∃ i, MemAP a d i m)
    (hess : ∀ i, ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m) :
    s ≥ bound (lcmDiff d) := by
  simpa only [Fintype.card_fin] using card_ge_bound_of_allEssential hd hcover hess


#print axioms truncated_cover_bound
#print axioms T23prime
#print axioms problem7

/-! 递归检查最终证明的实际常量依赖，而不只搜索本文件中的调用文本。
类型和 theorem/opaque 的证明体均递归展开；出现禁用工具立即报错。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut todo : List Name := [``ElementaryAPProof.problem7, ``ElementaryAPProof.T23prime]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then
      continue
    seen := seen.insert n
    let s := n.toString
    for token in ["HallMarriageTheorem", "all_card_le_biUnion_card", "strict_deficiency",
        "sorryAx", "Lean.ofReduceBool", "Simpson"] do
      if (s.splitOn token).length > 1 then
        throwError "禁用工具出现在最终证明依赖中：{n}"
    if let some info := env.find? n then
      for dep in info.type.getUsedConstants do
        todo := dep :: todo
      if let some value := info.value? (allowOpaque := true) then
        for dep in value.getUsedConstants do
          todo := dep :: todo
  logInfo m!"初等路线依赖审计通过：递归检查 {seen.size} 个常量，无 Hall、亏格稳定性、sorryAx 或原题文献定理。"

end ElementaryAPProof
