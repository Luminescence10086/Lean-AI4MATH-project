import Mathlib

/-! ## 探针 _gap2_probe：缺口 2 —— 纤维非本质块计数引理 -/

/-- 第 i 个等差数列是否包含整数 m：m = aᵢ + dᵢ·k（k ∈ ℤ） -/
def MemAP {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) (m : ℤ) : Prop :=
  ∃ k : ℤ, m = a i + (d i : ℤ) * k

/-- s 个公差的最小公倍数 n -/
def lcmDiff {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ :=
  Finset.univ.lcm d

/-- 条件(2)的提纯形式：P_i 含独占数 -/
def Essential {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) : Prop :=
  ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m

theorem dvd_lcmDiff {ι : Type*} [Fintype ι] {d : ι → ℕ} (i : ι) : d i ∣ lcmDiff d :=
  Finset.dvd_lcm (Finset.mem_univ i)

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

open Classical in
/-- 【拆n·路2】冗余度 ρ：无私有点（非本质）的块数。独占族上 ρ = 0。 -/
noncomputable def rho {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) : ℕ :=
  Fintype.card {i : ι // ¬ Essential a d i}

open Classical in
/-- rho 的改写引理（固定与定义相同的 Classical 可判定性实例） -/
theorem rho_def' {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) :
    rho a d = Fintype.card {i : ι // ¬ Essential a d i} := rfl

open Classical in
/-- 【缺口 2】hpd 下每块恰居一纤维，原独占 ⇒ 纤维独占，
故各纤维非本质块数之和 ≤ 原族非本质块数。 -/
theorem sum_rho_le {ι : Type*} [Fintype ι] {p k : ℕ} (hp : p.Prime)
    {a : ι → ℤ} {d : ι → ℕ} (hpd : ∀ i, p ∣ d i) (hess : ∀ i, Essential a d i) :
    ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) ≤ rho a d := by
  classical
  -- 纤维两两不交：p ∣ c₁ − c₂ ⇒ c₁ = c₂
  have key : ∀ x y : Fin p, (p : ℤ) ∣ ((x : ℕ) : ℤ) - ((y : ℕ) : ℤ) → x = y := by
    intro x y h
    have hx0 : 0 ≤ ((x : ℕ) : ℤ) := Nat.cast_nonneg _
    have hy0 : 0 ≤ ((y : ℕ) : ℤ) := Nat.cast_nonneg _
    have hx : ((x : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast x.isLt
    have hy : ((y : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast y.isLt
    rcases le_or_gt ((x : ℕ) : ℤ) ((y : ℕ) : ℤ) with hle | hlt
    · have hd : (p : ℤ) ∣ ((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) := by
        obtain ⟨q, hq⟩ := h
        refine ⟨-q, ?_⟩
        linarith
      have h0 : ((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith) (by linarith) hd
      exact Fin.val_injective (by omega)
    · have h0 : ((x : ℕ) : ℤ) - ((y : ℕ) : ℤ) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith) (by linarith) h
      exact Fin.val_injective (by omega)
  -- 单射：Σ_c {纤维内非本质块} → {原族非本质块}
  have hinj : Function.Injective
      (fun x : Σ c : Fin p, {i : Fiber p a ((c:ℕ):ℤ) // ¬ Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i} =>
        (⟨x.2.1.val, fun _ => x.2.2 (fiber_essential hp hpd ((x.1 : ℕ) : ℤ) hess x.2.1)⟩ :
          {i : ι // ¬ Essential a d i})) := by
    rintro ⟨c₁, j₁, hE₁⟩ ⟨c₂, j₂, hE₂⟩ hxy
    have hv : j₁.val = j₂.val := congrArg Subtype.val hxy
    have h1 : (p : ℤ) ∣ a j₁.val - ((c₁ : ℕ) : ℤ) := j₁.2
    have h2 : (p : ℤ) ∣ a j₂.val - ((c₂ : ℕ) : ℤ) := j₂.2
    rw [← hv] at h2
    obtain ⟨q, hq⟩ := dvd_sub h2 h1
    have hc : c₁ = c₂ := key c₁ c₂ ⟨q, by linarith⟩
    subst hc
    exact congrArg (Sigma.mk c₁) (Subtype.ext (Subtype.ext hv))
  -- 计数：Σ_c ρ_c = card(Σ_c S_c) ≤ card{原非本质} = ρ
  calc ∑ c : Fin p, rho (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d)
      = Fintype.card (Σ c : Fin p, {i : Fiber p a ((c:ℕ):ℤ) // ¬ Essential (fibA p a ((c:ℕ):ℤ)) (fibD p a ((c:ℕ):ℤ) d) i}) := by
        rw [Fintype.card_sigma]
        exact Finset.sum_congr rfl fun c _ => rho_def' _ _
    _ ≤ Fintype.card {i : ι // ¬ Essential a d i} := Fintype.card_le_of_injective _ hinj
    _ = rho a d := (rho_def' a d).symm
