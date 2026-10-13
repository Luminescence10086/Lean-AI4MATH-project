import Mathlib

def MemAP {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) (m : ℤ) : Prop :=
  ∃ k : ℤ, m = a i + (d i : ℤ) * k
def lcmDiff {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ := Finset.univ.lcm d
def bound (n : ℕ) : ℕ := 1 + ∑ p ∈ n.primeFactors, n.factorization p * (p - 1)
def Essential {ι : Type*} (a : ι → ℤ) (d : ι → ℕ) (i : ι) : Prop :=
  ∃ m, MemAP a d i m ∧ ∀ j, j ≠ i → ¬ MemAP a d j m
def diffCount {ι : Type*} [Fintype ι] (d : ι → ℕ) (ν : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => d i = ν)).card

def lineCount {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (p : ℕ) (y : ℤ) (b : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => p ∣ d i ∧ (d i).factorization p = b ∧
    (d i / p ^ (d i).factorization p : ℤ) ∣ y - a i)).card

def overfullLayers {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : Finset ℕ :=
  ((Finset.univ.image d).filter (fun ν => p ∣ ν ∧ bound ν < diffCount d ν)).image
    (fun ν => ν.factorization p)

def lineScore {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (p : ℕ) (y : ℤ) : ℕ :=
  ∑ b ∈ Finset.range ((lcmDiff d).factorization p + 1),
    min (lineCount a d p y b) ((p - 1) * b + 1)

def saturatedLayers {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ)
    (p : ℕ) (y : ℤ) : Finset ℕ :=
  (overfullLayers d p).filter (fun b => (p - 1) * b + 1 ≤ lineCount a d p y b)

def deep_presence {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (p : ℕ) : Prop :=
  ∀ y : ℤ, (p - 1) * (lcmDiff d).factorization p + 1 ≤ lineScore a d p y →
    0 < lineCount a d p y ((lcmDiff d).factorization p)

def V_final {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (p : ℕ) : Prop :=
  ∀ y : ℤ, (p - 1) * (lcmDiff d).factorization p + 1 ≤ lineScore a d p y →
    (∑ b ∈ overfullLayers d p, b) < (lcmDiff d).factorization p →
    (saturatedLayers a d p y).card ≤ 1

def one_saturation {ι : Type*} [Fintype ι] (a : ι → ℤ) (d : ι → ℕ) (p : ℕ) : Prop :=
  ∀ y : ℤ, 0 < lineCount a d p y ((lcmDiff d).factorization p) →
    (∑ b ∈ overfullLayers d p, b) < (lcmDiff d).factorization p →
    (saturatedLayers a d p y).card ≤ 1

def Tpp_levels_falsified_record {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : Prop :=
  2 ≤ (overfullLayers d p).card →
    (lcmDiff d).factorization p ≤ ∑ b ∈ overfullLayers d p, b

def deep_saturation_candidate {ι : Type*} [Fintype ι] (d : ι → ℕ) (p : ℕ) : Prop :=
  2 ≤ (overfullLayers d p).card →
    (∀ ν ∈ (Finset.univ.image d), p ∣ ν → ν.factorization p = (lcmDiff d).factorization p →
      diffCount d ν ≤ bound ν) →
    (p - 1) * (lcmDiff d).factorization p + 1 ≤
      ∑ ν ∈ (Finset.univ.image d).filter (fun ν => ν.factorization p = (lcmDiff d).factorization p),
        min (diffCount d ν) ((p - 1) * (lcmDiff d).factorization p + 1)

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
