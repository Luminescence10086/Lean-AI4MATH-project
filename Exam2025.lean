import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# 2025 examinations: checked mathematical components

This file is an explicitly PARTIAL formalization of the accompanying PDF.
It contains no `sorry`, no new axioms, and no assumed version of an exam answer.
The section comments describe exactly which reductions are formalized.
Analytic/probabilistic bridges that are not formalized are listed in COVERAGE.md.
Compile from the supplied existing Mathlib project; see CHECK.ps1.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Exam2025
open scoped BigOperators

/-! ## Applied 1: Taylor coefficient algebra (not the Taylor remainder theorem). -/
def linearError (a : ℝ) : ℝ := 1 - a
def quadraticError (a b c₂ : ℝ) : ℝ := a * (1 - 2 * b) * c₂
def cubicError (a b c₂ c₃ : ℝ) : ℝ :=
  -a * ((2 - 8*b + 4*b^2)*c₂^2 + (-2 + 6*b - 3*b^2)*c₃)

theorem optimal_parameters (a b : ℝ) :
    (linearError a = 0 ∧ ∀ c₂, quadraticError a b c₂ = 0) ↔
    a = 1 ∧ b = 1/2 := by
  constructor
  · rintro ⟨ha, hb⟩
    have ha' : a = 1 := by unfold linearError at ha; linarith
    subst a
    have h := hb 1
    unfold quadraticError at h
    constructor
    · rfl
    · nlinarith
  · rintro ⟨rfl, rfl⟩
    constructor
    · norm_num [linearError]
    · intro c₂; norm_num [quadraticError]

theorem cubic_error_optimal (c₂ c₃ : ℝ) :
    cubicError 1 (1/2) c₂ c₃ = c₂^2 - c₃/4 := by
  unfold cubicError
  ring

theorem cubic_error_not_identically_zero : cubicError 1 (1/2) 1 0 = 1 := by
  norm_num [cubicError]

/-! ## Applied 2: exact path-matrix invertibility and characteristic polynomial.
The sine eigenbasis and the spectral-radius minimization are in the PDF only. -/
def path8 : Matrix (Fin 8) (Fin 8) ℝ :=
  !![0,1,0,0,0,0,0,0; 1,0,1,0,0,0,0,0; 0,1,0,1,0,0,0,0;
     0,0,1,0,1,0,0,0; 0,0,0,1,0,1,0,0; 0,0,0,0,1,0,1,0;
     0,0,0,0,0,1,0,1; 0,0,0,0,0,0,1,0]

def inverse8 : Matrix (Fin 8) (Fin 8) ℝ :=
  !![0,1,0,-1,0,1,0,-1; 1,0,0,0,0,0,0,0; 0,0,0,1,0,-1,0,1;
     -1,0,1,0,0,0,0,0; 0,0,0,0,0,1,0,-1; 1,0,-1,0,1,0,0,0;
     0,0,0,0,0,0,0,1; -1,0,1,0,-1,0,1,0]

theorem path8_inverse_left : inverse8 * path8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path8, inverse8, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem path8_inverse_right : path8 * inverse8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path8, inverse8, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

def continuant (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x
  | n+2 => x * continuant x (n+1) - continuant x n

theorem continuant_eight (x : ℝ) :
    continuant x 8 = x^8 - 7*x^6 + 15*x^4 - 10*x^2 + 1 := by
  simp only [continuant]
  ring

/-! ## Applied 3: the polynomial root-count step and positive diagonal system.
Legendre identities, weighted basis independence and L2 integration are not
asserted by these lemmas. -/
theorem interpolation_root_step {N : ℕ} (q : Polynomial ℝ)
    (x : Fin N → ℝ) (hx : Function.Injective x)
    (hd : q.natDegree < N) (hz : ∀ i, q.eval (x i) = 0) : q = 0 := by
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q hx hz
    (by simpa using hd)

def legendreWeight (k : ℕ) : ℝ := 2 * (k : ℝ) * (k+1) / (2*k+1)

theorem legendreWeight_pos (k : ℕ) (hk : 1 ≤ k) : 0 < legendreWeight k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold legendreWeight
  positivity

theorem diagonal_system_unique {N : ℕ} (w b a a' : Fin N → ℝ)
    (hw : ∀ k, w k ≠ 0) (ha : ∀ k, w k * a k = b k)
    (ha' : ∀ k, w k * a' k = b k) : a = a' := by
  funext k
  exact mul_left_cancel₀ (hw k) ((ha k).trans (ha' k).symm)

theorem diagonal_system_solution {N : ℕ} (w b : Fin N → ℝ)
    (hw : ∀ k, w k ≠ 0) : ∀ k, w k * (b k / w k) = b k := by
  intro k
  field_simp [hw k]

theorem odd_integral_cancellation (I : ℝ) (h : I = -I) : I = 0 := by
  linarith

/-! ## Applied 4: finite-dimensional spectral weight bound.
The PDF proves that orthonormal vectors give the weights in this lemma. -/
theorem spectral_weight_bound {N : ℕ} (s : Finset (Fin N))
    (lam weight : Fin N → ℝ) (cut : ℝ)
    (hw0 : ∀ i, 0 ≤ weight i) (hw1 : ∀ i, weight i ≤ 1)
    (hhi : ∀ i ∈ s, cut ≤ lam i)
    (hlo : ∀ i ∉ s, lam i ≤ cut)
    (hmass : ∑ i, weight i = s.card) :
    ∑ i, lam i * weight i ≤ ∑ i ∈ s, lam i := by
  classical
  have hpoint : ∀ i, (lam i - cut) * weight i ≤
      if i ∈ s then lam i - cut else 0 := by
    intro i
    split_ifs with hi
    · nlinarith [hhi i hi, hw1 i]
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hlo i hi)) (hw0 i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hr : (∑ i : Fin N, if i ∈ s then lam i - cut else 0) =
      ∑ i ∈ s, (lam i - cut) := by simp
  rw [hr] at hsum
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/-! ## Applied 5: exact scalar stability inequalities and norm induction.
The operator and Fourier/Plancherel bridges are in the PDF. -/
def thetaFactor (θ z : ℝ) : ℝ := (1-(1-θ)*z)/(1+θ*z)

theorem theta_stable_iff (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    |thetaFactor θ z| ≤ 1 ↔ (1-2*θ)*z ≤ 2 := by
  have hd : 0 < 1+θ*z := by positivity
  unfold thetaFactor
  rw [abs_le]
  constructor
  · intro h
    have hlow := (le_div_iff₀ hd).mp h.1
    nlinarith
  · intro h
    constructor
    · apply (le_div_iff₀ hd).mpr
      nlinarith
    · apply (div_le_iff₀ hd).mpr
      nlinarith

theorem theta_unconditional (θ z : ℝ) (hθ : 1/2 ≤ θ) (hz : 0 ≤ z) :
    |thetaFactor θ z| ≤ 1 := by
  apply (theta_stable_iff θ z (by linarith) hz).mpr
  have : (1-2*θ)*z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hz
  linarith

theorem positive_stencil (θ dt r : ℝ) (hθ : θ ≤ 1) (_hdt : 0 ≤ dt)
    (hr : 0 ≤ r) (hc : (1-θ)*(dt+4*r) ≤ 1) :
    0 ≤ 1-(1-θ)*(dt+2*r) ∧
    (1-(1-θ)*(dt+2*r)) + 2*((1-θ)*r) = 1-(1-θ)*dt := by
  constructor
  · have : 0 ≤ (1-θ)*r := mul_nonneg (by linarith) hr
    nlinarith
  · ring

theorem geometric_norm_bound (u : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ m, u (m+1) ≤ q*u m) : ∀ m, u m ≤ q^m*u 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      u (m+1) ≤ q*u m := hstep m
      _ ≤ q*(q^m*u 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q^(m+1)*u 0 := by ring

/-! ## Applied 6: exact solution, scalar factors and modal recurrences. -/
def exactY₁ (t : ℝ) : ℝ := Real.exp (-t) + Real.exp (-1000*t)
def exactY₂ (t : ℝ) : ℝ := Real.exp (-t)

theorem exact_initial : exactY₁ 0 = 2 ∧ exactY₂ 0 = 1 := by
  norm_num [exactY₁, exactY₂]

theorem exact_ode_first (t : ℝ) :
    HasDerivAt exactY₁ (-1000*exactY₁ t + 999*exactY₂ t) t := by
  have h₁ : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
    convert ((hasDerivAt_id t).neg.exp) using 1 <;> simp
  have h₂ : HasDerivAt (fun x : ℝ => Real.exp (-1000*x))
      (-1000*Real.exp (-1000*t)) t := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using
      ((hasDerivAt_id t).const_mul (-1000)).exp
  have hh := h₁.add h₂
  have he : -Real.exp (-t) + -1000 * Real.exp (-1000*t) =
      -1000*exactY₁ t + 999*exactY₂ t := by
    dsimp [exactY₁, exactY₂]
    ring
  rw [he] at hh
  exact hh

theorem exact_ode_second (t : ℝ) : HasDerivAt exactY₂ (-exactY₂ t) t := by
  change HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t
  simpa using ((hasDerivAt_id t).neg.exp)

theorem explicit_stability (h : ℝ) (hh : 0 < h) :
    |1-1000*h| ≤ 1 ↔ h ≤ 1/500 := by
  rw [abs_le]
  constructor <;> intro hs
  · linarith [hs.1]
  · constructor <;> linarith

theorem explicit_unstable (h : ℝ) (hh : 1/500 < h) : 1 < |1-1000*h| := by
  rw [abs_of_neg (by linarith)]
  linarith

theorem implicit_decay (z : ℝ) (hz : 0 < z) : 0 < 1/(1+z) ∧ 1/(1+z) < 1 := by
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 1+z)).mpr
    linarith

theorem trapezoidal_decay (z : ℝ) (hz : 0 < z) :
    |(1-z/2)/(1+z/2)| < 1 := by
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 1+z/2)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity : 0 < 1+z/2)).mpr
    linarith

theorem explicit_modes (h : ℝ) (m : ℕ) :
    ((1-h)^(m+1)+(1-1000*h)^(m+1)) =
      ((1-h)^m+(1-1000*h)^m) +
      h*(-1000*((1-h)^m+(1-1000*h)^m)+999*(1-h)^m) := by
  simp only [pow_succ]
  ring

/-! ## Statistics 1: interval geometry and obstruction to fixed expected length.
Normal CDF integration is given in the PDF. -/
def inCI (x μ c₁ c₂ : ℝ) : Prop :=
  (0 < x ∧ c₁*x ≤ μ ∧ μ ≤ c₂*x) ∨
  (x < 0 ∧ c₂*x ≤ μ ∧ μ ≤ c₁*x)

theorem ci_reflection (x μ c₁ c₂ : ℝ) :
    inCI (-x) (-μ) c₁ c₂ ↔ inCI x μ c₁ c₂ := by
  unfold inCI
  constructor
  · rintro (h | h)
    · right; constructor
      · linarith [h.1]
      · constructor <;> nlinarith [h.2.1, h.2.2]
    · left; constructor
      · linarith [h.1]
      · constructor <;> nlinarith [h.2.1, h.2.2]
  · rintro (h | h)
    · right; constructor
      · linarith [h.1]
      · constructor <;> nlinarith [h.2.1, h.2.2]
    · left; constructor
      · linarith [h.1]
      · constructor <;> nlinarith [h.2.1, h.2.2]

theorem ci_at_zero (x c₁ c₂ : ℝ) (hx : x ≠ 0) :
    inCI x 0 c₁ c₂ ↔ c₁ ≤ 0 ∧ 0 ≤ c₂ := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · simp only [inCI, not_lt_of_gt hx, false_and, false_or, hx, true_and]
    constructor
    · rintro ⟨h₂, h₁⟩
      constructor <;> nlinarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> nlinarith
  · simp only [inCI, hx, true_and, not_lt_of_gt hx, false_and, or_false]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> nlinarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> nlinarith

theorem no_constant_expected_length (a : ℝ) :
    ¬ ∃ L : ℝ, L*a = 2 ∧ L*(2*a) = 2 := by
  rintro ⟨L, h₁, h₂⟩
  nlinarith

/-! ## Statistics 2: two injective rules confined to opposite halves of [0,1].
Integration against the observation mixture is not formalized here. -/
def ruleLow (r : ℝ) : ℝ := 1/4 + Real.arctan r / (2*Real.pi)
def ruleHigh (r : ℝ) : ℝ := 3/4 + Real.arctan r / (2*Real.pi)

theorem ruleLow_bounds (r : ℝ) : 0 < ruleLow r ∧ ruleLow r < 1/2 := by
  have hp := Real.pi_pos
  have hl := Real.neg_pi_div_two_lt_arctan r
  have hu := Real.arctan_lt_pi_div_two r
  have hd : 0 < 2*Real.pi := by positivity
  have h₁ : -(1/4 : ℝ) < Real.arctan r / (2*Real.pi) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have h₂ : Real.arctan r / (2*Real.pi) < (1/4 : ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  unfold ruleLow
  constructor <;> linarith

theorem ruleHigh_bounds (r : ℝ) : 1/2 < ruleHigh r ∧ ruleHigh r < 1 := by
  have h := ruleLow_bounds r
  dsimp [ruleLow, ruleHigh] at *
  constructor <;> linarith

theorem ruleLow_injective : Function.Injective ruleLow := by
  intro x y h
  unfold ruleLow at h
  have h' : Real.arctan x = Real.arctan y := by
    have := add_left_cancel h
    exact (div_left_inj' (by positivity : (2:ℝ)*Real.pi ≠ 0)).mp this
  have := congrArg Real.tan h'
  simpa only [Real.tan_arctan] using this

theorem ruleHigh_injective : Function.Injective ruleHigh := by
  intro x y h
  apply ruleLow_injective
  dsimp [ruleHigh] at h
  dsimp [ruleLow]
  linarith

/-! ## Statistics 3: the two-point cyclic construction and recurrence algebra.
`lowFace` and `highFace` are the actual face locations.  For interior pairs
the only losing outcome is high followed by low.  The later DiceParameters and FiniteProduct namespaces verify the parameters
and finite product normalization/rectangle independence. Their assembly into
one cyclic random-variable existence theorem remains unformalized. -/
def lowFace (n i : ℕ) : ℝ := (i : ℝ) - n
def highFace (i : ℕ) : ℝ := i
def face (n i : ℕ) (high : Bool) : ℝ := if high then highFace i else lowFace n i

theorem cyclic_face_order (n i : ℕ) (hi : 1 ≤ i) (hin : i+1 < n)
    (b c : Bool) :
    face n i b < face n (i+1) c ↔ ¬ (b = true ∧ c = false) := by
  have hn : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  cases b <;> cases c <;>
    simp [face, lowFace, highFace, Nat.cast_add, Nat.cast_one] <;> linarith

theorem first_face_order (n : ℕ) (hn : 2 ≤ n) (b : Bool) :
    0 < face n 1 b ↔ b = true := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  cases b <;> simp [face, lowFace, highFace]
  all_goals linarith

theorem last_face_order (n : ℕ) (hn : 2 ≤ n) (b : Bool) :
    face n (n-1) b < 0 ↔ b = false := by
  have he : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  cases b <;> simp [face, lowFace, highFace, he]
  all_goals linarith

theorem interior_win_mass (a b q : ℝ) (h : (1-a)*b = q) :
    a*b + a*(1-b) + (1-a)*(1-b) = 1-q := by nlinarith

theorem recurrence_step (q a : ℝ) (ha : a ≠ 1) :
    (1-a)*(q/(1-a)) = q := by
  have h : 1-a ≠ 0 := by intro he; apply ha; linarith
  field_simp

theorem sine_recurrence (t u : ℝ) :
    2*Real.cos t*Real.sin (u+t)-Real.sin u = Real.sin (u+2*t) := by
  have hc := Real.sin_sq_add_cos_sq t
  rw [show u+2*t = (u+t)+t by ring]
  simp only [Real.sin_add, Real.cos_add]
  nlinarith [congrArg (fun x : ℝ => Real.sin u * x) hc]

/-! ## Statistics 4: explicit smooth-score counterexample's exact algebra.
The PDF verifies the C1 joins, derivative and positive-probability bad event. -/
def bumpScore (x : ℝ) : ℝ :=
  if |x| ≤ 1 then 1 - (3/2)*(1-x^2)^2 else 1

theorem bumpScore_lower (x : ℝ) : -(1/2 : ℝ) ≤ bumpScore x := by
  unfold bumpScore
  split_ifs with h
  · have hx := abs_le.mp h
    have hs : 0 ≤ x^2 := sq_nonneg x
    have hs' : x^2 ≤ 1 := by nlinarith [sq_nonneg (x-1), sq_nonneg (x+1)]
    have ht : (1-x^2)^2 ≤ 1 := by nlinarith [sq_nonneg (x^2)]
    nlinarith
  · norm_num

theorem bumpScore_upper (x : ℝ) : bumpScore x ≤ 1 := by
  unfold bumpScore
  split_ifs <;> nlinarith [sq_nonneg (1-x^2)]

theorem bumpScore_values : bumpScore (1/4) = -163/512 ∧ bumpScore 3 = 1 := by
  norm_num [bumpScore]

theorem bumpScore_mean_zero :
    (512/675 : ℝ)*bumpScore (1/4)+(163/675)*bumpScore 3 = 0 := by
  rw [bumpScore_values.1, bumpScore_values.2]
  norm_num

theorem bumpScore_mean_derivative : (512/675 : ℝ)*(45/32)+(163/675)*0 = 16/15 := by
  norm_num

theorem bumpScore_pair_positive (b : ℝ) :
    0 < bumpScore (1/4-b)+bumpScore (3-b) := by
  have h₁ := bumpScore_lower (1/4-b)
  have h₂ := bumpScore_lower (3-b)
  by_cases h : |1/4-b| ≤ 1
  · have hb := abs_le.mp h
    have h' : ¬ |3-b| ≤ 1 := by
      intro hh
      have hb' := abs_le.mp hh
      linarith
    have he : bumpScore (3-b) = 1 := by simp [bumpScore, h']
    rw [he]
    linarith
  · have he : bumpScore (1/4-b) = 1 := by simp only [bumpScore, ite_eq_right h]
    rw [he]
    linarith

theorem bumpScore_pair_no_root :
    ¬ ∃ b : ℝ, bumpScore (1/4-b)+bumpScore (3-b) = 0 := by
  rintro ⟨b, hb⟩
  have := bumpScore_pair_positive b
  linarith

theorem union_tail_algebra (p n B t : ℝ) (hp : 0 ≤ p)
    (h : Real.exp (-B*t) ≤ 1/n) :
    2*p*Real.exp (-B*t) ≤ 2*p/n := by
  have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*p)
  simpa only [mul_one_div] using this

end Exam2025


namespace DiceParameters
open Real

def angle (n : ℕ) : ℝ := Real.pi / ((n : ℝ)+2)
def q (n : ℕ) : ℝ := 1 / (4 * Real.cos (angle n)^2)
def a (n i : ℕ) : ℝ :=
  Real.sin ((i : ℝ)*angle n) /
    (2*Real.cos (angle n)*Real.sin (((i : ℝ)+1)*angle n))

theorem angle_pos (n : ℕ) : 0 < angle n := by
  unfold angle
  positivity

theorem angle_product (n : ℕ) : ((n : ℝ)+2)*angle n = Real.pi := by
  unfold angle
  field_simp

theorem angle_small (n : ℕ) (hn : 2 ≤ n) : angle n < Real.pi/2 := by
  have h := angle_product n
  have hp := angle_pos n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem cos_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Real.cos (angle n) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have := angle_pos n; have := Real.pi_pos; linarith
  · exact angle_small n hn

theorem sine_pos (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n+1) :
    0 < Real.sin ((k : ℝ)*angle n) := by
  have hp := angle_pos n
  have he := angle_product n
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n+1 := by exact_mod_cast hkn
  apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith

theorem sine_step (t u : ℝ) :
    2*Real.cos t*Real.sin (u+t)-Real.sin u = Real.sin (u+2*t) := by
  have hc := Real.sin_sq_add_cos_sq t
  rw [show u+2*t = (u+t)+t by ring]
  simp only [Real.sin_add, Real.cos_add]
  nlinarith [congrArg (fun x : ℝ => Real.sin u*x) hc]

theorem complement (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n-1) :
    1-a n i = Real.sin (((i : ℝ)+2)*angle n) /
      (2*Real.cos (angle n)*Real.sin (((i : ℝ)+1)*angle n)) := by
  have hc := cos_pos n hn
  have hs := sine_pos n (i+1) (by omega) (by omega)
  have hs' : Real.sin (((i : ℝ)+1)*angle n) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ne_of_gt hs
  have he := sine_step (angle n) ((i : ℝ)*angle n)
  rw [show (i : ℝ)*angle n + angle n = ((i : ℝ)+1)*angle n by ring,
      show (i : ℝ)*angle n + 2*angle n = ((i : ℝ)+2)*angle n by ring] at he
  unfold a
  have hd : 2*Real.cos (angle n)*Real.sin (((i : ℝ)+1)*angle n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hc)) hs'
  apply (eq_div_iff hd).mpr
  rw [sub_mul, div_mul_cancel₀ _ hd, one_mul]
  exact he

theorem a_bounds (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n-1) :
    0 < a n i ∧ a n i < 1 := by
  have hc := cos_pos n hn
  have hs := sine_pos n i hi (by omega)
  have hs₁ := sine_pos n (i+1) (by omega) (by omega)
  have hs₂ := sine_pos n (i+2) (by omega) (by omega)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hs₁ hs₂
  constructor
  · unfold a
    positivity
  · have he := complement n i hn hi hin
    have : 0 < 1-a n i := by rw [he]; positivity
    linarith

theorem a_first (n : ℕ) (hn : 2 ≤ n) : a n 1 = q n := by
  have hc : Real.cos (angle n) ≠ 0 := ne_of_gt (cos_pos n hn)
  have hs : Real.sin (angle n) ≠ 0 := by
    simpa using ne_of_gt (sine_pos n 1 (by omega) (by omega))
  unfold a q
  norm_num only [Nat.cast_one, one_mul, show (1 : ℝ)+1 = 2 by norm_num]
  rw [Real.sin_two_mul]
  field_simp [hc, hs]
  ring

theorem a_recurrence (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i)
    (hin : i+1 ≤ n-1) : (1-a n i)*a n (i+1) = q n := by
  have hc : Real.cos (angle n) ≠ 0 := ne_of_gt (cos_pos n hn)
  have h₁ := sine_pos n (i+1) (by omega) (by omega)
  have h₂ := sine_pos n (i+2) (by omega) (by omega)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h₁ h₂
  rw [complement n i hn hi (by omega)]
  unfold a q
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (i : ℝ)+1+1 = (i : ℝ)+2 by ring]
  generalize Real.sin (((i : ℝ)+1)*angle n) = x at *
  generalize Real.sin (((i : ℝ)+2)*angle n) = y at *
  generalize Real.cos (angle n) = c at *
  field_simp [hc, ne_of_gt h₁, ne_of_gt h₂]
  ring

theorem a_last (n : ℕ) (hn : 2 ≤ n) : a n (n-1) = 1-q n := by
  have he := complement n (n-1) hn (by omega) (by omega)
  have hn' : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hn'] at he
  have prod := angle_product n
  have h₁ : ((n : ℝ)-1+2)*angle n = Real.pi-angle n := by nlinarith
  have h₂ : ((n : ℝ)-1+1)*angle n = Real.pi-2*angle n := by nlinarith
  rw [h₁, h₂, Real.sin_pi_sub, Real.sin_pi_sub] at he
  have hf := a_first n hn
  unfold a at hf
  norm_num only [Nat.cast_one, one_mul, show (1 : ℝ)+1 = 2 by norm_num] at hf
  rw [hf] at he
  linarith

/-- All parameters needed by the explicit finite independent construction. -/
theorem construction_parameters (n : ℕ) (hn : 2 ≤ n) :
    (∀ i, 1 ≤ i → i ≤ n-1 → 0 < a n i ∧ a n i < 1) ∧
    a n 1 = q n ∧ a n (n-1) = 1-q n ∧
    (∀ i, 1 ≤ i → i+1 ≤ n-1 → (1-a n i)*a n (i+1) = q n) := by
  exact ⟨fun i hi hin => a_bounds n i hn hi hin,
    a_first n hn, a_last n hn, fun i hi hin => a_recurrence n i hn hi hin⟩
end DiceParameters


namespace FiniteProduct
open scoped BigOperators

def bernoulliWeight (a : ℝ) (b : Bool) : ℝ := if b then 1-a else a

theorem bernoulliWeight_nonneg (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight a b := by
  cases b <;> simp [bernoulliWeight] <;> linarith

theorem bernoulliWeight_sum (a : ℝ) : ∑ b : Bool, bernoulliWeight a b = 1 := by
  simp [bernoulliWeight]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (w : ι → Bool → ℝ) (ω : ι → Bool) : ℝ := ∏ i, w i (ω i)

omit [DecidableEq ι] in
theorem mass_nonneg (w : ι → Bool → ℝ) (h : ∀ i b, 0 ≤ w i b) (ω : ι → Bool) :
    0 ≤ mass w ω := by
  exact Finset.prod_nonneg (fun i _ => h i (ω i))

theorem total_mass_one (w : ι → Bool → ℝ) (h : ∀ i, ∑ b, w i b = 1) :
    ∑ ω : ι → Bool, mass w ω = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp only [h, Finset.prod_const_one]

/-- Rectangle factorization: the finite-probability definition of independence. -/
theorem rectangle_mass (w : ι → Bool → ℝ) (E : ι → Bool → Prop)
    [∀ i b, Decidable (E i b)] :
    (∑ ω : ι → Bool, if ∀ i, E i (ω i) then mass w ω else 0) =
      ∏ i, ∑ b : Bool, if E i b then w i b else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ∀ i, E i (ω i)
  · rw [ite_eq_left h]
    unfold mass
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (h i)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hi]

/-- The independent Bernoulli product has nonnegative masses summing to one. -/
theorem bernoulli_product (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    (∀ ω : ι → Bool, 0 ≤ mass (fun i => bernoulliWeight (a i)) ω) ∧
    (∑ ω : ι → Bool, mass (fun i => bernoulliWeight (a i)) ω) = 1 := by
  constructor
  · exact mass_nonneg _ (fun i b => bernoulliWeight_nonneg _ (ha i).1 (ha i).2 b)
  · exact total_mass_one _ (fun i => bernoulliWeight_sum (a i))

end FiniteProduct
