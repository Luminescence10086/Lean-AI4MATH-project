import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic
noncomputable section
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
  <;> ring

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
