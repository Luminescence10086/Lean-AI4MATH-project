import Mathlib.Tactic
noncomputable section
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
