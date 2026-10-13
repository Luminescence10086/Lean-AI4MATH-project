import Mathlib

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
