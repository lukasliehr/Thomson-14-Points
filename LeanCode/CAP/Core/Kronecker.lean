module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import CAP.Core.PackedLemmas

/-!
# Kronecker substitution

A polynomial `F` in three variables with natural coefficients is evaluated at the point
`(X, X ^ q, X ^ (q * q))` with `X = 2 ^ W`. If every exponent of `F` is below `q`, the value is
the packed number, with `q * (q * q)` slots of width `W`, whose slot at the position
`x + q * (y + q * z)` is the coefficient of `u ^ x * v ^ y * t ^ z` (`eval_kpt`). No bound on the
coefficients is needed for this equation; a bound is needed only when a slot is read.
-/

@[expose] public section

namespace CAP

open Finset MvPolynomial

/-- The exponent vector of `u ^ x * v ^ y * t ^ z`. -/
noncomputable def expo (x y z : ℕ) : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![x, y, z]

@[simp] theorem expo_zero (x y z : ℕ) : expo x y z 0 = x := by simp [expo]
@[simp] theorem expo_one (x y z : ℕ) : expo x y z 1 = y := by simp [expo]
@[simp] theorem expo_two (x y z : ℕ) : expo x y z 2 = z := by simp [expo]

theorem expo_eta (m : Fin 3 →₀ ℕ) : expo (m 0) (m 1) (m 2) = m := by
  ext i
  fin_cases i <;> simp

/-- The position of the monomial with the exponent vector `m`. -/
def pos (q : ℕ) (m : Fin 3 →₀ ℕ) : ℕ := m 0 + q * (m 1 + q * m 2)

/-- The exponent vector of the monomial at the position `p`. -/
noncomputable def unpos (q p : ℕ) : Fin 3 →₀ ℕ := expo (p % q) (p / q % q) (p / (q * q))

/-- The Kronecker point `(X, X ^ q, X ^ (q * q))` with `X = 2 ^ W`. -/
def kpt (W q : ℕ) : Fin 3 → ℕ := ![2 ^ W, 2 ^ (W * q), 2 ^ (W * (q * q))]

theorem digit_lt {q a B L : ℕ} (ha : a < q) (hB : B < L) : a + q * B < q * L := by
  calc a + q * B < q + q * B := by omega
    _ = q * (B + 1) := by ring
    _ ≤ q * L := Nat.mul_le_mul_left _ hB

theorem pos_lt {q : ℕ} {m : Fin 3 →₀ ℕ} (hm : ∀ i, m i < q) : pos q m < q * (q * q) :=
  digit_lt (hm 0) (digit_lt (hm 1) (hm 2))

theorem unpos_pos {q : ℕ} {m : Fin 3 →₀ ℕ} (hm : ∀ i, m i < q) : unpos q (pos q m) = m := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (hm 0)
  have h0 : pos q m % q = m 0 := by
    unfold pos
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hm 0)]
  have h1 : pos q m / q = m 1 + q * m 2 := by
    unfold pos
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (hm 0), zero_add]
  have h2 : pos q m / q % q = m 1 := by
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hm 1)]
  have h3 : pos q m / (q * q) = m 2 := by
    rw [← Nat.div_div_eq_div_mul, h1, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (hm 1), zero_add]
  unfold unpos
  rw [h0, h2, h3, expo_eta]

theorem pos_unpos (q p : ℕ) : pos q (unpos q p) = p := by
  unfold pos unpos
  rw [expo_zero, expo_one, expo_two, ← Nat.div_div_eq_div_mul, Nat.mod_add_div, Nat.mod_add_div]

theorem unpos_digits {q x y z : ℕ} (hx : x < q) (hy : y < q) (hz : z < q) :
    unpos q (x + q * (y + q * z)) = expo x y z := by
  have h := unpos_pos (q := q) (m := expo x y z) (by
    intro i
    fin_cases i <;> simpa)
  unfold pos at h
  rwa [expo_zero, expo_one, expo_two] at h

/-- The value of a monomial at the Kronecker point. -/
theorem prod_kpt (W q : ℕ) (m : Fin 3 →₀ ℕ) : ∏ i, kpt W q i ^ m i = 2 ^ (W * pos q m) := by
  rw [Fin.prod_univ_three]
  show (2 ^ W) ^ m 0 * (2 ^ (W * q)) ^ m 1 * (2 ^ (W * (q * q))) ^ m 2 = _
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  unfold pos
  ring

/-- **Kronecker substitution.** If every exponent of `F` is below `q`, the value of `F` at the
Kronecker point is the packed number of the coefficients of `F`. -/
theorem eval_kpt (W q : ℕ) (F : MvPolynomial (Fin 3) ℕ) (hF : ∀ m ∈ F.support, ∀ i, m i < q) :
    eval (kpt W q) F = packSum W (q * (q * q)) (fun p => coeff (unpos q p) F) := by
  rw [eval_eq']
  simp only [packSum]
  rw [← Finset.sum_filter_of_ne (p := fun p => unpos q p ∈ F.support)
    (fun p _ hp => mem_support_iff.mpr (fun h0 => hp (by rw [h0, zero_mul])))]
  refine Finset.sum_nbij' (pos q) (unpos q) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range, unpos_pos (hF m hm)]
    exact ⟨pos_lt (hF m hm), hm⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro m hm
    exact unpos_pos (hF m hm)
  · intro p _
    exact pos_unpos q p
  · intro m hm
    rw [unpos_pos (hF m hm), prod_kpt]

/-- Reading a coefficient: if every exponent of `F` is below `q` and every coefficient is below
`2 ^ W`, the slot of the value at the position of `u ^ x * v ^ y * t ^ z` is the coefficient. -/
theorem slot_eval_kpt (W q : ℕ) (F : MvPolynomial (Fin 3) ℕ) (hF : ∀ m ∈ F.support, ∀ i, m i < q)
    (hc : ∀ m, coeff m F < 2 ^ W) {x y z : ℕ} (hx : x < q) (hy : y < q) (hz : z < q) :
    slot W (eval (kpt W q) F) (x + q * (y + q * z)) = coeff (expo x y z) F := by
  rw [eval_kpt W q F hF, slot_packSum W _ _ (fun p _ => hc _) _ (digit_lt hx (digit_lt hy hz)),
    unpos_digits hx hy hz]

end CAP
