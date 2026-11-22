module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CAP.Core.PackedLemmas

/-!
# Products of packed numbers

The product of two packed numbers is the packed number of the convolution of their slots, as long
as no slot of the convolution exceeds `2 ^ w`. A checker reads a scalar product from one slot of
such a product: for vectors `f` and `g` with `n` slots the slot `n - 1` of
`packSum w n f * packSum w n g` is `∑ i < n, f i * g (n - 1 - i)` (`slot_mul_packSum`).

A packed number is the value of a polynomial at `2 ^ w`, so the statement is the formula for the
coefficients of a product of polynomials.
-/

@[expose] public section

namespace CAP

open Finset Polynomial

/-- The polynomial with the coefficients `f 0, …, f (n - 1)`. -/
noncomputable def packPoly (n : ℕ) (f : ℕ → ℕ) : ℕ[X] := ∑ i ∈ range n, C (f i) * X ^ i

theorem packPoly_eval (w n : ℕ) (f : ℕ → ℕ) : (packPoly n f).eval (2 ^ w) = packSum w n f := by
  simp [packPoly, packSum, eval_finsetSum, pow_mul]

theorem packPoly_coeff (n : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (packPoly n f).coeff k = if k < n then f k else 0 := by
  simp only [packPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (range n) k f]
  simp

theorem packPoly_natDegree_le (n : ℕ) (f : ℕ → ℕ) : (packPoly n f).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le (range n) _ fun i hi =>
    (natDegree_C_mul_X_pow_le (f i) i).trans (by have := mem_range.mp hi; omega)

/-- The slot `k` of the product of two packed numbers. -/
def convAt (n m : ℕ) (f g : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ range (k + 1), (if i < n then f i else 0) * (if k - i < m then g (k - i) else 0)

theorem coeff_packPoly_mul (n m : ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    (packPoly n f * packPoly m g).coeff k = convAt n m f g k := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_congr rfl fun i _ => by rw [packPoly_coeff, packPoly_coeff]

/-- The product of two packed numbers is the packed number of the convolution. -/
theorem packSum_mul_packSum (w n m : ℕ) (f g : ℕ → ℕ) (hn : 0 < n) (hm : 0 < m) :
    packSum w n f * packSum w m g = packSum w (n + m - 1) (convAt n m f g) := by
  have hdeg : (packPoly n f * packPoly m g).natDegree < n + m - 1 := by
    have h1 := packPoly_natDegree_le n f
    have h2 := packPoly_natDegree_le m g
    have h3 := natDegree_mul_le (p := packPoly n f) (q := packPoly m g)
    omega
  rw [← packPoly_eval, ← packPoly_eval, ← eval_mul, eval_eq_sum_range' hdeg]
  unfold packSum
  exact sum_congr rfl fun k _ => by rw [coeff_packPoly_mul, pow_mul]

/-- A slot of the convolution is below `n * B` if every product of two slots is below `B`. -/
theorem convAt_lt (n m : ℕ) (f g : ℕ → ℕ) (B : ℕ) (hn : 0 < n) (hB : 0 < B)
    (h : ∀ i j, i < n → j < m → f i * g j < B) (k : ℕ) : convAt n m f g k < n * B := by
  have hterm : ∀ i ∈ range (k + 1),
      (if i < n then f i else 0) * (if k - i < m then g (k - i) else 0) ≤ if i < n then B - 1 else 0 := by
    intro i _
    by_cases hi : i < n
    · by_cases hj : k - i < m
      · rw [if_pos hi, if_pos hj, if_pos hi]
        have := h i (k - i) hi hj
        omega
      · rw [if_neg hj, mul_zero]
        exact Nat.zero_le _
    · rw [if_neg hi, zero_mul, if_neg hi]
  have hcard : ((range (k + 1)).filter (· < n)).card ≤ n := by
    calc ((range (k + 1)).filter (· < n)).card ≤ (range n).card :=
          card_le_card fun i hi => mem_range.mpr (mem_filter.mp hi).2
      _ = n := card_range n
  calc convAt n m f g k ≤ ∑ i ∈ range (k + 1), (if i < n then B - 1 else 0) := sum_le_sum hterm
    _ = ((range (k + 1)).filter (· < n)).card * (B - 1) := by
        rw [← sum_filter, sum_const, smul_eq_mul]
    _ ≤ n * (B - 1) := Nat.mul_le_mul_right _ hcard
    _ < n * B := (Nat.mul_lt_mul_left hn).mpr (by omega)

/-- **A scalar product in one slot.** For vectors `f` and `g` with `n` slots whose products are
below `B`, with `n * B ≤ 2 ^ w`, the slot `n - 1` of the product of the packed numbers is
`∑ i < n, f i * g (n - 1 - i)`. -/
theorem slot_mul_packSum (w n : ℕ) (f g : ℕ → ℕ) (B : ℕ) (hn : 0 < n) (hB : 0 < B) (hBw : n * B ≤ 2 ^ w)
    (h : ∀ i j, i < n → j < n → f i * g j < B) :
    slot w (packSum w n f * packSum w n g) (n - 1) = ∑ i ∈ range n, f i * g (n - 1 - i) := by
  rw [packSum_mul_packSum w n n f g hn hn,
    slot_packSum w (n + n - 1) _ (fun k _ => (convAt_lt n n f g B hn hB h k).trans_le hBw) (n - 1) (by omega)]
  unfold convAt
  rw [Nat.sub_add_cancel hn]
  exact sum_congr rfl fun i hi => by
    have := mem_range.mp hi
    rw [if_pos this, if_pos (by omega)]

end CAP
