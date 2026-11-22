module

public import CAP.Core.PackedLemmas

/-!
# Triangular arrays as packed numbers

The upper triangle of a matrix of order `n` is stored row by row in one natural number: row `i`
has the `n - i` slots of the entries `(i, j)`, `j = i, …, n - 1`. Row `i` therefore starts
`triOff n i` slots after the beginning. Both the checker of E2 and the checkers of the schemas
read their matrices in this layout, so that the same number is the matrix in all statements.
-/

@[expose] public section

namespace CAP

open Finset

/-- The number of slots before row `i` of a triangular array of order `n`. -/
def triOff (n i : ℕ) : ℕ := ∑ t ∈ range i, (n - t)

theorem triOff_zero (n : ℕ) : triOff n 0 = 0 := by simp [triOff]

theorem triOff_succ (n i : ℕ) : triOff n (i + 1) = triOff n i + (n - i) := sum_range_succ _ _

/-- Row `i` of a triangular array stored in `x`: a packed vector with `n - i` slots. -/
def triRow (w n x i : ℕ) : ℕ := x / 2 ^ (w * triOff n i) % 2 ^ (w * (n - i))

/-- Slot `s` of row `i` of a triangular array stored in `x`: the entry `(i, i + s)`. -/
def triEnt (w n x i s : ℕ) : ℕ := slot w x (triOff n i + s)

theorem triEnt_lt (w n x i s : ℕ) : triEnt w n x i s < 2 ^ w := slot_lt _ _ _

theorem triRow_eq (w n x i : ℕ) : triRow w n x i = packSum w (n - i) (triEnt w n x i) := by
  have h : triRow w n x i < 2 ^ (w * (n - i)) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h1 := packSum_slot w (n - i) (triRow w n x i) h
  rw [← h1]
  refine packSum_congr _ _ fun s hs => ?_
  unfold triRow triEnt
  rw [slot_mod _ _ _ _ hs, slot_div]

/-- The remaining rows after row `i`. -/
theorem triRow_rest (w n x i : ℕ) :
    x / 2 ^ (w * triOff n i) / 2 ^ (w * (n - i)) = x / 2 ^ (w * triOff n (i + 1)) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, ← mul_add, ← triOff_succ]

end CAP
