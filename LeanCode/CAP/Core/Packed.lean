module

/-!
# Packed natural numbers (`Init` only)

A vector `(x₀, …, xₙ₋₁)` of natural numbers below `2 ^ w` is stored as the single natural number
`∑ⱼ xⱼ * 2 ^ (w * j)`. The entries are the *slots*, and `w` is the *slot width*. Sums of packed
vectors and products with scalars are sums and products of natural numbers, as long as no slot
exceeds `2 ^ w`.

All definitions call the primitive operations on `Nat` explicitly, since these are the operations
that the Lean kernel evaluates with arbitrary-precision arithmetic. The Python module
`certgen/packed.py` contains the same functions.
-/

@[expose] public section

namespace CAP

/-- `2 ^ w - 1` -/
def mask (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

/-- Slot `j` of the packed vector `x` with slot width `w`. -/
def slot (w x j : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul w j)) (mask w)

/-- The packed vector `(1, …, 1)` of length `n`. -/
def ones (w n : Nat) : Nat := Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul w n)) 1) (mask w)

end CAP
