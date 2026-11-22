module

public import N14.Box.Kernel

/-!
# T7, a polynomial constraint that is given by its terms: the checker (`Init` only)

A run has polynomial constraints `g ≥ 0` (`Run.polys`): an excluded ball, the ellipsoid of a local region, the
tube of a node. The number of a constraint holds the biased coefficients of `-2 ^ sg * g`. This file states
which polynomial a number stands for: for a list of terms `(e₁, e₂, e₃, p, q)`, the term `(p - q) x₁^e₁ x₂^e₂
x₃^e₃` of `2 ^ sg * g`, the number is `quadPp R l`, formed as the generator forms it (the bias of every slot, plus
`q` and minus `p` at the place of the term). `quadOk R l Pp` tests that `Pp` is this number, that the terms have
distinct places, and that no slot overflows (`p ≤ bias` and `bias + q < 2 ^ V` for every term). The soundness
theorem is `N14.Box.polyVal_quad`.

The checker is bit-exact with `quad_ok` of `N14/py/boxref.py`.
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein

/-- A term of a polynomial constraint: the exponents of the three coordinates and the two parts `p`, `q` of its
coefficient `p - q`. -/
structure QTerm where
  e1 : Nat
  e2 : Nat
  e3 : Nat
  p : Nat
  q : Nat

/-- The sum over the terms of `p` times the unit of the place of the term. -/
noncomputable def qPos (R : Run) : List QTerm → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => Nat.add (Nat.mul t.p (unit3 R t.e1 t.e2 t.e3)) ih)

/-- The sum over the terms of `q` times the unit of the place of the term. -/
noncomputable def qNeg (R : Run) : List QTerm → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => Nat.add (Nat.mul t.q (unit3 R t.e1 t.e2 t.e3)) ih)

/-- The place of a term in the array of the coefficients. -/
noncomputable def qIdx (n : Nat) (t : QTerm) : Nat :=
  Nat.add t.e1 (Nat.mul (Nat.succ n) (Nat.add t.e2 (Nat.mul (Nat.succ n) t.e3)))

/-- No term of the list has the place `i`. -/
noncomputable def qNotIn (n i : Nat) : List QTerm → Bool :=
  List.rec (motive := fun _ => Bool) true (fun t _ ih => !(Nat.beq (qIdx n t) i) && ih)

/-- The places of the terms are distinct. -/
noncomputable def qDistinct (n : Nat) : List QTerm → Bool :=
  List.rec (motive := fun _ => Bool) true (fun t l ih => qNotIn n (qIdx n t) l && ih)

/-- Both parts of every coefficient fit their slot: `p ≤ bias` and `bias + q < top`. -/
noncomputable def qBounds (bias top : Nat) : List QTerm → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => Nat.ble t.p bias && Nat.blt (Nat.add bias t.q) top && ih)

/-- All exponents are at most `n`. -/
noncomputable def qFits (n : Nat) : List QTerm → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => Nat.ble t.e1 n && Nat.ble t.e2 n && Nat.ble t.e3 n && ih)

/-- The number of the constraint `g ≥ 0` with `2 ^ sg * g = ∑ (p - q) x₁^e₁ x₂^e₂ x₃^e₃`: the biased coefficients
of `-2 ^ sg * g`. -/
noncomputable def quadPp (R : Run) (l : List QTerm) : Nat := Nat.sub (Nat.add (biasG R) (qNeg R l)) (qPos R l)

/-- The checker: `Pp` is the number of the constraint with the terms `l`, the places of the terms are distinct,
and no slot overflows. -/
noncomputable def quadOk (R : Run) (l : List QTerm) (Pp : Nat) : Bool :=
  Nat.ble 1 R.V && qFits R.n l && qDistinct R.n l &&
    Nat.blt (Nat.shiftLeft 1 (Nat.sub R.aG 1)) (Nat.shiftLeft 1 R.V) &&
    qBounds (Nat.shiftLeft 1 (Nat.sub R.aG 1)) (Nat.shiftLeft 1 R.V) l && Nat.beq Pp (quadPp R l)

end N14.Box
