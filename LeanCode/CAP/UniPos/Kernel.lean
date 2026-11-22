module

public import CAP.Core.Packed

/-!
# E3, the minorant condition: the checker (`Init` only)

**Statement.** Let `Hh d`, `d ≤ 2 * D`, be integers and `Dn` a natural number, and put
`Ĥ(t) = ∑ d, Hh d * t ^ d`. Then `Ĥ(t) ≤ Dn * (2 - 2 * t) ^ (-1/2)` for all `-1 ≤ t < 1`. This is
`H ≤ f` for the Coulomb potential `f(t) = (2 - 2 * t) ^ (-1/2)` and `H = Ĥ / Dn`. It follows from
`Dn ^ 2 - (2 - 2 * t) * Ĥ(t) ^ 2 ≥ 0`, which the checker verifies.

**Witness.** Cut points `1 = t_m > … > t_0 = -1` of the form `t_k = 1 - lam_k / 2 ^ s` with natural
numbers `2 ^ (s + 1) = lam_0 > lam_1 > … > lam_m = 0`.

**Method.** On the piece between `lam_k` and `lam_(k+1)` the variable is `t = (L2 - M) / L2` with
the linear forms `L2 = 2 ^ s * (1 + y)` and `M = lam_k + lam_(k+1) * y`, `y ≥ 0`. The polynomial

  `B(y) = Dn ^ 2 * L2 ^ (4 * D + 1) - 2 * M * Hb(y) ^ 2`,
  `Hb = ∑ d, Hh d * (L2 - M) ^ d * L2 ^ (2 * D - d)`,

equals `L2 ^ (4 * D + 1) * (Dn ^ 2 - (2 - 2 * t) * Ĥ(t) ^ 2)`. If all coefficients of `B` are
nonnegative, then `B(y) ≥ 0` for `y ≥ 0`, and the inequality holds on the piece. Up to positive
factors the coefficients of `B` are the Bernstein coefficients of the polynomial on the piece.

**Arithmetic.** A polynomial in `y` with natural coefficients is the number obtained at
`y = 2 ^ V`; a polynomial with integer coefficients is a pair (positive part, negative part).
`Hb` is computed by Horner's rule with the two linear forms, which are shifts and products with
small numbers. The same program with `V = 0` gives the sums of the coefficients, which bound the
coefficients.

**Data.** `Hp` is the packed number of the identity (`CAP.ThreePoint`): slot `d` of width `W` is
`Hh d + 2 ^ (aH - 1)`. The cuts are the list `[lam_1, …, lam_m]`.

The checker is bit-exact with `certgen/unipos.py`.
-/

@[expose] public section

namespace CAP.UniPos

/-- Parameters of the minorant condition. -/
structure Params where
  /-- the polynomial has degree at most `2 * D` -/
  D : Nat
  /-- slot width of the data `Hp` -/
  W : Nat
  /-- the coefficient `d` is slot `d` of `Hp` minus `2 ^ (aH - 1)` -/
  aH : Nat
  /-- slot width of the polynomials in `y` -/
  V : Nat
  /-- the cut points are `1 - lam / 2 ^ s` -/
  s : Nat

/-- `X * (2 ^ s * (1 + y))` for a polynomial `X` at `y = 2 ^ V`. -/
def mulL2 (V s X : Nat) : Nat := Nat.shiftLeft (Nat.add X (Nat.shiftLeft X V)) s

/-- `X * (lk + lk1 * y)` for a polynomial `X` at `y = 2 ^ V`. -/
def mulM (V lk lk1 X : Nat) : Nat := Nat.add (Nat.mul lk X) (Nat.mul lk1 (Nat.shiftLeft X V))

/-- Horner's rule for `Hb`. With `cnt` coefficients left, the next coefficient has the index
`cnt - 1`; the state is the pair of the partial sum and the power of `L2`. -/
noncomputable def hornerGo (P : Params) (V Hp lk lk1 : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun Sp Sn _ => (Sp, Sn))
    (fun k ih Sp Sn Pw =>
      ih (Nat.add (Nat.add (mulL2 V P.s Sp) (mulM V lk lk1 Sn)) (Nat.mul (slot P.W Hp k) Pw))
        (Nat.add (Nat.add (mulL2 V P.s Sn) (mulM V lk lk1 Sp))
          (Nat.mul (Nat.shiftLeft 1 (Nat.sub P.aH 1)) Pw))
        (mulL2 V P.s Pw))
    cnt

/-- `(2 ^ s * (1 + y)) ^ cnt` at `y = 2 ^ V`. -/
noncomputable def powL2 (V s : Nat) (cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun _ ih => mulL2 V s ih) cnt

/-- The pair of `B = Dn ^ 2 * L2 ^ (4 * D + 1) - 2 * M * Hb ^ 2` at `y = 2 ^ V`. -/
noncomputable def bern (P : Params) (V Hp Dn lk lk1 : Nat) : Nat × Nat :=
  (Nat.add (Nat.mul (Nat.mul Dn Dn) (powL2 V P.s (Nat.succ (Nat.mul 4 P.D))))
      (Nat.mul 2 (mulM V lk lk1 (Nat.mul 2
        (Nat.mul (hornerGo P V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).1
          (hornerGo P V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).2)))),
    Nat.mul 2 (mulM V lk lk1 (Nat.add
      (Nat.mul (hornerGo P V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).1
        (hornerGo P V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).1)
      (Nat.mul (hornerGo P V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).2
        (hornerGo P V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).2))))

/-- Every slot of `Bn` is at most the corresponding slot of `Bp`, for packed numbers with `m`
slots of width `V` below `2 ^ (V - 1)`: the difference added to `Bn` is `Bp`, and no slot of the
difference has its highest bit set. -/
def geTest (V m Bp Bn : Nat) : Bool :=
  Nat.beq (Nat.add (Nat.sub Bp Bn) Bn) Bp &&
  Nat.beq (Nat.land (Nat.sub Bp Bn)
    (Nat.mul (Nat.sub (Nat.shiftLeft 1 V) (Nat.shiftLeft 1 (Nat.sub V 1))) (ones V m))) 0

/-- The test of the piece between the cuts `lk > lk1`: the sums of the coefficients of both parts
of `B` are below `2 ^ (V - 1)`, and the coefficients of `B` are nonnegative. -/
noncomputable def intervalOk (P : Params) (Hp Dn lk lk1 : Nat) : Bool :=
  Nat.blt (bern P 0 Hp Dn lk lk1).1 (Nat.shiftLeft 1 (Nat.sub P.V 1)) &&
  Nat.blt (bern P 0 Hp Dn lk lk1).2 (Nat.shiftLeft 1 (Nat.sub P.V 1)) &&
  geTest P.V (Nat.add (Nat.mul 4 P.D) 4) (bern P P.V Hp Dn lk lk1).1 (bern P P.V Hp Dn lk lk1).2

/-- The loop over the cuts; `prev` is the previous cut. The cuts decrease, and the last one is `0`. -/
noncomputable def cutsGo (P : Params) (Hp Dn : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun prev => Nat.beq prev 0)
    (fun lam _ ih prev => Nat.blt lam prev && intervalOk P Hp Dn prev lam && ih lam)

/-- The checker of the minorant condition. -/
noncomputable def check (P : Params) (Hp Dn : Nat) (cuts : List Nat) : Bool :=
  Nat.ble 1 P.V && cutsGo P Hp Dn cuts (Nat.shiftLeft 1 (Nat.succ P.s))

end CAP.UniPos
