module

public import CAP.Core.Packed

/-!
# Schema S2, the three-point identity: the checker (`Init` only)

**Statement.** Let `N`, `D` be given and `q = 2 * D + 1`. The data are, for every block of the
three-point bound, an upper triangular array `X` of integers, and integers `Hh d` (`d ≤ 2 * D`)
and `ch`. With

* `φₖ = ∑_{i ≤ j} Xₖ i j • u ^ i * v ^ j` for the moment block `k = 0, …, D`,
* `Pₖ = φₖ * Qₖ`, where `Q₀ = 1`, `Q₁ = t - u * v`,
  `Qₖ = 2 * (t - u * v) * Qₖ₋₁ - (1 - u ^ 2) * (1 - v ^ 2) * Qₖ₋₂`,
* `G_B = g_B * ∑_{i ≤ j} X_B i j • zᵢ * zⱼ` for a block `B` with weight `g_B` and basis `z`,
* `Qh = 9 * (N - 2) * ∑ₖ Pₖ + ∑_B f_B * G_B`,
* `Sh x = ∑ₖ Pₖ (x, x, 1) + Pₖ (x, 1, x) + Pₖ (1, x, x)`,
* `Z = (N - 1) * Qh + 9 * (N - 1) * Sh u + 9 * ∑_{i ≤ j} X₀ i j - 9 * (N - 1) * Hh u + 9 * (N - 1) * ch`,

the assertion is that the sum of `Z ∘ σ` over the six permutations `σ` of `(u, v, t)` vanishes.
For the data of a certificate of the three-point bound this is `54 * (N - 1)` times the common
denominator times the identity of the bound.

**Method.** All polynomials are evaluated at the point `(X, X ^ q, X ^ (q ^ 2))` with
`X = 2 ^ W` (Kronecker substitution). A polynomial with natural coefficients below `X` and degree
below `q` in each variable becomes the natural number whose digit in base `X` at the position
`a + q * b + q ^ 2 * c` is the coefficient of `u ^ a * v ^ b * t ^ c`; sums and products of
polynomials become sums and products of natural numbers. A polynomial with integer coefficients is
a pair (positive part, negative part). The same code at the points `(X, X, 1)`, `(X, 1, X)`,
`(1, X, X)` gives the univariate polynomials in `Sh`, and at `(1, 1, 1)` sums of coefficients,
which bound the coefficients of `Z`.

**Data.** The matrix data are those of `CAP.PSD` (slot width `w`, bias `2 ^ (a - 1)`). A
polynomial that is part of the data (a basis element or a weight) is a sequence of terms, each
stored in `fw = 3 * eb + cb + 1` bits: three exponents of `eb` bits, a coefficient of `cb` bits and
a sign bit.

The checker is bit-exact with `certgen/threepoint.py`.
-/

@[expose] public section

namespace CAP.ThreePoint

/-- Parameters of the identity. -/
structure Params where
  /-- number of points -/
  N : Nat
  /-- the polynomials have degree at most `2 * D` -/
  D : Nat
  /-- slot width of the Kronecker substitution -/
  W : Nat
  /-- slot width of the matrix data -/
  w : Nat
  /-- matrix data bits: `0 ≤ X i j + 2 ^ (a - 1) < 2 ^ a` -/
  a : Nat
  /-- target bits: `0 ≤ Hh d + 2 ^ (aH - 1) < 2 ^ aH` and `0 ≤ ch < 2 ^ aH` -/
  aH : Nat
  /-- bits of an exponent field -/
  eb : Nat
  /-- bits of a coefficient field -/
  cb : Nat

/-- A block with a sum of squares. -/
structure Sos where
  /-- order of the matrix -/
  n : Nat
  /-- number of term fields of a basis element -/
  T : Nat
  /-- bound for the degree of the basis elements -/
  dz : Nat
  /-- bound for the sum of the coefficients of a basis element -/
  cmax : Nat
  /-- the basis: `n * T` term fields -/
  basis : Nat
  /-- number of term fields of the weight -/
  gT : Nat
  /-- bound for the degree of the weight -/
  gdeg : Nat
  /-- the weight: `gT` term fields -/
  weight : Nat
  /-- the factor `f_B` -/
  f : Nat
  /-- the matrix data -/
  rows : Nat

/-- A point `(X ^ pu, X ^ pv, X ^ pt)`. -/
structure Pt where
  pu : Nat
  pv : Nat
  pt : Nat

/-! ## Terms -/

/-- width of a term field -/
def fw (P : Params) : Nat := Nat.succ (Nat.add (Nat.mul 3 P.eb) P.cb)

/-- the term field of `± coef * u ^ a * v ^ b * t ^ c` -/
def term (P : Params) (a b c coef neg : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add a (Nat.shiftLeft b P.eb)) (Nat.shiftLeft c (Nat.mul 2 P.eb)))
    (Nat.shiftLeft coef (Nat.mul 3 P.eb))) (Nat.shiftLeft neg (Nat.add (Nat.mul 3 P.eb) P.cb))

/-- the lowest term field of a sequence -/
def fld (P : Params) (tf : Nat) : Nat := Nat.land tf (mask (fw P))

def tExp (P : Params) (f i : Nat) : Nat := Nat.land (Nat.shiftRight f (Nat.mul P.eb i)) (mask P.eb)

def tCoef (P : Params) (f : Nat) : Nat := Nat.land (Nat.shiftRight f (Nat.mul 3 P.eb)) (mask P.cb)

def tNeg (P : Params) (f : Nat) : Bool := Nat.beq (Nat.shiftRight f (Nat.add (Nat.mul 3 P.eb) P.cb)) 1

/-- `W` times the position of the monomial of a term at a point -/
def tPos (P : Params) (pt : Pt) (f : Nat) : Nat :=
  Nat.mul P.W (Nat.add (Nat.add (Nat.mul (tExp P f 0) pt.pu) (Nat.mul (tExp P f 1) pt.pv))
    (Nat.mul (tExp P f 2) pt.pt))

def tDeg (P : Params) (f : Nat) : Nat := Nat.add (Nat.add (tExp P f 0) (tExp P f 1)) (tExp P f 2)

/-- The polynomial with the `T` term fields `tf` at a point: `(positive part, negative part,
sum of the coefficients, all terms have degree ≤ dz)`. -/
noncomputable def polyEval (P : Params) (pt : Pt) (dz : Nat) (T : Nat) :
    Nat → Nat → Nat → Nat → Bool → Nat × Nat × Nat × Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool → Nat × Nat × Nat × Bool)
    (fun _ p n nm ok => (p, n, nm, ok))
    (fun _ ih tf p n nm ok =>
      Bool.rec (motive := fun _ => Nat × Nat × Nat × Bool)
        (ih (Nat.shiftRight tf (fw P))
          (Nat.add p (Nat.shiftLeft (tCoef P (fld P tf)) (tPos P pt (fld P tf)))) n
          (Nat.add nm (tCoef P (fld P tf))) (ok && Nat.ble (tDeg P (fld P tf)) dz))
        (ih (Nat.shiftRight tf (fw P))
          p (Nat.add n (Nat.shiftLeft (tCoef P (fld P tf)) (tPos P pt (fld P tf))))
          (Nat.add nm (tCoef P (fld P tf))) (ok && Nat.ble (tDeg P (fld P tf)) dz))
        (tNeg P (fld P tf)))
    T

/-- `(yp, yn) + poly tf * (xp, xn)` for the polynomial with the `T` term fields `tf`. -/
noncomputable def mulTerms (P : Params) (pt : Pt) (T : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat × Nat)
    (fun _ _ _ yp yn => (yp, yn))
    (fun _ ih tf xp xn yp yn =>
      Bool.rec (motive := fun _ => Nat × Nat)
        (Bool.rec (motive := fun _ => Nat × Nat)
          (ih (Nat.shiftRight tf (fw P)) xp xn
            (Nat.add yp (Nat.mul (tCoef P (fld P tf)) (Nat.shiftLeft xp (tPos P pt (fld P tf)))))
            (Nat.add yn (Nat.mul (tCoef P (fld P tf)) (Nat.shiftLeft xn (tPos P pt (fld P tf))))))
          (ih (Nat.shiftRight tf (fw P)) xp xn
            (Nat.add yp (Nat.mul (tCoef P (fld P tf)) (Nat.shiftLeft xn (tPos P pt (fld P tf)))))
            (Nat.add yn (Nat.mul (tCoef P (fld P tf)) (Nat.shiftLeft xp (tPos P pt (fld P tf))))))
          (tNeg P (fld P tf)))
        (ih (Nat.shiftRight tf (fw P)) xp xn yp yn)
        (Nat.beq (tCoef P (fld P tf)) 0))
    T

/-! ## The kernels `Qₖ` -/

/-- `t - u * v` -/
def tuv (P : Params) : Nat := Nat.add (term P 0 0 1 1 0) (Nat.shiftLeft (term P 1 1 0 1 1) (fw P))

/-- `(1 - u ^ 2) * (1 - v ^ 2) = 1 - u ^ 2 - v ^ 2 + u ^ 2 * v ^ 2` -/
def wuv (P : Params) : Nat :=
  Nat.add (Nat.add (Nat.add (term P 0 0 0 1 0) (Nat.shiftLeft (term P 2 0 0 1 1) (fw P)))
    (Nat.shiftLeft (term P 0 2 0 1 1) (Nat.mul 2 (fw P)))) (Nat.shiftLeft (term P 2 2 0 1 0) (Nat.mul 3 (fw P)))

/-- `Qₖ₊₁ = 2 * (t - u * v) * Qₖ - (1 - u ^ 2) * (1 - v ^ 2) * Qₖ₋₁` for `cur = Qₖ`, `prev = Qₖ₋₁`. -/
noncomputable def qNext (P : Params) (pt : Pt) (cur prev : Nat × Nat) : Nat × Nat :=
  (Nat.add (Nat.mul 2 (mulTerms P pt 2 (tuv P) cur.1 cur.2 0 0).1) (mulTerms P pt 4 (wuv P) prev.1 prev.2 0 0).2,
   Nat.add (Nat.mul 2 (mulTerms P pt 2 (tuv P) cur.1 cur.2 0 0).2) (mulTerms P pt 4 (wuv P) prev.1 prev.2 0 0).1)

/-! ## Moment blocks -/

/-- One row of `φ`: the `cnt` lowest slots of `rho` are added at the shifts `s, s + dv, …`. -/
noncomputable def phiRow (w mw beta dv : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat × Nat)
    (fun _ _ php phn => (php, phn))
    (fun _ ih rho s php phn =>
      ih (Nat.shiftRight rho w) (Nat.add s dv)
        (Nat.add php (Nat.shiftLeft (Nat.land rho mw) s)) (Nat.add phn (Nat.shiftLeft beta s)))
    cnt

/-- The loop over the rows of a moment block of order `n`; the state is the remaining data, the
index of the row, the two parts of `φ` and the flag of the data. -/
noncomputable def phiGo (P : Params) (pt : Pt) (n : Nat) (cnt : Nat) :
    Nat → Nat → Nat → Nat → Bool → Nat × Nat × Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool → Nat × Nat × Bool)
    (fun R _ php phn ok => (php, phn, ok && Nat.beq R 0))
    (fun _ ih R i php phn ok =>
      ih (Nat.shiftRight R (Nat.mul P.w (Nat.sub n i))) (Nat.succ i)
        (phiRow P.w (mask P.w) (Nat.shiftLeft 1 (Nat.sub P.a 1)) (Nat.mul P.W pt.pv) (Nat.sub n i)
          (Nat.land R (mask (Nat.mul P.w (Nat.sub n i))))
          (Nat.mul P.W (Nat.mul i (Nat.add pt.pu pt.pv))) php phn).1
        (phiRow P.w (mask P.w) (Nat.shiftLeft 1 (Nat.sub P.a 1)) (Nat.mul P.W pt.pv) (Nat.sub n i)
          (Nat.land R (mask (Nat.mul P.w (Nat.sub n i))))
          (Nat.mul P.W (Nat.mul i (Nat.add pt.pu pt.pv))) php phn).2
        (ok && Nat.beq (Nat.land (Nat.land R (mask (Nat.mul P.w (Nat.sub n i))))
          (Nat.mul (Nat.sub (Nat.shiftLeft 1 P.w) (Nat.shiftLeft 1 P.a)) (ones P.w (Nat.sub n i)))) 0))
    cnt

/-- `φ = ∑_{i ≤ j} X i j • u ^ i * v ^ j` at a point, with the flag of the data. -/
noncomputable def phiEval (P : Params) (pt : Pt) (n rows : Nat) : Nat × Nat × Bool :=
  phiGo P pt n n rows 0 0 0 true

/-- The loop over the moment blocks; the state is `k`, `Qₖ`, `Qₖ₋₁`, the two parts of the sum and
the flag. -/
noncomputable def momentGo (P : Params) (pt : Pt) :
    List Nat → Nat → Nat × Nat → Nat × Nat → Nat → Nat → Bool → Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat → Nat → Nat → Bool → Nat × Nat × Bool)
    (fun k _ _ Mp Mn ok => (Mp, Mn, ok && Nat.beq k (Nat.succ P.D)))
    (fun rows _ ih k cur prev Mp Mn ok =>
      ih (Nat.succ k)
        (Bool.rec (motive := fun _ => Nat × Nat) (qNext P pt cur prev)
          (mulTerms P pt 2 (tuv P) 1 0 0 0) (Nat.beq k 0))
        cur
        (Nat.add Mp (Nat.add (Nat.mul (phiEval P pt (Nat.sub (Nat.succ P.D) k) rows).1 cur.1)
          (Nat.mul (phiEval P pt (Nat.sub (Nat.succ P.D) k) rows).2.1 cur.2)))
        (Nat.add Mn (Nat.add (Nat.mul (phiEval P pt (Nat.sub (Nat.succ P.D) k) rows).1 cur.2)
          (Nat.mul (phiEval P pt (Nat.sub (Nat.succ P.D) k) rows).2.1 cur.1)))
        (ok && (phiEval P pt (Nat.sub (Nat.succ P.D) k) rows).2.2))

/-- `∑ₖ φₖ * Qₖ` at a point, with the flag of the data. -/
noncomputable def moment (P : Params) (pt : Pt) (mrows : List Nat) : Nat × Nat × Bool :=
  momentGo P pt mrows 0 (1, 0) (0, 0) 0 0 true

/-! ## Blocks with a sum of squares -/

/-- A basis element: `(positive part, negative part, term fields, sum of coefficients, degree flag)`. -/
abbrev Elt := Nat × Nat × Nat × Nat × Bool

/-- The basis elements of a block at a point. -/
noncomputable def basisGo (P : Params) (pt : Pt) (B : Sos) (cnt : Nat) : Nat → List Elt :=
  Nat.rec (motive := fun _ => Nat → List Elt)
    (fun _ => List.nil)
    (fun _ ih tf =>
      List.cons
        ((polyEval P pt B.dz B.T (Nat.land tf (mask (Nat.mul (fw P) B.T))) 0 0 0 true).1,
         (polyEval P pt B.dz B.T (Nat.land tf (mask (Nat.mul (fw P) B.T))) 0 0 0 true).2.1,
         Nat.land tf (mask (Nat.mul (fw P) B.T)),
         (polyEval P pt B.dz B.T (Nat.land tf (mask (Nat.mul (fw P) B.T))) 0 0 0 true).2.2.1,
         (polyEval P pt B.dz B.T (Nat.land tf (mask (Nat.mul (fw P) B.T))) 0 0 0 true).2.2.2)
        (ih (Nat.shiftRight tf (Nat.mul (fw P) B.T))))
    cnt

/-- first entry of a list of pairs, `(0, 0)` for the empty list -/
noncomputable def hd : List (Nat × Nat) → Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (0, 0) (fun x _ _ => x)

/-- the list without its first entry -/
noncomputable def tl : List (Nat × Nat) → List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) List.nil (fun _ xs _ => xs)

/-- The suffix sums of the two parts of the basis elements: entry `i` is the sum over `j ≥ i`. -/
noncomputable def sufGo : List Elt → List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) (List.cons (0, 0) List.nil)
    (fun b _ ih => List.cons (Nat.add b.1 (hd ih).1, Nat.add b.2.1 (hd ih).2) ih)

/-- All basis elements have degree at most `dz` and sum of coefficients at most `cmax`. -/
noncomputable def basisOk (cmax : Nat) : List Elt → Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => b.2.2.2.2 && Nat.ble b.2.2.2.1 cmax && ih)

/-- `(rp, rn) + ∑ⱼ ξⱼ • (bⱼ⁺, bⱼ⁻)`, where `ξⱼ` are the slots of `rho` and `bⱼ` the listed basis
elements. -/
noncomputable def rowAcc (w mw : Nat) : List Elt → Nat → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun _ rp rn => (rp, rn))
    (fun b _ ih rho rp rn =>
      ih (Nat.shiftRight rho w) (Nat.add rp (Nat.mul (Nat.land rho mw) b.1))
        (Nat.add rn (Nat.mul (Nat.land rho mw) b.2.1)))

/-- The loop over the rows of a block. The state is the list of suffix sums from row `i` on, the
remaining data, `i`, the two parts of `∑_{i ≤ j} X i j • zᵢ * zⱼ` and the flag of the data. -/
noncomputable def sosGo (P : Params) (pt : Pt) (B : Sos) :
    List Elt → List (Nat × Nat) → Nat → Nat → Nat → Nat → Bool → Nat × Nat × Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Nat → Nat → Nat → Nat → Bool → Nat × Nat × Bool)
    (fun _ R _ Qp Qn ok => (Qp, Qn, ok && Nat.beq R 0))
    (fun b rest ih suf R i Qp Qn ok =>
      let wm := Nat.mul P.w (Nat.sub B.n i)
      let rho := Nat.land R (mask wm)
      let beta := Nat.shiftLeft 1 (Nat.sub P.a 1)
      let r := rowAcc P.w (mask P.w) (List.cons b rest) rho (Nat.mul beta (hd suf).2) (Nat.mul beta (hd suf).1)
      let Q := mulTerms P pt B.T b.2.2.1 r.1 r.2 Qp Qn
      ih (tl suf) (Nat.shiftRight R wm) (Nat.succ i) Q.1 Q.2
        (ok && Nat.beq (Nat.land rho
          (Nat.mul (Nat.sub (Nat.shiftLeft 1 P.w) (Nat.shiftLeft 1 P.a)) (ones P.w (Nat.sub B.n i)))) 0))

/-- A block at a point: the two parts of `g * ∑_{i ≤ j} X i j • zᵢ * zⱼ`, the flag of the data, and a
bound for the sum of the coefficients of each part of `f * g * ∑ …`. -/
noncomputable def sosBlock (P : Params) (pt : Pt) (B : Sos) : Nat × Nat × Bool × Nat :=
  let bs := basisGo P pt B B.n B.basis
  let Q := sosGo P pt B bs (sufGo bs) B.rows 0 0 0 true
  let G := mulTerms P pt B.gT B.weight Q.1 Q.2.1 0 0
  let g := polyEval P pt B.gdeg B.gT B.weight 0 0 0 true
  (G.1, G.2,
    Q.2.2 && basisOk B.cmax bs && g.2.2.2 &&
      Nat.ble (Nat.add (Nat.mul 2 B.dz) B.gdeg) (Nat.mul 2 P.D) &&
      Nat.beq (Nat.shiftRight B.basis (Nat.mul (Nat.mul (fw P) B.T) B.n)) 0,
    Nat.shiftLeft (Nat.mul (Nat.mul (Nat.mul (Nat.mul B.f g.2.2.1) (Nat.mul B.cmax B.cmax)) B.n) B.n)
      (Nat.succ P.a))

/-- The loop over the blocks; the state is the two parts of the sum, the bound and the flag. -/
noncomputable def sosAll (P : Params) (pt : Pt) : List Sos → Nat → Nat → Nat → Bool → Nat × Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool → Nat × Nat × Nat × Bool)
    (fun Qp Qn bd ok => (Qp, Qn, bd, ok))
    (fun B _ ih Qp Qn bd ok =>
      ih (Nat.add Qp (Nat.mul B.f (sosBlock P pt B).1)) (Nat.add Qn (Nat.mul B.f (sosBlock P pt B).2.1))
        (Nat.add bd (sosBlock P pt B).2.2.2) (ok && (sosBlock P pt B).2.2.1))

/-! ## The identity -/

/-- the digit of `Dd` at the position of `u ^ x * v ^ y * t ^ z` -/
def slotAt (W q Dd x y z : Nat) : Nat :=
  Nat.land (Nat.shiftRight Dd (Nat.mul W (Nat.add x (Nat.mul q (Nat.add y (Nat.mul q z)))))) (mask W)

/-- The six digits at the permutations of `(e1, e2, e3)` add up to `B6`. -/
def orbitOk (W q Dd B6 e1 e2 e3 : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (slotAt W q Dd e1 e2 e3) (slotAt W q Dd e1 e3 e2))
      (slotAt W q Dd e2 e1 e3)) (slotAt W q Dd e2 e3 e1)) (slotAt W q Dd e3 e1 e2)) (slotAt W q Dd e3 e2 e1))
    B6

/-- `orbitOk` for all `e1 < cnt` with `e1 + e2 + e3 ≤ d2` -/
noncomputable def loop1 (W q Dd B6 d2 e3 e2 : Nat) (cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun e1 ih => ih && Bool.rec (motive := fun _ => Bool) (orbitOk W q Dd B6 e1 e2 e3) true
      (Nat.blt d2 (Nat.add (Nat.add e1 e2) e3)))
    cnt

/-- `orbitOk` for all `e1 ≤ e2 < cnt` with `e1 + e2 + e3 ≤ d2` -/
noncomputable def loop2 (W q Dd B6 d2 e3 : Nat) (cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun e2 ih => ih && loop1 W q Dd B6 d2 e3 e2 (Nat.succ e2)) cnt

/-- `orbitOk` for all `e1 ≤ e2 ≤ e3 < cnt` with `e1 + e2 + e3 ≤ d2` -/
noncomputable def loop3 (W q Dd B6 d2 : Nat) (cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun e3 ih => ih && loop2 W q Dd B6 d2 e3 (Nat.succ e3)) cnt

/-- first entry of a list of numbers, `0` for the empty list -/
noncomputable def hdNat : List Nat → Nat := List.rec (motive := fun _ => Nat) 0 (fun x _ _ => x)

/-- The checker of the three-point identity. `mrows` are the matrix data of the moment blocks
`k = 0, …, D`, `sos` are the other blocks, `Hp` has the slots `Hh d + 2 ^ (aH - 1)` of width `W`
for `d = 0, …, 2 * D`, and `cp = ch`. The conditions `2 ≤ eb` and `1 ≤ cb` ensure that the term
fields of the fixed polynomials `t - u * v` and `(1 - u ^ 2) * (1 - v ^ 2)` are read as written. -/
noncomputable def check (P : Params) (mrows : List Nat) (sos : List Sos) (Hp cp : Nat) : Bool :=
  let q := Nat.succ (Nat.mul 2 P.D)
  let main : Pt := ⟨1, q, Nat.mul q q⟩
  let M := moment P main mrows
  let S1 := moment P ⟨1, 1, 0⟩ mrows
  let S2 := moment P ⟨1, 0, 1⟩ mrows
  let S3 := moment P ⟨0, 1, 1⟩ mrows
  let M1 := moment P ⟨0, 0, 0⟩ mrows
  let x0 := phiEval P ⟨0, 0, 0⟩ (Nat.succ P.D) (hdNat mrows)
  let n9 := Nat.mul 9 (Nat.sub P.N 2)
  let A := sosAll P main sos (Nat.mul n9 M.1) (Nat.mul n9 M.2.1) (Nat.mul n9 (Nat.add M1.1 M1.2.1)) M.2.2
  let n1 := Nat.sub P.N 1
  let m9 := Nat.mul 9 n1
  let Zp := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul n1 A.1)
    (Nat.mul m9 (Nat.add (Nat.add S1.1 S2.1) S3.1))) (Nat.mul 9 x0.1))
    (Nat.mul (Nat.mul m9 (Nat.shiftLeft 1 (Nat.sub P.aH 1))) (ones P.W q))) (Nat.mul m9 cp)
  let Zn := Nat.add (Nat.add (Nat.add (Nat.mul n1 A.2.1)
    (Nat.mul m9 (Nat.add (Nat.add S1.2.1 S2.2.1) S3.2.1))) (Nat.mul 9 x0.2.1)) (Nat.mul m9 Hp)
  let bound := Nat.add (Nat.add (Nat.add (Nat.mul n1 A.2.2.1)
    (Nat.mul (Nat.mul 27 n1) (Nat.add M1.1 M1.2.1))) (Nat.mul 9 (Nat.add x0.1 x0.2.1)))
    (Nat.mul (Nat.mul m9 (Nat.succ q)) (Nat.shiftLeft 1 P.aH))
  let Bq := Nat.shiftLeft 1 (Nat.sub P.W 1)
  let Dd := Nat.sub (Nat.add Zp (Nat.mul Bq (ones P.W (Nat.mul q (Nat.mul q q))))) Zn
  Nat.ble 3 P.N && Nat.blt q (Nat.shiftLeft 1 P.eb) && Nat.ble P.a P.w && Nat.ble 1 P.a && Nat.ble 1 P.aH &&
  Nat.ble 2 P.eb && Nat.ble 1 P.cb &&
  Nat.beq (Nat.shiftRight Hp (Nat.mul P.W q)) 0 &&
  Nat.beq (Nat.land Hp (Nat.mul (Nat.sub (Nat.shiftLeft 1 P.W) (Nat.shiftLeft 1 P.aH)) (ones P.W q))) 0 &&
  Nat.beq (Nat.shiftRight cp P.aH) 0 &&
  A.2.2.2 && Nat.blt bound Bq && loop3 P.W q Dd (Nat.mul 6 Bq) (Nat.mul 2 P.D) q

/-! ## The weights of the blocks

The bound for the energy needs that the weight of every block is nonnegative at the inner products
of three points of the sphere. The certificates use three weights: `1`, `1 - u ^ 2`, and the Gram
determinant `1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2`. The following checker compares the term
fields of the weights with those of these three polynomials. -/

/-- the term fields of the weight `1` -/
def wOne (P : Params) : Nat := term P 0 0 0 1 0

/-- the term fields of the weight `1 - u ^ 2` -/
def wU (P : Params) : Nat := Nat.add (term P 0 0 0 1 0) (Nat.shiftLeft (term P 2 0 0 1 1) (fw P))

/-- the term fields of the weight `1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2` -/
def wDet (P : Params) : Nat :=
  Nat.add (term P 0 0 0 1 0) (Nat.shiftLeft
    (Nat.add (term P 1 1 1 2 0) (Nat.shiftLeft
      (Nat.add (term P 2 0 0 1 1) (Nat.shiftLeft
        (Nat.add (term P 0 2 0 1 1) (Nat.shiftLeft (term P 0 0 2 1 1) (fw P))) (fw P))) (fw P))) (fw P))

/-- The weight of the block is one of the three weights. -/
def weightOk (P : Params) (B : Sos) : Bool :=
  (Nat.beq B.gT 1 && Nat.beq B.weight (wOne P)) || (Nat.beq B.gT 2 && Nat.beq B.weight (wU P))
    || (Nat.beq B.gT 5 && Nat.beq B.weight (wDet P))

/-- `weightOk` for all blocks of a list -/
noncomputable def weightsAll (P : Params) : List Sos → Bool :=
  List.rec (motive := fun _ => Bool) true (fun B _ ih => weightOk P B && ih)

/-- The weight of every block is one of the three weights. The conditions `2 ≤ eb` and `2 ≤ cb`
ensure that the exponent `2` and the coefficient `2` are read as written. -/
noncomputable def weightsOk (P : Params) (sos : List Sos) : Bool :=
  Nat.ble 2 P.eb && Nat.ble 2 P.cb && weightsAll P sos

end CAP.ThreePoint
