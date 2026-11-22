module

public import CAP.Core.Packed

/-!
# E2, positive definiteness: the checker (`Init` only)

**Statement.** Let `X i j`, `i ≤ j < n`, be integers, and let `G` be the symmetric matrix with
`G i i = 2 * X i i` and `G i j = G j i = X i j` for `i < j`. Then `G` is positive definite.

**Witness.** An integer lower triangular matrix `L` and exponents `p2`, `e` such that
`R = 2 ^ p2 • G - L * Lᵀ` satisfies

* `|R i j| ≤ 2 ^ e` for `i < j`,
* `R i i > (n - 1) * 2 ^ e` for all `i`.

Then `R` is strictly diagonally dominant with positive diagonal, hence positive definite, and so is
`2 ^ p2 • G = L * Lᵀ + R`. The checker verifies the two conditions. It only multiplies, adds and
compares; in particular it neither divides nor takes square roots.

**Data** (slot width `w`, see `CAP.Core.Packed`). Two natural numbers:

* `rows`: the concatenation of the rows `i = 0, …, n - 1`, where row `i` has the `n - i` slots
  `X i j + 2 ^ (a - 1)`, `j = i, …, n - 1`;
* `cols`: the concatenation of the columns `k = 0, …, n - 1`, where column `k` has the `n - k`
  slots `L j k + 2 ^ (aL - 1)`, `j = k, …, n - 1`.

For row `i`, the entries `(L * Lᵀ) i j`, `j ≥ i`, are obtained as one packed vector from the columns
`k ≤ i`, with one multiplication per column. The checker is bit-exact with `certgen/psd.py`.
-/

@[expose] public section

namespace CAP.PSD

/-- Parameters of a block. -/
structure Params where
  /-- order of the matrix -/
  n : Nat
  /-- slot width -/
  w : Nat
  /-- data bits: `0 ≤ X i j + 2 ^ (a - 1) < 2 ^ a` -/
  a : Nat
  /-- factor bits: `0 ≤ L j k + 2 ^ (aL - 1) < 2 ^ aL` -/
  aL : Nat
  /-- the scale is `2 ^ p2` -/
  p2 : Nat
  /-- the bound for the off-diagonal entries of `R` is `2 ^ e` -/
  e : Nat
  /-- `n < 2 ^ nb` -/
  nb : Nat

/-- The inequalities between the parameters under which no slot overflows. -/
def paramsOk (P : Params) : Bool :=
  Nat.blt P.n (Nat.shiftLeft 1 P.nb) && Nat.ble 1 P.a && Nat.ble 1 P.aL &&
  Nat.ble (Nat.add (Nat.add P.p2 P.a) 4) P.w &&
  Nat.ble (Nat.add (Nat.add (Nat.mul 2 P.aL) P.nb) 4) P.w &&
  Nat.ble (Nat.add P.e 3) P.w

/-- Constants of a block, computed once. -/
structure Consts where
  /-- `2 ^ w - 1` -/
  mw : Nat
  /-- `ones w n` -/
  onN : Nat
  /-- `2 ^ (w - 1)` -/
  H : Nat
  /-- `2 ^ p2 * 2 ^ (a - 1)` -/
  sbeta : Nat
  /-- `2 ^ (aL - 1)` -/
  betaL : Nat
  /-- `betaL ^ 2` -/
  betaL2 : Nat
  /-- `2 ^ w - 2 ^ a` -/
  hiA : Nat
  /-- `2 ^ w - 2 ^ aL` -/
  hiL : Nat
  /-- `2 ^ w - 2 ^ (e + 1)` -/
  hiE : Nat
  /-- `2 ^ (w - 1) + 2 ^ e` -/
  He : Nat
  /-- `(n - 1) * 2 ^ e + 1` -/
  dg : Nat

def mkConsts (P : Params) : Consts :=
  { mw := mask P.w,
    onN := ones P.w P.n,
    H := Nat.shiftLeft 1 (Nat.sub P.w 1),
    sbeta := Nat.shiftLeft 1 (Nat.add P.p2 (Nat.sub P.a 1)),
    betaL := Nat.shiftLeft 1 (Nat.sub P.aL 1),
    betaL2 := Nat.shiftLeft 1 (Nat.mul 2 (Nat.sub P.aL 1)),
    hiA := Nat.sub (Nat.shiftLeft 1 P.w) (Nat.shiftLeft 1 P.a),
    hiL := Nat.sub (Nat.shiftLeft 1 P.w) (Nat.shiftLeft 1 P.aL),
    hiE := Nat.sub (Nat.shiftLeft 1 P.w) (Nat.shiftLeft 1 (Nat.succ P.e)),
    He := Nat.add (Nat.shiftLeft 1 (Nat.sub P.w 1)) (Nat.shiftLeft 1 P.e),
    dg := Nat.succ (Nat.shiftLeft (Nat.sub P.n 1) P.e) }

/-- The columns `k = i, i - 1, …, 0` are listed in `stack`. With `τₖ` the column `k` shifted to
row `i` (slots `L j k + betaL`, `j ≥ i`) and `ℓₖ` its lowest slot, the result is
`(∑ₖ ℓₖ * τₖ, ∑ₖ τₖ)`. -/
noncomputable def colGo (w mw : Nat) : List Nat → Nat → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun _ U V => (U, V))
    (fun lam _ ih sh U V =>
      ih (Nat.add sh w)
        (Nat.add U (Nat.mul (Nat.land (Nat.shiftRight lam sh) mw) (Nat.shiftRight lam sh)))
        (Nat.add V (Nat.shiftRight lam sh)))

/-- The conditions for row `i`. Here `rho` is row `i` of the data, `lam` is column `i` of the
factor (both with `n - i` slots), and `stack` lists the columns `i, i - 1, …, 0`.

With `(U, V) = colGo …` and `σ` the lowest slot of `V`, the packed vectors `A` and `B` have slots
below `2 ^ (w - 2)` and satisfy `A - B = R i j` in slot `j - i`. -/
noncomputable def rowOk (P : Params) (c : Consts) (rho lam : Nat) (stack : List Nat) (i : Nat) : Bool :=
  let on := Nat.shiftRight c.onN (Nat.mul P.w i)
  let on1 := Nat.shiftRight on P.w
  let UV := colGo P.w c.mw stack 0 0 0
  let A := Nat.add (Nat.add (Nat.add (Nat.shiftLeft rho P.p2) (Nat.mul c.betaL UV.2))
    (Nat.mul (Nat.mul c.betaL (Nat.land UV.2 c.mw)) on)) (Nat.shiftLeft (Nat.land rho c.mw) P.p2)
  let B := Nat.add (Nat.add UV.1 (Nat.mul (Nat.add (Nat.mul (Nat.succ i) c.betaL2) c.sbeta) on)) c.sbeta
  Nat.beq (Nat.land rho (Nat.mul c.hiA on)) 0 && Nat.beq (Nat.land lam (Nat.mul c.hiL on)) 0 &&
  Nat.ble (Nat.add (Nat.land B c.mw) c.dg) (Nat.land A c.mw) &&
  Nat.beq
    (Nat.land (Nat.sub (Nat.add (Nat.shiftRight A P.w) (Nat.mul c.He on1)) (Nat.shiftRight B P.w))
      (Nat.mul c.hiE on1))
    (Nat.mul c.H on1)

/-- The loop over the rows. The arguments are the rows and the columns that are not yet used
(as packed numbers), the columns already used (in reverse order) and the index of the current
row. In every step the next row and the next column, with `n - i` slots each, are split off. -/
noncomputable def rowGo (P : Params) (c : Consts) (cnt : Nat) : Nat → Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → Nat → Bool)
    (fun R C _ _ => Nat.beq R 0 && Nat.beq C 0)
    (fun _ ih R C stack i =>
      Bool.rec (motive := fun _ => Bool) false
        (ih (Nat.shiftRight R (Nat.mul P.w (Nat.sub P.n i))) (Nat.shiftRight C (Nat.mul P.w (Nat.sub P.n i)))
          (List.cons (Nat.land C (mask (Nat.mul P.w (Nat.sub P.n i)))) stack) (Nat.succ i))
        (rowOk P c (Nat.land R (mask (Nat.mul P.w (Nat.sub P.n i))))
          (Nat.land C (mask (Nat.mul P.w (Nat.sub P.n i))))
          (List.cons (Nat.land C (mask (Nat.mul P.w (Nat.sub P.n i)))) stack) i))
    cnt

/-- The checker of E2. -/
noncomputable def check (P : Params) (rows cols : Nat) : Bool :=
  paramsOk P && rowGo P (mkConsts P) P.n rows cols List.nil 0

end CAP.PSD
