module

public import CAP.Subdivision.BernKernel

/-!
# T7, the slack of a three-point certificate on a domain: the checker (`Init` only)

**Statement.** A slack of the proof for 14 points is a function

  `λ(x) = M(x₁, x₂, x₃) + U₁(x₁) + U₂(x₂) + U₃(x₃)`,

where `M` is a polynomial of degree at most `n` in each variable and `U_a(x) = p_a(x) + w_a (2 - 2x)^(-1/2)`
with a polynomial `p_a` in one variable. The assertion is `λ ≥ θ` at all points of a box that satisfy the
*constraints* of the run: the Gram inequality `1 + 2 x₁ x₂ x₃ - x₁² - x₂² - x₃² ≥ 0` and finitely many *cuts*
`x_a ≥ c`, `x_a ≤ c`, `x_a ≥ x_b`.

**Cells.** Every coordinate has a list of *intervals*: the interval with the level `e`
and the position `c` is `[c / 2^e - 1, (c + 1) / 2^e - 1]`. A *cell* `(i, j, k)` is the product of the intervals
`i`, `j`, `k` of the three coordinates. Every interval carries a *table entry*: a polynomial `T` of degree at
most `n` with `T ≤ U_a` on the interval. On a cell the polynomial `M + T_i(x₁) + T_j(x₂) + T_k(x₃) - θ` has
integer coefficients after scaling, and the checker of `CAP.Bernstein` computes its Bernstein array on the cell.

**Table entries** (`entryOk`). `T ≤ p + w (2 - 2x)^(-1/2)` on an interval follows from
`Dn² - (2 - 2x) Ĥ(x)² ≥ 0` for `Ĥ = Dn (T - p) / w`, which the checker `CAP.UniPos.intervalOk` verifies on
pieces of the interval. The coefficients of `Ĥ` are formed from those of `T` by one product and one sum.

**Constraints.** The coefficients of `-g` are formed from the constraint `g ≥ 0` (`conPp`). The array `Y` of
`-g` on a cell is the array of the root of `CAP.Bernstein` for this polynomial, with the offset `A_g`. It is
computed only if a leaf uses it: the kernel evaluates an argument when it is needed.

**Trees** (`go`). The certificate of a cell is a tree, stored as one number that is read from its low bits.
A node begins with three bits:

* `0`, `1`, `2`: a split in this coordinate; the two subtrees follow. The arrays of the two halves are those of
  `CAP.Bernstein.child`, for the array `X` of the polynomial and for the arrays of the constraints.
* `3`: a leaf; every entry of `X` is at least `A` times that of the binomial array `J`.
* `4`: a leaf with multipliers `μ_c` (`mb` bits for every constraint, in their order): every entry of
  `X + ∑ μ_c Y_c` is at least `A + ∑ μ_c A_c` times that of `J`. At a point that satisfies the constraints, the
  value of `Y_c` is at most `A_c` times that of `J`, hence the value of `X` is at least `A` times that of `J`.
* `5`: a leaf outside the domain, followed by three bits `c`: every entry of `Y_c` is at least `A_c + 1` times
  that of `J`, so the constraint `c` fails on the whole box of the leaf.

**The cover** (`cover`, `groupOk`). The cube `[-1, 1]³` is divided into the boxes of a grid, and every box of
the grid is covered by cells: a second tree bisects the box, and each of its leaves either violates a cut at all
of its points (a comparison of integers) or is the box of the next cell of the certificate, whose tree is
accepted. Hence the cells may have different sizes.

The checker is bit-exact with `N14/py/boxref.py`.
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein

/-- A cut of a run. `kind = 0`: `x_a + 1 ≥ vn / vd`; `kind = 1`: `x_a + 1 ≤ vn / vd`; every other value:
`x_a ≥ x_b`. The coordinates `a`, `b` are `0`, `1`, and every other value means the third one. -/
structure Cut where
  kind : Nat
  a : Nat
  b : Nat
  vn : Nat
  vd : Nat

/-- An interval of a coordinate, `[c / 2 ^ e - 1, (c + 1) / 2 ^ e - 1]`, with its table entry: the polynomial
`T`, whose coefficient `d` is slot `d` (`T = 0`: no entry), and the cuts of the pieces on which the minorant
condition is verified. -/
structure Ent where
  e : Nat
  c : Nat
  T : Nat
  cuts : List Nat

/-- The parameters of a run. -/
structure Run where
  /-- the mixed part has degree at most `n` in each variable -/
  n : Nat
  /-- slot width of the arrays and of the coefficients -/
  V : Nat
  /-- entry `e` of the coefficients of a cell is the coefficient plus `2 ^ (aH - 1)` -/
  aH : Nat
  /-- the bound of the two arrays of the root of a cell, in units of `J` -/
  A : Nat
  /-- the coefficients of the mixed part, biased -/
  PpM : Nat
  /-- slot width of the polynomials of the table entries -/
  W : Nat
  /-- the intervals of the three coordinates with their table entries -/
  t1 : List Ent
  t2 : List Ent
  t3 : List Ent
  /-- the constraint polynomials have the scale `2 ^ sg` -/
  sg : Nat
  /-- entry `e` of the coefficients of a constraint is the coefficient plus `2 ^ (aG - 1)` -/
  aG : Nat
  /-- the bound of the two arrays of the root of a constraint, in units of `J` -/
  AG : Nat
  /-- the cuts; the constraints of a cell are the Gram inequality, the cuts, and the polynomial constraints
  that the cell selects, in this order -/
  cuts : List Cut
  /-- the polynomial constraints `g ≥ 0`: the coefficients of `-2 ^ sg * g`, biased like those of the cuts
  (excluded balls, ellipsoids) -/
  polys : List Nat
  /-- bits of a multiplier -/
  mb : Nat
  /-- a bound for the depth of the trees -/
  fuel : Nat
  /-- bits of the number of the constraint in a leaf of a box on which a constraint fails -/
  ob : Nat := 3

/-- A cell of the certificate: its three indices, the polynomial constraints that it uses (bit `p` of `use`
selects the constraint `p` of the run), and its tree. -/
structure Cell where
  i : Nat
  j : Nat
  k : Nat
  use : Nat
  tree : Nat

/-! ## Lists -/

/-- Entry `i` of a list of numbers; `0` if there is none. -/
noncomputable def nth : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun i' _ => ih i') i)

/-- Entry `i` of a list of intervals; an interval without a table entry if there is none. -/
noncomputable def ent : List Ent → Nat → Ent :=
  List.rec (motive := fun _ => Nat → Ent) (fun _ => { e := 0, c := 0, T := 0, cuts := List.nil })
    (fun x _ ih i => Nat.rec (motive := fun _ => Ent) x (fun i' _ => ih i') i)

/-- The length of a list. -/
noncomputable def len {α : Type} : List α → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih)

/-! ## The polynomial of a cell -/

/-- The parameters of `CAP.Bernstein` for a polynomial on the cell `(i, j, k)`. -/
noncomputable def boxP (R : Run) (aH A i j k : Nat) : Params :=
  { n := R.n, V := R.V, aH := aH, th := 0, A := A,
    c1 := (ent R.t1 i).c, w1 := 1, o1 := Nat.shiftLeft 1 (ent R.t1 i).e, q1 := Nat.shiftLeft 1 (ent R.t1 i).e,
    c2 := (ent R.t2 j).c, w2 := 1, o2 := Nat.shiftLeft 1 (ent R.t2 j).e, q2 := Nat.shiftLeft 1 (ent R.t2 j).e,
    c3 := (ent R.t3 k).c, w3 := 1, o3 := Nat.shiftLeft 1 (ent R.t3 k).e, q3 := Nat.shiftLeft 1 (ent R.t3 k).e }

/-- The slots `0, …, cnt - 1` of width `W` of `T`, placed at the distance `Vs`. -/
noncomputable def place (W Vs T : Nat) (cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun d ih => Nat.add ih (Nat.shiftLeft (Nat.land (Nat.shiftRight T (Nat.mul W d)) (mask W)) (Nat.mul Vs d)))
    cnt

/-- The coefficients of the polynomial of the cell `(i, j, k)`: those of the mixed part, and those of the three
table entries on the three axes. -/
noncomputable def cellPp (R : Run) (i j k : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add R.PpM
      (place R.W R.V (ent R.t1 i).T (Nat.succ R.n)))
      (place R.W (Nat.mul R.V (Nat.succ R.n)) (ent R.t2 j).T (Nat.succ R.n)))
      (place R.W (Nat.mul (Nat.mul R.V (Nat.succ R.n)) (Nat.succ R.n)) (ent R.t3 k).T (Nat.succ R.n))

/-- The array of the root for a polynomial on a box, or `0` if the tests of the root fail. -/
noncomputable def rootArr (P : Params) (Pp : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (rootX P Pp) (rootOk P Pp)

/-! ## The constraints -/

/-- `2 ^ (V * (e₁ + m * e₂ + m² * e₃))`: the unit of the entry `(e₁, e₂, e₃)`. -/
def unit3 (R : Run) (e1 e2 e3 : Nat) : Nat :=
  Nat.shiftLeft 1 (Nat.mul R.V (Nat.add e1 (Nat.mul (Nat.succ R.n) (Nat.add e2 (Nat.mul (Nat.succ R.n) e3)))))

/-- The unit of the entry with the exponent `d` in the coordinate `a` and `0` in the others. -/
noncomputable def unitA (R : Run) (a d : Nat) : Nat :=
  sel a (unit3 R d 0 0) (unit3 R 0 d 0) (unit3 R 0 0 d)

/-- The array all of whose entries are the bias of the constraints. -/
def biasG (R : Run) : Nat := Nat.mul (Nat.shiftLeft 1 (Nat.sub R.aG 1)) (ones R.V (cube R.n))

/-- The coefficients of `-2 ^ sg * (1 + 2 x₁ x₂ x₃ - x₁² - x₂² - x₃²)`, biased. -/
def gramPp (R : Run) : Nat :=
  Nat.sub
    (Nat.add (biasG R) (Nat.mul (Nat.shiftLeft 1 R.sg)
      (Nat.add (Nat.add (unit3 R 2 0 0) (unit3 R 0 2 0)) (unit3 R 0 0 2))))
    (Nat.mul (Nat.shiftLeft 1 R.sg) (Nat.add (unit3 R 0 0 0) (Nat.mul 2 (unit3 R 1 1 1))))

/-- The coefficients of `-2 ^ sg * g`, biased, for the cut `g ≥ 0`. The scale of a cut with the value
`vn / vd` is `2 ^ sg`, and `vd` has to divide `2 ^ sg` (`cutFits`).
`kind = 0`: `g = x_a + 1 - vn / vd`; `kind = 1`: `g = vn / vd - x_a - 1`; otherwise `g = x_a - x_b`. -/
noncomputable def cutPp (R : Run) (c : Cut) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    -- `-g = vn / vd - 1 - x_a`
    (Nat.sub (Nat.add (biasG R) (Nat.mul (Nat.div (Nat.mul c.vn (Nat.shiftLeft 1 R.sg)) c.vd) (unit3 R 0 0 0)))
      (Nat.mul (Nat.shiftLeft 1 R.sg) (Nat.add (unit3 R 0 0 0) (unitA R c.a 1))))
    (fun k _ => Nat.rec (motive := fun _ => Nat)
      -- `-g = x_a + 1 - vn / vd`
      (Nat.sub (Nat.add (biasG R) (Nat.mul (Nat.shiftLeft 1 R.sg) (Nat.add (unit3 R 0 0 0) (unitA R c.a 1))))
        (Nat.mul (Nat.div (Nat.mul c.vn (Nat.shiftLeft 1 R.sg)) c.vd) (unit3 R 0 0 0)))
      -- `-g = x_b - x_a`
      (fun _ _ => Nat.sub (Nat.add (biasG R) (Nat.mul (Nat.shiftLeft 1 R.sg) (unitA R c.b 1)))
        (Nat.mul (Nat.shiftLeft 1 R.sg) (unitA R c.a 1)))
      k)
    c.kind

/-- The arrays of the cuts on the cell `(i, j, k)`, before the arrays `tail`. -/
noncomputable def cutArrs (R : Run) (i j k : Nat) (tail : List Nat) : List Cut → List Nat :=
  List.rec (motive := fun _ => List Nat) tail
    (fun c _ ih => List.cons (rootArr (boxP R R.aG R.AG i j k) (cutPp R c)) ih)

/-- The arrays on the cell `(i, j, k)` of the polynomial constraints that the bits of `use` select. -/
noncomputable def polyArrs (R : Run) (i j k : Nat) : List Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun Pp _ ih use => Nat.rec (motive := fun _ => List Nat) (ih (Nat.shiftRight use 1))
      (fun _ _ => List.cons (rootArr (boxP R R.aG R.AG i j k) Pp) (ih (Nat.shiftRight use 1)))
      (Nat.land use 1))

/-- The arrays of the constraints on the cell `(i, j, k)`: the Gram inequality, the cuts, and the selected
polynomial constraints. -/
noncomputable def conArrs (R : Run) (i j k use : Nat) : List Nat :=
  List.cons (rootArr (boxP R R.aG R.AG i j k) (gramPp R))
    (cutArrs R i j k (polyArrs R i j k R.polys use) R.cuts)

/-! ## Trees -/

/-- The arrays of one half of a split, for a list of arrays. -/
noncomputable def childs (P : Params) (a side : Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun Y _ ih => List.cons (child P a side Y) ih)

/-- The sum `X + ∑ μ_c * Y_c` and the number `∑ μ_c`, for the multipliers `μ_c` that are read from `s`, `mb`
bits for each array of the list. -/
noncomputable def accGo (mb : Nat) : List Nat → Nat → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun _ X m => (X, m))
    (fun Y _ ih s X m =>
      ih (Nat.shiftRight s mb) (lin (Nat.land s (mask mb)) Y X) (Nat.add m (Nat.land s (mask mb))))

/-- The number `s` without the multipliers of a leaf. -/
noncomputable def skip (mb : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s) (fun _ _ ih s => ih (Nat.shiftRight s mb))

/-- The test of a leaf with multipliers. -/
noncomputable def accOk (R : Run) (P : Params) (J s X : Nat) (Ys : List Nat) : Bool :=
  UniPos.geTest P.V (cube P.n) (accGo R.mb Ys s X 0).1
    (Nat.mul (Nat.add P.A (Nat.mul (accGo R.mb Ys s X 0).2 R.AG)) J)

/-- The checker of a tree. `s` is the rest of the number of the tree, `X` the array of the polynomial, `Ys`
the arrays of the constraints, and `k` the test of the rest of the number after the tree. The first argument
bounds the depth. -/
noncomputable def go (R : Run) (P : Params) (J : Nat) : Nat → Nat → Nat → List Nat → (Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → (Nat → Bool) → Bool)
    (fun _ _ _ _ => false)
    (fun _ ih s X Ys k =>
      Bool.rec (motive := fun _ => Bool)
        -- a leaf
        (Nat.rec (motive := fun _ => Bool)
          (UniPos.geTest P.V (cube P.n) X (Nat.mul P.A J) && k (Nat.shiftRight s 3))
          (fun t _ => Nat.rec (motive := fun _ => Bool)
            (accOk R P J (Nat.shiftRight s 3) X Ys && k (skip R.mb Ys (Nat.shiftRight s 3)))
            (fun t' _ => Nat.rec (motive := fun _ => Bool)
              (UniPos.geTest P.V (cube P.n) (nth Ys (Nat.land (Nat.shiftRight s 3) (mask R.ob)))
                  (Nat.mul (Nat.succ R.AG) J) && k (Nat.shiftRight s (Nat.add 3 R.ob)))
              (fun _ _ => false)
              t')
            t)
          (Nat.sub (Nat.land s 7) 3))
        -- a split
        (ih (Nat.shiftRight s 3) (child P (Nat.land s 7) 0 X) (childs P (Nat.land s 7) 0 Ys)
          (fun s' => ih s' (child P (Nat.land s 7) 1 X) (childs P (Nat.land s 7) 1 Ys) k))
        (Nat.blt (Nat.land s 7) 3))

/-- The checker of a cell: its three table entries exist, and its tree is accepted. -/
noncomputable def cellOk (R : Run) (c : Cell) : Bool :=
  Nat.blt 0 (ent R.t1 c.i).T && Nat.blt 0 (ent R.t2 c.j).T && Nat.blt 0 (ent R.t3 c.k).T &&
  go R (boxP R R.aH R.A c.i c.j c.k) (binomJ (boxP R R.aH R.A c.i c.j c.k)) R.fuel c.tree
    (rootArr (boxP R R.aH R.A c.i c.j c.k) (cellPp R c.i c.j c.k)) (conArrs R c.i c.j c.k c.use)
    (fun _ => true)

/-! ## The cover -/

/-- The box with the intervals `(e₁, c₁)`, `(e₂, c₂)`, `(e₃, c₃)` violates the cut at all of its points. In
the coordinate `x + 1` the interval with the level `e` and the position `c` is `[c / 2 ^ e, (c + 1) / 2 ^ e]`. -/
noncomputable def cutOut (c : Cut) (e1 c1 e2 c2 e3 c3 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool)
    -- `x_a + 1 ≥ vn / vd` fails: `(c_a + 1) / 2 ^ e_a < vn / vd`
    (Nat.blt (Nat.mul (Nat.succ (sel c.a c1 c2 c3)) c.vd) (Nat.shiftLeft c.vn (sel c.a e1 e2 e3)))
    (fun t _ => Nat.rec (motive := fun _ => Bool)
      -- `x_a + 1 ≤ vn / vd` fails: `vn / vd < c_a / 2 ^ e_a`
      (Nat.blt (Nat.shiftLeft c.vn (sel c.a e1 e2 e3)) (Nat.mul (sel c.a c1 c2 c3) c.vd))
      -- `x_a ≥ x_b` fails: `(c_a + 1) / 2 ^ e_a < c_b / 2 ^ e_b`
      (fun _ _ => Nat.blt (Nat.shiftLeft (Nat.succ (sel c.a c1 c2 c3)) (sel c.b e1 e2 e3))
        (Nat.shiftLeft (sel c.b c1 c2 c3) (sel c.a e1 e2 e3)))
      t)
    c.kind

/-- The box violates one of the cuts at all of its points. -/
noncomputable def boxOut (e1 c1 e2 c2 e3 c3 : Nat) : List Cut → Bool :=
  List.rec (motive := fun _ => Bool) false (fun c _ ih => cutOut c e1 c1 e2 c2 e3 c3 || ih)

/-- The cell has the box with the intervals `(e₁, c₁)`, `(e₂, c₂)`, `(e₃, c₃)`. -/
noncomputable def cellIs (R : Run) (c : Cell) (e1 c1 e2 c2 e3 c3 : Nat) : Bool :=
  Nat.beq (ent R.t1 c.i).e e1 && Nat.beq (ent R.t1 c.i).c c1 &&
  Nat.beq (ent R.t2 c.j).e e2 && Nat.beq (ent R.t2 c.j).c c2 &&
  Nat.beq (ent R.t3 c.k).e e3 && Nat.beq (ent R.t3 c.k).c c3

/-- The checker of the cover of a box by cells. The cover is a tree, stored as a number that is read from its
low bits, two bits for a node: `0`, `1`, `2` is a bisection of the box in this coordinate, and the two
subtrees follow; `3` is a leaf. At a leaf the box violates a cut at all of its points, or it is the box of the
next cell of the list, and the tree of this cell is accepted. `k` tests the rest of the number and of the list
after the tree. The first argument bounds the depth. -/
noncomputable def cover (R : Run) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Cell → (Nat → List Cell → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Cell → (Nat → List Cell → Bool) → Bool)
    (fun _ _ _ _ _ _ _ _ _ => false)
    (fun _ ih s e1 c1 e2 c2 e3 c3 l k =>
      Nat.rec (motive := fun _ => Bool)
        (ih (Nat.shiftRight s 2) (Nat.succ e1) (Nat.mul 2 c1) e2 c2 e3 c3 l
          (fun s' l' => ih s' (Nat.succ e1) (Nat.succ (Nat.mul 2 c1)) e2 c2 e3 c3 l' k))
        (fun t _ => Nat.rec (motive := fun _ => Bool)
          (ih (Nat.shiftRight s 2) e1 c1 (Nat.succ e2) (Nat.mul 2 c2) e3 c3 l
            (fun s' l' => ih s' e1 c1 (Nat.succ e2) (Nat.succ (Nat.mul 2 c2)) e3 c3 l' k))
          (fun t' _ => Nat.rec (motive := fun _ => Bool)
            (ih (Nat.shiftRight s 2) e1 c1 e2 c2 (Nat.succ e3) (Nat.mul 2 c3) l
              (fun s' l' => ih s' e1 c1 e2 c2 (Nat.succ e3) (Nat.succ (Nat.mul 2 c3)) l' k))
            (fun _ _ =>
              Bool.rec (motive := fun _ => Bool)
                (List.rec (motive := fun _ => Bool) false
                  (fun c rest _ => cellIs R c e1 c1 e2 c2 e3 c3 && cellOk R c && k (Nat.shiftRight s 2) rest) l)
                (k (Nat.shiftRight s 2) l)
                (boxOut e1 c1 e2 c2 e3 c3 R.cuts))
            t')
          t)
        (Nat.land s 3))

/-- The covers of the boxes with the numbers `b, b + 1, …` of the grid of the level `lv`: the box with the
number `b` has the intervals `(lv, b / m²)`, `(lv, (b / m) % m)`, `(lv, b % m)`, where `m = 2 ^ (lv + 1)`. The
trees follow one another in the number `s`, and at the end the list of the cells is empty. -/
noncomputable def groupGo (R : Run) (lv : Nat) : Nat → Nat → Nat → List Cell → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List Cell → Bool)
    (fun _ _ l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun _ ih b s l =>
      cover R R.fuel s lv (Nat.div b (Nat.mul (Nat.shiftLeft 2 lv) (Nat.shiftLeft 2 lv)))
        lv (Nat.mod (Nat.div b (Nat.shiftLeft 2 lv)) (Nat.shiftLeft 2 lv)) lv (Nat.mod b (Nat.shiftLeft 2 lv)) l
        (fun s' l' => ih (Nat.succ b) s' l'))

/-! ## Table entries -/

/-- The parameters of a table of minorants of a function `U = p + w (2 - 2x)^(-1/2)` of one variable, `w ≥ 0`
(`Dn = 0` if there is no Coulomb term). An entry
is a polynomial `T` of degree at most `n`, whose coefficient `d` is slot `d` of width `P.W` (a natural number
below `2 ^ aT`). The polynomial `Ĥ` of `CAP.UniPos` has the coefficients `c1 * T_d + K_d - 2 ^ (P.aH - 1)`, where
`K_d` is slot `d` of `K`. -/
structure Tab where
  P : UniPos.Params
  Dn : Nat
  c1 : Nat
  K : Nat
  n : Nat
  aT : Nat

/-- The test of a piece for a function without a Coulomb term: `Ĥ ≤ 0` on the piece between the cuts
`lk > lk1`. With the linear forms of `CAP.UniPos`, `Hb = ∑ d, Hh d * (L2 - M) ^ d * L2 ^ (2 * D - d)` is
`L2 ^ (2 * D) * Ĥ(t)`. The sums of the coefficients of both parts of `Hb` are below `2 ^ (V - 1)`, and every
coefficient of the positive part is at most the coefficient of the negative part. -/
noncomputable def negOk (P : UniPos.Params) (Hp lk lk1 : Nat) : Bool :=
  Nat.blt (UniPos.hornerGo P 0 Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).1 (Nat.shiftLeft 1 (Nat.sub P.V 1)) &&
  Nat.blt (UniPos.hornerGo P 0 Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).2 (Nat.shiftLeft 1 (Nat.sub P.V 1)) &&
  UniPos.geTest P.V (Nat.add (Nat.mul 2 P.D) 2)
    (UniPos.hornerGo P P.V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).2
    (UniPos.hornerGo P P.V Hp lk lk1 (Nat.succ (Nat.mul 2 P.D)) 0 0 1).1

/-- The test of a piece: `Ĥ(t) ≤ Dn * (2 - 2 t) ^ (-1/2)` on the piece. With a Coulomb term (`Dn > 0`) it is
the test of `CAP.UniPos`, without one (`Dn = 0`) it is `negOk`. -/
noncomputable def pieceOk (P : UniPos.Params) (Hp Dn lk lk1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (negOk P Hp lk lk1) (fun _ _ => UniPos.intervalOk P Hp Dn lk lk1) Dn

/-- The pieces between `prev` and the cuts of the list are accepted, and the last cut is at most `last`. -/
noncomputable def piecesGo (P : UniPos.Params) (Hp Dn last : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun prev => Nat.ble prev last)
    (fun lam _ ih prev => Nat.blt lam prev && pieceOk P Hp Dn prev lam && ih lam)

/-- The table entry of an interval: `T ≤ U` at the points below `1` of `[c / 2 ^ e - 1, (c + 1) / 2 ^ e - 1]`.
In the units `2 ^ P.s * (1 - x)` of `CAP.UniPos` the interval is
`[(2 ^ (e + 1) - c - 1) * 2 ^ (s - e), (2 ^ (e + 1) - c) * 2 ^ (s - e)]`; the pieces reach below its lower end. -/
noncomputable def entryOk (U : Tab) (x : Ent) : Bool :=
  Nat.blt x.T (Nat.shiftLeft 1 (Nat.mul U.P.W (Nat.succ U.n))) &&
  Nat.beq (Nat.land x.T
    (Nat.mul (Nat.sub (Nat.shiftLeft 1 U.P.W) (Nat.shiftLeft 1 U.aT)) (ones U.P.W (Nat.succ U.n)))) 0 &&
  Nat.ble x.e U.P.s && Nat.blt x.c (Nat.shiftLeft 2 x.e) &&
  piecesGo U.P (Nat.add (Nat.mul U.c1 x.T) U.K) U.Dn
    (Nat.sub (Nat.shiftLeft (Nat.sub (Nat.sub (Nat.shiftLeft 2 x.e) x.c) 1) (Nat.sub U.P.s x.e)) 1)
    x.cuts (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 2 x.e) x.c) (Nat.sub U.P.s x.e))

/-- The table entries of a list of intervals. An interval with `T = 0` has no entry. -/
noncomputable def tableGo (U : Tab) : List Ent → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Nat.rec (motive := fun _ => Bool) true (fun _ _ => entryOk U x) x.T && ih)

/-- The tests of the parameters of a table. -/
noncomputable def tabOk (U : Tab) : Bool :=
  Nat.ble 1 U.P.V && Nat.ble 1 U.P.W && Nat.ble U.aT U.P.W && Nat.ble 1 U.c1 &&
  Nat.ble U.n (Nat.mul 2 U.P.D) &&
  Nat.ble (Nat.mul U.c1 (Nat.shiftLeft 1 U.aT)) (Nat.shiftLeft 1 (Nat.sub U.P.W 1)) &&
  Nat.blt U.K (Nat.shiftLeft 1 (Nat.mul U.P.W (Nat.succ (Nat.mul 2 U.P.D)))) &&
  Nat.beq (Nat.land U.K
    (Nat.mul (Nat.shiftLeft 1 (Nat.sub U.P.W 1)) (ones U.P.W (Nat.succ (Nat.mul 2 U.P.D))))) 0

/-- The checker of a table, or of a part of it: the parameters and the entries of the list. -/
noncomputable def tableOk (U : Tab) (entries : List Ent) : Bool :=
  tabOk U && tableGo U entries

/-! ## The parameters -/

/-- A cut fits the scale of the constraints: `vd` divides `vn * 2 ^ sg`, and the value is at most `2`. -/
noncomputable def cutFits (R : Run) (c : Cut) : Bool :=
  Nat.ble 1 c.vd &&
  Nat.beq (Nat.mul (Nat.div (Nat.mul c.vn (Nat.shiftLeft 1 R.sg)) c.vd) c.vd) (Nat.mul c.vn (Nat.shiftLeft 1 R.sg)) &&
  Nat.ble c.vn (Nat.mul 2 c.vd)

/-- All cuts fit. -/
noncomputable def cutsFit (R : Run) : List Cut → Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => cutFits R c && ih)

/-- The tests of the parameters of a run: the entries of all arrays of the trees and of the sums of the
leaves fit into the slots, the coefficients of the mixed part and the polynomials of the table entries fit, and
the constraints fit their scale. -/
noncomputable def runOk (R : Run) : Bool :=
  Nat.ble 1 R.V && Nat.ble R.n R.V && Nat.ble 2 R.n && Nat.ble 1 R.A && Nat.ble 1 R.AG &&
  -- the sums of the leaves
  Nat.blt (Nat.shiftLeft
      (Nat.mul 2 (Nat.add R.A (Nat.mul (Nat.mul (Nat.succ (Nat.add (len R.cuts) (len R.polys)))
        (Nat.shiftLeft 1 R.mb)) (Nat.succ R.AG))))
      (Nat.mul 3 R.n))
    (Nat.shiftLeft 1 (Nat.sub R.V 1)) &&
  -- the coefficients: those of the mixed part are below `2 ^ aH`, those of an entry below `2 ^ W`
  Nat.ble 2 R.aH && Nat.ble (Nat.add R.aH R.n) R.V && Nat.blt R.W (Nat.sub R.aH 3) &&
  Nat.blt R.PpM (Nat.shiftLeft 1 (Nat.mul R.V (cube R.n))) &&
  Nat.beq (Nat.land R.PpM
    (Nat.mul (Nat.sub (Nat.shiftLeft 1 R.V) (Nat.shiftLeft 1 R.aH)) (ones R.V (cube R.n)))) 0 &&
  -- the constraints
  Nat.blt (Nat.add R.sg 2) (Nat.sub R.aG 1) && Nat.ble R.aG R.V && cutsFit R R.cuts

/-- The checker of a group of boxes of the grid of the level `lv`: the boxes with the numbers
`b, …, b + cnt - 1` are covered by cells whose trees are accepted, or they violate a cut. -/
noncomputable def groupOk (R : Run) (lv b cnt s : Nat) (cells : List Cell) : Bool :=
  groupGo R lv cnt b s cells

end N14.Box
