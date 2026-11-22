module

public import CAP.UniPos.Kernel

/-!
# E11, the sign of a polynomial in three variables on a box: the checker (`Init` only)

**Statement.** Let `p(x) = ∑ i j k ≤ n, P i j k * x₁ ^ i * x₂ ^ j * x₃ ^ k` with integers `P i j k`.
Then `p ≥ 0` on a box (`th = 0`), respectively `p > 0` on the box (`th = 1`). In coordinate `a` the
box is `[(c - off) / q, (c + w - off) / q]` with natural numbers `c`, `w`, `off`, `q`.

**Arrays.** Put `m = n + 1`. An array of `m ^ 3` natural numbers is one number: the entry
`(e₁, e₂, e₃)` is slot `e₁ + m * e₂ + m ^ 2 * e₃` of width `V`. The digits of coordinate `a` have
the distance `Vs = V * m ^ a` in bits. A *slice* of coordinate `a` consists of the entries with
one value of the digit `e_a`; it is cut out by a shift and a mask with a periodic pattern.

**Method.** Every coordinate of the box has homogeneous coordinates `(u, v)` with `u, v ≥ 0`: the
point is `x = (c - off + w * v / (u + v)) / q`. The *value* of an array `X` at `(u, v)` is
`∑ e, X e * ∏ a, u_a ^ (n - e_a) * v_a ^ e_a`. The operations of the checker are substitutions in
one coordinate, each of them `n + 1` steps of Horner's rule on whole arrays:

* `desc` turns the pair (positive part, negative part) of a polynomial in `x_a` into that of the
  polynomial in `t = (q * x - c + off) / w`: the value at `(u, v)` is the old value at
  `(q * u, (c - off) * u + w * v)`;
* `asc`: the value at `(u, v)` is the old value at `(u + v, v)`;
* `half`: the value at `(u, v)` is the old value at `(u, u + 2 * v)`;
* `halfR`: the value at `(u, v)` is the old value at `(u + 2 * v, u)`.

`rootP`, `rootN` apply `desc` and `asc` in every coordinate. They are the two parts of an array
`B` whose value at `(u, v)` is `∏ a, (q_a * (u_a + v_a)) ^ n` times `p(x)`. Up to positive factors
the entries of `B` are the Bernstein coefficients of `p` on the box. Let `J` be the array of the
products of three binomial coefficients; its value is `∏ a, (u_a + v_a) ^ n`. The checker tests
`B⁺ ≤ A * J` and `B⁻ ≤ A * J` entry by entry and continues with the single array
`X = B⁺ + (A * J - B⁻)`, whose value is that of `B` plus `A` times that of `J`.

**Certificate.** A binary tree. At a leaf the checker tests `X ≥ (A + th) * J` entry by entry. At
a split in coordinate `a` every entry of `X` is divided by `2 ^ n` and rounded down, and the two
subtrees get `half` and `halfR` of the result. These are the two halves of the box in this
coordinate: every `(u, v)` with `u, v ≥ 0` is `(u', u' + 2 * v')` or `(u' + 2 * v', u')` with
`u', v' ≥ 0`. Both substitutions multiply the value of `J` by `2 ^ n`, so that the value of the new
array is at most the old value at the new point, and the offset `A * J` is the same at all nodes.

**Division of a tree.** The kernel keeps all intermediate arrays of an evaluation. A certificate
can therefore contain the array of the root (`rootIs`), and the subtrees below a cut of the tree
are checked by `treeOk` in evaluations of their own, each starting from the array of the root.

**Bounds.** Entries are read only where they are known to be below `2 ^ V`: the entries of the data
are below `2 ^ aH` by a test of their bits, those of `root` are below the product `rootBound` of
the sizes of the substitutions, and the entries of the arrays of the tree are at most `2 * A`
times those of `J`.

The checker is bit-exact with `certgen/bernstein.py`.
-/

@[expose] public section

namespace CAP.Bernstein

/-- Parameters of the sign condition on a box. -/
structure Params where
  /-- the polynomial has degree at most `n` in each variable -/
  n : Nat
  /-- slot width of the arrays -/
  V : Nat
  /-- the entry `e` of the data is the coefficient plus `2 ^ (aH - 1)` -/
  aH : Nat
  /-- `0` for `p ≥ 0`, `1` for `p > 0` -/
  th : Nat
  /-- the bound of the two arrays of the root, in units of `J` -/
  A : Nat
  /-- coordinate 1 of the box is `[(c1 - o1) / q1, (c1 + w1 - o1) / q1]` -/
  c1 : Nat
  w1 : Nat
  o1 : Nat
  q1 : Nat
  /-- coordinate 2 of the box -/
  c2 : Nat
  w2 : Nat
  o2 : Nat
  q2 : Nat
  /-- coordinate 3 of the box -/
  c3 : Nat
  w3 : Nat
  o3 : Nat
  q3 : Nat

/-- A subdivision tree for a box in three coordinates. -/
inductive Tree where
  /-- the entries of the array of the box pass the test -/
  | leaf
  /-- the box is bisected in coordinate `a` (`0`, `1`; every other value means the third one) -/
  | split (a : Nat) (l r : Tree)

/-- The number of entries of an array. -/
def cube (n : Nat) : Nat := Nat.mul (Nat.mul (Nat.succ n) (Nat.succ n)) (Nat.succ n)

/-- The mask of a slice: `r` blocks of `Vs` ones with the period `Vs * m`. -/
def sliceMask (Vs m r : Nat) : Nat := Nat.mul (mask Vs) (ones (Nat.mul Vs m) r)

/-- The distance of the digits of coordinate 1, 2, 3. -/
def vs1 (P : Params) : Nat := P.V
def vs2 (P : Params) : Nat := Nat.mul P.V (Nat.succ P.n)
def vs3 (P : Params) : Nat := Nat.mul (Nat.mul P.V (Nat.succ P.n)) (Nat.succ P.n)

/-- The masks of the slices of coordinate 1, 2, 3. -/
def msk1 (P : Params) : Nat := sliceMask (vs1 P) (Nat.succ P.n) (Nat.mul (Nat.succ P.n) (Nat.succ P.n))
def msk2 (P : Params) : Nat := sliceMask (vs2 P) (Nat.succ P.n) (Nat.succ P.n)
def msk3 (P : Params) : Nat := sliceMask (vs3 P) (Nat.succ P.n) 1

/-- `x1` for `a = 0`, `x2` for `a = 1`, `x3` otherwise. -/
noncomputable def sel (a x1 x2 x3 : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x1 (fun k _ => Nat.rec (motive := fun _ => Nat) x2 (fun _ _ => x3) k) a

/-- `a * X + Y`, without the product if `a = 0`. -/
noncomputable def lin (a X Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Y (fun _ _ => Nat.add (Nat.mul a X) Y) a

/-- Horner's rule for `desc`. With `cnt` slices left, the next slice has the index `cnt - 1`; the
state is the pair of the partial sums and the power of `q`. -/
noncomputable def descGo (Vs msk c w off q Xp Xn : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun Sp Sn _ => (Sp, Sn))
    (fun k ih Sp Sn gp =>
      ih (lin c Sp (lin off Sn (Nat.add (Nat.mul w (Nat.shiftLeft Sp Vs))
            (Nat.mul (Nat.land (Nat.shiftRight Xp (Nat.mul Vs k)) msk) gp))))
        (lin c Sn (lin off Sp (Nat.add (Nat.mul w (Nat.shiftLeft Sn Vs))
            (Nat.mul (Nat.land (Nat.shiftRight Xn (Nat.mul Vs k)) msk) gp))))
        (Nat.mul gp q))
    cnt

/-- The substitution `(u, v) ↦ (q * u, (c - off) * u + w * v)` in one coordinate, for a pair. -/
noncomputable def desc (n Vs msk c w off q : Nat) (X : Nat × Nat) : Nat × Nat :=
  descGo Vs msk c w off q X.1 X.2 (Nat.succ n) 0 0 1

/-- Horner's rule for `asc`; the state is the partial sum and the position of the next slice. -/
noncomputable def ascGo (Vs msk X : Nat) (cnt : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun S _ => S)
    (fun _ ih S sh =>
      ih (Nat.add (Nat.add S (Nat.shiftLeft S Vs)) (Nat.land X (Nat.shiftLeft msk sh))) (Nat.add sh Vs))
    cnt

/-- The substitution `(u, v) ↦ (u + v, v)` in one coordinate. -/
noncomputable def asc (n Vs msk X : Nat) : Nat := ascGo Vs msk X (Nat.succ n) 0 0

/-- Horner's rule for `half`. With `cnt` slices left, the next slice has the index `cnt - 1`. -/
noncomputable def halfGo (Vs msk X : Nat) (cnt : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun S => S)
    (fun k ih S =>
      ih (Nat.add (Nat.add S (Nat.shiftLeft S (Nat.succ Vs))) (Nat.land (Nat.shiftRight X (Nat.mul Vs k)) msk)))
    cnt

/-- The substitution `(u, v) ↦ (u, u + 2 * v)` in one coordinate. -/
noncomputable def half (n Vs msk X : Nat) : Nat := halfGo Vs msk X (Nat.succ n) 0

/-- Horner's rule for `halfR`: the partial sum for the slices `0, …, cnt - 1`, which are read in
the opposite order. -/
noncomputable def halfRGo (Vs msk X : Nat) (cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k ih =>
      Nat.add (Nat.add ih (Nat.shiftLeft ih (Nat.succ Vs))) (Nat.land (Nat.shiftRight X (Nat.mul Vs k)) msk))
    cnt

/-- The substitution `(u, v) ↦ (u + 2 * v, u)` in one coordinate. -/
noncomputable def halfR (n Vs msk X : Nat) : Nat := halfRGo Vs msk X (Nat.succ n)

/-- `∑ d ≤ n, a ^ d * b ^ (n - d)`, as the first component; the second one is `b ^ n`. -/
noncomputable def gsum (a b : Nat) (n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (1, 1)
    (fun _ ih => (Nat.add (Nat.mul ih.1 a) (Nat.mul ih.2 b), Nat.mul ih.2 b)) n

/-- The array `J`: the entry `(e₁, e₂, e₃)` is the product of the binomial coefficients
`n choose e_a`. -/
def binomJ (P : Params) : Nat :=
  Nat.mul (Nat.mul (Nat.pow (Nat.add 1 (Nat.shiftLeft 1 (vs1 P))) P.n)
      (Nat.pow (Nat.add 1 (Nat.shiftLeft 1 (vs2 P))) P.n))
    (Nat.pow (Nat.add 1 (Nat.shiftLeft 1 (vs3 P))) P.n)

/-- The data are an array with entries below `2 ^ aH`. -/
def dataOk (P : Params) (Pp : Nat) : Bool :=
  Nat.ble P.aH P.V && Nat.blt Pp (Nat.shiftLeft 1 (Nat.mul P.V (cube P.n))) &&
  Nat.beq (Nat.land Pp (Nat.mul (Nat.sub (Nat.shiftLeft 1 P.V) (Nat.shiftLeft 1 P.aH)) (ones P.V (cube P.n)))) 0

/-- A bound for all entries that `root` computes. -/
noncomputable def rootBound (P : Params) : Nat :=
  Nat.shiftLeft
    (Nat.mul (Nat.mul (Nat.mul (Nat.shiftLeft 1 P.aH)
        (gsum (Nat.add (Nat.add P.c1 P.w1) P.o1) P.q1 P.n).1)
      (gsum (Nat.add (Nat.add P.c2 P.w2) P.o2) P.q2 P.n).1)
      (gsum (Nat.add (Nat.add P.c3 P.w3) P.o3) P.q3 P.n).1)
    (Nat.mul 3 (Nat.succ P.n))

/-- `desc` in the three coordinates, applied to the data and the array of the bias. -/
noncomputable def root (P : Params) (Pp : Nat) : Nat × Nat :=
  desc P.n (vs3 P) (msk3 P) P.c3 P.w3 P.o3 P.q3
    (desc P.n (vs2 P) (msk2 P) P.c2 P.w2 P.o2 P.q2
      (desc P.n (vs1 P) (msk1 P) P.c1 P.w1 P.o1 P.q1
        (Pp, Nat.mul (Nat.shiftLeft 1 (Nat.sub P.aH 1)) (ones P.V (cube P.n)))))

/-- `asc` in the three coordinates. -/
noncomputable def asc3 (P : Params) (X : Nat) : Nat :=
  asc P.n (vs3 P) (msk3 P) (asc P.n (vs2 P) (msk2 P) (asc P.n (vs1 P) (msk1 P) X))

/-- The positive part of the array `B` of the box. -/
noncomputable def rootP (P : Params) (Pp : Nat) : Nat := asc3 P (root P Pp).1

/-- The negative part of the array `B` of the box. -/
noncomputable def rootN (P : Params) (Pp : Nat) : Nat := asc3 P (root P Pp).2

/-- The entries `2 * A * J` and `(A + th) * J` are below `2 ^ (V - 1)`. -/
def fits (P : Params) : Bool :=
  Nat.blt (Nat.shiftLeft (Nat.add (Nat.mul 2 P.A) P.th) (Nat.mul 3 P.n)) (Nat.shiftLeft 1 (Nat.sub P.V 1))

/-- Every entry divided by `2 ^ n`, rounded down. -/
def floorN (P : Params) (X : Nat) : Nat :=
  Nat.shiftRight
    (Nat.land X (Nat.mul (Nat.sub (Nat.shiftLeft 1 P.V) (Nat.shiftLeft 1 P.n)) (ones P.V (cube P.n)))) P.n

/-- The array of one half of a split in the coordinate `a`: `half` of the divided array for
`side = 0`, `halfR` otherwise. -/
noncomputable def child (P : Params) (a side X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (half P.n (sel a (vs1 P) (vs2 P) (vs3 P)) (sel a (msk1 P) (msk2 P) (msk3 P)) (floorN P X))
    (fun _ _ => halfR P.n (sel a (vs1 P) (vs2 P) (vs3 P)) (sel a (msk1 P) (msk2 P) (msk3 P)) (floorN P X))
    side

/-- The array `(A + th) * J`, with which a leaf compares its array. -/
def offJ (P : Params) : Nat := Nat.mul (Nat.add P.A P.th) (binomJ P)

/-- The checker of a tree for the array `X`; `AJ` is the array `(A + th) * J`. -/
noncomputable def treeOk (P : Params) (AJ : Nat) : Tree → Nat → Bool :=
  Tree.rec (motive := fun _ => Nat → Bool)
    (fun X => CAP.UniPos.geTest P.V (cube P.n) X AJ)
    (fun a _ _ ihl ihr X => ihl (child P a 0 X) && ihr (child P a 1 X))

/-- The tests of the checker that do not concern the tree. -/
noncomputable def rootOk (P : Params) (Pp : Nat) : Bool :=
  Nat.ble 1 P.V && Nat.ble P.n P.V && Nat.ble P.th 1 && Nat.ble 1 P.q1 && Nat.ble 1 P.q2 && Nat.ble 1 P.q3 &&
  dataOk P Pp && Nat.blt (rootBound P) (Nat.shiftLeft 1 (Nat.sub P.V 1)) && fits P &&
  CAP.UniPos.geTest P.V (cube P.n) (Nat.mul P.A (binomJ P)) (rootP P Pp) &&
  CAP.UniPos.geTest P.V (cube P.n) (Nat.mul P.A (binomJ P)) (rootN P Pp)

/-- The array `X = B⁺ + (A * J - B⁻)` of the root. -/
noncomputable def rootX (P : Params) (Pp : Nat) : Nat :=
  Nat.add (rootP P Pp) (Nat.sub (Nat.mul P.A (binomJ P)) (rootN P Pp))

/-- The checker of the sign of a polynomial in three variables on a box. -/
noncomputable def check (P : Params) (Pp : Nat) (T : Tree) : Bool :=
  rootOk P Pp && treeOk P (offJ P) T (rootX P Pp)

/-- The tests of the root for a certificate that contains the array `X` of the root. With it the
tree can be divided: the trees of the parts are checked by `treeOk`, each for the array that
`child` gives along the way from the root, in kernel evaluations of their own. -/
noncomputable def rootIs (P : Params) (Pp X : Nat) : Bool :=
  rootOk P Pp && Nat.beq (rootX P Pp) X

end CAP.Bernstein
