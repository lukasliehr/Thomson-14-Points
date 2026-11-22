module

public import N14.Jet.Kernel
public import CAP.PSD.Kernel

/-!
# Statement 7 of T7, the assembly of the three forms: the checkers (`Init` only)

The checker of a pair (`N14.Jet.pairOk`) accepts enclosures of the coefficients of degree 2, 3 and 4 of the
energy of a pair of points in the gauge coordinates of the pair. This file contains the tests that turn the
enclosures of the 91 pairs into the bounds of Proposition 9.1 of the source.

* `pairExpW i j wit`: the expression of the energy of the pair `(i, j)`; `wit` lists the witnesses of its roots.
* `scat`: the centres of the local monomials are added into the slots of the global monomials (width 64).
* `quartOk`: for a pair, the two matrices `A ± M'` of order 16 are positive definite (`CAP.PSD.check`), where
  `M'` is the symmetric matrix of the centres of degree 4 (all 24 orders of the four variables).
* `hessOk`: the matrix `2000 c_ab - [a = b] 193 * 2^47` of order 25 is positive definite, where `c_ab` is the sum
  of the centres of the global monomial `D_a D_b`.
* `cubOk`: the matrix `A3 - T Tᵗ` of order 25 is positive definite, where `T` is the symmetric tensor of the
  centres of degree 3 (all six orders), flattened to its rows.
* `rowsOk`, `budgetOk`: the sums of the bounds of the pairs that contain a point, and the sums of the radii.

The tests are bit-exact with `N14/py/localasm.py`, which was written first. Soundness: `N14/Local/`.
-/

@[expose] public section

namespace N14.Local

open CAP N14.Jet

/-! ## Lists -/

/-- Entry `i` of a list of natural numbers; `d` outside the list. -/
noncomputable def lgetD (d : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun t _ ih i => Nat.rec (motive := fun _ => Nat) t (fun j _ => ih j) i)

/-- Entry `i` of a list of pairs; `(0, 0)` outside the list. -/
noncomputable def wget : List (Nat × Nat) → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => (0, 0))
    (fun t _ ih i => Nat.rec (motive := fun _ => Nat × Nat) t (fun j _ => ih j) i)

/-! ## The expressions of the pair energies -/

/-- The gauge coordinates of the point `n`: none for the first pole, two for the second pole, the height for
the first point of the upper hexagon, the height and the angle for the other points. -/
def own (n : Nat) : List Nat :=
  cond (Nat.beq n 0) [] (cond (Nat.beq n 1) [0, 1] (cond (Nat.beq n 2) [2]
    [Nat.sub (Nat.mul 2 n) 3, Nat.sub (Nat.mul 2 n) 2]))

/-- The gauge coordinates of the pair `(i, j)`: the local variable `v` is the coordinate `lgetD 25 (gl i j) v`;
the index 25 stands for a variable that the pair does not have. -/
def gl (i j : Nat) : List Nat := List.append (own i) (own j)

/-- The index of `cos (k π / 6)` in the table of the constants `h, -h, 0, 1, -1, 1/2, -1/2, √3/2, -√3/2`. -/
noncomputable def cosI (k : Nat) : Nat := lgetD 0 [3, 7, 5, 2, 6, 8, 4, 8, 6, 2, 5, 7] (Nat.mod k 12)

/-- The index of `sin (k π / 6)`. -/
noncomputable def sinI (k : Nat) : Nat := cosI (Nat.add k 9)

/-- The index of the negative of a constant. -/
noncomputable def negI (i : Nat) : Nat := lgetD 0 [1, 0, 2, 4, 3, 6, 5, 8, 7] i

/-- The angle of a point of a hexagon in units of 30 degrees. -/
def ang12 (n : Nat) : Nat :=
  cond (Nat.blt n 8) (Nat.mul 2 (Nat.sub n 2)) (Nat.add (Nat.mul 2 (Nat.sub n 8)) 1)

/-- The index of the height of a point of a hexagon: `h` for the upper one, `-h` for the lower one. -/
def hI (n : Nat) : Nat := cond (Nat.blt n 8) 0 1

/-- `√(1 - z²)`. -/
def rhoE (z : JExp) (b : Nat × Nat) : JExp := .sqrt (.add (.nat 1) (.neg (.mul z z))) b.1 b.2

/-- `2 - 2 s`. -/
def twoMinus (sx : JExp) : JExp := .add (.nat 2) (.neg (.add sx sx))

/-- `√(1 - a² - b²)` for the two coordinates of the second pole. -/
def wE (b : Nat × Nat) : JExp :=
  .sqrt (.add (.nat 1) (.neg (.add (.mul (.var 0 2) (.var 0 2)) (.mul (.var 1 2) (.var 1 2))))) b.1 b.2

/-- **The energy of the pair `(i, j)`**, `i < j`, in the gauge coordinates of the pair: `(2 - 2 <x_i, x_j>)^(-1/2)`.
The list `wit` has the witnesses of the roots. -/
noncomputable def pairExpW (i j : Nat) (wit : List (Nat × Nat)) : JExp :=
  cond (Nat.beq i 0)
    (cond (Nat.beq j 1)
      (.isqrt (.add (.nat 2) (.add (wE (wget wit 0)) (wE (wget wit 0)))) (wget wit 1).1 (wget wit 1).2)
      (.isqrt (twoMinus (.var 0 (hI j))) (wget wit 0).1 (wget wit 0).2))
    (cond (Nat.beq i 1)
      (cond (Nat.beq j 2)
        (.isqrt (twoMinus (.add (.mul (.var 0 2) (rhoE (.var 2 0) (wget wit 1)))
          (.neg (.mul (wE (wget wit 0)) (.var 2 0))))) (wget wit 2).1 (wget wit 2).2)
        (.isqrt (twoMinus (.add
          (.mul (rhoE (.var 2 (hI j)) (wget wit 1))
            (.add (.mul (.var 0 2) (.trig 3 (cosI (ang12 j)) (sinI (ang12 j))))
              (.mul (.var 1 2) (.trig 3 (sinI (ang12 j)) (negI (cosI (ang12 j)))))))
          (.neg (.mul (wE (wget wit 0)) (.var 2 (hI j)))))) (wget wit 2).1 (wget wit 2).2))
      (cond (Nat.beq i 2)
        (.isqrt (twoMinus (.add
          (.mul (.mul (rhoE (.var 0 0) (wget wit 0)) (rhoE (.var 1 (hI j)) (wget wit 1)))
            (.trig 2 (cosI (ang12 j)) (sinI (ang12 j))))
          (.mul (.var 0 0) (.var 1 (hI j))))) (wget wit 2).1 (wget wit 2).2)
        (.isqrt (twoMinus (.add
          (.mul (.mul (rhoE (.var 0 (hI i)) (wget wit 0)) (rhoE (.var 2 (hI j)) (wget wit 1)))
            (.add (.mul (.trig 1 (cosI (ang12 i)) (sinI (ang12 i))) (.trig 3 (cosI (ang12 j)) (sinI (ang12 j))))
              (.mul (.trig 1 (sinI (ang12 i)) (negI (cosI (ang12 i))))
                (.trig 3 (sinI (ang12 j)) (negI (cosI (ang12 j)))))))
          (.mul (.var 0 (hI i)) (.var 2 (hI j))))) (wget wit 2).1 (wget wit 2).2)))

/-! ## The slots of the monomials of degree 2, 3, 4 with their local variables -/

def slots2 : List (Nat × Nat × Nat) :=
  [(432, 0, 0), (433, 0, 1), (434, 1, 1), (438, 0, 2), (439, 1, 2), (444, 2, 2), (468, 0, 3), (469, 1, 3),
   (474, 2, 3), (504, 3, 3)]

def slots3 : List (Nat × Nat × Nat × Nat) :=
  [(648, 0, 0, 0), (649, 0, 0, 1), (650, 0, 1, 1), (651, 1, 1, 1), (654, 0, 0, 2), (655, 0, 1, 2),
   (656, 1, 1, 2), (660, 0, 2, 2), (661, 1, 2, 2), (666, 2, 2, 2), (684, 0, 0, 3), (685, 0, 1, 3),
   (686, 1, 1, 3), (690, 0, 2, 3), (691, 1, 2, 3), (696, 2, 2, 3), (720, 0, 3, 3), (721, 1, 3, 3),
   (726, 2, 3, 3), (756, 3, 3, 3)]

def slots4 : List (Nat × Nat × Nat × Nat × Nat) :=
  [(864, 0, 0, 0, 0), (865, 0, 0, 0, 1), (866, 0, 0, 1, 1), (867, 0, 1, 1, 1), (868, 1, 1, 1, 1),
   (870, 0, 0, 0, 2), (871, 0, 0, 1, 2), (872, 0, 1, 1, 2), (873, 1, 1, 1, 2), (876, 0, 0, 2, 2),
   (877, 0, 1, 2, 2), (878, 1, 1, 2, 2), (882, 0, 2, 2, 2), (883, 1, 2, 2, 2), (888, 2, 2, 2, 2),
   (900, 0, 0, 0, 3), (901, 0, 0, 1, 3), (902, 0, 1, 1, 3), (903, 1, 1, 1, 3), (906, 0, 0, 2, 3),
   (907, 0, 1, 2, 3), (908, 1, 1, 2, 3), (912, 0, 2, 2, 3), (913, 1, 2, 2, 3), (918, 2, 2, 2, 3),
   (936, 0, 0, 3, 3), (937, 0, 1, 3, 3), (938, 1, 1, 3, 3), (942, 0, 2, 3, 3), (943, 1, 2, 3, 3),
   (948, 2, 2, 3, 3), (972, 0, 3, 3, 3), (973, 1, 3, 3, 3), (978, 2, 3, 3, 3), (1008, 3, 3, 3, 3)]

/-! ## The terms of the centres -/

/-- A global index, with 25 for all indices from 25 on. -/
def cl (a : Nat) : Nat := cond (Nat.ble a 25) a 25

/-- The slot of the global monomial `D_a D_b`: `26 min + max`. -/
def key2 (a b : Nat) : Nat :=
  cond (Nat.ble (cl a) (cl b)) (Nat.add (Nat.mul 26 (cl a)) (cl b)) (Nat.add (Nat.mul 26 (cl b)) (cl a))

/-- The terms of degree 2 of a packed number `c` of a pair with the gauge coordinates `g`: the value of a slot
and the slot of the global monomial. -/
noncomputable def terms2 (w c : Nat) (g : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) []
    (fun t _ ih => (slot w c t.1, key2 (lgetD 25 g t.2.1) (lgetD 25 g t.2.2)) :: ih) slots2

/-- A term of degree 3 in front of a list, if its first global index is `a`. -/
def p3 (a v x y z : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  cond (Nat.beq x a) ((v, Nat.add (Nat.mul 26 y) z) :: l) l

/-- The six orders of a term of degree 3. -/
def tm3 (a v x y z : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  p3 a v x y z (p3 a v x z y (p3 a v y x z (p3 a v y z x (p3 a v z x y (p3 a v z y x l)))))

/-- The terms of degree 3 whose first global index is `a`, with the slot `26 y + z` of the other two indices,
for all six orders of the three variables. -/
noncomputable def terms3r (w c : Nat) (g : List Nat) (a : Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) []
    (fun t _ ih => tm3 a (slot w c t.1) (cl (lgetD 25 g t.2.1)) (cl (lgetD 25 g t.2.2.1))
      (cl (lgetD 25 g t.2.2.2)) ih) slots3

/-- The slot of an order of four local variables. -/
def k4 (a b c d : Nat) : Nat := Nat.add (Nat.add (Nat.add (Nat.mul 64 a) (Nat.mul 16 b)) (Nat.mul 4 c)) d

/-- The 24 orders of a term of degree 4. -/
def tm4 (v a b c d : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
    (v, k4 a b c d) ::
    (v, k4 a b d c) ::
    (v, k4 a c b d) ::
    (v, k4 a c d b) ::
    (v, k4 a d b c) ::
    (v, k4 a d c b) ::
    (v, k4 b a c d) ::
    (v, k4 b a d c) ::
    (v, k4 b c a d) ::
    (v, k4 b c d a) ::
    (v, k4 b d a c) ::
    (v, k4 b d c a) ::
    (v, k4 c a b d) ::
    (v, k4 c a d b) ::
    (v, k4 c b a d) ::
    (v, k4 c b d a) ::
    (v, k4 c d a b) ::
    (v, k4 c d b a) ::
    (v, k4 d a b c) ::
    (v, k4 d a c b) ::
    (v, k4 d b a c) ::
    (v, k4 d b c a) ::
    (v, k4 d c a b) ::
    (v, k4 d c b a) :: l

/-- The terms of degree 4, for all 24 orders of the four variables. -/
noncomputable def terms4 (w c : Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) []
    (fun t _ ih => tm4 (slot w c t.1) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 ih) slots4

/-- The sum of `v * 2^(64 k)` over the terms `(v, k)`. -/
noncomputable def scat : List (Nat × Nat) → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => Nat.add ih (Nat.shiftLeft t.1 (Nat.mul 64 t.2)))

/-- The sum of the values of the terms. -/
noncomputable def tot : List (Nat × Nat) → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => Nat.add ih t.1)

/-- The sum of the listed slots of a packed number. -/
noncomputable def rsumK (w c : Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun e _ ih => Nat.add ih (slot w c e))

def sl2 : List Nat := [432, 433, 434, 438, 439, 444, 468, 469, 474, 504]

def sl3 : List Nat :=
  [648, 649, 650, 651, 654, 655, 656, 660, 661, 666, 684, 685, 686, 690, 691, 696, 720, 721, 726, 756]

def sl4 : List Nat :=
  [864, 865, 866, 867, 868, 870, 871, 872, 873, 876, 877, 878, 882, 883, 888, 900, 901, 902, 903, 906, 907, 908,
   912, 913, 918, 936, 937, 938, 942, 943, 948, 972, 973, 978, 1008]

/-! ## The upper triangle of a matrix of E2 -/

/-- The test `t i s (X i (i + s))` for all entries of the upper triangle of order `n` that is stored in `rows`
with the slot width `w`. -/
noncomputable def triAll (w n rows : Nat) (t : Nat → Nat → Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih i off =>
      Nat.rec (motive := fun _ => Bool) true (fun s ihs => ihs && t i s (slot w rows (Nat.add off s)))
        (Nat.sub n i)
      && ih (Nat.succ i) (Nat.add off (Nat.sub n i))) n 0 0

/-! ## The pairs -/

/-- The data of a pair: the points, the witnesses of the roots, the claims (the packed numbers `cP`, `cN`, `cR`
of the coefficients of degree 2, 3, 4, the bound `n5` for the coefficients of degree 5 and the bound `K` of
order six), and the test of the quartic form: the number `A`, the scattered centres `MP`, `MN` and the two
instances of E2. -/
structure PairD where
  i : Nat
  j : Nat
  wit : List (Nat × Nat)
  cP : Nat
  cN : Nat
  cR : Nat
  n5 : Nat
  K : Nat
  A : Nat
  MP : Nat
  MN : Nat
  qp : CAP.PSD.Params
  rowsP : Nat
  colsP : Nat
  qm : CAP.PSD.Params
  rowsM : Nat
  colsM : Nat

/-- The test of an entry of a quartic matrix: `A + M'` for `sgn = true`, `A - M'` for `sgn = false`. An entry
off the diagonal is compared with the sum of the two slots of `M'` that belong to it. -/
def qEntry (a A MP MN : Nat) (sgn : Bool) (k s ent : Nat) : Bool :=
  cond (Nat.beq s 0)
    (Nat.beq (Nat.add (Nat.mul 2 ent) (slot 64 (cond sgn MN MP) (Nat.mul 17 k)))
      (Nat.add (Nat.add (Nat.shiftLeft 1 a) A) (slot 64 (cond sgn MP MN) (Nat.mul 17 k))))
    (Nat.beq
      (Nat.add (Nat.add (Nat.mul 2 ent) (slot 64 (cond sgn MN MP) (Nat.add (Nat.mul 17 k) s)))
        (slot 64 (cond sgn MN MP) (Nat.add (Nat.mul 17 k) (Nat.mul 16 s))))
      (Nat.add (Nat.add (Nat.shiftLeft 1 a) (slot 64 (cond sgn MP MN) (Nat.add (Nat.mul 17 k) s)))
        (slot 64 (cond sgn MP MN) (Nat.add (Nat.mul 17 k) (Nat.mul 16 s)))))

/-- **The quartic form of a pair**: the two matrices `A ± M'` are positive definite. -/
noncomputable def quartOk (w : Nat) (d : PairD) : Bool :=
  Nat.beq d.qp.n 16 && Nat.beq d.qm.n 16
    && Nat.beq d.MP (scat (terms4 w d.cP)) && Nat.beq d.MN (scat (terms4 w d.cN))
    && Nat.blt (tot (terms4 w d.cP)) (Nat.shiftLeft 1 64) && Nat.blt (tot (terms4 w d.cN)) (Nat.shiftLeft 1 64)
    && CAP.PSD.check d.qp d.rowsP d.colsP && CAP.PSD.check d.qm d.rowsM d.colsM
    && triAll d.qp.w 16 d.rowsP (qEntry d.qp.a d.A d.MP d.MN true)
    && triAll d.qm.w 16 d.rowsM (qEntry d.qm.a d.A d.MP d.MN false)

/-- **The checker of a pair**: the enclosures of the coefficients and the quartic form. -/
noncomputable def pairAll (par : Par) (tab : List T3) (d : PairD) : Bool :=
  pairOk par tab (pairExpW d.i d.j d.wit) d.cP d.cN d.cR d.n5 d.K && quartOk par.w d

/-! ## The forms of degree 2 and 3 -/

/-- The sum of the scattered terms of all pairs. -/
noncomputable def scatL (f : PairD → List (Nat × Nat)) : List PairD → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add ih (scat (f d)))

/-- The sum of the values of the terms of all pairs. -/
noncomputable def totL (f : PairD → List (Nat × Nat)) : List PairD → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add ih (tot (f d)))

/-- The data of the Hessian: the instance of E2 and the scattered centres. -/
structure HessD where
  Pp : CAP.PSD.Params
  rows : Nat
  cols : Nat
  SP : Nat
  SN : Nat

/-- The test of an entry of the matrix of the Hessian: `X_ab = 2000 c_ab - [a = b] 193 * 2^47`. -/
def hEntry (a SP SN : Nat) (i s ent : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.add ent (Nat.mul 2000 (slot 64 SN (Nat.add (Nat.mul 27 i) s))))
      (cond (Nat.beq s 0) 27162335252578304 0))
    (Nat.add (Nat.shiftLeft 1 (Nat.sub a 1)) (Nat.mul 2000 (slot 64 SP (Nat.add (Nat.mul 27 i) s))))

/-- **The Hessian.** -/
noncomputable def hessOk (w : Nat) (pairs : List PairD) (H : HessD) : Bool :=
  Nat.beq H.Pp.n 25
    && Nat.beq H.SP (scatL (fun d => terms2 w d.cP (gl d.i d.j)) pairs)
    && Nat.beq H.SN (scatL (fun d => terms2 w d.cN (gl d.i d.j)) pairs)
    && Nat.blt (totL (fun d => terms2 w d.cP (gl d.i d.j)) pairs) (Nat.shiftLeft 1 64)
    && Nat.blt (totL (fun d => terms2 w d.cN (gl d.i d.j)) pairs) (Nat.shiftLeft 1 64)
    && CAP.PSD.check H.Pp H.rows H.cols
    && triAll H.Pp.w 25 H.rows (hEntry H.Pp.a H.SP H.SN)

/-- The data of the cubic form: the instance of E2, the number `A3` and the rows of the tensor of the centres. -/
structure CubD where
  Pp : CAP.PSD.Params
  rows : Nat
  cols : Nat
  A3 : Nat
  TP : List Nat
  TN : List Nat

/-- `∑_{k < 676} X_k Y_k` for two packed numbers. -/
noncomputable def dotK (X Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.add ih (Nat.mul (slot 64 X k) (slot 64 Y k))) 676

/-- The test of an entry of the matrix of the cubic form: `X_aa = A3 - (T Tᵗ)_aa`, `X_ab = -2 (T Tᵗ)_ab`. -/
noncomputable def cEntry (a A3 : Nat) (TP TN : List Nat) (i s ent : Nat) : Bool :=
  cond (Nat.beq s 0)
    (Nat.beq
      (Nat.add ent (Nat.add (dotK (lgetD 0 TP i) (lgetD 0 TP i)) (dotK (lgetD 0 TN i) (lgetD 0 TN i))))
      (Nat.add (Nat.add (Nat.shiftLeft 1 (Nat.sub a 1)) A3)
        (Nat.add (dotK (lgetD 0 TP i) (lgetD 0 TN i)) (dotK (lgetD 0 TN i) (lgetD 0 TP i)))))
    (Nat.beq
      (Nat.add ent (Nat.mul 2 (Nat.add (dotK (lgetD 0 TP i) (lgetD 0 TP (Nat.add i s)))
        (dotK (lgetD 0 TN i) (lgetD 0 TN (Nat.add i s))))))
      (Nat.add (Nat.shiftLeft 1 (Nat.sub a 1))
        (Nat.mul 2 (Nat.add (dotK (lgetD 0 TP i) (lgetD 0 TN (Nat.add i s)))
          (dotK (lgetD 0 TN i) (lgetD 0 TP (Nat.add i s)))))))

/-- The rows of the tensor are the scattered centres. -/
noncomputable def cubRows (w : Nat) (pairs : List PairD) (C : CubD) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun a ih => ih
      && Nat.beq (lgetD 0 C.TP a) (scatL (fun d => terms3r w d.cP (gl d.i d.j) a) pairs)
      && Nat.beq (lgetD 0 C.TN a) (scatL (fun d => terms3r w d.cN (gl d.i d.j) a) pairs)) 25

/-- The sum of the slots of degree 3 of all pairs. -/
noncomputable def tot3 (w : Nat) (f : PairD → Nat) : List PairD → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add ih (rsumK w (f d) sl3))

/-- **The cubic form.** -/
noncomputable def cubOk (w : Nat) (pairs : List PairD) (C : CubD) : Bool :=
  Nat.beq C.Pp.n 25
    && Nat.ble (Nat.mul 1000000 C.A3) (Nat.pow (Nat.mul 30234 (Nat.shiftLeft 1 48)) 2)
    && Nat.blt (Nat.mul 6 (tot3 w (fun d => d.cP) pairs)) (Nat.shiftLeft 1 64)
    && Nat.blt (Nat.mul 6 (tot3 w (fun d => d.cN) pairs)) (Nat.shiftLeft 1 64)
    && cubRows w pairs C
    && CAP.PSD.check C.Pp C.rows C.cols
    && triAll C.Pp.w 25 C.rows (cEntry C.Pp.a C.A3 C.TP C.TN)

/-! ## The rows and the budgets -/

/-- The bound of the quartic remainder of a pair, in units of `2^-48 / (24 * 125²)`. -/
noncomputable def sInt (w : Nat) (d : PairD) : Nat :=
  Nat.add (Nat.mul d.A 15625)
    (Nat.mul 24 (Nat.add (Nat.add (Nat.mul (rsumK w d.cR sl4) 15625) (Nat.mul d.n5 125)) d.K))

/-- The sum of the bounds of the pairs that contain the point `n`. -/
noncomputable def rowInt (w n : Nat) : List PairD → Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun d _ ih => Nat.add ih (cond (Nat.beq d.i n || Nat.beq d.j n) (sInt w d) 0))

/-- **The rows**: `2 ∑_{d ∋ n} s_d ≤ 147` for every point `n`. -/
noncomputable def rowsOk (w : Nat) (pairs : List PairD) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun n ih => ih && Nat.ble (Nat.mul 2 (rowInt w n pairs)) (Nat.mul 55125000 (Nat.shiftLeft 1 48))) 14

/-- The sum of the radii of the listed slots over all pairs. -/
noncomputable def radL (w : Nat) (l : List Nat) : List PairD → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add ih (rsumK w d.cR l))

/-- **The budgets**: the radii of degree 2 sum to at most `2^48 / 20000`, those of degree 3 to at most
`2^48 / 1000`. -/
noncomputable def budgetOk (w : Nat) (pairs : List PairD) : Bool :=
  Nat.ble (Nat.mul 20000 (radL w sl2 pairs)) (Nat.shiftLeft 1 48)
    && Nat.ble (Nat.mul 1000 (radL w sl3 pairs)) (Nat.shiftLeft 1 48)

/-- **The assembly**: all tests of the three forms. -/
noncomputable def formsOk (w : Nat) (pairs : List PairD) (H : HessD) (C : CubD) : Bool :=
  hessOk w pairs H && cubOk w pairs C && rowsOk w pairs && budgetOk w pairs

end N14.Local
