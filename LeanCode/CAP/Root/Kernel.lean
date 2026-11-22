module

public import CAP.Interval.Kernel

/-!
# E7, isolated zeros: the checker (`Init` only)

**Statement.** Let `F` be a real function of one variable that is given by a program of
`CAP.Interval` (sums, differences, products, reciprocals, square roots), and let `g = F` (`c = 0`)
or `g = F'` (`c = 1`). Let `I` be a ball and let `a < b` be two dyadic points of `I`. Then `g` has
exactly one zero in `I`, and this zero lies between `a` and `b`.

**Method.** The checker evaluates the program with *jets*: every register consists of three balls,
which enclose the value, the first derivative and the second derivative of the register as a
function of the variable. The rules for the derivatives are those of calculus, applied to balls
with the operations of `CAP.Interval`. Three evaluations are made:

* on `I`, where the ball of `g'` has to be positive;
* at `a`, where the ball of `g` has to be negative;
* at `b`, where the ball of `g` has to be positive.

**Data.** A register has six slots of width `W`: midpoint and radius of the value, of the first
and of the second derivative. Register `0` is the variable, with the derivatives `1` and `0`.
The witnesses of the square roots are given separately for each of the three evaluations.

The checker is bit-exact with `certgen/root.py`.
-/

@[expose] public section

namespace CAP.Root

open CAP.Interval

/-- A jet: the balls of the value, of the first and of the second derivative, each with a flag. -/
abbrev Jet := (Nat × Nat × Bool) × (Nat × Nat × Bool) × (Nat × Nat × Bool)

/-- `(x + y)'' = x'' + y''` -/
def jadd (B : Nat) (x y : Jet) : Jet :=
  (fadd B x.1 y.1, fadd B x.2.1 y.2.1, fadd B x.2.2 y.2.2)

/-- `(x - y)'' = x'' - y''` -/
def jsub (B : Nat) (x y : Jet) : Jet :=
  (fsub B x.1 y.1, fsub B x.2.1 y.2.1, fsub B x.2.2 y.2.2)

/-- `(x y)' = x' y + x y'` and `(x y)'' = x'' y + x' y' + x' y' + x y''` -/
def jmul (p B : Nat) (x y : Jet) : Jet :=
  (fmul p B x.1 y.1,
    fadd B (fmul p B x.2.1 y.1) (fmul p B x.1 y.2.1),
    fadd B (fadd B (fadd B (fmul p B x.2.2 y.1) (fmul p B x.2.1 y.2.1)) (fmul p B x.2.1 y.2.1))
      (fmul p B x.1 y.2.2))

/-- With `w = 1 / x`: `w' = - x' w w` and `w'' = (x' w w) (x' w) + (x' w w) (x' w) - x'' w w`. -/
def jinv (p B : Nat) (x : Jet) : Jet :=
  (finv p B x.1,
    fsub B (B, 0, true) (fmul p B x.2.1 (fmul p B (finv p B x.1) (finv p B x.1))),
    fsub B
      (fadd B
        (fmul p B (fmul p B x.2.1 (fmul p B (finv p B x.1) (finv p B x.1))) (fmul p B x.2.1 (finv p B x.1)))
        (fmul p B (fmul p B x.2.1 (fmul p B (finv p B x.1) (finv p B x.1))) (fmul p B x.2.1 (finv p B x.1))))
      (fmul p B x.2.2 (fmul p B (finv p B x.1) (finv p B x.1))))

/-- The ball of `1 / (2 s)` for the square root `s` of the value of `x`. -/
def halfInv (p B : Nat) (x : Jet) (t : Nat) : Nat × Nat × Bool :=
  fmul p B (Nat.add B (Nat.shiftLeft 1 (Nat.sub p 1)), 0, true) (finv p B (fsqrt p B x.1 t))

/-- With `s = sqrt x` and `h = 1 / (2 s)`: `s' = x' h` and `s'' = x'' h - (x' h) (x' h) / s`. -/
def jsqrt (p B : Nat) (x : Jet) (t : Nat) : Jet :=
  (fsqrt p B x.1 t,
    fmul p B x.2.1 (halfInv p B x t),
    fsub B (fmul p B x.2.2 (halfInv p B x t))
      (fmul p B (fmul p B (fmul p B x.2.1 (halfInv p B x t)) (fmul p B x.2.1 (halfInv p B x t)))
        (finv p B (fsqrt p B x.1 t))))

/-- Register `i` of the packed registers `R`. -/
def rdJ (W R i : Nat) : Jet :=
  ((slot W R (Nat.mul 6 i), slot W R (Nat.add (Nat.mul 6 i) 1), true),
    (slot W R (Nat.add (Nat.mul 6 i) 2), slot W R (Nat.add (Nat.mul 6 i) 3), true),
    (slot W R (Nat.add (Nat.mul 6 i) 4), slot W R (Nat.add (Nat.mul 6 i) 5), true))

/-- The six slots of a jet as one number. -/
def packJ (W : Nat) (x : Jet) : Nat :=
  Nat.add x.1.1 (Nat.shiftLeft (Nat.add x.1.2.1 (Nat.shiftLeft (Nat.add x.2.1.1 (Nat.shiftLeft
    (Nat.add x.2.1.2.1 (Nat.shiftLeft (Nat.add x.2.2.1 (Nat.shiftLeft x.2.2.2.1 W)) W)) W)) W)) W)

/-- The three flags of a jet hold, and its six numbers fit into a slot. -/
def okJ (W : Nat) (x : Jet) : Bool :=
  x.1.2.2 && x.2.1.2.2 && x.2.2.2.2 &&
  Nat.beq (Nat.shiftRight (Nat.lor (Nat.lor (Nat.lor x.1.1 x.1.2.1) (Nat.lor x.2.1.1 x.2.1.2.1))
    (Nat.lor x.2.2.1 x.2.2.2.1)) W) 0

/-- The jet that an instruction defines, the test of its indices, and the remaining witnesses. -/
noncomputable def stepJ (P : Params) (B R k : Nat) (wit : List Nat) (ins : Instr) :
    (Jet × Bool) × List Nat :=
  Instr.rec (motive := fun _ => (Jet × Bool) × List Nat)
    (fun n => ((((Nat.add B (Nat.shiftLeft n P.p), 0, true), (B, 0, true), (B, 0, true)), true), wit))
    (fun b => ((((b, 0, true), (B, 0, true), (B, 0, true)), true), wit))
    (fun i j => ((jadd B (rdJ P.W R i) (rdJ P.W R j), Nat.blt i k && Nat.blt j k), wit))
    (fun i j => ((jsub B (rdJ P.W R i) (rdJ P.W R j), Nat.blt i k && Nat.blt j k), wit))
    (fun i j => ((jmul P.p B (rdJ P.W R i) (rdJ P.W R j), Nat.blt i k && Nat.blt j k), wit))
    (fun i => ((jinv P.p B (rdJ P.W R i), Nat.blt i k), wit))
    (fun i => List.rec (motive := fun _ => (Jet × Bool) × List Nat)
      ((((0, 0, false), (0, 0, false), (0, 0, false)), false), List.nil)
      (fun t tl _ => ((jsqrt P.p B (rdJ P.W R i) t, Nat.blt i k), tl)) wit)
    ins

/-- The loop over the instructions, as in `CAP.Interval.run`, with registers of six slots. -/
noncomputable def runJ (P : Params) (B : Nat) (fin : Nat → Nat → Bool) :
    List Instr → Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → Bool)
    (fun R k _ => fin R k)
    (fun ins _ ih R k wit =>
      Bool.rec (motive := fun _ => Bool) false
        (ih (Nat.add R (Nat.shiftLeft (packJ P.W (stepJ P B R k wit ins).1.1) (Nat.mul (Nat.mul 6 P.W) k)))
          (Nat.succ k) (stepJ P B R k wit ins).2)
        (okJ P.W (stepJ P B R k wit ins).1.1 && (stepJ P B R k wit ins).1.2))

/-- The ball of the derivative of order `c` of register `i` is positive. -/
def posAt (W B R i c : Nat) : Bool :=
  Nat.ble (Nat.add (Nat.succ B) (slot W R (Nat.succ (Nat.add (Nat.mul 6 i) (Nat.mul 2 c)))))
    (slot W R (Nat.add (Nat.mul 6 i) (Nat.mul 2 c)))

/-- The ball of the derivative of order `c` of register `i` is negative. -/
def negAt (W B R i c : Nat) : Bool :=
  Nat.ble (Nat.succ (Nat.add (slot W R (Nat.add (Nat.mul 6 i) (Nat.mul 2 c)))
    (slot W R (Nat.succ (Nat.add (Nat.mul 6 i) (Nat.mul 2 c)))))) B

/-- The register of the variable in the ball `(xb, xr)`: the derivatives are `1` and `0`. -/
def initJ (P : Params) (B xb xr : Nat) : Nat :=
  packJ P.W ((xb, xr, true), (Nat.add B (Nat.shiftLeft 1 P.p), 0, true), (B, 0, true))

/-- The checker of E7 for the derivative of order `c ≤ 1` of register `k`: the ball `(cb, cr)` is
the interval `I`, and `ab`, `bb` are the midpoints of the points `a < b` of `I`. -/
noncomputable def check (P : Params) (prog : List Instr) (k c cb cr ab bb : Nat)
    (witI witA witB : List Nat) : Bool :=
  Nat.ble 1 P.p && Nat.ble (Nat.add P.p 2) P.W && Nat.ble c 1 &&
  Nat.beq (Nat.shiftRight (Nat.lor (Nat.lor cb cr) (Nat.lor ab bb)) P.W) 0 &&
  Nat.ble cb (Nat.add ab cr) && Nat.blt ab bb && Nat.ble bb (Nat.add cb cr) &&
  runJ P (Nat.shiftLeft 1 (Nat.sub P.W 1))
    (fun R n => Nat.blt k n && posAt P.W (Nat.shiftLeft 1 (Nat.sub P.W 1)) R k (Nat.succ c))
    prog (initJ P (Nat.shiftLeft 1 (Nat.sub P.W 1)) cb cr) 1 witI &&
  runJ P (Nat.shiftLeft 1 (Nat.sub P.W 1))
    (fun R n => Nat.blt k n && negAt P.W (Nat.shiftLeft 1 (Nat.sub P.W 1)) R k c)
    prog (initJ P (Nat.shiftLeft 1 (Nat.sub P.W 1)) ab 0) 1 witA &&
  runJ P (Nat.shiftLeft 1 (Nat.sub P.W 1))
    (fun R n => Nat.blt k n && posAt P.W (Nat.shiftLeft 1 (Nat.sub P.W 1)) R k c)
    prog (initJ P (Nat.shiftLeft 1 (Nat.sub P.W 1)) bb 0) 1 witB

end CAP.Root
