module

public import CAP.Core.Packed

/-!
# E6, interval arithmetic: the checker (`Init` only)

**Statement.** Let a real number be given by a program, that is, by a finite sequence of sums,
differences, products, reciprocals and square roots that starts from the inputs and from dyadic
constants. If every input lies in its given ball, then the value of each claimed register lies in
its claimed interval.

**Numbers.** A real number `x` is enclosed by a *ball* `(b, r)` of two natural numbers: with the
precision `p` and the bias `B = 2 ^ (W - 1)`,

  `|x * 2 ^ p - (b - B)| ≤ r`.

The operations split the midpoint `b - B` into its positive part `b - B` and its negative part
`B - b` (truncated differences), one of which vanishes. No operation requires a bound on `b`.

**Programs.** Instruction number `j` defines register number `nin + j` from earlier registers; the
registers `0, …, nin - 1` are the inputs. All registers are stored in one natural number `R`:
register `i` has its midpoint in slot `2 * i` and its radius in slot `2 * i + 1`, with slot width
`W`.

**Witnesses.** A square root uses a witness `t` with `t ^ 2 ≤ m * 2 ^ p < (t + 1) ^ 2` for the
midpoint `m`. The checker verifies these two inequalities and does not compute a root. A
reciprocal is one division of natural numbers.

The checker is bit-exact with `certgen/interval.py`.
-/

@[expose] public section

namespace CAP.Interval

/-- Parameters of a program. -/
structure Params where
  /-- precision: a midpoint `m` stands for `m / 2 ^ p` -/
  p : Nat
  /-- slot width of the registers; the bias is `2 ^ (W - 1)` -/
  W : Nat

/-- An instruction defines the next register. -/
inductive Instr where
  /-- the integer `n` -/
  | nat (n : Nat)
  /-- the dyadic number `(b - B) / 2 ^ p` -/
  | cst (b : Nat)
  /-- the sum of two registers -/
  | add (i j : Nat)
  /-- the difference of two registers -/
  | sub (i j : Nat)
  /-- the product of two registers -/
  | mul (i j : Nat)
  /-- the reciprocal of a register whose ball does not contain `0` -/
  | inv (i : Nat)
  /-- the square root of a register whose ball is positive; it uses one witness -/
  | sqrt (i : Nat)

/-! ## Balls

Every operation returns the midpoint, the radius, and the flag of its test. -/

/-- The sum of two balls. -/
def addB (B b1 r1 b2 r2 : Nat) : Nat × Nat × Bool :=
  (Nat.sub (Nat.add b1 b2) B, Nat.add r1 r2, Nat.ble B (Nat.add b1 b2))

/-- The difference of two balls. -/
def subB (B b1 r1 b2 r2 : Nat) : Nat × Nat × Bool :=
  (Nat.sub (Nat.add b1 B) b2, Nat.add r1 r2, Nat.ble b2 (Nat.add b1 B))

/-- The product of two balls. The midpoint is the product of the midpoints, truncated towards
zero; the radius bounds `|m₁| r₂ + |m₂| r₁ + r₁ r₂` and the two truncations. -/
def mulB (p B b1 r1 b2 r2 : Nat) : Nat × Nat × Bool :=
  let p1 := Nat.sub b1 B
  let n1 := Nat.sub B b1
  let p2 := Nat.sub b2 B
  let n2 := Nat.sub B b2
  let U := Nat.add B (Nat.shiftRight (Nat.add (Nat.mul p1 p2) (Nat.mul n1 n2)) p)
  let off := Nat.shiftRight (Nat.add (Nat.mul p1 n2) (Nat.mul n1 p2)) p
  (Nat.sub U off,
    Nat.add (Nat.shiftRight (Nat.add (Nat.add (Nat.mul (Nat.add p1 n1) r2) (Nat.mul (Nat.add p2 n2) r1))
      (Nat.mul r1 r2)) p) 2,
    Nat.ble off U)

/-- The reciprocal of a ball that does not contain `0`. With `m` the midpoint and `a = |m| - r`,
the midpoint is `2 ^ (2 * p) / |m|` with the sign of `m`, and the radius bounds
`2 ^ (2 * p) * r / (a * |m|)` and the two truncations. A division by `0` yields `0`. -/
def invB (p B b r : Nat) : Nat × Nat × Bool :=
  let mp := Nat.sub b B
  let mn := Nat.sub B b
  let am := Nat.add mp mn
  let S2 := Nat.shiftLeft 1 (Nat.mul 2 p)
  let U := Nat.add B (Nat.div S2 mp)
  let off := Nat.div S2 mn
  (Nat.sub U off, Nat.add (Nat.div (Nat.mul S2 r) (Nat.mul (Nat.sub am r) am)) 2,
    Nat.blt r am && Nat.ble off U)

/-- The square root of a positive ball, with the witness `t`: `t ^ 2 ≤ m * 2 ^ p < (t + 1) ^ 2` for
the midpoint `m`. The radius bounds `2 ^ p * r / t` and the two truncations. -/
def sqrtB (p B b r t : Nat) : Nat × Nat × Bool :=
  let mp := Nat.sub b B
  let n := Nat.shiftLeft mp p
  (Nat.add B t, Nat.add (Nat.div (Nat.shiftLeft r p) t) 2,
    Nat.blt r mp && Nat.ble (Nat.mul t t) n && Nat.blt n (Nat.mul (Nat.succ t) (Nat.succ t)))

/-- A further condition for a ball. -/
def withFlag (x : Nat × Nat × Bool) (g : Bool) : Nat × Nat × Bool := (x.1, x.2.1, x.2.2 && g)

/-! ## Balls with flags

A ball together with the conjunction of the flags of all operations that produced it. The
checkers that compose several operations for one register (`CAP.Root`) use these. -/

/-- The sum of two balls with flags. -/
def fadd (B : Nat) (x y : Nat × Nat × Bool) : Nat × Nat × Bool :=
  withFlag (addB B x.1 x.2.1 y.1 y.2.1) (x.2.2 && y.2.2)

/-- The difference of two balls with flags. -/
def fsub (B : Nat) (x y : Nat × Nat × Bool) : Nat × Nat × Bool :=
  withFlag (subB B x.1 x.2.1 y.1 y.2.1) (x.2.2 && y.2.2)

/-- The product of two balls with flags. -/
def fmul (p B : Nat) (x y : Nat × Nat × Bool) : Nat × Nat × Bool :=
  withFlag (mulB p B x.1 x.2.1 y.1 y.2.1) (x.2.2 && y.2.2)

/-- The reciprocal of a ball with a flag. -/
def finv (p B : Nat) (x : Nat × Nat × Bool) : Nat × Nat × Bool :=
  withFlag (invB p B x.1 x.2.1) x.2.2

/-- The square root of a ball with a flag, with the witness `t`. -/
def fsqrt (p B : Nat) (x : Nat × Nat × Bool) (t : Nat) : Nat × Nat × Bool :=
  withFlag (sqrtB p B x.1 x.2.1 t) x.2.2

/-! ## Programs -/

/-- The ball that an instruction defines, and the witnesses that remain. `R` holds the `k`
registers that are defined so far. -/
noncomputable def step (P : Params) (B R k : Nat) (wit : List Nat) (ins : Instr) :
    (Nat × Nat × Bool) × List Nat :=
  Instr.rec (motive := fun _ => (Nat × Nat × Bool) × List Nat)
    (fun n => ((Nat.add B (Nat.shiftLeft n P.p), 0, true), wit))
    (fun b => ((b, 0, true), wit))
    (fun i j => (withFlag (addB B (slot P.W R (Nat.mul 2 i)) (slot P.W R (Nat.succ (Nat.mul 2 i)))
        (slot P.W R (Nat.mul 2 j)) (slot P.W R (Nat.succ (Nat.mul 2 j)))) (Nat.blt i k && Nat.blt j k), wit))
    (fun i j => (withFlag (subB B (slot P.W R (Nat.mul 2 i)) (slot P.W R (Nat.succ (Nat.mul 2 i)))
        (slot P.W R (Nat.mul 2 j)) (slot P.W R (Nat.succ (Nat.mul 2 j)))) (Nat.blt i k && Nat.blt j k), wit))
    (fun i j => (withFlag (mulB P.p B (slot P.W R (Nat.mul 2 i)) (slot P.W R (Nat.succ (Nat.mul 2 i)))
        (slot P.W R (Nat.mul 2 j)) (slot P.W R (Nat.succ (Nat.mul 2 j)))) (Nat.blt i k && Nat.blt j k), wit))
    (fun i => (withFlag (invB P.p B (slot P.W R (Nat.mul 2 i)) (slot P.W R (Nat.succ (Nat.mul 2 i))))
        (Nat.blt i k), wit))
    (fun i => List.rec (motive := fun _ => (Nat × Nat × Bool) × List Nat) ((0, 0, false), List.nil)
      (fun t tl _ => (withFlag (sqrtB P.p B (slot P.W R (Nat.mul 2 i)) (slot P.W R (Nat.succ (Nat.mul 2 i))) t)
        (Nat.blt i k), tl)) wit)
    ins

/-- The loop over the instructions. The state consists of the registers `R`, their number `k` and
the remaining witnesses. A new register is stored if its test holds and if its midpoint and its
radius fit into a slot. At the end the test `fin` is applied to the registers. -/
noncomputable def run (P : Params) (B : Nat) (fin : Nat → Nat → Bool) :
    List Instr → Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → Bool)
    (fun R k _ => fin R k)
    (fun ins _ ih R k wit =>
      Bool.rec (motive := fun _ => Bool) false
        (ih (Nat.add R (Nat.shiftLeft
            (Nat.add (step P B R k wit ins).1.1 (Nat.shiftLeft (step P B R k wit ins).1.2.1 P.W))
            (Nat.mul (Nat.mul 2 P.W) k)))
          (Nat.succ k) (step P B R k wit ins).2)
        ((step P B R k wit ins).1.2.2 &&
          Nat.beq (Nat.shiftRight (Nat.lor (step P B R k wit ins).1.1 (step P B R k wit ins).1.2.1) P.W) 0))

/-- The claims `(i, lo, hi)`: the ball of register `i` lies in `[lo - B, hi - B]`. -/
noncomputable def claimsOk (P : Params) (R k : Nat) : List (Nat × Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih =>
      Nat.blt c.1 k &&
      Nat.ble (Nat.add c.2.1 (slot P.W R (Nat.succ (Nat.mul 2 c.1)))) (slot P.W R (Nat.mul 2 c.1)) &&
      Nat.ble (Nat.add (slot P.W R (Nat.mul 2 c.1)) (slot P.W R (Nat.succ (Nat.mul 2 c.1)))) c.2.2 && ih)

/-- The checker of E6. `R0` holds the balls of the `nin` inputs. -/
noncomputable def check (P : Params) (prog : List Instr) (wit : List Nat) (R0 nin : Nat)
    (claims : List (Nat × Nat × Nat)) : Bool :=
  Nat.ble 1 P.W && Nat.beq (Nat.shiftRight R0 (Nat.mul (Nat.mul 2 P.W) nin)) 0 &&
  run P (Nat.shiftLeft 1 (Nat.sub P.W 1)) (fun R k => claimsOk P R k claims) prog R0 nin wit

end CAP.Interval
