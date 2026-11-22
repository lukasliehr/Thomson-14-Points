module

public import CAP.Interval.Kernel

/-!
# E6, interval arithmetic: the expression of a register

A program defines every register by one operation on earlier registers. A statement about a
register needs the register as an expression in the inputs and in constants. An expression is a
tree (`Tm`). The checker `agrees prog nin t i` tests that the tree `t` is the expression of
register `i` of a program with `nin` inputs: an input is the tree `var`, and for a later register
the root of `t` is the operation of its instruction and the subtrees are the expressions of the
operands. The tree is part of the certificate. The checker does not compute it.

The soundness theorem is `CAP.Interval.agrees_sound` in `CAP/Interval/TermSound.lean`. The same
construction for the programs of E4 is in `CAP/NumberField/Term.lean`.
-/

@[expose] public section

namespace CAP.Interval

/-- Expressions in the inputs and in constants. -/
inductive Tm where
  | var (i : Nat)
  | nat (n : Nat)
  | cst (b : Nat)
  | add (a b : Tm)
  | sub (a b : Tm)
  | mul (a b : Tm)
  | inv (a : Tm)
  | sqrt (a : Tm)

/-- Instruction `i` of a program; `.nat 0` beyond its end. -/
noncomputable def nth : Nat → List Instr → Instr :=
  Nat.rec (motive := fun _ => List Instr → Instr)
    (fun l => List.rec (motive := fun _ => Instr) (.nat 0) (fun a _ _ => a) l)
    (fun _ ih l => List.rec (motive := fun _ => Instr) (.nat 0) (fun _ t _ => ih t) l)

/-- The instruction is the integer `n`. -/
noncomputable def isNat (n : Nat) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun m => Nat.beq m n) (fun _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ => false) ins

/-- The instruction is the constant `b`. -/
noncomputable def isCst (b : Nat) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun _ => false) (fun c => Nat.beq c b) (fun _ _ => false)
    (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ => false) ins

/-- The instruction is a sum, and `f` accepts its operands. -/
noncomputable def isAdd (f : Nat → Nat → Bool) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun j k => f j k)
    (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ => false) ins

/-- The instruction is a difference, and `f` accepts its operands. -/
noncomputable def isSub (f : Nat → Nat → Bool) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ _ => false)
    (fun j k => f j k) (fun _ _ => false) (fun _ => false) (fun _ => false) ins

/-- The instruction is a product, and `f` accepts its operands. -/
noncomputable def isMul (f : Nat → Nat → Bool) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun j k => f j k) (fun _ => false) (fun _ => false) ins

/-- The instruction is a reciprocal, and `f` accepts its operand. -/
noncomputable def isInv (f : Nat → Bool) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ _ => false) (fun j => f j) (fun _ => false) ins

/-- The instruction is a square root, and `f` accepts its operand. -/
noncomputable def isSqrt (f : Nat → Bool) (ins : Instr) : Bool :=
  Instr.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun j => f j) ins

/-- The operands `j`, `k` of register `i` are earlier registers with the expressions that `fa`,
`fb` test. -/
noncomputable def both (fa fb : Nat → Bool) (i j k : Nat) : Bool :=
  Nat.blt j i && (Nat.blt k i && (fa j && fb k))

/-- The operand `j` of register `i` is an earlier register with the expression that `fa` tests. -/
noncomputable def one (fa : Nat → Bool) (i j : Nat) : Bool :=
  Nat.blt j i && fa j

/-- `agrees prog nin t i`: the tree `t` is the expression of register `i` of the program with
`nin` inputs. -/
noncomputable def agrees (prog : List Instr) (nin : Nat) : Tm → Nat → Bool :=
  Tm.rec (motive := fun _ => Nat → Bool)
    (fun k i => Nat.beq i k && Nat.blt k nin)
    (fun n i => Nat.ble nin i && isNat n (nth (Nat.sub i nin) prog))
    (fun b i => Nat.ble nin i && isCst b (nth (Nat.sub i nin) prog))
    (fun _ _ fa fb i => Nat.ble nin i && isAdd (both fa fb i) (nth (Nat.sub i nin) prog))
    (fun _ _ fa fb i => Nat.ble nin i && isSub (both fa fb i) (nth (Nat.sub i nin) prog))
    (fun _ _ fa fb i => Nat.ble nin i && isMul (both fa fb i) (nth (Nat.sub i nin) prog))
    (fun _ fa i => Nat.ble nin i && isInv (one fa i) (nth (Nat.sub i nin) prog))
    (fun _ fa i => Nat.ble nin i && isSqrt (one fa i) (nth (Nat.sub i nin) prog))

end CAP.Interval
