module

public meta import Lean.Elab.Term

/-!
# E14, certificate transport: large numerals

Lean reads a numeral `0x…` digit by digit, with one multiplication of the accumulated number per
digit. The time is quadratic in the length of the numeral: on the compute server, 800 kB of
hexadecimal digits take 1.2 s as 1000 numerals and 101 s as 2 numerals.

The term `hex% "…"` denotes the same natural number as `0x…`, but it is read by divide and
conquer: the digit string is cut into pieces of 15 digits, each of which is a machine word, and
the values of two halves are combined by one shift. The time is linear in the length up to a
logarithmic factor.

This module forms a library of its own, which Lake compiles to native code
(`precompileModules`). A leaf that is compiled with the option `--load-dynlib` for this library
runs the compiled reader; without the option the same program is interpreted, which is
several times slower.

The elaborator only produces a `Nat` literal. It is not part of the trusted base: the kernel
checks every theorem about the resulting literal, and the literal can be inspected with `#print`.

This is a file of Lean's module system. Its definitions are `meta`: they run while a leaf is
elaborated, and a leaf that imports the file can use the notation.
-/

public meta section

open Lean Elab Term

namespace CAP.Transport

/-- The value of a hexadecimal digit given by its byte, or `16` for another byte. -/
@[inline] def digit (c : UInt8) : UInt64 :=
  if 48 ≤ c && c ≤ 57 then (c - 48).toUInt64
  else if 97 ≤ c && c ≤ 102 then (c - 87).toUInt64
  else if 65 ≤ c && c ≤ 70 then (c - 55).toUInt64
  else 16

/-- The number with the digits `b[lo], …, b[hi - 1]` for `hi - lo ≤ 15`, as a machine word; the
second component is `false` if a byte is not a hexadecimal digit. -/
def word (b : ByteArray) (lo hi : Nat) : UInt64 × Bool := Id.run do
  let mut v : UInt64 := 0
  let mut ok := true
  for i in [lo:hi] do
    let d := digit (b.get! i)
    if d == 16 then ok := false
    v := (v <<< 4) ||| d
  return (v, ok)

/-- The number whose hexadecimal digits are the bytes `b[lo], …, b[hi - 1]`, most significant
digit first; `none` if a byte is not a hexadecimal digit. -/
partial def hexValue (b : ByteArray) (lo hi : Nat) : Option Nat :=
  if hi - lo ≤ 15 then
    let (v, ok) := word b lo hi
    if ok then some v.toNat else none
  else
    let mid := (lo + hi) / 2
    match hexValue b lo mid, hexValue b mid hi with
    | some x, some y => some ((x <<< (4 * (hi - mid))) ||| y)
    | _, _ => none

/-- `hex% "1f"` is the natural number `0x1f`. -/
syntax (name := hexNat) "hex% " str : term

@[term_elab hexNat] def elabHexNat : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  let b := s.toUTF8
  if b.size == 0 then throwError "hex%: empty numeral"
  let some n := hexValue b 0 b.size | throwError "hex%: not a hexadecimal numeral"
  return mkRawNatLit n

end CAP.Transport
