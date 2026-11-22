module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CAP.Interval.Sound
public import CAP.Root.Kernel

/-!
# E7, isolated zeros: jets

A *real jet* is a triple of real numbers: a value, a first and a second derivative. The file
contains

* the real jets `jden` that the instructions define, with the formulas of the checker;
* `jadd_sound`, …, `jsqrt_sound`: the jets of the checker enclose the real jets;
* `hasDeriv_mul2`, `hasDeriv_inv2`, `hasDeriv_sqrt2`: the formulas for the first and the second
  component are the derivatives of the first and of the second component.
-/

@[expose] public section

namespace CAP.Root

open CAP.Interval

/-- A real jet: value, first derivative, second derivative. -/
abbrev RJ := ℝ × ℝ × ℝ

/-- The jet of a product. -/
def rmul (x y : RJ) : RJ :=
  (x.1 * y.1, x.2.1 * y.1 + x.1 * y.2.1, x.2.2 * y.1 + x.2.1 * y.2.1 + x.2.1 * y.2.1 + x.1 * y.2.2)

/-- The jet of a reciprocal. -/
noncomputable def rinv (x : RJ) : RJ :=
  (x.1⁻¹, 0 - x.2.1 * (x.1⁻¹ * x.1⁻¹),
    x.2.1 * (x.1⁻¹ * x.1⁻¹) * (x.2.1 * x.1⁻¹) + x.2.1 * (x.1⁻¹ * x.1⁻¹) * (x.2.1 * x.1⁻¹)
      - x.2.2 * (x.1⁻¹ * x.1⁻¹))

/-- The jet of a square root. -/
noncomputable def rsqrt (x : RJ) : RJ :=
  (Real.sqrt x.1, x.2.1 * (2⁻¹ * (Real.sqrt x.1)⁻¹),
    x.2.2 * (2⁻¹ * (Real.sqrt x.1)⁻¹)
      - x.2.1 * (2⁻¹ * (Real.sqrt x.1)⁻¹) * (x.2.1 * (2⁻¹ * (Real.sqrt x.1)⁻¹)) * (Real.sqrt x.1)⁻¹)

/-- The real jet that an instruction defines from the registers `regs`. -/
noncomputable def jden (P : Params) (regs : List RJ) : Instr → RJ
  | .nat n => (n, 0, 0)
  | .cst b => (((b : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p, 0, 0)
  | .add i j => ((regs.getD i 0).1 + (regs.getD j 0).1, (regs.getD i 0).2.1 + (regs.getD j 0).2.1,
      (regs.getD i 0).2.2 + (regs.getD j 0).2.2)
  | .sub i j => ((regs.getD i 0).1 - (regs.getD j 0).1, (regs.getD i 0).2.1 - (regs.getD j 0).2.1,
      (regs.getD i 0).2.2 - (regs.getD j 0).2.2)
  | .mul i j => rmul (regs.getD i 0) (regs.getD j 0)
  | .inv i => rinv (regs.getD i 0)
  | .sqrt i => rsqrt (regs.getD i 0)

/-- The registers after a program that starts with the registers `regs`. -/
noncomputable def jsemFrom (P : Params) : List Instr → List RJ → List RJ
  | [], regs => regs
  | ins :: rest, regs => jsemFrom P rest (regs ++ [jden P regs ins])

/-- The registers of a program as functions of the variable `x`, which is register `0`. -/
noncomputable def jsem (P : Params) (prog : List Instr) (x : ℝ) : List RJ :=
  jsemFrom P prog [(x, 1, 0)]

/-! ## Enclosures -/

/-- The jet `x` of the checker encloses the real jet `v`. -/
def JEnc (p B : ℕ) (x : Jet) (v : RJ) : Prop :=
  FEnc p B x.1 v.1 ∧ FEnc p B x.2.1 v.2.1 ∧ FEnc p B x.2.2 v.2.2

theorem zero_enc (p B : ℕ) : FEnc p B (B, 0, true) 0 := by
  intro _
  show |(0 : ℝ) * 2 ^ p - ((B : ℝ) - B)| ≤ ((0 : ℕ) : ℝ)
  simp

theorem half_enc (p B : ℕ) (hp : 1 ≤ p) : FEnc p B (B + 1 <<< (p - 1), 0, true) (2⁻¹ : ℝ) := by
  intro _
  show |(2⁻¹ : ℝ) * 2 ^ p - (((B + 1 <<< (p - 1) : ℕ) : ℝ) - B)| ≤ ((0 : ℕ) : ℝ)
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.one_shiftLeft]
  push_cast
  rw [show (2⁻¹ : ℝ) * 2 ^ (j + 1) - ((B : ℝ) + 2 ^ j - B) = 0 by rw [pow_succ]; ring]
  simp

theorem one_enc (p B : ℕ) : FEnc p B (B + 1 <<< p, 0, true) 1 := by
  intro _
  show |(1 : ℝ) * 2 ^ p - (((B + 1 <<< p : ℕ) : ℝ) - B)| ≤ ((0 : ℕ) : ℝ)
  rw [Nat.one_shiftLeft]
  push_cast
  rw [show (1 : ℝ) * 2 ^ p - ((B : ℝ) + 2 ^ p - B) = 0 by ring]
  simp

theorem jadd_sound {p B : ℕ} {x y : Jet} {a b : RJ} (hx : JEnc p B x a) (hy : JEnc p B y b) :
    JEnc p B (jadd B x y) (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2) :=
  ⟨fadd_sound hx.1 hy.1, fadd_sound hx.2.1 hy.2.1, fadd_sound hx.2.2 hy.2.2⟩

theorem jsub_sound {p B : ℕ} {x y : Jet} {a b : RJ} (hx : JEnc p B x a) (hy : JEnc p B y b) :
    JEnc p B (jsub B x y) (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2) :=
  ⟨fsub_sound hx.1 hy.1, fsub_sound hx.2.1 hy.2.1, fsub_sound hx.2.2 hy.2.2⟩

theorem jmul_sound {p B : ℕ} {x y : Jet} {a b : RJ} (hx : JEnc p B x a) (hy : JEnc p B y b) :
    JEnc p B (jmul p B x y) (rmul a b) :=
  ⟨fmul_sound hx.1 hy.1, fadd_sound (fmul_sound hx.2.1 hy.1) (fmul_sound hx.1 hy.2.1),
    fadd_sound (fadd_sound (fadd_sound (fmul_sound hx.2.2 hy.1) (fmul_sound hx.2.1 hy.2.1))
      (fmul_sound hx.2.1 hy.2.1)) (fmul_sound hx.1 hy.2.2)⟩

theorem jinv_sound {p B : ℕ} {x : Jet} {a : RJ} (hx : JEnc p B x a) : JEnc p B (jinv p B x) (rinv a) :=
  ⟨finv_sound hx.1,
    fsub_sound (zero_enc p B) (fmul_sound hx.2.1 (fmul_sound (finv_sound hx.1) (finv_sound hx.1))),
    fsub_sound
      (fadd_sound
        (fmul_sound (fmul_sound hx.2.1 (fmul_sound (finv_sound hx.1) (finv_sound hx.1)))
          (fmul_sound hx.2.1 (finv_sound hx.1)))
        (fmul_sound (fmul_sound hx.2.1 (fmul_sound (finv_sound hx.1) (finv_sound hx.1)))
          (fmul_sound hx.2.1 (finv_sound hx.1))))
      (fmul_sound hx.2.2 (fmul_sound (finv_sound hx.1) (finv_sound hx.1)))⟩

theorem halfInv_sound {p B t : ℕ} {x : Jet} {a : RJ} (hp : 1 ≤ p) (hx : JEnc p B x a) :
    FEnc p B (halfInv p B x t) (2⁻¹ * (Real.sqrt a.1)⁻¹) :=
  fmul_sound (half_enc p B hp) (finv_sound (fsqrt_sound hx.1))

theorem jsqrt_sound {p B t : ℕ} {x : Jet} {a : RJ} (hp : 1 ≤ p) (hx : JEnc p B x a) :
    JEnc p B (jsqrt p B x t) (rsqrt a) :=
  ⟨fsqrt_sound hx.1, fmul_sound hx.2.1 (halfInv_sound hp hx),
    fsub_sound (fmul_sound hx.2.2 (halfInv_sound hp hx))
      (fmul_sound (fmul_sound (fmul_sound hx.2.1 (halfInv_sound hp hx)) (fmul_sound hx.2.1 (halfInv_sound hp hx)))
        (finv_sound (fsqrt_sound hx.1)))⟩

/-! ## Derivatives -/

theorem hasDeriv_mul2 {f g f' g' : ℝ → ℝ} {f'' g'' x : ℝ} (hf : HasDerivAt f (f' x) x)
    (hg : HasDerivAt g (g' x) x) (hf' : HasDerivAt f' f'' x) (hg' : HasDerivAt g' g'' x) :
    HasDerivAt (fun y => f y * g y) (f' x * g x + f x * g' x) x ∧
      HasDerivAt (fun y => f' y * g y + f y * g' y)
        (f'' * g x + f' x * g' x + f' x * g' x + f x * g'') x :=
  ⟨hf.fun_mul hg, ((hf'.fun_mul hg).fun_add (hf.fun_mul hg')).congr_deriv (by ring)⟩

theorem hasDeriv_inv2 {f f' : ℝ → ℝ} {f'' x : ℝ} (hf : HasDerivAt f (f' x) x) (hf' : HasDerivAt f' f'' x)
    (h0 : f x ≠ 0) :
    HasDerivAt (fun y => (f y)⁻¹) (0 - f' x * ((f x)⁻¹ * (f x)⁻¹)) x ∧
      HasDerivAt (fun y => 0 - f' y * ((f y)⁻¹ * (f y)⁻¹))
        (f' x * ((f x)⁻¹ * (f x)⁻¹) * (f' x * (f x)⁻¹) + f' x * ((f x)⁻¹ * (f x)⁻¹) * (f' x * (f x)⁻¹)
          - f'' * ((f x)⁻¹ * (f x)⁻¹)) x := by
  have hw : HasDerivAt (fun y => (f y)⁻¹) (0 - f' x * ((f x)⁻¹ * (f x)⁻¹)) x :=
    (hf.fun_inv h0).congr_deriv (by rw [div_eq_mul_inv, pow_two, mul_inv]; ring)
  exact ⟨hw, ((hasDerivAt_const x (0 : ℝ)).fun_sub (hf'.fun_mul (hw.fun_mul hw))).congr_deriv (by ring)⟩

theorem hasDeriv_sqrt2 {f f' : ℝ → ℝ} {f'' x : ℝ} (hf : HasDerivAt f (f' x) x) (hf' : HasDerivAt f' f'' x)
    (h0 : 0 < f x) :
    HasDerivAt (fun y => Real.sqrt (f y)) (f' x * (2⁻¹ * (Real.sqrt (f x))⁻¹)) x ∧
      HasDerivAt (fun y => f' y * (2⁻¹ * (Real.sqrt (f y))⁻¹))
        (f'' * (2⁻¹ * (Real.sqrt (f x))⁻¹)
          - f' x * (2⁻¹ * (Real.sqrt (f x))⁻¹) * (f' x * (2⁻¹ * (Real.sqrt (f x))⁻¹)) * (Real.sqrt (f x))⁻¹) x := by
  have hs0 : Real.sqrt (f x) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  have hs : HasDerivAt (fun y => Real.sqrt (f y)) (f' x * (2⁻¹ * (Real.sqrt (f x))⁻¹)) x :=
    (hf.sqrt h0.ne').congr_deriv (by rw [div_eq_mul_inv, mul_inv])
  exact ⟨hs, (hf'.fun_mul ((hs.fun_inv hs0).const_mul (2⁻¹ : ℝ))).congr_deriv
    (by rw [div_eq_mul_inv, pow_two, mul_inv]; ring)⟩

end CAP.Root
