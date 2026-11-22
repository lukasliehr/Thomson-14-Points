module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

/-!
# Jets: the remainders of the roots, of the cosine and of the sine

The jets of `N14.Jet` have an exact polynomial of degree 5. For the functions of one variable that occur in the
pair energies this file gives the Taylor polynomial of degree 5 with a bound of order six for the rest. No
derivative is used.

* `isqrt_taylor`: `(u₀ + n)^(-1/2)` for `|n| ≤ u₀ / 8`, with `b₀ = u₀^(-1/2)`: the rest is at most
  `b₀¹³ |n|⁶ / 2`. The proof is algebraic: with `q = n / u₀`, `y = (1 + q)^(-1/2)` and the Taylor polynomial `T`
  one has `(1 + q) T² = 1 + q⁶ W(q)` for a polynomial `W`, hence `(y - T) (1 + q) (y + T) = -q⁶ W(q)`.
* `sqrt_taylor`: `(u₀ + n)^(1/2)`, with the rest at most `b₀¹¹ |n|⁶ / 16`; here `T² = 1 + q + q⁶ W(q)`.
* `cos_bound6`, `sin_bound7`: the rests of the cosine and of the sine after the terms of degree 4 and 5, from
  the bound of Mathlib for the exponential series (`Complex.exp_bound`).
-/

@[expose] public section

namespace N14.Jet

/-- A polynomial of degree 5 on `|q| ≤ δ`, from bounds for the absolute values of its coefficients. -/
theorem abs_poly5_le (w0 w1 w2 w3 w4 w5 a0 a1 a2 a3 a4 a5 q δ : ℝ) (hq : |q| ≤ δ) (h0 : |w0| ≤ a0)
    (h1 : |w1| ≤ a1) (h2 : |w2| ≤ a2) (h3 : |w3| ≤ a3) (h4 : |w4| ≤ a4) (h5 : |w5| ≤ a5) :
    |w0 + w1 * q + w2 * q ^ 2 + w3 * q ^ 3 + w4 * q ^ 4 + w5 * q ^ 5|
      ≤ a0 + a1 * δ + a2 * δ ^ 2 + a3 * δ ^ 3 + a4 * δ ^ 4 + a5 * δ ^ 5 := by
  have hp : ∀ k : ℕ, |q ^ k| ≤ δ ^ k := fun k => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg q) hq k
  have t : ∀ (w a : ℝ) (k : ℕ), |w| ≤ a → |w * q ^ k| ≤ a * δ ^ k := fun w a k hw => by
    rw [abs_mul]
    exact mul_le_mul hw (hp k) (abs_nonneg _) (le_trans (abs_nonneg w) hw)
  have b0 := abs_le.mp h0
  have b1 := abs_le.mp (t w1 a1 1 h1)
  rw [pow_one, pow_one] at b1
  have b2 := abs_le.mp (t w2 a2 2 h2)
  have b3 := abs_le.mp (t w3 a3 3 h3)
  have b4 := abs_le.mp (t w4 a4 4 h4)
  have b5 := abs_le.mp (t w5 a5 5 h5)
  rw [abs_le]
  constructor <;> linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]

/-! ## The inverse root -/

/-- The Taylor polynomial of degree 5 of `(1 + q)^(-1/2)`. -/
noncomputable def tinv (q : ℝ) : ℝ :=
  1 - q / 2 + 3 * q ^ 2 / 8 - 5 * q ^ 3 / 16 + 35 * q ^ 4 / 128 - 63 * q ^ 5 / 256

/-- The polynomial `W` with `(1 + q) T² = 1 + q⁶ W`. -/
noncomputable def winv (q : ℝ) : ℝ :=
  -231 / 512 + 99 / 512 * q + -2079 / 16384 * q ^ 2 + 385 / 4096 * q ^ 3 + -4851 / 65536 * q ^ 4
    + 3969 / 65536 * q ^ 5

theorem tinv_sq (q : ℝ) : (1 + q) * tinv q ^ 2 = 1 + q ^ 6 * winv q := by
  unfold tinv winv
  ring

theorem tinv_ge (q : ℝ) (hq : |q| ≤ 1 / 8) : (93 : ℝ) / 100 ≤ tinv q := by
  have h := abs_poly5_le 0 (-1 / 2) (3 / 8) (-5 / 16) (35 / 128) (-63 / 256) 0 (1 / 2) (3 / 8) (5 / 16)
    (35 / 128) (63 / 256) q (1 / 8) hq (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
  have e : (0 : ℝ) + -1 / 2 * q + 3 / 8 * q ^ 2 + -5 / 16 * q ^ 3 + 35 / 128 * q ^ 4 + -63 / 256 * q ^ 5
      = tinv q - 1 := by
    unfold tinv
    ring
  rw [e] at h
  have h2 := (abs_le.mp h).1
  norm_num at h2
  linarith

theorem winv_le (q : ℝ) (hq : |q| ≤ 1 / 8) : |winv q| ≤ 48 / 100 := by
  have h := abs_poly5_le (-231 / 512) (99 / 512) (-2079 / 16384) (385 / 4096) (-4851 / 65536) (3969 / 65536)
    (231 / 512) (99 / 512) (2079 / 16384) (385 / 4096) (4851 / 65536) (3969 / 65536) q (1 / 8) hq
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
  have e : (-231 : ℝ) / 512 + 99 / 512 * q + -2079 / 16384 * q ^ 2 + 385 / 4096 * q ^ 3
      + -4851 / 65536 * q ^ 4 + 3969 / 65536 * q ^ 5 = winv q := by
    unfold winv
    ring
  rw [e] at h
  refine le_trans h ?_
  norm_num

/-- The rest of the inverse root in the variable `q`. -/
theorem inv_root_bound (y q : ℝ) (hq : |q| ≤ 1 / 8) (hy : 0 < y) (hyq : y ^ 2 * (1 + q) = 1) :
    |y - tinv q| ≤ 1 / 2 * |q| ^ 6 := by
  have hq' := abs_le.mp hq
  have h1 : (7 : ℝ) / 8 ≤ 1 + q := by linarith [hq'.1]
  have h2 : 1 + q ≤ 9 / 8 := by linarith [hq'.2]
  have hy15 : (15 : ℝ) / 16 ≤ y := by
    by_contra h
    have hlt : y < 15 / 16 := not_le.mp h
    have h3 : y ^ 2 < (15 / 16) ^ 2 := by nlinarith
    nlinarith
  have hT := tinv_ge q hq
  have hW := winv_le q hq
  have key : (y - tinv q) * ((1 + q) * (y + tinv q)) = -(q ^ 6 * winv q) := by
    linear_combination hyq - tinv_sq q
  have hD : (3 : ℝ) / 2 ≤ (1 + q) * (y + tinv q) := by nlinarith
  have hDpos : 0 < (1 + q) * (y + tinv q) := by linarith
  have habs : |y - tinv q| * ((1 + q) * (y + tinv q)) = |q| ^ 6 * |winv q| := by
    rw [← abs_of_pos hDpos, ← abs_mul, key, abs_neg, abs_mul, abs_pow]
  have ha := abs_nonneg (y - tinv q)
  have hq6 : 0 ≤ |q| ^ 6 := pow_nonneg (abs_nonneg q) 6
  have h4 : |y - tinv q| * (3 / 2) ≤ |q| ^ 6 * (48 / 100) := by
    calc |y - tinv q| * (3 / 2) ≤ |y - tinv q| * ((1 + q) * (y + tinv q)) :=
          mul_le_mul_of_nonneg_left hD ha
      _ = |q| ^ 6 * |winv q| := habs
      _ ≤ |q| ^ 6 * (48 / 100) := mul_le_mul_of_nonneg_left hW hq6
  linarith

/-- **The inverse root.** For `b₀ > 0` with `b₀² u₀ = 1` and `|n| b₀² ≤ 1/8`: `u₀ + n > 0`, and
`(u₀ + n)^(-1/2)` differs from its Taylor polynomial of degree 5 at `u₀` by at most `b₀¹³ |n|⁶ / 2`. -/
theorem isqrt_taylor (u0 b0 n : ℝ) (hb : 0 < b0) (hbu : b0 ^ 2 * u0 = 1) (hn : |n| * b0 ^ 2 ≤ 1 / 8) :
    0 < u0 + n ∧
    |(Real.sqrt (u0 + n))⁻¹ - (b0 - b0 ^ 3 * n / 2 + 3 * b0 ^ 5 * n ^ 2 / 8 - 5 * b0 ^ 7 * n ^ 3 / 16
        + 35 * b0 ^ 9 * n ^ 4 / 128 - 63 * b0 ^ 11 * n ^ 5 / 256)| ≤ 1 / 2 * b0 ^ 13 * |n| ^ 6 := by
  have hb2 : 0 < b0 ^ 2 := by positivity
  set q := n * b0 ^ 2 with hqdef
  have hq : |q| ≤ 1 / 8 := by
    rw [hqdef, abs_mul, abs_of_pos hb2]
    exact hn
  have hq' := abs_le.mp hq
  have hsum : b0 ^ 2 * (u0 + n) = 1 + q := by
    rw [hqdef]
    linear_combination hbu
  have hpos : 0 < u0 + n := by
    have h1 : 0 < b0 ^ 2 * (u0 + n) := by
      rw [hsum]
      linarith [hq'.1]
    exact (mul_pos_iff_of_pos_left hb2).mp h1
  have hs : 0 < Real.sqrt (u0 + n) := Real.sqrt_pos.mpr hpos
  set y := (Real.sqrt (u0 + n))⁻¹ / b0 with hydef
  have hy : 0 < y := div_pos (inv_pos.mpr hs) hb
  have hss : Real.sqrt (u0 + n) ^ 2 = u0 + n := Real.sq_sqrt hpos.le
  have hyq : y ^ 2 * (1 + q) = 1 := by
    rw [hydef, ← hsum]
    field_simp
    rw [hss]
  have hr := inv_root_bound y q hq hy hyq
  refine ⟨hpos, ?_⟩
  have e1 : (Real.sqrt (u0 + n))⁻¹ = b0 * y := by
    rw [hydef]
    field_simp
  have e2 : b0 - b0 ^ 3 * n / 2 + 3 * b0 ^ 5 * n ^ 2 / 8 - 5 * b0 ^ 7 * n ^ 3 / 16
      + 35 * b0 ^ 9 * n ^ 4 / 128 - 63 * b0 ^ 11 * n ^ 5 / 256 = b0 * tinv q := by
    unfold tinv
    rw [hqdef]
    ring
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hb]
  have e3 : |q| ^ 6 = b0 ^ 12 * |n| ^ 6 := by
    rw [hqdef, abs_mul, abs_of_pos hb2]
    ring
  calc b0 * |y - tinv q| ≤ b0 * (1 / 2 * |q| ^ 6) := mul_le_mul_of_nonneg_left hr hb.le
    _ = 1 / 2 * b0 ^ 13 * |n| ^ 6 := by
      rw [e3]
      ring

/-! ## The root -/

/-- The Taylor polynomial of degree 5 of `(1 + q)^(1/2)`. -/
noncomputable def tsq (q : ℝ) : ℝ := 1 + q / 2 - q ^ 2 / 8 + q ^ 3 / 16 - 5 * q ^ 4 / 128 + 7 * q ^ 5 / 256

/-- The polynomial `W` with `T² = 1 + q + q⁶ W`. -/
noncomputable def wsq (q : ℝ) : ℝ :=
  21 / 512 + -3 / 256 * q + 81 / 16384 * q ^ 2 + -35 / 16384 * q ^ 3 + 49 / 65536 * q ^ 4 + 0 * q ^ 5

theorem tsq_sq (q : ℝ) : tsq q ^ 2 = 1 + q + q ^ 6 * wsq q := by
  unfold tsq wsq
  ring

theorem tsq_ge (q : ℝ) (hq : |q| ≤ 1 / 8) : (93 : ℝ) / 100 ≤ tsq q := by
  have h := abs_poly5_le 0 (1 / 2) (-1 / 8) (1 / 16) (-5 / 128) (7 / 256) 0 (1 / 2) (1 / 8) (1 / 16)
    (5 / 128) (7 / 256) q (1 / 8) hq (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
  have e : (0 : ℝ) + 1 / 2 * q + -1 / 8 * q ^ 2 + 1 / 16 * q ^ 3 + -5 / 128 * q ^ 4 + 7 / 256 * q ^ 5
      = tsq q - 1 := by
    unfold tsq
    ring
  rw [e] at h
  have h2 := (abs_le.mp h).1
  norm_num at h2
  linarith

theorem wsq_le (q : ℝ) (hq : |q| ≤ 1 / 8) : |wsq q| ≤ 43 / 1000 := by
  have h := abs_poly5_le (21 / 512) (-3 / 256) (81 / 16384) (-35 / 16384) (49 / 65536) 0
    (21 / 512) (3 / 256) (81 / 16384) (35 / 16384) (49 / 65536) 0 q (1 / 8) hq
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
  have e : (21 : ℝ) / 512 + -3 / 256 * q + 81 / 16384 * q ^ 2 + -35 / 16384 * q ^ 3 + 49 / 65536 * q ^ 4
      + 0 * q ^ 5 = wsq q := by
    unfold wsq
    ring
  rw [e] at h
  refine le_trans h ?_
  norm_num

/-- The rest of the root in the variable `q`. -/
theorem root_bound (y q : ℝ) (hq : |q| ≤ 1 / 8) (hy : 0 ≤ y) (hyq : y ^ 2 = 1 + q) :
    |y - tsq q| ≤ 1 / 16 * |q| ^ 6 := by
  have hT := tsq_ge q hq
  have hW := wsq_le q hq
  have key : (y - tsq q) * (y + tsq q) = -(q ^ 6 * wsq q) := by
    linear_combination hyq - tsq_sq q
  have hD : (93 : ℝ) / 100 ≤ y + tsq q := by linarith
  have hDpos : 0 < y + tsq q := by linarith
  have habs : |y - tsq q| * (y + tsq q) = |q| ^ 6 * |wsq q| := by
    rw [← abs_of_pos hDpos, ← abs_mul, key, abs_neg, abs_mul, abs_pow]
  have ha := abs_nonneg (y - tsq q)
  have hq6 : 0 ≤ |q| ^ 6 := pow_nonneg (abs_nonneg q) 6
  have h4 : |y - tsq q| * (93 / 100) ≤ |q| ^ 6 * (43 / 1000) := by
    calc |y - tsq q| * (93 / 100) ≤ |y - tsq q| * (y + tsq q) := mul_le_mul_of_nonneg_left hD ha
      _ = |q| ^ 6 * |wsq q| := habs
      _ ≤ |q| ^ 6 * (43 / 1000) := mul_le_mul_of_nonneg_left hW hq6
  linarith

/-- **The root.** For `b₀ > 0` with `b₀² u₀ = 1` and `|n| b₀² ≤ 1/8`: `(u₀ + n)^(1/2)` differs from its Taylor
polynomial of degree 5 at `u₀` by at most `b₀¹¹ |n|⁶ / 16`. -/
theorem sqrt_taylor (u0 b0 n : ℝ) (hb : 0 < b0) (hbu : b0 ^ 2 * u0 = 1) (hn : |n| * b0 ^ 2 ≤ 1 / 8) :
    |Real.sqrt (u0 + n) - (u0 * b0 + b0 * n / 2 - b0 ^ 3 * n ^ 2 / 8 + b0 ^ 5 * n ^ 3 / 16
        - 5 * b0 ^ 7 * n ^ 4 / 128 + 7 * b0 ^ 9 * n ^ 5 / 256)| ≤ 1 / 16 * b0 ^ 11 * |n| ^ 6 := by
  have hb2 : 0 < b0 ^ 2 := by positivity
  set q := n * b0 ^ 2 with hqdef
  have hq : |q| ≤ 1 / 8 := by
    rw [hqdef, abs_mul, abs_of_pos hb2]
    exact hn
  have hq' := abs_le.mp hq
  have hsum : b0 ^ 2 * (u0 + n) = 1 + q := by
    rw [hqdef]
    linear_combination hbu
  have hpos : 0 ≤ u0 + n := by
    have h1 : 0 < b0 ^ 2 * (u0 + n) := by
      rw [hsum]
      linarith [hq'.1]
    exact ((mul_pos_iff_of_pos_left hb2).mp h1).le
  set y := b0 * Real.sqrt (u0 + n) with hydef
  have hy : 0 ≤ y := mul_nonneg hb.le (Real.sqrt_nonneg _)
  have hss : Real.sqrt (u0 + n) ^ 2 = u0 + n := Real.sq_sqrt hpos
  have hyq : y ^ 2 = 1 + q := by
    rw [hydef, mul_pow, hss, hsum]
  have hr := root_bound y q hq hy hyq
  have hb0 : b0 ≠ 0 := ne_of_gt hb
  have e1 : Real.sqrt (u0 + n) = y / b0 := by
    rw [hydef]
    field_simp
  have e2 : u0 * b0 + b0 * n / 2 - b0 ^ 3 * n ^ 2 / 8 + b0 ^ 5 * n ^ 3 / 16
      - 5 * b0 ^ 7 * n ^ 4 / 128 + 7 * b0 ^ 9 * n ^ 5 / 256 = tsq q / b0 := by
    have hub : u0 * b0 = 1 / b0 := by
      field_simp
      linear_combination hbu
    rw [hub]
    unfold tsq
    rw [hqdef]
    field_simp
  rw [e1, e2, ← sub_div, abs_div, abs_of_pos hb]
  have e3 : |q| ^ 6 = b0 ^ 12 * |n| ^ 6 := by
    rw [hqdef, abs_mul, abs_of_pos hb2]
    ring
  rw [div_le_iff₀ hb]
  calc |y - tsq q| ≤ 1 / 16 * |q| ^ 6 := hr
    _ = 1 / 16 * b0 ^ 11 * |n| ^ 6 * b0 := by
      rw [e3]
      ring

/-! ## The cosine and the sine -/

open Finset in
theorem ccos_bound6 {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)‖ ≤ ‖x‖ ^ 6 * (7 / 4320) :=
  calc
    ‖Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)‖ =
        ‖(Complex.exp (-x * Complex.I) - ∑ m ∈ range 6, (-x * Complex.I) ^ m / m.factorial) / 2 +
         (Complex.exp (x * Complex.I) - ∑ m ∈ range 6, (x * Complex.I) ^ m / m.factorial) / 2‖ := by
      simp [Complex.cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [Complex.I_sq, two_ne_zero]
    _ ≤ ‖Complex.exp (-x * Complex.I) - ∑ m ∈ range 6, (-x * Complex.I) ^ m / m.factorial‖ / 2 +
        ‖Complex.exp (x * Complex.I) - ∑ m ∈ range 6, (x * Complex.I) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ ≤ ‖-x * Complex.I‖ ^ 6 * (Nat.succ 6 * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * Complex.I‖ ^ 6 * (Nat.succ 6 * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (by simpa) (by simp), Complex.exp_bound (by simpa) (by simp)]
    _ = ‖x‖ ^ 6 * (7 / 4320) := by norm_num [mul_one_div, Nat.factorial]

open Finset in
theorem csin_bound7 {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)‖ ≤ ‖x‖ ^ 7 / 4410 :=
  calc
    ‖Complex.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)‖ =
        ‖(Complex.exp (-x * Complex.I) - ∑ m ∈ range 7, (-x * Complex.I) ^ m / m.factorial) * Complex.I / 2 -
         (Complex.exp (x * Complex.I) - ∑ m ∈ range 7, (x * Complex.I) ^ m / m.factorial) * Complex.I / 2‖ := by
      simp [Complex.sin, field, Finset.sum_range_succ, Nat.factorial]
      grind [Complex.I_sq, two_ne_zero]
    _ ≤ ‖Complex.exp (-x * Complex.I) - ∑ m ∈ range 7, (-x * Complex.I) ^ m / m.factorial‖ / 2 +
        ‖Complex.exp (x * Complex.I) - ∑ m ∈ range 7, (x * Complex.I) ^ m / m.factorial‖ / 2 := by
      grw [norm_sub_le]
      simp
    _ ≤ ‖-x * Complex.I‖ ^ 7 * (Nat.succ 7 * (Nat.factorial 7 * (7 : ℕ) : ℝ)⁻¹) / 2 +
        ‖x * Complex.I‖ ^ 7 * (Nat.succ 7 * (Nat.factorial 7 * (7 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (by simpa) (by simp), Complex.exp_bound (by simpa) (by simp)]
    _ = ‖x‖ ^ 7 / 4410 := by norm_num [mul_one_div, Nat.factorial]

/-- **The cosine**: the rest after the terms of degree at most 4. -/
theorem cos_bound6 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ |x| ^ 6 * (7 / 4320) := by
  simpa [← Complex.ofReal_cos, ← Real.norm_eq_abs, ← Complex.norm_real] using
    ccos_bound6 (x := x) (by simpa)

/-- **The sine**: the rest after the terms of degree at most 5. -/
theorem sin_bound7 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)| ≤ |x| ^ 7 / 4410 := by
  simpa [← Complex.ofReal_sin, ← Real.norm_eq_abs, ← Complex.norm_real] using
    csin_bound7 (x := x) (by simpa)

end N14.Jet
