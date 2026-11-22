module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Statement 6 of T7: the constants of the rigidity lemma

Lemma 8.1 of the source (rigidity) bounds the gauge coordinates of a configuration whose triples lie within
`τ` of nodes of the candidate. Its proof uses a list of inequalities between numbers that depend on the
stationary height `h`, on `π` and on values of the sine and the cosine; the program `audit_geometry.py` of the
source checks them at `τ = 10⁻³` (they are monotone in `τ`, which is an argument of the paper, not of the
program). This file states these inequalities (`Consts h`) and proves them for every `h` in
`[0.45536779, 0.4553678]` (`consts_of`); the stationary height lies in this interval by statement 1.

The numbers: `β = (h + τ) / √(1 - (h + τ)²)`, `r = √(1 - h²)`,
`η = (1 + 2h + τ + 2rβ + β²τ) / (r - βτ)²`, `η' = (1 + 2h + τ + (√3/2)(2rβ + β²τ)) / (r - βτ)²`,
`a = 1.16 · 3.569`, `b = 1.001 · 3.414`, `c = 2.32 · 3.414`, and the bounds of the two coordinates of the second
pole.
-/

@[expose] public section

namespace N14.Rigid

open Real

/-- `β` at `τ = 10⁻³`. -/
noncomputable def beta (h : ℝ) : ℝ := (h + 1 / 1000) / √(1 - (h + 1 / 1000) ^ 2)

/-- The radius of the hexagons. -/
noncomputable def rr (h : ℝ) : ℝ := √(1 - h ^ 2)

/-- `η` at `τ = 10⁻³`. -/
noncomputable def eta (h : ℝ) : ℝ :=
  (1 + 2 * h + 1 / 1000 + 2 * rr h * beta h + beta h ^ 2 * (1 / 1000)) / (rr h - beta h * (1 / 1000)) ^ 2

/-- `η'` at `τ = 10⁻³`. -/
noncomputable def etap (h : ℝ) : ℝ :=
  (1 + 2 * h + 1 / 1000 + √3 / 2 * (2 * rr h * beta h + beta h ^ 2 * (1 / 1000)))
    / (rr h - beta h * (1 / 1000)) ^ 2

/-- `a = 1.16 · 3.569`. -/
noncomputable def ca : ℝ := 116 / 100 * (3569 / 1000)

/-- `b = 1.001 · 3.414`. -/
noncomputable def cb : ℝ := 1001 / 1000 * (3414 / 1000)

/-- `c = 2.32 · 3.414`. -/
noncomputable def cc : ℝ := 232 / 100 * (3414 / 1000)

/-- The bound for the first coordinate of the second pole, divided by `τ`. -/
noncomputable def poleA (h : ℝ) : ℝ := (2 + h) / (rr h - beta h * (1 / 1000))

/-- The bound for the second coordinate of the second pole, divided by `τ`. -/
noncomputable def poleB (h : ℝ) : ℝ :=
  (poleA h + poleA h * sin ((ca + cb) * (1 / 1000))) / cos ((ca + cb) * (1 / 1000))

/-- **The inequalities of the rigidity lemma** at `τ = 10⁻³`, for the height `h`: the list of
`audit_geometry.py` of the source. -/
structure Consts (h : ℝ) : Prop where
  beta_lt : beta h < 513 / 1000
  eta_lt : eta h < 3569 / 1000
  etap_lt : etap h < 3414 / 1000
  sin_a : 1 < 116 / 100 * sin (π / 3 - ca * (1 / 1000))
  cos_b : 1 < 1001 / 1000 * cos (cb * (1 / 1000))
  sin_c : 1 < 232 / 100 * sin (π / 6 - cc * (1 / 1000))
  seven : 2 * π < 7 * (π / 3 - ca * (1 / 1000))
  gap : π / 3 + 5 * ca * (1 / 1000) < 2 * π / 3 - ca * (1 / 1000)
  cos_gap : -1 + 3569 / 1000 * (1 / 1000) < cos (π / 3 + 5 * ca * (1 / 1000))
  six : 6 * ca * (1 / 1000) < π / 3
  cos_opp : -1 + 3569 / 1000 * (1 / 1000) < cos (2 * π / 3 + 2 * ca * (1 / 1000))
  lower_slots : (2 * cc + 2 * ca) * (1 / 1000) < π / 3
  lower : 2 * (ca + cb) * (1 / 1000) < π / 3 - ca * (1 / 1000)
  poleA_lt : poleA h < 279 / 100
  poleB_lt : poleB h < 279 / 100
  norm2 : 12 + 4 * ca ^ 2 + (2 * ca) ^ 2 + 6 * (ca + cb) ^ 2 + 2 * (279 / 100 : ℝ) ^ 2 < 23 ^ 2
  inf : 2 * ca < 9 ∧ ca + cb < 9
  coupling : 9 / 10 < 2 * h - 2 * (1 / 1000) ∧ √(2 * (1 / 1000)) < 5 / 100

theorem sqrt3_ge : (1732 / 1000 : ℝ) ≤ √3 := by
  calc (1732 / 1000 : ℝ) = √((1732 / 1000) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ √3 := Real.sqrt_le_sqrt (by norm_num)

theorem sqrt3_le : √3 ≤ (17320509 / 10000000 : ℝ) := by
  calc √3 ≤ √((17320509 / 10000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 17320509 / 10000000 := Real.sqrt_sq (by norm_num)

theorem sin_third_sub (x : ℝ) (hx : 0 ≤ x) : √3 / 2 * (1 - x ^ 2 / 2) - x / 2 ≤ sin (π / 3 - x) := by
  rw [sin_sub, sin_pi_div_three, cos_pi_div_three]
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.sin_le hx
  have h3 : (0 : ℝ) ≤ √3 / 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left h1 h3]

theorem sin_sixth_sub (x : ℝ) (hx : 0 ≤ x) : 1 / 2 * (1 - x ^ 2 / 2) - √3 / 2 * x ≤ sin (π / 6 - x) := by
  rw [sin_sub, sin_pi_div_six, cos_pi_div_six]
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.sin_le hx
  have h3 : (0 : ℝ) ≤ √3 / 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left h2 h3]

theorem cos_third_add (x : ℝ) (hx : 0 ≤ x) : 1 / 2 * (1 - x ^ 2 / 2) - √3 / 2 * x ≤ cos (π / 3 + x) := by
  rw [cos_add, sin_pi_div_three, cos_pi_div_three]
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.sin_le hx
  have h3 : (0 : ℝ) ≤ √3 / 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left h2 h3]

theorem cos_two_thirds_add (x : ℝ) (hx : 0 ≤ x) : -(1 / 2) - √3 / 2 * x ≤ cos (2 * π / 3 + x) := by
  have e : 2 * π / 3 = π - π / 3 := by ring
  rw [e, cos_add, cos_pi_sub, sin_pi_sub, sin_pi_div_three, cos_pi_div_three]
  have h1 := Real.cos_le_one x
  have h2 := Real.sin_le hx
  have h3 : (0 : ℝ) ≤ √3 / 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left h2 h3]

/-- **The constants of rigidity** for every height in `[0.45536779, 0.4553678]`. -/
theorem consts_of (h : ℝ) (hl : (45536779 / 100000000 : ℝ) ≤ h) (hu : h ≤ (4553678 / 10000000 : ℝ)) :
    Consts h := by
  have h0 : 0 ≤ h := le_trans (by norm_num) hl
  have s3l := sqrt3_ge
  have s3u := sqrt3_le
  have hpi := Real.two_le_pi
  -- the roots
  have hsq_u : h ^ 2 ≤ (4553678 / 10000000 : ℝ) ^ 2 := pow_le_pow_left₀ h0 hu 2
  have hsq_l : (45536779 / 100000000 : ℝ) ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ (by norm_num) hl 2
  have Hsq_u : (h + 1 / 1000) ^ 2 ≤ (4563678 / 10000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have rl : (8903034127 / 10000000000 : ℝ) ≤ rr h := by
    unfold rr
    calc (8903034127 / 10000000000 : ℝ) = √((8903034127 / 10000000000 : ℝ) ^ 2) :=
          (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(1 - h ^ 2) := Real.sqrt_le_sqrt (by
          have e : (8903034127 / 10000000000 : ℝ) ^ 2 ≤ 1 - (4553678 / 10000000 : ℝ) ^ 2 := by norm_num
          linarith)
  have ru : rr h ≤ (8903034179 / 10000000000 : ℝ) := by
    unfold rr
    calc √(1 - h ^ 2) ≤ √((8903034179 / 10000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by
          have e : 1 - (45536779 / 100000000 : ℝ) ^ 2 ≤ (8903034179 / 10000000000 : ℝ) ^ 2 := by norm_num
          linarith)
      _ = 8903034179 / 10000000000 := Real.sqrt_sq (by norm_num)
  have sl : (8897912289 / 10000000000 : ℝ) ≤ √(1 - (h + 1 / 1000) ^ 2) := by
    calc (8897912289 / 10000000000 : ℝ) = √((8897912289 / 10000000000 : ℝ) ^ 2) :=
          (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(1 - (h + 1 / 1000) ^ 2) := Real.sqrt_le_sqrt (by
          have e : (8897912289 / 10000000000 : ℝ) ^ 2 ≤ 1 - (4563678 / 10000000 : ℝ) ^ 2 := by norm_num
          linarith)
  have s_pos : 0 < √(1 - (h + 1 / 1000) ^ 2) := lt_of_lt_of_le (by norm_num) sl
  have r0 : 0 ≤ rr h := le_trans (by norm_num) rl
  -- β
  have Bu : beta h ≤ 2564465603 / 5000000000 := by
    unfold beta
    rw [div_le_iff₀ s_pos]
    calc h + 1 / 1000 ≤ 2564465603 / 5000000000 * (8897912289 / 10000000000 : ℝ) := by
          have e : (4553678 / 10000000 : ℝ) + 1 / 1000
              ≤ 2564465603 / 5000000000 * (8897912289 / 10000000000 : ℝ) := by norm_num
          linarith
      _ ≤ 2564465603 / 5000000000 * √(1 - (h + 1 / 1000) ^ 2) :=
          mul_le_mul_of_nonneg_left sl (by norm_num)
  have B0 : 0 ≤ beta h := div_nonneg (by linarith) s_pos.le
  have hbeta : beta h < 513 / 1000 := lt_of_le_of_lt Bu (by norm_num)
  -- the denominator
  have ml : (4448952597897 / 5000000000000 : ℝ) ≤ rr h - beta h * (1 / 1000) := by
    have h1 := mul_le_mul_of_nonneg_right Bu (show (0 : ℝ) ≤ 1 / 1000 by norm_num)
    have e : (8903034127 / 10000000000 : ℝ) - 2564465603 / 5000000000 * (1 / 1000)
        = 4448952597897 / 5000000000000 := by norm_num
    linarith
  have m_pos : 0 < rr h - beta h * (1 / 1000) := lt_of_lt_of_le (by norm_num) ml
  have den_ge : (4448952597897 / 5000000000000 : ℝ) ^ 2 ≤ (rr h - beta h * (1 / 1000)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) ml 2
  have den_pos : 0 < (rr h - beta h * (1 / 1000)) ^ 2 := lt_of_lt_of_le (by norm_num) den_ge
  have prod_le : rr h * beta h ≤ 8903034179 / 10000000000 * (2564465603 / 5000000000 : ℝ) :=
    mul_le_mul ru Bu B0 (by norm_num)
  have Bsq : beta h ^ 2 ≤ (2564465603 / 5000000000 : ℝ) ^ 2 := pow_le_pow_left₀ B0 Bu 2
  have prod0 : 0 ≤ rr h * beta h := mul_nonneg r0 B0
  -- η
  have heta : eta h < 3569 / 1000 := by
    unfold eta
    rw [div_lt_iff₀ den_pos]
    calc 1 + 2 * h + 1 / 1000 + 2 * rr h * beta h + beta h ^ 2 * (1 / 1000)
        ≤ 1 + 2 * (4553678 / 10000000 : ℝ) + 1 / 1000
          + 2 * (8903034179 / 10000000000 * (2564465603 / 5000000000 : ℝ))
          + (2564465603 / 5000000000 : ℝ) ^ 2 * (1 / 1000) := by linarith
      _ < 3569 / 1000 * (4448952597897 / 5000000000000 : ℝ) ^ 2 := by norm_num
      _ ≤ 3569 / 1000 * (rr h - beta h * (1 / 1000)) ^ 2 := mul_le_mul_of_nonneg_left den_ge (by norm_num)
  -- η'
  have hetap : etap h < 3414 / 1000 := by
    unfold etap
    rw [div_lt_iff₀ den_pos]
    have hX : 2 * rr h * beta h + beta h ^ 2 * (1 / 1000)
        ≤ 2 * (8903034179 / 10000000000 * (2564465603 / 5000000000 : ℝ))
          + (2564465603 / 5000000000 : ℝ) ^ 2 * (1 / 1000) := by linarith
    have hX0 : 0 ≤ 2 * rr h * beta h + beta h ^ 2 * (1 / 1000) := by
      have := sq_nonneg (beta h)
      linarith
    have hS : √3 / 2 ≤ (17320509 / 10000000 : ℝ) / 2 := by linarith
    have hprod := mul_le_mul hS hX hX0 (by norm_num)
    calc 1 + 2 * h + 1 / 1000 + √3 / 2 * (2 * rr h * beta h + beta h ^ 2 * (1 / 1000))
        ≤ 1 + 2 * (4553678 / 10000000 : ℝ) + 1 / 1000
          + (17320509 / 10000000 : ℝ) / 2 * (2 * (8903034179 / 10000000000 * (2564465603 / 5000000000 : ℝ))
            + (2564465603 / 5000000000 : ℝ) ^ 2 * (1 / 1000)) := by linarith
      _ < 3414 / 1000 * (4448952597897 / 5000000000000 : ℝ) ^ 2 := by norm_num
      _ ≤ 3414 / 1000 * (rr h - beta h * (1 / 1000)) ^ 2 := mul_le_mul_of_nonneg_left den_ge (by norm_num)
  -- the coordinates of the second pole
  have hPA : poleA h ≤ 276 / 100 := by
    unfold poleA
    rw [div_le_iff₀ m_pos]
    have h1 := mul_le_mul_of_nonneg_left ml (show (0 : ℝ) ≤ 276 / 100 by norm_num)
    have e : (2 : ℝ) + 4553678 / 10000000 ≤ 276 / 100 * (4448952597897 / 5000000000000) := by norm_num
    linarith
  have hPA0 : 0 ≤ poleA h := div_nonneg (by linarith) m_pos.le
  have hx : (ca + cb) * (1 / 1000) = (7557454 / 1000000000 : ℝ) := by
    unfold ca cb
    norm_num
  have hpoleB : poleB h < 279 / 100 := by
    unfold poleB
    rw [hx]
    have hc := Real.one_sub_sq_div_two_le_cos (x := (7557454 / 1000000000 : ℝ))
    have hs := Real.sin_le (show (0 : ℝ) ≤ 7557454 / 1000000000 by norm_num)
    have cpos : 0 < cos (7557454 / 1000000000 : ℝ) := lt_of_lt_of_le (by norm_num) hc
    rw [div_lt_iff₀ cpos]
    have h1 := mul_le_mul_of_nonneg_left hs hPA0
    have h2 := mul_le_mul_of_nonneg_right hPA (show (0 : ℝ) ≤ 1 + 7557454 / 1000000000 by norm_num)
    have e : (276 / 100 : ℝ) * (1 + 7557454 / 1000000000)
        < 279 / 100 * (1 - (7557454 / 1000000000 : ℝ) ^ 2 / 2) := by norm_num
    have h3 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 279 / 100 by norm_num)
    linarith
  -- the numbers a, b, c
  have ha : ca * (1 / 1000) = (414004 / 100000000 : ℝ) := by
    unfold ca
    norm_num
  have hb : cb * (1 / 1000) = (3417414 / 1000000000 : ℝ) := by
    unfold cb
    norm_num
  have hc : cc * (1 / 1000) = (792048 / 100000000 : ℝ) := by
    unfold cc
    norm_num
  refine ⟨hbeta, heta, hetap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpoleB, ?_, ?_, ?_⟩
  · -- sin (π/3 - a τ)
    rw [ha]
    have h1 := sin_third_sub (414004 / 100000000) (by norm_num)
    have h2 : (1732 / 1000 : ℝ) / 2 * (1 - (414004 / 100000000 : ℝ) ^ 2 / 2)
        ≤ √3 / 2 * (1 - (414004 / 100000000 : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have e : (1 : ℝ) < 116 / 100 * ((1732 / 1000 : ℝ) / 2 * (1 - (414004 / 100000000 : ℝ) ^ 2 / 2)
        - 414004 / 100000000 / 2) := by norm_num
    linarith
  · -- cos (b τ)
    rw [hb]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := (3417414 / 1000000000 : ℝ))
    have e : (1 : ℝ) < 1001 / 1000 * (1 - (3417414 / 1000000000 : ℝ) ^ 2 / 2) := by norm_num
    linarith
  · -- sin (π/6 - c τ)
    rw [hc]
    have h1 := sin_sixth_sub (792048 / 100000000) (by norm_num)
    have h2 : √3 / 2 * (792048 / 100000000 : ℝ) ≤ (17320509 / 10000000 : ℝ) / 2 * (792048 / 100000000) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have e : (1 : ℝ) < 232 / 100 * (1 / 2 * (1 - (792048 / 100000000 : ℝ) ^ 2 / 2)
        - (17320509 / 10000000 : ℝ) / 2 * (792048 / 100000000)) := by norm_num
    linarith
  · rw [ha]
    linarith
  · rw [mul_assoc, ha]
    linarith
  · -- cos (π/3 + 5 a τ)
    rw [mul_assoc, ha]
    have h1 := cos_third_add (5 * (414004 / 100000000)) (by norm_num)
    have h2 : √3 / 2 * (5 * (414004 / 100000000 : ℝ))
        ≤ (17320509 / 10000000 : ℝ) / 2 * (5 * (414004 / 100000000)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have e : (-1 : ℝ) + 3569 / 1000 * (1 / 1000) < 1 / 2 * (1 - (5 * (414004 / 100000000 : ℝ)) ^ 2 / 2)
        - (17320509 / 10000000 : ℝ) / 2 * (5 * (414004 / 100000000)) := by norm_num
    linarith
  · rw [mul_assoc, ha]
    linarith
  · -- cos (2π/3 + 2 a τ)
    rw [mul_assoc, ha]
    have h1 := cos_two_thirds_add (2 * (414004 / 100000000)) (by norm_num)
    have h2 : √3 / 2 * (2 * (414004 / 100000000 : ℝ))
        ≤ (17320509 / 10000000 : ℝ) / 2 * (2 * (414004 / 100000000)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have e : (-1 : ℝ) + 3569 / 1000 * (1 / 1000)
        < -(1 / 2) - (17320509 / 10000000 : ℝ) / 2 * (2 * (414004 / 100000000)) := by norm_num
    linarith
  · have e : (2 * cc + 2 * ca) * (1 / 1000) = 2 * (cc * (1 / 1000)) + 2 * (ca * (1 / 1000)) := by ring
    rw [e, ha, hc]
    linarith
  · have e : 2 * (ca + cb) * (1 / 1000) = 2 * ((ca + cb) * (1 / 1000)) := by ring
    rw [e, hx, ha]
    linarith
  · exact lt_of_le_of_lt hPA (by norm_num)
  · unfold ca cb
    norm_num
  · unfold ca cb
    constructor <;> norm_num
  · constructor
    · linarith
    · rw [Real.sqrt_lt' (by norm_num)]
      norm_num

end N14.Rigid
