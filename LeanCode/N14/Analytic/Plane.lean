module

public import N14.Candidate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-!
# The theorem for 14 points, analytic part: unit vectors of the plane near a direction (row A6)

The rigidity lemma of the source (Lemma 8.1) compares the angles of the points of the two hexagons with the
multiples of 30 degrees. In this file the angle of a point is a unit vector `(c, s)` of the plane, a direction is
a unit vector `(γ, ς)`, and the *deviation* of `(c, s)` from the direction consists of the two numbers

  `C = γ c + ς s` (along the direction), `S = γ s - ς c` (across it), `C² + S² = 1`.

Numbers of this file: `τ = 39/200000 = 1.95 · 10⁻⁴` is the radius of the tubes of the source; `351/500000 = 3.6 τ`
bounds the error of a cosine (`cos_dev`); `1053/625000 = 2.4 · 3.6 τ` and `3159/1250000 = 3.6 · 3.6 τ` bound a
deviation `|S|`; `3/80` is the first bound for the point opposite to the reference point.

* `dev_direct`: a unit vector whose first coordinate is close to that of a direction `(γ, ς)` with `|ς| ≥ 1/2`,
  on the side of the direction: `C ≥ 249/250` and `|S| ≤ 1053/625000`;
* `dev_pi`: the same for the direction `(-1, 0)`, with the bound `3/80`;
* `dev_refine`: the deviation of the point near `(-1, 0)` from a second point near the direction of 60 degrees;
* `arcsin_abs_le`, `cos_gauge`, `sin_gauge`: the angle `arcsin S + k π / 6` of a unit vector with the deviation
  `(C, S)` from the direction `k`;
* `cos_dev`: the cosine of the angle between two points of the rings, from their inner product and heights.
-/

@[expose] public section

namespace N14.Plane

open Real

theorem abs_le_one_of_sq_le_one {x : ℝ} (h : x ^ 2 ≤ 1) : |x| ≤ 1 :=
  abs_le_of_sq_le_sq (by rw [one_pow]; exact h) (by norm_num)

theorem abs_mul_le_mul {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- The components along and across a direction form a unit vector. -/
theorem dev_unit (γ ς c s : ℝ) (hw : γ ^ 2 + ς ^ 2 = 1) (hu : c ^ 2 + s ^ 2 = 1) :
    (γ * c + ς * s) ^ 2 + (γ * s - ς * c) ^ 2 = 1 := by
  linear_combination (c ^ 2 + s ^ 2) * hw + hu

/-- A unit vector in terms of its components along and across a direction. -/
theorem recon (γ ς c s : ℝ) (hw : γ ^ 2 + ς ^ 2 = 1) :
    c = γ * (γ * c + ς * s) - ς * (γ * s - ς * c) ∧ s = ς * (γ * c + ς * s) + γ * (γ * s - ς * c) := by
  constructor
  · linear_combination (-c) * hw
  · linear_combination (-s) * hw

theorem le_abs_of_sq_le {a x : ℝ} (h : a ^ 2 ≤ x ^ 2) : a ≤ |x| := by
  by_contra hlt
  rw [not_le] at hlt
  have := sq_abs x
  nlinarith [abs_nonneg x]

theorem sq_le_mul_abs {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B * |x| := by
  have := sq_abs x
  nlinarith [abs_nonneg x]

/-- The component along the direction, in the situation of `dev_direct`. -/
theorem dev_coarse (γ ς c s : ℝ) (hw : γ ^ 2 + ς ^ 2 = 1) (hς : 1 / 4 ≤ ς ^ 2) (hu : c ^ 2 + s ^ 2 = 1)
    (hc : |c - γ| ≤ 351 / 500000) (hs : 0 < s * ς) : 249 / 250 ≤ γ * c + ς * s := by
  have hγ1 : |γ| ≤ 1 := abs_le_one_of_sq_le_one (by nlinarith [sq_nonneg ς])
  have hγe : |γ * (c - γ)| ≤ 1 * (351 / 500000) := abs_mul_le_mul hγ1 hc
  have hγe' := abs_le.mp hγe
  -- the square of `s`
  have hd : 2 * γ * (c - γ) + (c - γ) ^ 2 ≤ 15 / 10000 := by
    have h2 : (c - γ) ^ 2 ≤ (351 / 500000) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    linarith [hγe'.2]
  have hs2 : s ^ 2 = ς ^ 2 - (2 * γ * (c - γ) + (c - γ) ^ 2) := by linear_combination hu - hw
  -- the product `s ς`
  have hp : ς ^ 2 - 3 / 1000 ≤ s * ς := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : 0 < ς ^ 2 - 3 / 1000 := lt_trans hs hlt
    have h1 : (s * ς) ^ 2 < (ς ^ 2 - 3 / 1000) ^ 2 := by
      have := mul_pos (sub_pos.mpr hlt) (add_pos h0 hs)
      linarith
    have h2 : (s * ς) ^ 2 = ς ^ 2 * (ς ^ 2 - (2 * γ * (c - γ) + (c - γ) ^ 2)) := by
      rw [mul_pow, hs2]
      ring
    have h3 := mul_nonneg (sq_nonneg ς) (sub_nonneg.mpr hd)
    obtain ⟨u, hu'⟩ : ∃ u : ℝ, u = 2 * γ * (c - γ) + (c - γ) ^ 2 := ⟨_, rfl⟩
    rw [← hu'] at h2 h3
    obtain ⟨w, hw'⟩ : ∃ w : ℝ, w = ς ^ 2 := ⟨_, rfl⟩
    rw [← hw'] at h1 h2 h3 hς
    nlinarith
  have e : γ * c + ς * s = γ ^ 2 + γ * (c - γ) + s * ς := by ring
  rw [e]
  linarith [hγe'.1]

/-- The component across the direction: if `C² + S² = 1`, `C ≥ 249/250`, and `ς S = γ (C - 1) - e` with
`|γ| ≤ 1`, `|ς| ≥ 1/2` and `|e| ≤ 3.6 τ`, then `|S| ≤ 2.4 · 3.6 τ`. -/
theorem dev_fine (γ ς C S e : ℝ) (hγ1 : |γ| ≤ 1) (hς : 1 / 4 ≤ ς ^ 2) (hCS : C ^ 2 + S ^ 2 = 1)
    (hC : 249 / 250 ≤ C) (hid : ς * S = γ * (C - 1) - e) (he : |e| ≤ 351 / 500000) :
    |S| ≤ 1053 / 625000 := by
  have hC1 : C ≤ 1 := by nlinarith [sq_nonneg S, sq_nonneg (C - 1)]
  have hS2 : S ^ 2 ≤ (9 / 100) ^ 2 := by
    have hCC : (249 / 250 : ℝ) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by norm_num) hC 2
    linarith
  have hS9 : |S| ≤ 9 / 100 := abs_le_of_sq_le_sq hS2 (by norm_num)
  have h1 : |ς * S| ≤ (1 - C) + 351 / 500000 := by
    rw [hid]
    have hC1' : |C - 1| ≤ 1 - C := le_of_eq (by rw [abs_sub_comm, abs_of_nonneg (by linarith)])
    have h2 : |γ * (C - 1)| ≤ 1 * (1 - C) := abs_mul_le_mul hγ1 hC1'
    calc |γ * (C - 1) - e| ≤ |γ * (C - 1)| + |e| := abs_sub _ _
      _ ≤ (1 - C) + 351 / 500000 := by linarith
  have hς2 : 1 / 2 ≤ |ς| := le_abs_of_sq_le (by linarith)
  have h3 : |S| / 2 ≤ (1 - C) + 351 / 500000 := by
    have e' : |ς * S| = |ς| * |S| := abs_mul _ _
    have := mul_le_mul_of_nonneg_right hς2 (abs_nonneg S)
    linarith
  have h4 : (1 - C) * (1996 / 1000) ≤ S ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hC1) (sub_nonneg.mpr hC)
    linarith
  have h5 : S ^ 2 ≤ 9 / 100 * |S| := sq_le_mul_abs hS9
  linarith

/-- **A unit vector near a direction.** If the first coordinate of the unit vector `(c, s)` is within
`3.6 τ` of the first coordinate of the direction `(γ, ς)`, `|ς| ≥ 1/2`, and `s` has the sign of `ς`, then the
component of `(c, s)` along the direction is at least `249/250` and the component across it is at most
`2.4 · 3.6 τ` in absolute value. -/
theorem dev_direct (γ ς c s : ℝ) (hw : γ ^ 2 + ς ^ 2 = 1) (hς : 1 / 4 ≤ ς ^ 2) (hu : c ^ 2 + s ^ 2 = 1)
    (hc : |c - γ| ≤ 351 / 500000) (hs : 0 < s * ς) :
    249 / 250 ≤ γ * c + ς * s ∧ |γ * s - ς * c| ≤ 1053 / 625000 := by
  have hC := dev_coarse γ ς c s hw hς hu hc hs
  refine ⟨hC, ?_⟩
  have hγ1 : |γ| ≤ 1 := abs_le_one_of_sq_le_one (by nlinarith [sq_nonneg ς])
  have hid : ς * (γ * s - ς * c) = γ * (γ * c + ς * s - 1) - (c - γ) := by linear_combination (-c) * hw
  exact dev_fine γ ς (γ * c + ς * s) (γ * s - ς * c) (c - γ) hγ1 hς (dev_unit γ ς c s hw hu) hC hid hc

/-- **A unit vector near the direction `(-1, 0)`.** -/
theorem dev_pi (c s : ℝ) (hu : c ^ 2 + s ^ 2 = 1) (hc : |c + 1| ≤ 351 / 500000) :
    249 / 250 ≤ -c ∧ |s| ≤ 3 / 80 := by
  have hce := abs_le.mp hc
  refine ⟨by linarith, ?_⟩
  have h1 : s ^ 2 ≤ (3 / 80) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -c - (1 - 351 / 500000))
      (by linarith : (0 : ℝ) ≤ -c + (1 - 351 / 500000))]
  exact abs_le_of_sq_le_sq h1 (by norm_num)

/-- The first step of `dev_refine`: the sine of the difference of the two deviations. -/
theorem refine_T (ς K T P : ℝ) (hς : ς ^ 2 = 3 / 4) (hKT : K ^ 2 + T ^ 2 = 1) (hK99 : 99 / 100 ≤ K)
    (hT4 : |T| ≤ 1 / 25) (hP : P = -(1 / 2) * K - ς * T)
    (hopt : |P - 1 / 2| ≤ 351 / 500000 ∨ |P + 1 / 2| ≤ 351 / 500000 ∨ |P + 1| ≤ 351 / 500000) :
    |T| ≤ 1169 / 1000 * (351 / 500000) := by
  have hK1 : K ≤ 1 := by nlinarith [sq_nonneg T, sq_nonneg (K - 1)]
  have hς1 : (433 / 500 : ℝ) ≤ |ς| := le_abs_of_sq_le (by rw [hς]; norm_num)
  have hς2 : |ς| ≤ 8661 / 10000 := abs_le_of_sq_le_sq (by rw [hς]; norm_num) (by norm_num)
  have hςT : |ς * T| ≤ 8661 / 10000 * (1 / 25) := abs_mul_le_mul hς2 hT4
  have hςT' := abs_le.mp hςT
  -- the inner product is near `-1/2`
  have hmid : |P + 1 / 2| ≤ 351 / 500000 := by
    rcases hopt with h | h | h
    · exfalso
      have := (abs_le.mp h).1
      rw [hP] at this
      linarith
    · exact h
    · exfalso
      have := (abs_le.mp h).2
      rw [hP] at this
      linarith
  have hid : ς * T = (1 - K) / 2 - (P + 1 / 2) := by
    rw [hP]
    ring
  have h3 : |ς * T| ≤ (1 - K) / 2 + 351 / 500000 := by
    rw [hid]
    calc |(1 - K) / 2 - (P + 1 / 2)| ≤ |(1 - K) / 2| + |P + 1 / 2| := abs_sub _ _
      _ ≤ (1 - K) / 2 + 351 / 500000 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
  have h4 : (1 - K) * (199 / 100) ≤ T ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hK1) (sub_nonneg.mpr hK99)
    linarith
  have h5 : T ^ 2 ≤ 1 / 25 * |T| := sq_le_mul_abs hT4
  have h6 : 433 / 500 * |T| ≤ |ς * T| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hς1 (abs_nonneg T)
  linarith

/-- **The point opposite to the reference point.** Let `(C₁, S₁)` be the deviation of a unit vector from the
direction of 180 degrees, known up to `3/80`, and `(C₂, S₂)` the deviation of a second unit vector from the
direction of 60 degrees. Their inner product is `P = -K/2 - ς T` with `ς = √3/2`. If `P` is within `3.6 τ` of one
of the numbers `1/2`, `-1/2`, `-1`, it is `-1/2`, and `|S₁| ≤ 3.6 · 3.6 τ`. -/
theorem dev_refine (ς C₁ S₁ C₂ S₂ : ℝ) (hς : ς ^ 2 = 3 / 4) (h1 : C₁ ^ 2 + S₁ ^ 2 = 1)
    (h2 : C₂ ^ 2 + S₂ ^ 2 = 1) (hC1 : 249 / 250 ≤ C₁) (hS1 : |S₁| ≤ 3 / 80) (hC2 : 249 / 250 ≤ C₂)
    (hS2 : |S₂| ≤ 1053 / 625000) (P : ℝ)
    (hP : P = -(1 / 2) * (C₁ * C₂ + S₁ * S₂) - ς * (S₁ * C₂ - C₁ * S₂))
    (hopt : |P - 1 / 2| ≤ 351 / 500000 ∨ |P + 1 / 2| ≤ 351 / 500000 ∨ |P + 1| ≤ 351 / 500000) :
    |S₁| ≤ 3159 / 1250000 := by
  have hC1' : C₁ ≤ 1 := by nlinarith [sq_nonneg S₁, sq_nonneg (C₁ - 1)]
  have hC2' : C₂ ≤ 1 := by nlinarith [sq_nonneg S₂, sq_nonneg (C₂ - 1)]
  have hKT : (C₁ * C₂ + S₁ * S₂) ^ 2 + (S₁ * C₂ - C₁ * S₂) ^ 2 = 1 := by
    linear_combination (C₂ ^ 2 + S₂ ^ 2) * h1 + h2
  have aC1 : |C₁| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; exact hC1'
  have aC2 : |C₂| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; exact hC2'
  have a2 : |C₁ * S₂| ≤ 1 * (1053 / 625000) := abs_mul_le_mul aC1 hS2
  have hT4 : |S₁ * C₂ - C₁ * S₂| ≤ 1 / 25 := by
    have a1 : |S₁ * C₂| ≤ 3 / 80 * 1 := abs_mul_le_mul hS1 aC2
    calc |S₁ * C₂ - C₁ * S₂| ≤ |S₁ * C₂| + |C₁ * S₂| := abs_sub _ _
      _ ≤ 1 / 25 := by linarith
  have hK99 : 99 / 100 ≤ C₁ * C₂ + S₁ * S₂ := by
    have a1 : |S₁ * S₂| ≤ 3 / 80 * (1053 / 625000) := abs_mul_le_mul hS1 hS2
    have a1' := abs_le.mp a1
    have a3 : 249 / 250 * (249 / 250) ≤ C₁ * C₂ := mul_le_mul hC1 hC2 (by norm_num) (by linarith)
    linarith
  have hT' := refine_T ς (C₁ * C₂ + S₁ * S₂) (S₁ * C₂ - C₁ * S₂) P hς hKT hK99 hT4 hP hopt
  have hC2'' : 1 - (1053 / 625000) ^ 2 ≤ C₂ := by
    have hS22 : S₂ ^ 2 ≤ (1053 / 625000) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hS2 2
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ C₂) (sub_nonneg.mpr hC2')
    linarith
  have h8 : |S₁| * C₂ ≤ |S₁ * C₂ - C₁ * S₂| + 1053 / 625000 := by
    have e : |S₁ * C₂| = |S₁| * C₂ := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ C₂)]
    have h7 : S₁ * C₂ = (S₁ * C₂ - C₁ * S₂) + C₁ * S₂ := by ring
    rw [← e]
    calc |S₁ * C₂| = |(S₁ * C₂ - C₁ * S₂) + C₁ * S₂| := by rw [← h7]
      _ ≤ |S₁ * C₂ - C₁ * S₂| + |C₁ * S₂| := abs_add_le _ _
      _ ≤ |S₁ * C₂ - C₁ * S₂| + 1053 / 625000 := by linarith
  have hm := mul_nonneg (abs_nonneg S₁) (sub_nonneg.mpr hC2'')
  linarith [abs_nonneg S₁]

/-! ## Angles -/

/-- The angle of a small deviation. -/
theorem arcsin_abs_le (S : ℝ) (h : |S| ≤ 1 / 100) : |arcsin S| ≤ 1001 / 1000 * |S| := by
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 100 → arcsin x ≤ 1001 / 1000 * x := by
    intro x h0 h1
    rcases eq_or_lt_of_le h0 with rfl | hpos
    · simp
    · have hy0 : 0 < 1001 / 1000 * x := by positivity
      have hpi := Real.pi_gt_three
      rw [arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩]
      have hs := sin_gt_sub_cube hy0
      have hx2 : (1001 / 1000 * x) ^ 2 ≤ 1 / 5000 := by nlinarith
      have hx3 : (1001 / 1000 * x) ^ 3 ≤ 1001 / 1000 * x * (1 / 5000) := by
        have e : (1001 / 1000 * x) ^ 3 = 1001 / 1000 * x * (1001 / 1000 * x) ^ 2 := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hx2 hy0.le
      linarith
  rcases le_total 0 S with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    rw [abs_of_nonneg (arcsin_nonneg.mpr h0)]
    exact key S h0 h
  · rw [abs_of_nonpos h0] at h ⊢
    rw [abs_of_nonpos (arcsin_nonpos.mpr h0), ← arcsin_neg]
    exact key (-S) (by linarith) h

theorem cos_arcsin_of (C S : ℝ) (h : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C) : cos (arcsin S) = C := by
  rw [cos_arcsin, show 1 - S ^ 2 = C ^ 2 by linarith, Real.sqrt_sq hC]

theorem sin_arcsin_of (C S : ℝ) (h : C ^ 2 + S ^ 2 = 1) : sin (arcsin S) = S := by
  have h1 : S ^ 2 ≤ 1 := by nlinarith [sq_nonneg C]
  have h2 := abs_le.mp (abs_le_one_of_sq_le_one h1)
  exact sin_arcsin h2.1 h2.2

theorem c12_sq_add_s12_sq (k : ℕ) (hk : k < 12) : c12 k ^ 2 + s12 k ^ 2 = 1 := by
  rw [← cos_tab k hk, ← sin_tab k hk]
  exact cos_sq_add_sin_sq _

/-- The cosine of the angle `arcsin S + k π / 6`. -/
theorem cos_gauge (k : ℕ) (hk : k < 12) (C S : ℝ) (h : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C) :
    cos (arcsin S + (k : ℝ) * (π / 6)) = c12 k * C - s12 k * S := by
  rw [cos_add, cos_arcsin_of C S h hC, sin_arcsin_of C S h, cos_tab k hk, sin_tab k hk]
  ring

/-- The sine of the angle `arcsin S + k π / 6`. -/
theorem sin_gauge (k : ℕ) (hk : k < 12) (C S : ℝ) (h : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C) :
    sin (arcsin S + (k : ℝ) * (π / 6)) = s12 k * C + c12 k * S := by
  rw [sin_add, cos_arcsin_of C S h hC, sin_arcsin_of C S h, cos_tab k hk, sin_tab k hk]
  ring

/-! ## The cosine of the angle between two points of the rings -/

/-- **The cosine of the angle between two points of the rings.** `a`, `b` are the heights of the two points over
the first pole, `ρa`, `ρb` the radii of their parallels, `d` is their inner product, `m = ± h²`, and `c` is the
cosine of the candidate. -/
theorem cos_dev (h a b ρa ρb d m c : ℝ) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (hρa0 : 0 ≤ ρa)
    (hρb0 : 0 ≤ ρb) (hρa : |ρa ^ 2 - (1 - h ^ 2)| ≤ 39 / 200000 * (2 * h + 39 / 200000))
    (hρb : |ρb ^ 2 - (1 - h ^ 2)| ≤ 39 / 200000 * (2 * h + 39 / 200000))
    (hab : |a * b - m| ≤ 39 / 200000 * (2 * h + 39 / 200000))
    (hd : |d - (m + (1 - h ^ 2) * c)| ≤ 39 / 200000) (hc : |c| ≤ 1) :
    |(d - a * b) / (ρa * ρb) - c| ≤ 351 / 500000 := by
  obtain ⟨hh1, hh2⟩ := hh
  have hq1 : 79261 / 100000 ≤ 1 - h ^ 2 := by nlinarith
  have hδ1 : 39 / 200000 * (2 * h + 39 / 200000) ≤ 1777 / 10000000 := by linarith
  have hδ0 : 0 ≤ 39 / 200000 * (2 * h + 39 / 200000) := by positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - h ^ 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 39 / 200000 * (2 * h + 39 / 200000) := ⟨_, rfl⟩
  rw [← hq] at hq1 hρa hρb hd
  rw [← hδ] at hδ1 hδ0 hρa hρb hab
  have ha' := abs_le.mp hρa
  have hb' := abs_le.mp hρb
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ρa * ρb := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact mul_nonneg hρa0 hρb0
  have hR2 : R ^ 2 = ρa ^ 2 * ρb ^ 2 := by
    rw [hR]
    ring
  have hpos : 0 < q - δ := by linarith
  have hRlo : q - δ ≤ R := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : R ^ 2 < (q - δ) ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg hpos hR0)]
    have h2 : (q - δ) * (q - δ) ≤ ρa ^ 2 * ρb ^ 2 :=
      mul_le_mul (by linarith) (by linarith) hpos.le (by linarith)
    nlinarith
  have hRhi : R ≤ q + δ := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (q + δ) ^ 2 < R ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg (by linarith : (0 : ℝ) < q + δ) hR0)]
    have h2 : ρa ^ 2 * ρb ^ 2 ≤ (q + δ) * (q + δ) :=
      mul_le_mul (by linarith) (by linarith) (sq_nonneg ρb) (by linarith)
    nlinarith
  have hG : |(d - a * b) - q * c| ≤ 39 / 200000 + δ := by
    have e : (d - a * b) - q * c = (d - (m + q * c)) - (a * b - m) := by ring
    rw [e]
    calc |(d - (m + q * c)) - (a * b - m)| ≤ |d - (m + q * c)| + |a * b - m| := abs_sub _ _
      _ ≤ 39 / 200000 + δ := by linarith
  have hRc : |(q - R) * c| ≤ δ * 1 := abs_mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) hc
  have hGR : |(d - a * b) - R * c| ≤ 39 / 200000 + 2 * δ := by
    have e : (d - a * b) - R * c = ((d - a * b) - q * c) + (q - R) * c := by ring
    rw [e]
    calc |((d - a * b) - q * c) + (q - R) * c| ≤ |(d - a * b) - q * c| + |(q - R) * c| := abs_add_le _ _
      _ ≤ 39 / 200000 + 2 * δ := by linarith
  have hRpos : 0 < R := by linarith
  have e : (d - a * b) / R - c = ((d - a * b) - R * c) / R := by
    field_simp
  rw [e, abs_div, abs_of_pos hRpos, div_le_iff₀ hRpos]
  linarith

end N14.Plane
