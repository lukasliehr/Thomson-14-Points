module

public import N14.Box.Quad

/-!
# T7, the domain of a run of a node in the coordinates of the source

The source describes the local region of a node by coordinates `y`: `x = s + M y` with the node `s`, a matrix `M`
and an ellipsoid `∑ (y_j / σ_j)² ≤ 1`. A run of `N14.Box` describes its domain by cuts of the coordinates `x` and
by polynomial constraints whose coefficients are rounded. The lemmas of this file are the steps from the first
description to the second one:

* `coord_bound`: a coordinate of a point of the ellipsoid lies in an interval around the coordinate of the node
  (Cauchy–Schwarz, `cs3`);
* `quad10_nonneg`: a polynomial of degree two whose constant is at least the sum of the absolute values of its
  other coefficients is nonnegative on the cube; this is the rounding of a constraint;
* `forall_polys2`: a statement about the two polynomial constraints of a run.
-/

@[expose] public section

namespace N14.Box

theorem cs3' (a1 a2 a3 b1 b2 b3 : ℝ) :
    (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 ≤ (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) := by
  nlinarith [sq_nonneg (a1 * b2 - a2 * b1), sq_nonneg (a1 * b3 - a3 * b1), sq_nonneg (a2 * b3 - a3 * b2)]

/-- The inequality of Cauchy and Schwarz for three terms with weights. -/
theorem cs3 (m1 m2 m3 y1 y2 y3 σ1 σ2 σ3 : ℝ) (h1 : 0 < σ1) (h2 : 0 < σ2) (h3 : 0 < σ3) :
    (m1 * y1 + m2 * y2 + m3 * y3) ^ 2
      ≤ (m1 ^ 2 * σ1 ^ 2 + m2 ^ 2 * σ2 ^ 2 + m3 ^ 2 * σ3 ^ 2)
        * ((y1 / σ1) ^ 2 + (y2 / σ2) ^ 2 + (y3 / σ3) ^ 2) := by
  have h := cs3' (m1 * σ1) (m2 * σ2) (m3 * σ3) (y1 / σ1) (y2 / σ2) (y3 / σ3)
  have e1 : m1 * σ1 * (y1 / σ1) = m1 * y1 := by field_simp
  have e2 : m2 * σ2 * (y2 / σ2) = m2 * y2 := by field_simp
  have e3 : m3 * σ3 * (y3 / σ3) = m3 * y3 := by field_simp
  rw [e1, e2, e3] at h
  have e4 : (m1 * σ1) ^ 2 + (m2 * σ2) ^ 2 + (m3 * σ3) ^ 2 = m1 ^ 2 * σ1 ^ 2 + m2 ^ 2 * σ2 ^ 2 + m3 ^ 2 * σ3 ^ 2 := by
    ring
  rw [e4] at h
  exact h

/-- **A coordinate of a point of an ellipsoid.** If `x = s + m · y`, the point `y` lies in the ellipsoid with the
semiaxes `σ`, and `∑ m_j² σ_j² ≤ ρ²`, then `|x - s| ≤ ρ`. -/
theorem coord_bound (m1 m2 m3 y1 y2 y3 σ1 σ2 σ3 s x ρ : ℝ) (h1 : 0 < σ1) (h2 : 0 < σ2) (h3 : 0 < σ3)
    (hx : x = s + m1 * y1 + m2 * y2 + m3 * y3) (hE : (y1 / σ1) ^ 2 + (y2 / σ2) ^ 2 + (y3 / σ3) ^ 2 ≤ 1)
    (hρ : 0 ≤ ρ) (hB : m1 ^ 2 * σ1 ^ 2 + m2 ^ 2 * σ2 ^ 2 + m3 ^ 2 * σ3 ^ 2 ≤ ρ ^ 2) :
    s - ρ ≤ x ∧ x ≤ s + ρ := by
  have h := cs3 m1 m2 m3 y1 y2 y3 σ1 σ2 σ3 h1 h2 h3
  have hx' : x - s = m1 * y1 + m2 * y2 + m3 * y3 := by
    rw [hx]
    ring
  have hB0 : 0 ≤ m1 ^ 2 * σ1 ^ 2 + m2 ^ 2 * σ2 ^ 2 + m3 ^ 2 * σ3 ^ 2 := by positivity
  have h2' : (x - s) ^ 2 ≤ ρ ^ 2 := by
    rw [hx']
    calc (m1 * y1 + m2 * y2 + m3 * y3) ^ 2
        ≤ (m1 ^ 2 * σ1 ^ 2 + m2 ^ 2 * σ2 ^ 2 + m3 ^ 2 * σ3 ^ 2)
          * ((y1 / σ1) ^ 2 + (y2 / σ2) ^ 2 + (y3 / σ3) ^ 2) := h
      _ ≤ (m1 ^ 2 * σ1 ^ 2 + m2 ^ 2 * σ2 ^ 2 + m3 ^ 2 * σ3 ^ 2) * 1 := mul_le_mul_of_nonneg_left hE hB0
      _ ≤ ρ ^ 2 := by
        rw [mul_one]
        exact hB
  have h3' := abs_le_of_sq_le_sq' h2' hρ
  constructor
  · linarith [h3'.1]
  · linarith [h3'.2]

/-- A ball is the ellipsoid with three equal semiaxes. -/
theorem ball_ellipsoid (y1 y2 y3 r r2 : ℝ) (hr : 0 < r) (h : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ r2) (hr2 : r2 ≤ r ^ 2) :
    (y1 / r) ^ 2 + (y2 / r) ^ 2 + (y3 / r) ^ 2 ≤ 1 := by
  have e : (y1 / r) ^ 2 + (y2 / r) ^ 2 + (y3 / r) ^ 2 = (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) / r ^ 2 := by
    field_simp
  rw [e, div_le_one (by positivity)]
  linarith

theorem mul_ge_neg (d b m : ℝ) (hd : |d| ≤ b) (hm : |m| ≤ 1) : -b ≤ d * m := by
  have h : |d * m| ≤ b := by
    rw [abs_mul]
    calc |d| * |m| ≤ |d| * 1 := mul_le_mul_of_nonneg_left hm (abs_nonneg d)
      _ ≤ b := by
        rw [mul_one]
        exact hd
  exact (abs_le.mp h).1

theorem abs_mul_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  calc |a| * |b| ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg b) (by norm_num)
    _ = 1 := by norm_num

/-- **The rounding of a constraint.** A polynomial of degree two in three variables whose constant is at least
the sum of bounds for the absolute values of its other coefficients is nonnegative on the cube. -/
theorem quad10_nonneg (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 b1 b2 b3 b4 b5 b6 b7 b8 b9 x1 x2 x3 : ℝ)
    (hx1 : |x1| ≤ 1) (hx2 : |x2| ≤ 1) (hx3 : |x3| ≤ 1)
    (h1 : |d1| ≤ b1) (h2 : |d2| ≤ b2) (h3 : |d3| ≤ b3) (h4 : |d4| ≤ b4) (h5 : |d5| ≤ b5) (h6 : |d6| ≤ b6)
    (h7 : |d7| ≤ b7) (h8 : |d8| ≤ b8) (h9 : |d9| ≤ b9) (hd : b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 ≤ d0) :
    0 ≤ d0 + d1 * x1 + d2 * x2 + d3 * x3 + d4 * (x1 * x1) + d5 * (x1 * x2) + d6 * (x1 * x3) + d7 * (x2 * x2)
      + d8 * (x2 * x3) + d9 * (x3 * x3) := by
  have a1 := mul_ge_neg d1 b1 x1 h1 hx1
  have a2 := mul_ge_neg d2 b2 x2 h2 hx2
  have a3 := mul_ge_neg d3 b3 x3 h3 hx3
  have a4 := mul_ge_neg d4 b4 (x1 * x1) h4 (abs_mul_le_one hx1 hx1)
  have a5 := mul_ge_neg d5 b5 (x1 * x2) h5 (abs_mul_le_one hx1 hx2)
  have a6 := mul_ge_neg d6 b6 (x1 * x3) h6 (abs_mul_le_one hx1 hx3)
  have a7 := mul_ge_neg d7 b7 (x2 * x2) h7 (abs_mul_le_one hx2 hx2)
  have a8 := mul_ge_neg d8 b8 (x2 * x3) h8 (abs_mul_le_one hx2 hx3)
  have a9 := mul_ge_neg d9 b9 (x3 * x3) h9 (abs_mul_le_one hx3 hx3)
  linarith

/-- **The rounding of a constraint, with natural numbers.** The coefficients are `(p_k - q_k) / D`; the
polynomial is nonnegative on the cube if `q_0 + ∑_{k ≥ 1} (p_k + q_k) ≤ p_0`. The generated modules use this form:
the hypothesis is one comparison of natural numbers (`decide`), where `quad10_nonneg` needs nineteen calls of
`norm_num` with rational numbers. -/
theorem quad10_nat (D p0 q0 p1 q1 p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 p7 q7 p8 q8 p9 q9 : ℕ) (x1 x2 x3 : ℝ)
    (hx1 : |x1| ≤ 1) (hx2 : |x2| ≤ 1) (hx3 : |x3| ≤ 1) (hD : 0 < D)
    (h : q0 + (p1 + q1) + (p2 + q2) + (p3 + q3) + (p4 + q4) + (p5 + q5) + (p6 + q6) + (p7 + q7) + (p8 + q8)
      + (p9 + q9) ≤ p0) :
    0 ≤ ((p0 : ℝ) - q0) / D + ((p1 : ℝ) - q1) / D * x1 + ((p2 : ℝ) - q2) / D * x2 + ((p3 : ℝ) - q3) / D * x3
      + ((p4 : ℝ) - q4) / D * (x1 * x1) + ((p5 : ℝ) - q5) / D * (x1 * x2) + ((p6 : ℝ) - q6) / D * (x1 * x3)
      + ((p7 : ℝ) - q7) / D * (x2 * x2) + ((p8 : ℝ) - q8) / D * (x2 * x3) + ((p9 : ℝ) - q9) / D * (x3 * x3) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hr : (q0 : ℝ) + ((p1 : ℝ) + q1) + ((p2 : ℝ) + q2) + ((p3 : ℝ) + q3) + ((p4 : ℝ) + q4) + ((p5 : ℝ) + q5)
      + ((p6 : ℝ) + q6) + ((p7 : ℝ) + q7) + ((p8 : ℝ) + q8) + ((p9 : ℝ) + q9) ≤ p0 := by exact_mod_cast h
  have ab : ∀ p q : ℕ, |((p : ℝ) - q) / D| ≤ ((p : ℝ) + q) / D := by
    intro p q
    have h1 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h2 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [abs_div, abs_of_pos hD']
    have h3 : |(p : ℝ) - q| ≤ (p : ℝ) + q := by
      rw [abs_le]
      constructor <;> linarith
    gcongr
  refine quad10_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x1 x2 x3 hx1 hx2 hx3 (ab p1 q1) (ab p2 q2) (ab p3 q3)
    (ab p4 q4) (ab p5 q5) (ab p6 q6) (ab p7 q7) (ab p8 q8) (ab p9 q9) ?_
  have e : ((p1 : ℝ) + q1) / D + ((p2 : ℝ) + q2) / D + ((p3 : ℝ) + q3) / D + ((p4 : ℝ) + q4) / D
      + ((p5 : ℝ) + q5) / D + ((p6 : ℝ) + q6) / D + ((p7 : ℝ) + q7) / D + ((p8 : ℝ) + q8) / D + ((p9 : ℝ) + q9) / D
      = (((p1 : ℝ) + q1) + ((p2 : ℝ) + q2) + ((p3 : ℝ) + q3) + ((p4 : ℝ) + q4) + ((p5 : ℝ) + q5) + ((p6 : ℝ) + q6)
        + ((p7 : ℝ) + q7) + ((p8 : ℝ) + q8) + ((p9 : ℝ) + q9)) / D := by
    ring
  rw [e]
  have h4 : ((p1 : ℝ) + q1) + ((p2 : ℝ) + q2) + ((p3 : ℝ) + q3) + ((p4 : ℝ) + q4) + ((p5 : ℝ) + q5) + ((p6 : ℝ) + q6)
      + ((p7 : ℝ) + q7) + ((p8 : ℝ) + q8) + ((p9 : ℝ) + q9) ≤ (p0 : ℝ) - q0 := by
    linarith
  gcongr

/-- A statement about the two polynomial constraints of a run. -/
theorem forall_polys2 (l : List ℕ) (hl : l.length = 2) (Q : ℕ → Prop) (h0 : Q (l.getD 0 0))
    (h1 : Q (l.getD 1 0)) : ∀ Pp ∈ l, Q Pp := by
  match l, hl with
  | [a, b], _ =>
    intro Pp hPp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hPp
    rcases hPp with rfl | rfl
    · exact h0
    · exact h1

/-- A statement about all polynomial constraints of a run, by their numbers in the list. -/
theorem forall_polys (l : List ℕ) (Q : ℕ → Prop) (h : ∀ i, i < l.length → Q (l.getD i 0)) : ∀ Pp ∈ l, Q Pp := by
  intro Pp hPp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hPp
  have h2 := h i hi
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h2

/-- A product with a factor of absolute value at most `a`. -/
theorem two_mul_le (b a z w : ℝ) (h : |b| ≤ a) : 2 * b * (z * w) ≤ a * (z ^ 2 + w ^ 2) := by
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (z + w)), mul_nonneg (by linarith : (0 : ℝ) ≤ a + b) (sq_nonneg (z - w))]

/-- **A symmetric quadratic form in three variables** is at most a bound for its absolute row sums times the
square of the norm. -/
theorem quad3_le (b11 b22 b33 b12 b13 b23 a12 a13 a23 R z1 z2 z3 : ℝ) (h12 : |b12| ≤ a12) (h13 : |b13| ≤ a13)
    (h23 : |b23| ≤ a23) (r1 : b11 + a12 + a13 ≤ R) (r2 : b22 + a12 + a23 ≤ R) (r3 : b33 + a13 + a23 ≤ R) :
    b11 * z1 ^ 2 + b22 * z2 ^ 2 + b33 * z3 ^ 2 + 2 * b12 * (z1 * z2) + 2 * b13 * (z1 * z3) + 2 * b23 * (z2 * z3)
      ≤ R * (z1 ^ 2 + z2 ^ 2 + z3 ^ 2) := by
  have e1 := two_mul_le b12 a12 z1 z2 h12
  have e2 := two_mul_le b13 a13 z1 z3 h13
  have e3 := two_mul_le b23 a23 z2 z3 h23
  have d1 := mul_le_mul_of_nonneg_right r1 (sq_nonneg z1)
  have d2 := mul_le_mul_of_nonneg_right r2 (sq_nonneg z2)
  have d3 := mul_le_mul_of_nonneg_right r3 (sq_nonneg z3)
  nlinarith

/-- **A ball around a nearby centre.** A point of the ball of radius `r` around `q` lies in the ball around `s`
whose squared radius is `ρ2`, if `ρ2` is at least `r² + 2 r ∑ d_a + ∑ d_a²` for bounds `d_a` of `|q_a - s_a|`. -/
theorem ball_shift (x1 x2 x3 q1 q2 q3 s1 s2 s3 d1 d2 d3 r r2 ρ2 : ℝ) (hr : 0 ≤ r) (hr2 : r2 ≤ r ^ 2)
    (hb : (x1 - q1) ^ 2 + (x2 - q2) ^ 2 + (x3 - q3) ^ 2 ≤ r2) (h1 : |q1 - s1| ≤ d1) (h2 : |q2 - s2| ≤ d2)
    (h3 : |q3 - s3| ≤ d3) (hρ : r ^ 2 + 2 * r * (d1 + d2 + d3) + (d1 ^ 2 + d2 ^ 2 + d3 ^ 2) ≤ ρ2) :
    (x1 - s1) ^ 2 + (x2 - s2) ^ 2 + (x3 - s3) ^ 2 ≤ ρ2 := by
  have step : ∀ x q s d : ℝ, (x - q) ^ 2 ≤ r ^ 2 → |q - s| ≤ d →
      (x - s) ^ 2 ≤ (x - q) ^ 2 + 2 * r * d + d ^ 2 := by
    intro x q s d hx hd
    have ha := abs_le_of_sq_le_sq' hx hr
    have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
    have hq := abs_le.mp hd
    have e : (x - s) ^ 2 = (x - q) ^ 2 + 2 * ((x - q) * (q - s)) + (q - s) ^ 2 := by ring
    have c1 : (x - q) * (q - s) ≤ r * d := by
      have h4 : |(x - q) * (q - s)| ≤ r * d := by
        rw [abs_mul]
        exact mul_le_mul (abs_le.mpr ha) hd (abs_nonneg _) hr
      exact le_trans (le_abs_self _) h4
    have c2 : (q - s) ^ 2 ≤ d ^ 2 := by
      have := sq_abs (q - s)
      rw [← this]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [e]
    linarith
  have s1' := step x1 q1 s1 d1 (by nlinarith [sq_nonneg (x2 - q2), sq_nonneg (x3 - q3)]) h1
  have s2' := step x2 q2 s2 d2 (by nlinarith [sq_nonneg (x1 - q1), sq_nonneg (x3 - q3)]) h2
  have s3' := step x3 q3 s3 d3 (by nlinarith [sq_nonneg (x1 - q1), sq_nonneg (x2 - q2)]) h3
  nlinarith

/-- **A positive semidefinite quadratic form in three variables** (the criterion of Sylvester, by completing
squares): the form with the entries `a11, a22, a33, a12, a13, a23` is nonnegative if `a11 > 0`, the minor of
order two is positive and the determinant, in the form of the second step of the elimination, is nonnegative. -/
theorem quad3_psd (a11 a22 a33 a12 a13 a23 y1 y2 y3 : ℝ) (h1 : 0 < a11) (h2 : 0 < a11 * a22 - a12 ^ 2)
    (h3 : 0 ≤ (a11 * a22 - a12 ^ 2) * (a11 * a33 - a13 ^ 2) - (a11 * a23 - a12 * a13) ^ 2) :
    0 ≤ a11 * y1 ^ 2 + a22 * y2 ^ 2 + a33 * y3 ^ 2 + 2 * a12 * (y1 * y2) + 2 * a13 * (y1 * y3)
      + 2 * a23 * (y2 * y3) := by
  set p := a11 * a22 - a12 ^ 2 with hp
  set q := a11 * a23 - a12 * a13 with hq
  set s := a11 * a33 - a13 ^ 2 with hs
  -- the form of the last two variables after the first step
  have e2 : p * (p * y2 ^ 2 + 2 * q * (y2 * y3) + s * y3 ^ 2) = (p * y2 + q * y3) ^ 2 + (p * s - q ^ 2) * y3 ^ 2 := by
    ring
  have r2 : 0 ≤ p * y2 ^ 2 + 2 * q * (y2 * y3) + s * y3 ^ 2 := by
    have h4 : 0 ≤ p * (p * y2 ^ 2 + 2 * q * (y2 * y3) + s * y3 ^ 2) := by
      rw [e2]
      exact add_nonneg (sq_nonneg _) (mul_nonneg h3 (sq_nonneg _))
    exact nonneg_of_mul_nonneg_right h4 h2
  have e1 : a11 * (a11 * y1 ^ 2 + a22 * y2 ^ 2 + a33 * y3 ^ 2 + 2 * a12 * (y1 * y2) + 2 * a13 * (y1 * y3)
      + 2 * a23 * (y2 * y3))
      = (a11 * y1 + a12 * y2 + a13 * y3) ^ 2 + (p * y2 ^ 2 + 2 * q * (y2 * y3) + s * y3 ^ 2) := by
    rw [hp, hq, hs]
    ring
  have h5 : 0 ≤ a11 * (a11 * y1 ^ 2 + a22 * y2 ^ 2 + a33 * y3 ^ 2 + 2 * a12 * (y1 * y2) + 2 * a13 * (y1 * y3)
      + 2 * a23 * (y2 * y3)) := by
    rw [e1]
    exact add_nonneg (sq_nonneg _) r2
  exact nonneg_of_mul_nonneg_right h5 h1

/-! ### The cuts and the forms of a region, by terms

The generated modules of the nodes prove the cuts of a domain and the forms of a region by the following lemmas,
not by `simp` and `linarith` over the whole context: with about twenty hypotheses that contain rational numbers of
fifty digits, one call of `linarith` takes half a second (`N14/STATUS.md`, third stage, the Lean time). -/

/-- A cut `x_a + 1 ≥ vn / vd` holds at a point whose coordinate `a` is at least `u ≥ vn / vd - 1`. -/
theorem cut_ge (a b vn vd : ℕ) (x1 x2 x3 x u : ℝ) (hx : co a x1 x2 x3 = x) (h : u ≤ x)
    (hu : (vn : ℝ) / vd - 1 ≤ u) : 0 ≤ cutVal ⟨0, a, b, vn, vd⟩ x1 x2 x3 := by
  have e : cutVal ⟨0, a, b, vn, vd⟩ x1 x2 x3 = co a x1 x2 x3 + 1 - (vn : ℝ) / vd := by simp [cutVal]
  rw [e, hx]
  linarith

/-- A cut `x_a + 1 ≤ vn / vd` holds at a point whose coordinate `a` is at most `u ≤ vn / vd - 1`. -/
theorem cut_le (a b vn vd : ℕ) (x1 x2 x3 x u : ℝ) (hx : co a x1 x2 x3 = x) (h : x ≤ u)
    (hu : u ≤ (vn : ℝ) / vd - 1) : 0 ≤ cutVal ⟨1, a, b, vn, vd⟩ x1 x2 x3 := by
  have e : cutVal ⟨1, a, b, vn, vd⟩ x1 x2 x3 = (vn : ℝ) / vd - co a x1 x2 x3 - 1 := by simp [cutVal]
  rw [e, hx]
  linarith

/-- A cut `x_a ≥ x_b`. -/
theorem cut_ord (a b vn vd : ℕ) (x1 x2 x3 x y : ℝ) (hx : co a x1 x2 x3 = x) (hy : co b x1 x2 x3 = y)
    (h : y ≤ x) : 0 ≤ cutVal ⟨2, a, b, vn, vd⟩ x1 x2 x3 := by
  have e : cutVal ⟨2, a, b, vn, vd⟩ x1 x2 x3 = co a x1 x2 x3 - co b x1 x2 x3 := by simp [cutVal]
  rw [e, hx, hy]
  linarith

/-- A statement about all entries of a list, entry by entry. -/
theorem forall_cons {α : Type} {P : α → Prop} {c : α} {l : List α} (h : P c) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ c :: l, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h'
  · exact h
  · exact hl x h'

theorem forall_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  intro x hx
  cases hx

/-- The form `c + |y|²` is nonnegative outside the ball of the squared radius `r = -c`. -/
theorem form_pos (c r y1 y2 y3 : ℝ) (hc : c + r = 0) (h : r ≤ y1 ^ 2 + y2 ^ 2 + y3 ^ 2) :
    0 ≤ c + (1 : ℝ) * y1 ^ 2 + (1 : ℝ) * y2 ^ 2 + (1 : ℝ) * y3 ^ 2 := by
  linarith

/-- The form `c - |y|²` is nonnegative in the ball of the squared radius `c`. -/
theorem form_neg (c y1 y2 y3 : ℝ) (h : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ c) :
    0 ≤ c + (-1 : ℝ) * y1 ^ 2 + (-1 : ℝ) * y2 ^ 2 + (-1 : ℝ) * y3 ^ 2 := by
  linarith

/-- A point that is close to a point close to a third one. -/
theorem abs_shift (q s S e1 e2 d : ℝ) (h1 : |q - s| ≤ e1) (h2 : |s - S| ≤ e2) (hd : e1 + e2 ≤ d) : |q - S| ≤ d := by
  have h := abs_sub_le q s S
  linarith

end N14.Box
