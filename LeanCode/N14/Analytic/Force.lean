module

public import N14.Basic
public import N32.Gram

/-!
# The theorem for 14 points, analytic part: the forces at the points of the candidate (row A10, first part)

Let `u c`, `c = 0, …, 8`, be weights of the nine classes of pairs of the family `X14 h`. The *force* at the point
`i` is the vector `∑_{j ≠ i} u (class of i, j) • X_j`. If the weights satisfy the one relation `starc u h = 0`,
the force at every point is a multiple of the point: `cfc u h i • X_i`.

* `force_scalar`: the inner products of this identity with three points of the family, as an identity between
  polynomials in `u`, `h` and `√3`, for the 42 pairs of a point and a test point;
* `triple_indep`: a vector orthogonal to three unit vectors with the inner products `h, h, g` vanishes;
* `force_vector`: the identity for the vectors.
-/

@[expose] public section

namespace N14

open Finset

/-- The Gram matrix of the family, for natural labels. -/
noncomputable def gramc (h : ℝ) (t j : ℕ) : ℝ := if t = j then 1 else ipVal h (pcS t j)

/-- The factor of a point in the force identity. -/
noncomputable def cfc (u : ℕ → ℝ) (h : ℝ) (i : ℕ) : ℝ :=
  if i < 2 then -u 0 + 6 * h * (u 1 - u 2) else u 3 - u 4 - u 5 + √3 * u 6 - √3 * u 8

/-- The relation between the weights: the stationarity of the family. -/
noncomputable def starc (u : ℕ → ℝ) (h : ℝ) : ℝ :=
  (u 1 - u 2) + h * (u 3 + 3 * u 4 + 2 * u 5 - (2 + √3) * u 6 - 2 * u 7 - (2 - √3) * u 8)

/-- The inner product of the force at the point `i` with the point `t`. -/
noncomputable def fsum (u : ℕ → ℝ) (h : ℝ) (i t : ℕ) : ℝ :=
  ∑ j ∈ range 14, (if j = i then 0 else u (pcS i j)) * gramc h t j

theorem force_pole (u : ℕ → ℝ) (h : ℝ) (i t : ℕ) (hi : i < 2) (ht : t = 0 ∨ t = 2 ∨ t = 3) :
    fsum u h i t = cfc u h i * gramc h t i := by
  interval_cases i <;> rcases ht with rfl | rfl | rfl <;>
    (simp only [fsum, Finset.sum_range_succ, Finset.sum_range_zero]
     norm_num [pcS, pc, gramc, ipVal, cfc]
     ring)

theorem force_upper (u : ℕ → ℝ) (h : ℝ) (hst : starc u h = 0) (i t : ℕ) (h2 : 2 ≤ i) (h8 : i < 8)
    (ht : t = 0 ∨ t = 2 ∨ t = 3) : fsum u h i t = cfc u h i * gramc h t i := by
  unfold starc at hst
  interval_cases i <;> rcases ht with rfl | rfl | rfl <;>
    (simp only [fsum, Finset.sum_range_succ, Finset.sum_range_zero]
     norm_num [pcS, pc, gramc, ipVal, cfc]
     first | linear_combination hst | linear_combination h * hst)

theorem force_lower (u : ℕ → ℝ) (h : ℝ) (hst : starc u h = 0) (i t : ℕ) (h8 : 8 ≤ i) (h14 : i < 14)
    (ht : t = 1 ∨ t = 8 ∨ t = 9) : fsum u h i t = cfc u h i * gramc h t i := by
  unfold starc at hst
  interval_cases i <;> rcases ht with rfl | rfl | rfl <;>
    (simp only [fsum, Finset.sum_range_succ, Finset.sum_range_zero]
     norm_num [pcS, pc, gramc, ipVal, cfc]
     first | linear_combination hst | linear_combination h * hst)

/-! ## From the inner products to the vectors -/

/-- A vector orthogonal to three unit vectors with the inner products `h`, `h`, `g` vanishes, if the Gram
determinant `(1 - g) (1 + g - 2 h²)` does not. -/
theorem triple_indep (v0 v1 v2 : Fin 3 → ℝ) (h g : ℝ) (e00 : ∑ c, v0 c * v0 c = 1) (e11 : ∑ c, v1 c * v1 c = 1)
    (e22 : ∑ c, v2 c * v2 c = 1) (e01 : ∑ c, v0 c * v1 c = h) (e02 : ∑ c, v0 c * v2 c = h)
    (e12 : ∑ c, v1 c * v2 c = g) (hdet : (1 - g) * (1 + g - 2 * h ^ 2) ≠ 0) (w : Fin 3 → ℝ)
    (h0 : ∑ c, v0 c * w c = 0) (h1 : ∑ c, v1 c * w c = 0) (h2 : ∑ c, v2 c * w c = 0) : w = 0 := by
  have e10 : ∑ c, v1 c * v0 c = h := by
    rw [← e01]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have e20 : ∑ c, v2 c * v0 c = h := by
    rw [← e02]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have e21 : ∑ c, v2 c * v1 c = g := by
    rw [← e12]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  obtain ⟨B, hB⟩ : ∃ B : Fin 3 → Fin 3 → ℝ, B = ![v0, v1, v2] := ⟨_, rfl⟩
  have b0 : B 0 = v0 := by rw [hB]; rfl
  have b1 : B 1 = v1 := by rw [hB]; rfl
  have b2 : B 2 = v2 := by rw [hB]; rfl
  have hd : (N32.gram3 B).det = (1 - g) * (1 + g - 2 * h ^ 2) := by
    rw [Matrix.det_fin_three]
    simp only [N32.gram3, Matrix.of_apply, b0, b1, b2, e00, e01, e02, e10, e11, e12, e20, e21, e22]
    ring
  refine N32.eq_zero_of_orth B (by rw [hd]; exact hdet) w (fun k => ?_)
  fin_cases k
  · show ∑ c, B 0 c * w c = 0
    rw [b0]
    exact h0
  · show ∑ c, B 1 c * w c = 0
    rw [b1]
    exact h1
  · show ∑ c, B 2 c * w c = 0
    rw [b2]
    exact h2

/-- The inner products of the points of the family. -/
theorem dot_X14_gramc (h : ℝ) (hh : h ^ 2 ≤ 1) (s t : Fin 14) :
    ∑ c, X14 h s c * X14 h t c = gramc h s.val t.val := by
  unfold gramc
  by_cases e : s.val = t.val
  · rw [if_pos e]
    have e' : s = t := Fin.ext e
    subst e'
    have := norm_X14N h hh s.val
    rw [← this]
    exact Finset.sum_congr rfl fun c _ => by
      show X14N h s.val c * X14N h s.val c = X14N h s.val c ^ 2
      ring
  · rw [if_neg e]
    exact dot_X14 h hh s t (fun e' => e (congrArg Fin.val e'))

/-- **The force at a point of the family is a multiple of the point**, if the weights satisfy the relation
`starc u h = 0`. -/
theorem force_vector (u : ℕ → ℝ) (h : ℝ) (h0 : 0 < h) (h1 : h < 1) (hst : starc u h = 0) (i : Fin 14)
    (k : Fin 3) :
    ∑ j : Fin 14, (if j.val = i.val then 0 else u (pcS i.val j.val)) * X14 h j k
      = cfc u h i.val * X14 h i k := by
  have hh : h ^ 2 ≤ 1 := by nlinarith
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → ℝ, w = fun k =>
      ∑ j : Fin 14, (if j.val = i.val then 0 else u (pcS i.val j.val)) * X14 h j k - cfc u h i.val * X14 h i k :=
    ⟨_, rfl⟩
  -- the inner product of `w` with a point of the family
  have key : ∀ t : Fin 14, ∑ c, X14 h t c * w c = fsum u h i.val t.val - cfc u h i.val * gramc h t.val i.val := by
    intro t
    have e1 : ∑ c, X14 h t c * w c
        = ∑ c, ∑ j : Fin 14, (if j.val = i.val then 0 else u (pcS i.val j.val)) * (X14 h t c * X14 h j c)
          - cfc u h i.val * ∑ c, X14 h t c * X14 h i c := by
      rw [hw, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · ring
    rw [e1, Finset.sum_comm]
    have e2 : ∀ j : Fin 14, ∑ c, (if j.val = i.val then 0 else u (pcS i.val j.val)) * (X14 h t c * X14 h j c)
        = (if j.val = i.val then 0 else u (pcS i.val j.val)) * gramc h t.val j.val := by
      intro j
      rw [← Finset.mul_sum, dot_X14_gramc h hh t j]
    rw [Finset.sum_congr rfl fun j _ => e2 j, dot_X14_gramc h hh t i]
    unfold fsum
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if j = i.val then 0 else u (pcS i.val j)) * gramc h t.val j) 14]
  have hg : (1 - ipVal h 3) * (1 + ipVal h 3 - 2 * h ^ 2) ≠ 0 := by
    have e : (1 - ipVal h 3) * (1 + ipVal h 3 - 2 * h ^ 2) = 3 / 4 * (1 - h ^ 2) ^ 2 := by
      simp only [ipVal]
      ring
    rw [e]
    have : (0 : ℝ) < 1 - h ^ 2 := by nlinarith
    positivity
  have hw0 : w = 0 := by
    by_cases h8 : i.val < 8
    · refine triple_indep (X14 h 0) (X14 h 2) (X14 h 3) h (ipVal h 3) ?_ ?_ ?_ ?_ ?_ ?_ hg w ?_ ?_ ?_
      · rw [dot_X14_gramc h hh]; norm_num [gramc]
      · rw [dot_X14_gramc h hh]; norm_num [gramc]
      · rw [dot_X14_gramc h hh]; norm_num [gramc]
      · rw [dot_X14_gramc h hh]; norm_num [gramc, pcS, pc, ipVal]
      · rw [dot_X14_gramc h hh]; norm_num [gramc, pcS, pc, ipVal]
      · rw [dot_X14_gramc h hh]; norm_num [gramc, pcS, pc]
      · rw [key 0]
        show fsum u h i.val 0 - cfc u h i.val * gramc h 0 i.val = 0
        by_cases h2 : i.val < 2
        · rw [force_pole u h i.val 0 h2 (Or.inl rfl)]
          ring
        · rw [force_upper u h hst i.val 0 (by omega) h8 (Or.inl rfl)]
          ring
      · rw [key 2]
        show fsum u h i.val 2 - cfc u h i.val * gramc h 2 i.val = 0
        by_cases h2 : i.val < 2
        · rw [force_pole u h i.val 2 h2 (Or.inr (Or.inl rfl))]
          ring
        · rw [force_upper u h hst i.val 2 (by omega) h8 (Or.inr (Or.inl rfl))]
          ring
      · rw [key 3]
        show fsum u h i.val 3 - cfc u h i.val * gramc h 3 i.val = 0
        by_cases h2 : i.val < 2
        · rw [force_pole u h i.val 3 h2 (Or.inr (Or.inr rfl))]
          ring
        · rw [force_upper u h hst i.val 3 (by omega) h8 (Or.inr (Or.inr rfl))]
          ring
    · refine triple_indep (X14 h 1) (X14 h 8) (X14 h 9) h (ipVal h 3) ?_ ?_ ?_ ?_ ?_ ?_ hg w ?_ ?_ ?_
      · rw [dot_X14_gramc h hh]; norm_num [gramc]
      · rw [dot_X14_gramc h hh]; norm_num [gramc]
      · rw [dot_X14_gramc h hh]; norm_num [gramc]
      · rw [dot_X14_gramc h hh]; norm_num [gramc, pcS, pc, ipVal]
      · rw [dot_X14_gramc h hh]; norm_num [gramc, pcS, pc, ipVal]
      · rw [dot_X14_gramc h hh]; norm_num [gramc, pcS, pc]
      · rw [key 1]
        show fsum u h i.val 1 - cfc u h i.val * gramc h 1 i.val = 0
        rw [force_lower u h hst i.val 1 (by omega) i.isLt (Or.inl rfl)]
        ring
      · rw [key 8]
        show fsum u h i.val 8 - cfc u h i.val * gramc h 8 i.val = 0
        rw [force_lower u h hst i.val 8 (by omega) i.isLt (Or.inr (Or.inl rfl))]
        ring
      · rw [key 9]
        show fsum u h i.val 9 - cfc u h i.val * gramc h 9 i.val = 0
        rw [force_lower u h hst i.val 9 (by omega) i.isLt (Or.inr (Or.inr rfl))]
        ring
  have := congrFun hw0 k
  rw [hw] at this
  exact sub_eq_zero.mp this

end N14
