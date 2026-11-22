module

public import N14.Analytic.Critical
public import N14.Analytic.Plane
public import N14.Local.Theorem

/-!
# The theorem for 14 points, analytic part: local minimality (rows A10, third part, and A11)

* `gauge_sphere`, `gauge_dist`: the configuration with the gauge coordinates `pStarN + D`, `|D_k| ≤ 1/125`,
  consists of points of the sphere, and the sum of the squares of the distances of its points from those of the
  candidate is at most `2 |D|²`;
* `dot_lt_one_of_near`: a configuration of the sphere near the candidate has distinct points;
* `linear_zero` (row A10): the linear form of statement 7 vanishes. By `energy_lower` the energy along a line
  `pStarN + t D` is at least `energy Xstar - K' t²`, and by statement 7 it is `energy Xstar + t L(D) + O(t²)`;
* `local_min` (row A11, Proposition 9.1 of the source): `energy Xstar < energyG (pStarN + D)` for
  `0 < |D|₂ ≤ 0.0075`, `|D_k| ≤ 1/125`.
-/

@[expose] public section

namespace N14

open Finset N14.T7 N14.Local

/-! ## The configuration in the gauge is close to the candidate -/

/-- The distance of two points of the sphere with the heights `z`, `z'` and the angles `θ`, `θ'`. -/
theorem ring_dist (z z' θ θ' : ℝ) (hz : |z| ≤ 51 / 100) (hz' : |z'| ≤ 51 / 100) :
    ∑ k, (ringPt z θ k - ringPt z' θ' k) ^ 2 ≤ 2 * (z - z') ^ 2 + (θ - θ') ^ 2 := by
  have hza := abs_le.mp hz
  have hza' := abs_le.mp hz'
  have hz2 : z * z ≤ (51 / 100) ^ 2 := by nlinarith
  have hz2' : z' * z' ≤ (51 / 100) ^ 2 := by nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = √(1 + -(z * z)) := ⟨_, rfl⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = √(1 + -(z' * z')) := ⟨_, rfl⟩
  have hρ2 : ρ ^ 2 = 1 - z * z := by
    rw [hρ, Real.sq_sqrt (by nlinarith)]
    ring
  have hρ2' : ρ' ^ 2 = 1 - z' * z' := by
    rw [hρ', Real.sq_sqrt (by nlinarith)]
    ring
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact Real.sqrt_nonneg _
  have hρ0' : 0 ≤ ρ' := by
    rw [hρ']
    exact Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by nlinarith [mul_self_nonneg z, sq_nonneg (ρ - 1)]
  have hρ1' : ρ' ≤ 1 := by nlinarith [mul_self_nonneg z', sq_nonneg (ρ' - 1)]
  have hρlo : 85 / 100 ≤ ρ := by
    have h1 : (85 / 100 : ℝ) ^ 2 ≤ ρ ^ 2 := by
      rw [hρ2]
      norm_num at hz2 ⊢
      linarith
    have := Plane.le_abs_of_sq_le h1
    rwa [abs_of_nonneg hρ0] at this
  have hρlo' : 85 / 100 ≤ ρ' := by
    have h1 : (85 / 100 : ℝ) ^ 2 ≤ ρ' ^ 2 := by
      rw [hρ2']
      norm_num at hz2' ⊢
      linarith
    have := Plane.le_abs_of_sq_le h1
    rwa [abs_of_nonneg hρ0'] at this
  -- the radii of the parallels
  have hab : (ρ - ρ') * (ρ + ρ') = -((z - z') * (z + z')) := by
    have e : (ρ - ρ') * (ρ + ρ') = ρ ^ 2 - ρ' ^ 2 := by ring
    rw [e, hρ2, hρ2']
    ring
  have hsq : (ρ - ρ') ^ 2 * (ρ + ρ') ^ 2 = (z - z') ^ 2 * (z + z') ^ 2 := by
    have e : (ρ - ρ') ^ 2 * (ρ + ρ') ^ 2 = ((ρ - ρ') * (ρ + ρ')) ^ 2 := by ring
    rw [e, hab]
    ring
  have hb2 : (17 / 10 : ℝ) ^ 2 ≤ (ρ + ρ') ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hd2 : (z + z') ^ 2 ≤ (102 / 100 : ℝ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hr : (ρ - ρ') ^ 2 ≤ (z - z') ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg (ρ - ρ'))
    have h2 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg (z - z'))
    nlinarith [sq_nonneg (z - z'), sq_nonneg (ρ - ρ')]
  -- the angles
  have hc1 : 1 - Real.cos (θ - θ') ≤ (θ - θ') ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := θ - θ')]
  have hc0 : 0 ≤ 1 - Real.cos (θ - θ') := by linarith [Real.cos_le_one (θ - θ')]
  have hρρ : ρ * ρ' ≤ 1 := by nlinarith
  have hang : ρ * ρ' * (1 - Real.cos (θ - θ')) ≤ 1 * ((θ - θ') ^ 2 / 2) :=
    mul_le_mul hρρ hc1 hc0 (by norm_num)
  -- the identity
  have hid : (ρ * Real.cos θ - ρ' * Real.cos θ') ^ 2 + (ρ * Real.sin θ - ρ' * Real.sin θ') ^ 2 + (z - z') ^ 2
      = (ρ - ρ') ^ 2 + 2 * (ρ * ρ' * (1 - Real.cos (θ - θ'))) + (z - z') ^ 2 := by
    rw [Real.cos_sub]
    linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq θ + ρ' ^ 2 * Real.cos_sq_add_sin_sq θ'
  unfold ringPt
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [← hρ, ← hρ', hid]
  linarith

/-- The distance of the second pole from the point `(0, 0, -1)`. -/
theorem pole_dist (a b : ℝ) (hab : a * a + b * b ≤ 1) :
    ∑ k, (polePt a b k - polePt 0 0 k) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have hs0 : 0 ≤ a * a + b * b := add_nonneg (mul_self_nonneg a) (mul_self_nonneg b)
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = √(1 + -(a * a + b * b)) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by
    rw [hw]
    exact Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 1 - (a * a + b * b) := by
    rw [hw, Real.sq_sqrt (by linarith)]
    ring
  have hw1 : w ≤ 1 := by nlinarith [sq_nonneg (w - 1)]
  have e0 : √(1 + -((0 : ℝ) * 0 + 0 * 0)) = 1 := by norm_num
  unfold polePt
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [← hw, e0]
  nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]

/-- The bound for the squared distance of the point `n` of the configuration with the gauge coordinates
`pStarN + D` from the point `n` of the candidate. -/
noncomputable def bd (D : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else if n = 1 then 2 * (D 0 ^ 2 + D 1 ^ 2) else if n = 2 then 2 * D 2 ^ 2
  else 2 * (D (2 * n - 3) ^ 2 + D (2 * n - 2) ^ 2)

theorem bd_sum (D : ℕ → ℝ) : ∑ n ∈ range 14, bd D n = 2 * nsq D := by
  unfold nsq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bd]
  norm_num
  ring

theorem gauge_dist_point (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (n : ℕ) :
    ∑ k, (gaugeN (qOf D) n k - gaugeN pStarN n k) ^ 2 ≤ bd D n := by
  have hsmall : ∀ k (s : ℝ), |s| ≤ 1 / 2 → |D k + s| ≤ 51 / 100 := by
    intro k s hs
    have h1 := abs_le.mp (hD k)
    have h2 := abs_le.mp hs
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hhalf : ∀ s : ℝ, |s| ≤ 1 / 2 → |s| ≤ 51 / 100 := fun s hs => by linarith
  by_cases h0 : n = 0
  · subst h0
    rw [gaugeN_0, gaugeN_0]
    unfold bd
    rw [if_pos rfl]
    simp
  by_cases h1 : n = 1
  · subst h1
    rw [gaugeN_1, gaugeN_1]
    unfold qOf bd
    rw [pStarN_0, pStarN_1, add_zero, add_zero, if_neg (by norm_num), if_pos rfl]
    refine pole_dist (D 0) (D 1) ?_
    have a0 := sq_small (D 0) (hD 0)
    have a1 := sq_small (D 1) (hD 1)
    linarith
  by_cases h2 : n = 2
  · subst h2
    rw [gaugeN_2, gaugeN_2]
    unfold qOf bd
    rw [pStarN_2, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    have := ring_dist (D 2 + hStar) hStar 0 0 (hsmall 2 hStar hh) (hhalf hStar hh)
    calc ∑ k, (ringPt (D 2 + hStar) 0 k - ringPt hStar 0 k) ^ 2
        ≤ 2 * (D 2 + hStar - hStar) ^ 2 + (0 - 0) ^ 2 := this
      _ = 2 * D 2 ^ 2 := by ring
  · have hn3 : 3 ≤ n := by omega
    rw [gaugeN_ring _ n hn3, gaugeN_ring _ n hn3]
    unfold qOf bd
    rw [if_neg h0, if_neg h1, if_neg h2, pStarN_z n hn3]
    have := ring_dist (D (2 * n - 3) + zs n * hStar) (zs n * hStar) (D (2 * n - 2) + pStarN (2 * n - 2))
      (pStarN (2 * n - 2)) (hsmall _ _ (zs_abs n hh)) (hhalf _ (zs_abs n hh))
    calc ∑ k, (ringPt (D (2 * n - 3) + zs n * hStar) (D (2 * n - 2) + pStarN (2 * n - 2)) k
          - ringPt (zs n * hStar) (pStarN (2 * n - 2)) k) ^ 2
        ≤ 2 * (D (2 * n - 3) + zs n * hStar - zs n * hStar) ^ 2
          + (D (2 * n - 2) + pStarN (2 * n - 2) - pStarN (2 * n - 2)) ^ 2 := this
      _ ≤ 2 * (D (2 * n - 3) ^ 2 + D (2 * n - 2) ^ 2) := by nlinarith [sq_nonneg (D (2 * n - 2))]

/-- **The configuration in the gauge is close to the candidate.** -/
theorem gauge_dist (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) :
    ∑ n : Fin 14, ∑ k, (gaugeN (qOf D) n.val k - Xstar n k) ^ 2 ≤ 2 * nsq D := by
  have e : ∀ n : Fin 14, Xstar n = gaugeN pStarN n.val := fun n => (gauge_star n.val n.isLt).symm
  rw [← bd_sum, ← Fin.sum_univ_eq_sum_range (bd D) 14]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [e n]
  exact gauge_dist_point D hD hh n.val

/-- The configuration in the gauge consists of points of the sphere. -/
theorem gauge_sphere (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) :
    OnSphere (fun n : Fin 14 => gaugeN (qOf D) n.val) := by
  intro n
  show ∑ k, gaugeN (qOf D) n.val k ^ 2 = 1
  by_cases h0 : n.val = 0
  · rw [h0, gaugeN_0]
    exact north_unit
  by_cases h1 : n.val = 1
  · rw [h1, gaugeN_1]
    refine pole_unit _ _ ?_
    unfold qOf
    rw [pStarN_0, pStarN_1, add_zero, add_zero]
    have a0 := sq_small (D 0) (hD 0)
    have a1 := sq_small (D 1) (hD 1)
    linarith
  by_cases h2 : n.val = 2
  · rw [h2, gaugeN_2]
    refine ring_unit _ _ ?_
    unfold qOf
    rw [pStarN_2]
    exact z_small (D 2) hStar (hD 2) hh
  · have hn3 : 3 ≤ n.val := by omega
    rw [gaugeN_ring _ n.val hn3]
    refine ring_unit _ _ ?_
    unfold qOf
    rw [pStarN_z n.val hn3]
    exact z_small _ _ (hD _) (zs_abs n.val hh)

theorem nsq_le (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) : nsq D ≤ 1 / 625 := by
  unfold nsq
  have h : ∀ k ∈ range 25, D k ^ 2 ≤ (1 / 125 : ℝ) ^ 2 := fun k _ =>
    sq_le_sq' (neg_le_of_abs_le (hD k)) (le_of_abs_le (hD k))
  have := Finset.sum_le_sum h
  rw [Finset.sum_const, Finset.card_range] at this
  norm_num at this
  linarith

/-! ## A configuration near the candidate has distinct points -/

theorem ipVal_le (h : ℝ) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (c : ℕ) : ipVal h c ≤ 61 / 100 := by
  have h3 : √3 ≤ 174 / 100 := by
    rw [show (174 / 100 : ℝ) = √((174 / 100) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have hq0 : 0 ≤ h ^ 2 := sq_nonneg h
  have hq : h ^ 2 ≤ (4554 / 10000) ^ 2 := pow_le_pow_left₀ (by linarith [hh.1]) hh.2 2
  have hql : (4553 / 10000 : ℝ) ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ (by norm_num) hh.1 2
  have hq1 : 0 ≤ 1 - h ^ 2 := by
    norm_num at hq
    linarith
  have hm := mul_nonneg h30 hq1
  have hm' := mul_le_mul_of_nonneg_right h3 hq1
  unfold ipVal
  split <;> norm_num at hq hql ⊢ <;> linarith [hh.1, hh.2]

/-- **A configuration of the sphere near the candidate has distinct points.** -/
theorem dot_lt_one_of_near (H : CAP) (y : Fin 14 → Fin 3 → ℝ) (hy : OnSphere y)
    (hnear : ∑ i : Fin 14, ∑ k, (y i k - Xstar i k) ^ 2 ≤ 1 / 100) (i j : Fin 14) (hij : i ≠ j) :
    dot y i j < 1 := by
  have hb := hStar_bounds H
  have hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hn : ∀ i : Fin 14, 0 ≤ ∑ k, (y i k - Xstar i k) ^ 2 := fun i => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnN : ∀ i : Fin 14, ∑ k, (y i k - Xstar i k) ^ 2 ≤ ∑ i : Fin 14, ∑ k, (y i k - Xstar i k) ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i : Fin 14 => ∑ k, (y i k - Xstar i k) ^ 2) (fun i _ => hn i)
      (Finset.mem_univ i)
  have hX := sqdist_dot Xstar H.candidate.1 i j
  have hY := sqdist_dot y hy i j
  have hv : dot Xstar i j ≤ 61 / 100 := by
    rw [H.values i j hij]
    exact ipVal_le hStar hh _
  have hk : ∀ k, (Xstar i k - Xstar j k) ^ 2
      ≤ 2 * (y i k - y j k) ^ 2 + 4 * (y i k - Xstar i k) ^ 2 + 4 * (y j k - Xstar j k) ^ 2 := by
    intro k
    nlinarith [sq_nonneg ((y i k - y j k) + (y i k - Xstar i k) - (y j k - Xstar j k)),
      sq_nonneg ((y i k - Xstar i k) + (y j k - Xstar j k))]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin 3))) => hk k
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hX,
    hY] at hsum
  linarith [hnN i, hnN j]

/-! ## The linear form vanishes -/

theorem eq_zero_of_scaling (L M : ℝ) (hM : 0 ≤ M) (h : ∀ t : ℝ, |t| ≤ 1 → -(M * t ^ 2) ≤ t * L) : L = 0 := by
  rcases lt_trichotomy L 0 with h1 | h1 | h1
  · exfalso
    have hs : 0 < min 1 (-L / (M + 1)) := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hs1 : min 1 (-L / (M + 1)) ≤ 1 := min_le_left _ _
    have hs2 : min 1 (-L / (M + 1)) ≤ -L / (M + 1) := min_le_right _ _
    have h2 := h (min 1 (-L / (M + 1))) (by rw [abs_of_pos hs]; exact hs1)
    have h3 : min 1 (-L / (M + 1)) * (M + 1) ≤ -L := by
      rw [le_div_iff₀ (by linarith)] at hs2
      exact hs2
    nlinarith
  · exact h1
  · exfalso
    have hs : 0 < min 1 (L / (M + 1)) := lt_min (by norm_num) (div_pos h1 (by linarith))
    have hs1 : min 1 (L / (M + 1)) ≤ 1 := min_le_left _ _
    have hs2 : min 1 (L / (M + 1)) ≤ L / (M + 1) := min_le_right _ _
    have h2 := h (-min 1 (L / (M + 1))) (by rw [abs_neg, abs_of_pos hs]; exact hs1)
    have h3 : min 1 (L / (M + 1)) * (M + 1) ≤ L := by
      rw [le_div_iff₀ (by linarith)] at hs2
      exact hs2
    nlinarith

/-- The energy along a line through the gauge coordinates of the candidate. -/
theorem energy_line (H : CAP) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ y : Fin 14 → Fin 3 → ℝ, OnSphere y → (∀ i j, i ≠ j → dot y i j < 1) →
      energy Xstar - K * ∑ i : Fin 14, ∑ k, (y i k - Xstar i k) ^ 2 ≤ energy y)
    (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) :
    energy Xstar - K * (2 * nsq D) ≤ energyG (qOf D) := by
  have hb := hStar_bounds H
  have hh : |hStar| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hdist := gauge_dist D hD hh
  have hy := gauge_sphere D hD hh
  have hn := nsq_le D hD
  have hlt := dot_lt_one_of_near H _ hy (le_trans hdist (by linarith))
  have h1 := hK _ hy hlt
  have h2 := mul_le_mul_of_nonneg_left hdist hK0
  unfold energyG
  linarith

/-- **The linear form of statement 7 vanishes** (row A10): the candidate is a critical point of the energy in
the gauge. -/
theorem linear_zero (H : CAP) (L Q C : (ℕ → ℝ) → ℝ) (hL : ∀ (t : ℝ) (D : ℕ → ℝ), L (fun k => t * D k) = t * L D)
    (hQ : ∀ (t : ℝ) (D : ℕ → ℝ), Q (fun k => t * D k) = t ^ 2 * Q D)
    (hC : ∀ (t : ℝ) (D : ℕ → ℝ), C (fun k => t * D k) = t ^ 3 * C D)
    (hR : ∀ D : ℕ → ℝ, Supp25 D → (∀ k, |D k| ≤ 1 / 125) →
      |energyG (qOf D) - energy Xstar - L D - Q D - C D| ≤ 147 * nsq D ^ 2)
    (D : ℕ → ℝ) (hS : Supp25 D) (hD : ∀ k, |D k| ≤ 1 / 125) : L D = 0 := by
  obtain ⟨K, hK0, hK⟩ := energy_lower H
  have hn0 := nsq_nonneg D
  refine eq_zero_of_scaling (L D) (2 * K * nsq D + |Q D| + |C D| + 147 * nsq D ^ 2) (by positivity)
    (fun t ht => ?_)
  have hSt : Supp25 (fun k => t * D k) := fun k hk => by
    show t * D k = 0
    rw [hS k hk, mul_zero]
  have hDt : ∀ k, |t * D k| ≤ 1 / 125 := fun k => by
    rw [abs_mul]
    calc |t| * |D k| ≤ 1 * (1 / 125) := mul_le_mul ht (hD k) (abs_nonneg _) (by norm_num)
      _ = 1 / 125 := one_mul _
  have hnsq : nsq (fun k => t * D k) = t ^ 2 * nsq D := by
    unfold nsq
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hR' := abs_le.mp (hR _ hSt hDt)
  have hlow := energy_line H K hK0 hK _ hDt
  rw [hL, hQ, hC, hnsq] at hR'
  rw [hnsq] at hlow
  -- the powers of `t`
  have ht2 : t ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg t) ht
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
  have a1 : t ^ 2 * Q D ≤ t ^ 2 * |Q D| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0
  have a2 : t ^ 3 * C D ≤ t ^ 2 * |C D| := by
    have h1 : t * C D ≤ |C D| :=
      calc t * C D ≤ |t * C D| := le_abs_self _
        _ = |t| * |C D| := abs_mul _ _
        _ ≤ 1 * |C D| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        _ = |C D| := one_mul _
    have e : t ^ 3 * C D = t ^ 2 * (t * C D) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 ht0
  have a3 : (t ^ 2 * nsq D) ^ 2 ≤ t ^ 2 * nsq D ^ 2 := by
    have e : (t ^ 2 * nsq D) ^ 2 = t ^ 2 * (t ^ 2 * nsq D ^ 2) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ ht0
    calc t ^ 2 * nsq D ^ 2 ≤ 1 * nsq D ^ 2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
      _ = nsq D ^ 2 := one_mul _
  nlinarith [hR'.2]

/-! ## Local minimality -/

/-- **Local minimality** (row A11, Proposition 9.1 of the source): the energy of the configuration with the gauge
coordinates `pStarN + D`, `0 < |D|₂ ≤ 0.0075` and `|D_k| ≤ 1/125`, is larger than the energy of the candidate. -/
theorem local_min (H : CAP) (D : ℕ → ℝ) (hS : Supp25 D) (hD : ∀ k, |D k| ≤ 1 / 125) (h0 : 0 < nsq D)
    (h1 : nsq D ≤ (3 / 400) ^ 2) : energy Xstar < energyG (qOf D) := by
  obtain ⟨L, Q, C, hL, hQ, hC, hQlow, hCb, hR⟩ := H.local7
  have hL0 := linear_zero H L Q C hL hQ hC hR D hS hD
  have hR' := abs_le.mp (hR D hS hD)
  have hq := hQlow D hS
  have hc := abs_le.mp (hCb D hS)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(nsq D) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    exact Real.sqrt_pos.mpr h0
  have hs2 : nsq D = s ^ 2 := by
    rw [hs, Real.sq_sqrt h0.le]
  have hs1 : s ≤ 3 / 400 := by
    rw [hs]
    exact (Real.sqrt_le_left (by norm_num)).mpr h1
  rw [← hs] at hc
  rw [hs2] at hc hq hR'
  rw [hL0] at hR'
  have hss : s * s ≤ 3 / 400 * (3 / 400) := mul_le_mul hs1 hs1 hs0.le (by norm_num)
  have hbr : 0 < 241 / 5000 - 126 / 25 * s - 147 * s ^ 2 := by nlinarith
  have hpos : 0 < s ^ 2 * (241 / 5000 - 126 / 25 * s - 147 * s ^ 2) := mul_pos (pow_pos hs0 2) hbr
  nlinarith [hR'.1, hc.1]

end N14
