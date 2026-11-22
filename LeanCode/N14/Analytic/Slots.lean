module

public import N14.Analytic.Plane

/-!
# The theorem for 14 points, analytic part: the slots (row A8, the part without configurations)

A point of the rings other than the reference point is assigned one of the eleven directions `k π / 6`,
`k = 1, …, 11`, by the sign of its height `z` over the first pole and by the cosine `c` and the sine `s` of its
angle to the reference point: the function `kdir`. Even `k` are the directions of the hexagon of the reference
point, odd `k` those of the other hexagon.

* `kdir_up`, `kdir_low`: if `c` is within `3.6 τ` of a cosine of the candidate, the point has the deviation
  `(C, S)` from its direction with `C ≥ 249/250` and `|S| ≤ 2.4 · 3.6 τ`, or `|S| ≤ 3/80` for the direction of 180
  degrees;
* `same_dir_dot`: two unit vectors with deviations from the same direction;
* `gidx`: the label of the candidate for a direction, and its inverse `ang`.
-/

@[expose] public section

namespace N14.Plane

open Real

/-! ## The table of the directions -/

theorem c12_1 : c12 1 = √3 / 2 := by simp [c12]
theorem c12_2 : c12 2 = 1 / 2 := by simp [c12]
theorem c12_3 : c12 3 = 0 := by simp [c12]
theorem c12_4 : c12 4 = -(1 / 2) := by norm_num [c12]
theorem c12_5 : c12 5 = -(√3 / 2) := by norm_num [c12]; ring
theorem c12_6 : c12 6 = -1 := by simp [c12]
theorem c12_7 : c12 7 = -(√3 / 2) := by norm_num [c12]; ring
theorem c12_8 : c12 8 = -(1 / 2) := by norm_num [c12]
theorem c12_9 : c12 9 = 0 := by simp [c12]
theorem c12_10 : c12 10 = 1 / 2 := by simp [c12]
theorem c12_11 : c12 11 = √3 / 2 := by simp [c12]
theorem s12_1 : s12 1 = 1 / 2 := by simp [s12, c12]
theorem s12_2 : s12 2 = √3 / 2 := by simp [s12, c12]
theorem s12_3 : s12 3 = 1 := by simp [s12, c12]
theorem s12_4 : s12 4 = √3 / 2 := by simp [s12, c12]
theorem s12_5 : s12 5 = 1 / 2 := by simp [s12, c12]
theorem s12_6 : s12 6 = 0 := by simp [s12, c12]
theorem s12_7 : s12 7 = -(1 / 2) := by norm_num [s12, c12]
theorem s12_8 : s12 8 = -(√3 / 2) := by norm_num [s12, c12]; ring
theorem s12_9 : s12 9 = -1 := by simp [s12, c12]
theorem s12_10 : s12 10 = -(√3 / 2) := by norm_num [s12, c12]; ring
theorem s12_11 : s12 11 = -(1 / 2) := by norm_num [s12, c12]

theorem sqrt3_half_ge : (1 / 2 : ℝ) ≤ √3 / 2 := by
  have h : (1 : ℝ) ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-! ## A unit vector near one of two mirror directions -/

/-- Two directions `kp`, `km` that are mirror images in the first axis, and a unit vector whose first coordinate
is within `3.6 τ` of theirs: it has a small deviation from `kp` if its second coordinate is positive, and from
`km` otherwise. -/
theorem dev_pair (kp km : ℕ) (hkp : kp < 12) (hγ : c12 km = c12 kp) (hς : s12 km = -s12 kp)
    (hpos : 1 / 2 ≤ s12 kp) (c s : ℝ) (hu : c ^ 2 + s ^ 2 = 1) (hc : |c - c12 kp| ≤ 351 / 500000) :
    (0 < s → 249 / 250 ≤ c12 kp * c + s12 kp * s ∧ |c12 kp * s - s12 kp * c| ≤ 1053 / 625000)
      ∧ (¬ 0 < s → 249 / 250 ≤ c12 km * c + s12 km * s ∧ |c12 km * s - s12 km * c| ≤ 1053 / 625000) := by
  have hw := c12_sq_add_s12_sq kp hkp
  have hς4 : 1 / 4 ≤ s12 kp ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hpos 2
    linarith
  -- the second coordinate does not vanish
  have hs0 : s ≠ 0 := by
    intro h0
    have hγ2 : c12 kp ^ 2 ≤ (867 / 1000) ^ 2 := by linarith
    have hγa : |c12 kp| ≤ 867 / 1000 := abs_le_of_sq_le_sq hγ2 (by norm_num)
    have hca : |c| ≤ 868 / 1000 := by
      have e : c = (c - c12 kp) + c12 kp := by ring
      rw [e]
      calc |(c - c12 kp) + c12 kp| ≤ |c - c12 kp| + |c12 kp| := abs_add_le _ _
        _ ≤ 868 / 1000 := by linarith
    have hc2 : c ^ 2 ≤ (868 / 1000) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hca 2
    have hc1 : c ^ 2 = 1 := by
      rw [h0] at hu
      linarith
    norm_num at hc2
    linarith
  constructor
  · intro hs
    exact dev_direct _ _ c s hw hς4 hu hc (mul_pos hs (by linarith))
  · intro hs
    have hneg : s < 0 := lt_of_le_of_ne (not_lt.mp hs) hs0
    rw [hγ, hς]
    have hw' : c12 kp ^ 2 + (-s12 kp) ^ 2 = 1 := by rw [neg_sq]; exact hw
    have hς4' : 1 / 4 ≤ (-s12 kp) ^ 2 := by rw [neg_sq]; exact hς4
    exact dev_direct _ _ c s hw' hς4' hu hc (by nlinarith)

/-! ## The direction of a point -/

/-- The direction `k π / 6` of a point of the rings, from the sign of its height `z` and from the cosine `c`
and the sine `s` of its angle to the reference point. -/
noncomputable def kdir (z c s : ℝ) : ℕ :=
  if 0 < z then
    (if 0 < c then (if 0 < s then 2 else 10)
      else if -(3 / 4) < c then (if 0 < s then 4 else 8) else 6)
  else
    (if 1 / 2 < c then (if 0 < s then 1 else 11)
      else if -(1 / 2) ≤ c then (if 0 < s then 3 else 9) else (if 0 < s then 5 else 7))

/-- **The direction of a point of the hexagon of the reference point.** -/
theorem kdir_up (z c s : ℝ) (hz : 0 < z) (hu : c ^ 2 + s ^ 2 = 1)
    (hopt : |c - 1 / 2| ≤ 351 / 500000 ∨ |c + 1 / 2| ≤ 351 / 500000 ∨ |c + 1| ≤ 351 / 500000) :
    kdir z c s % 2 = 0 ∧ 1 ≤ kdir z c s ∧ kdir z c s < 12
      ∧ 249 / 250 ≤ c12 (kdir z c s) * c + s12 (kdir z c s) * s
      ∧ |c12 (kdir z c s) * s - s12 (kdir z c s) * c| ≤ (if kdir z c s = 6 then 3 / 80 else 1053 / 625000) := by
  rcases hopt with h | h | h
  · have h' := abs_le.mp h
    have hc0 : 0 < c := by linarith
    have hp := dev_pair 2 10 (by norm_num) (by rw [c12_10, c12_2]) (by rw [s12_10, s12_2])
      (by rw [s12_2]; exact sqrt3_half_ge) c s hu (by rw [c12_2]; exact h)
    unfold kdir
    rw [if_pos hz, if_pos hc0]
    by_cases hs : 0 < s
    · rw [if_pos hs]
      exact ⟨by norm_num, by norm_num, by norm_num, (hp.1 hs).1, by rw [if_neg (by norm_num)]; exact (hp.1 hs).2⟩
    · rw [if_neg hs]
      exact ⟨by norm_num, by norm_num, by norm_num, (hp.2 hs).1, by rw [if_neg (by norm_num)]; exact (hp.2 hs).2⟩
  · have h' := abs_le.mp h
    have hc0 : ¬ 0 < c := by linarith
    have hc1 : -(3 / 4) < c := by linarith
    have hp := dev_pair 4 8 (by norm_num) (by rw [c12_8, c12_4]) (by rw [s12_8, s12_4])
      (by rw [s12_4]; exact sqrt3_half_ge) c s hu (by rw [c12_4, sub_neg_eq_add]; exact h)
    unfold kdir
    rw [if_pos hz, if_neg hc0, if_pos hc1]
    by_cases hs : 0 < s
    · rw [if_pos hs]
      exact ⟨by norm_num, by norm_num, by norm_num, (hp.1 hs).1, by rw [if_neg (by norm_num)]; exact (hp.1 hs).2⟩
    · rw [if_neg hs]
      exact ⟨by norm_num, by norm_num, by norm_num, (hp.2 hs).1, by rw [if_neg (by norm_num)]; exact (hp.2 hs).2⟩
  · have h' := abs_le.mp h
    have hc0 : ¬ 0 < c := by linarith
    have hc1 : ¬ -(3 / 4) < c := by linarith
    obtain ⟨hC, hS⟩ := dev_pi c s hu h
    unfold kdir
    rw [if_pos hz, if_neg hc0, if_neg hc1, c12_6, s12_6, if_pos rfl]
    refine ⟨by norm_num, by norm_num, by norm_num, by linarith, ?_⟩
    have e : -1 * s - 0 * c = -s := by ring
    rw [e, abs_neg]
    exact hS

/-- **The direction of a point of the other hexagon.** -/
theorem kdir_low (z c s : ℝ) (hz : ¬ 0 < z) (hu : c ^ 2 + s ^ 2 = 1)
    (hopt : |c - √3 / 2| ≤ 351 / 500000 ∨ |c - 0| ≤ 351 / 500000 ∨ |c - -(√3 / 2)| ≤ 351 / 500000) :
    kdir z c s % 2 = 1 ∧ 1 ≤ kdir z c s ∧ kdir z c s < 12
      ∧ 249 / 250 ≤ c12 (kdir z c s) * c + s12 (kdir z c s) * s
      ∧ |c12 (kdir z c s) * s - s12 (kdir z c s) * c| ≤ 1053 / 625000 := by
  have h3 := sqrt3_half_ge
  have h3' : √3 / 2 ≤ 1 := by
    have : √3 ≤ √4 := Real.sqrt_le_sqrt (by norm_num)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith
  rcases hopt with h | h | h
  · have h' := abs_le.mp h
    have hc0 : 1 / 2 < c := by
      have : (3 / 4 : ℝ) ≤ √3 / 2 := by
        have h4 : (3 / 2 : ℝ) ≤ √3 := Real.le_sqrt' (by norm_num) |>.mpr (by norm_num)
        linarith
      linarith
    have hp := dev_pair 1 11 (by norm_num) (by rw [c12_11, c12_1]) (by rw [s12_11, s12_1])
      (by rw [s12_1]) c s hu (by rw [c12_1]; exact h)
    unfold kdir
    rw [if_neg hz, if_pos hc0]
    by_cases hs : 0 < s
    · rw [if_pos hs]
      exact ⟨by norm_num, by norm_num, by norm_num, hp.1 hs⟩
    · rw [if_neg hs]
      exact ⟨by norm_num, by norm_num, by norm_num, hp.2 hs⟩
  · have h' := abs_le.mp h
    have hc0 : ¬ 1 / 2 < c := by linarith
    have hc1 : -(1 / 2) ≤ c := by linarith
    have hp := dev_pair 3 9 (by norm_num) (by rw [c12_9, c12_3]) (by rw [s12_9, s12_3])
      (by rw [s12_3]; norm_num) c s hu (by rw [c12_3]; exact h)
    unfold kdir
    rw [if_neg hz, if_neg hc0, if_pos hc1]
    by_cases hs : 0 < s
    · rw [if_pos hs]
      exact ⟨by norm_num, by norm_num, by norm_num, hp.1 hs⟩
    · rw [if_neg hs]
      exact ⟨by norm_num, by norm_num, by norm_num, hp.2 hs⟩
  · have h' := abs_le.mp h
    have h34 : (3 / 4 : ℝ) ≤ √3 / 2 := by
      have h4 : (3 / 2 : ℝ) ≤ √3 := Real.le_sqrt' (by norm_num) |>.mpr (by norm_num)
      linarith
    have hc0 : ¬ 1 / 2 < c := by linarith
    have hc1 : ¬ -(1 / 2) ≤ c := by linarith
    have hp := dev_pair 5 7 (by norm_num) (by rw [c12_7, c12_5]) (by rw [s12_7, s12_5])
      (by rw [s12_5]) c s hu (by rw [c12_5]; exact h)
    unfold kdir
    rw [if_neg hz, if_neg hc0, if_neg hc1]
    by_cases hs : 0 < s
    · rw [if_pos hs]
      exact ⟨by norm_num, by norm_num, by norm_num, hp.1 hs⟩
    · rw [if_neg hs]
      exact ⟨by norm_num, by norm_num, by norm_num, hp.2 hs⟩

/-! ## Two points with the same direction -/

/-- The inner product of two unit vectors, by their deviations from one direction. -/
theorem same_dir_dot (γ ς c s c' s' : ℝ) (hw : γ ^ 2 + ς ^ 2 = 1) :
    c * c' + s * s' = (γ * c + ς * s) * (γ * c' + ς * s') + (γ * s - ς * c) * (γ * s' - ς * c') := by
  linear_combination (-(c * c' + s * s')) * hw

/-- Two unit vectors with deviations from the same direction have an inner product of at least `99/100`. -/
theorem same_dir_close (γ ς c s c' s' : ℝ) (hw : γ ^ 2 + ς ^ 2 = 1) (hC : 249 / 250 ≤ γ * c + ς * s)
    (hS : |γ * s - ς * c| ≤ 3 / 80) (hC' : 249 / 250 ≤ γ * c' + ς * s') (hS' : |γ * s' - ς * c'| ≤ 3 / 80) :
    99 / 100 ≤ c * c' + s * s' := by
  rw [same_dir_dot γ ς c s c' s' hw]
  have a1 : |(γ * s - ς * c) * (γ * s' - ς * c')| ≤ 3 / 80 * (3 / 80) := abs_mul_le_mul hS hS'
  have a1' := abs_le.mp a1
  have a3 : 249 / 250 * (249 / 250) ≤ (γ * c + ς * s) * (γ * c' + ς * s') :=
    mul_le_mul hC hC' (by norm_num) (by linarith)
  linarith

/-! ## Directions and labels -/

/-- The label of the candidate with the direction `k`: `3, …, 7` for the even directions `2, …, 10`, and
`8, …, 13` for the odd directions `1, …, 11`. -/
def gidx (k : ℕ) : ℕ := if k % 2 = 0 then 2 + k / 2 else 8 + k / 2

theorem gidx_range (k : ℕ) (h1 : 1 ≤ k) (h2 : k < 12) : 3 ≤ gidx k ∧ gidx k < 14 := by
  unfold gidx
  split_ifs <;> omega

theorem gidx_inj (k k' : ℕ) (h1 : 1 ≤ k) (h1' : 1 ≤ k') (h : gidx k = gidx k') (h2 : k < 12) (h2' : k' < 12) :
    k = k' := by
  unfold gidx at h
  split_ifs at h <;> omega

/-- The direction of a label. -/
theorem ang_of_gidx (k n : ℕ) (h1 : 1 ≤ k) (h2 : k < 12) (h : gidx k = n) : k = ang n ∧ (k % 2 = 0 ↔ n < 8) := by
  unfold gidx at h
  unfold ang
  split_ifs at h ⊢ <;> omega

end N14.Plane
