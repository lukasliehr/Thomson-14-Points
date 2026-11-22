module

public import N14.Analytic.Cases
public import N14.Analytic.Slots

/-!
# The theorem for 14 points, analytic part: the rigidity lemma, first part (rows A7 and A8)

`Adapted h y a b r`: the configuration `y` satisfies the hypotheses `Tube h y a b` of the rigidity lemma, the
pole `a` is the point `(0, 0, 1)`, and the reference point `r`, a point of the upper ring, lies in the half plane
`y = 0`, `x > 0`. For such a configuration, and `i` a point of the rings (`i ≠ a`, `i ≠ b`):

* `rho y i`, `cc y i`, `ss y i`: the radius of the parallel of the point and the unit vector of its angle;
  `cos_same`, `cos_diff` (row A7): the cosine of the angle between two points of the rings is within `3.6 τ` of a
  cosine of the candidate;
* `kd y i`, `kd_spec`: the direction of a point other than `r` and its deviation;
* `gN`, `gN_inj`, `exists_perm`, `perm_spec` (row A8): the labels `0, 1, 2` for `a`, `b`, `r` and the label of the
  direction for every other point are an injective assignment, hence a relabelling `π` of the configuration.
-/

@[expose] public section

namespace N14

open Finset N14.Plane

theorem dot3 (y : Fin 14 → Fin 3 → ℝ) (i j : Fin 14) :
    dot y i j = y i 0 * y j 0 + y i 1 * y j 1 + y i 2 * y j 2 := by
  unfold dot
  rw [Fin.sum_univ_three]

/-- The product of two numbers near `h`. -/
theorem prod_near (u v h : ℝ) (hh : 0 ≤ h) (hu : |u - h| ≤ 39 / 200000) (hv : |v - h| ≤ 39 / 200000) :
    |u * v - h ^ 2| ≤ 39 / 200000 * (2 * h + 39 / 200000) := by
  have e : u * v - h ^ 2 = (u - h) * v + h * (v - h) := by ring
  have hv' := abs_le.mp hv
  have hva : |v| ≤ h + 39 / 200000 := abs_le.mpr ⟨by linarith, by linarith⟩
  have a1 : |(u - h) * v| ≤ 39 / 200000 * (h + 39 / 200000) := abs_mul_le_mul hu hva
  have a2 : |h * (v - h)| ≤ h * (39 / 200000) := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hv hh
  rw [e]
  calc |(u - h) * v + h * (v - h)| ≤ |(u - h) * v| + |h * (v - h)| := abs_add_le _ _
    _ ≤ 39 / 200000 * (2 * h + 39 / 200000) := by linarith

theorem abs_sub3 (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| :=
  calc |a - b - c| ≤ |a - b| + |c| := abs_sub _ _
    _ ≤ |a| + |b| + |c| := by linarith [abs_sub a b]

theorem vec3_eta (v : Fin 3 → ℝ) : v = ![v 0, v 1, v 2] := by
  ext j
  fin_cases j <;> rfl

/-- **A configuration in the frame of the rigidity lemma.** -/
structure Adapted (h : ℝ) (y : Fin 14 → Fin 3 → ℝ) (a b r : Fin 14) : Prop where
  sph : OnSphere y
  tube : Tube h y a b
  ra : r ≠ a
  rb : r ≠ b
  north : y a = ![0, 0, 1]
  ref1 : y r 1 = 0
  ref0 : 0 < y r 0
  up : 0 < y r 2

/-- The radius of the parallel of a point. -/
noncomputable def rho (y : Fin 14 → Fin 3 → ℝ) (i : Fin 14) : ℝ := √(1 - y i 2 ^ 2)

/-- The cosine of the angle of a point. -/
noncomputable def cc (y : Fin 14 → Fin 3 → ℝ) (i : Fin 14) : ℝ := y i 0 / rho y i

/-- The sine of the angle of a point. -/
noncomputable def ss (y : Fin 14 → Fin 3 → ℝ) (i : Fin 14) : ℝ := y i 1 / rho y i

/-- The direction of a point of the rings. -/
noncomputable def kd (y : Fin 14 → Fin 3 → ℝ) (i : Fin 14) : ℕ := kdir (y i 2) (cc y i) (ss y i)

/-- The label of the candidate for a point of the configuration. -/
noncomputable def gN (y : Fin 14 → Fin 3 → ℝ) (a b r i : Fin 14) : ℕ :=
  if i = a then 0 else if i = b then 1 else if i = r then 2 else gidx (kd y i)

namespace Adapted

variable {h : ℝ} {y : Fin 14 → Fin 3 → ℝ} {a b r : Fin 14}

theorem dot_north (hA : Adapted h y a b r) (i : Fin 14) : dot y a i = y i 2 := by
  rw [dot3, hA.north]
  simp

theorem sph3 (hA : Adapted h y a b r) (i : Fin 14) : y i 0 ^ 2 + y i 1 ^ 2 + y i 2 ^ 2 = 1 := by
  have := hA.sph i
  rw [Fin.sum_univ_three] at this
  exact this

/-- The heights of a point of the rings over the two poles. -/
theorem heights (hA : Adapted h y a b r) (i : Fin 14) (hia : i ≠ a) (hib : i ≠ b) :
    (|y i 2 - h| ≤ 39 / 200000 ∧ |dot y b i + h| ≤ 39 / 200000)
      ∨ (|y i 2 + h| ≤ 39 / 200000 ∧ |dot y b i - h| ≤ 39 / 200000) := by
  have := hA.tube.ring i hia hib
  rw [hA.dot_north] at this
  exact this

theorem z_cases (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h) (i : Fin 14) (hia : i ≠ a) (hib : i ≠ b) :
    (0 < y i 2 ∧ |y i 2 - h| ≤ 39 / 200000) ∨ (¬ 0 < y i 2 ∧ |y i 2 + h| ≤ 39 / 200000) := by
  rcases hA.heights i hia hib with ⟨h1, _⟩ | ⟨h1, _⟩
  · left
    have := abs_le.mp h1
    exact ⟨by linarith, h1⟩
  · right
    have := abs_le.mp h1
    exact ⟨by linarith, h1⟩

theorem rho_sq (hA : Adapted h y a b r) (i : Fin 14) : rho y i ^ 2 = 1 - y i 2 ^ 2 := by
  unfold rho
  exact Real.sq_sqrt (by nlinarith [hA.sph3 i, sq_nonneg (y i 0), sq_nonneg (y i 1)])

theorem rho_nonneg (y : Fin 14 → Fin 3 → ℝ) (i : Fin 14) : 0 ≤ rho y i := Real.sqrt_nonneg _

theorem rho_le_one (hA : Adapted h y a b r) (i : Fin 14) : rho y i ≤ 1 := by
  have h1 := hA.rho_sq i
  have h0 := rho_nonneg y i
  nlinarith [sq_nonneg (y i 2), sq_nonneg (rho y i - 1)]

/-- The square of the radius of the parallel of a point of the rings. -/
theorem rho_sq_near (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h) (i : Fin 14) (hia : i ≠ a) (hib : i ≠ b) :
    |rho y i ^ 2 - (1 - h ^ 2)| ≤ 39 / 200000 * (2 * h + 39 / 200000) := by
  rw [hA.rho_sq i]
  rcases hA.z_cases hh i hia hib with ⟨_, h1⟩ | ⟨_, h1⟩
  · have e : 1 - y i 2 ^ 2 - (1 - h ^ 2) = -((y i 2 - h) * (y i 2 + h)) := by ring
    rw [e, abs_neg]
    have h1' := abs_le.mp h1
    have h2 : |y i 2 + h| ≤ 2 * h + 39 / 200000 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact abs_mul_le_mul h1 h2
  · have e : 1 - y i 2 ^ 2 - (1 - h ^ 2) = -((y i 2 + h) * (y i 2 - h)) := by ring
    rw [e, abs_neg]
    have h1' := abs_le.mp h1
    have h2 : |y i 2 - h| ≤ 2 * h + 39 / 200000 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact abs_mul_le_mul h1 h2

theorem rho_ge (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) : 8901 / 10000 ≤ rho y i := by
  have h1 := abs_le.mp (hA.rho_sq_near hh.1 i hia hib)
  have hsq : h ^ 2 ≤ (4554 / 10000) ^ 2 := pow_le_pow_left₀ (by linarith) hh.2 2
  have h2 : (8901 / 10000 : ℝ) ^ 2 ≤ rho y i ^ 2 := by nlinarith [hh.2]
  have := le_abs_of_sq_le h2
  rwa [abs_of_nonneg (rho_nonneg y i)] at this

theorem cs_unit (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) : cc y i ^ 2 + ss y i ^ 2 = 1 := by
  have hρ := hA.rho_ge hh i hia hib
  have hρ0 : rho y i ≠ 0 := by linarith
  have h1 := hA.rho_sq i
  have h2 := hA.sph3 i
  unfold cc ss
  field_simp
  linarith

theorem x_eq (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) : y i 0 = rho y i * cc y i := by
  have hρ := hA.rho_ge hh i hia hib
  have hρ0 : rho y i ≠ 0 := by linarith
  unfold cc
  field_simp

theorem y_eq (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) : y i 1 = rho y i * ss y i := by
  have hρ := hA.rho_ge hh i hia hib
  have hρ0 : rho y i ≠ 0 := by linarith
  unfold ss
  field_simp

/-- The cosine of the angle between two points of the rings. -/
theorem cdot (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i j : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    cc y i * cc y j + ss y i * ss y j = (dot y i j - y i 2 * y j 2) / (rho y i * rho y j) := by
  have hi := hA.rho_ge hh i hia hib
  have hj := hA.rho_ge hh j hja hjb
  have hi0 : rho y i ≠ 0 := by linarith
  have hj0 : rho y j ≠ 0 := by linarith
  rw [dot3]
  unfold cc ss
  field_simp
  ring

/-- **The cosine of the angle between two points of the same ring** (row A7). -/
theorem cos_same (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i j : Fin 14)
    (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) (hij : i ≠ j) (hs : 0 < y i 2 ↔ 0 < y j 2) :
    |cc y i * cc y j + ss y i * ss y j - 1 / 2| ≤ 351 / 500000
      ∨ |cc y i * cc y j + ss y i * ss y j + 1 / 2| ≤ 351 / 500000
      ∨ |cc y i * cc y j + ss y i * ss y j + 1| ≤ 351 / 500000 := by
  obtain ⟨c, hc, hd⟩ := hA.tube.same i j hia hib hja hjb hij (by rw [hA.dot_north, hA.dot_north]; exact hs)
  have hh0 : (0 : ℝ) ≤ h := by linarith [hh.1]
  have hab : |y i 2 * y j 2 - h ^ 2| ≤ 39 / 200000 * (2 * h + 39 / 200000) := by
    rcases hA.z_cases hh.1 i hia hib with ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩
    · rcases hA.z_cases hh.1 j hja hjb with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact prod_near _ _ h hh0 hi1 hj1
      · exact absurd (hs.mp hi0) hj0
    · rcases hA.z_cases hh.1 j hja hjb with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact absurd (hs.mpr hj0) hi0
      · have e : y i 2 * y j 2 = -y i 2 * -y j 2 := by ring
        rw [e]
        refine prod_near _ _ h hh0 ?_ ?_
        · rw [show -y i 2 - h = -(y i 2 + h) by ring, abs_neg]
          exact hi1
        · rw [show -y j 2 - h = -(y j 2 + h) by ring, abs_neg]
          exact hj1
  have hc1 : |c| ≤ 1 := by
    rcases hc with rfl | rfl | rfl <;> norm_num [abs_le]
  have key := cos_dev h (y i 2) (y j 2) (rho y i) (rho y j) (dot y i j) (h ^ 2) c hh (rho_nonneg y i)
    (rho_nonneg y j) (hA.rho_sq_near hh.1 i hia hib) (hA.rho_sq_near hh.1 j hja hjb) hab hd hc1
  rw [hA.cdot hh i j hia hib hja hjb]
  rcases hc with rfl | rfl | rfl
  · left
    exact key
  · right
    left
    rw [sub_neg_eq_add] at key
    exact key
  · right
    right
    rw [sub_neg_eq_add] at key
    exact key

/-- **The cosine of the angle between two points of different rings** (row A7). -/
theorem cos_diff (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i j : Fin 14)
    (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) (hij : i ≠ j) (hs : ¬ (0 < y i 2 ↔ 0 < y j 2)) :
    |cc y i * cc y j + ss y i * ss y j - √3 / 2| ≤ 351 / 500000
      ∨ |cc y i * cc y j + ss y i * ss y j - 0| ≤ 351 / 500000
      ∨ |cc y i * cc y j + ss y i * ss y j - -(√3 / 2)| ≤ 351 / 500000 := by
  obtain ⟨c, hc, hd⟩ := hA.tube.diff i j hia hib hja hjb hij (by rw [hA.dot_north, hA.dot_north]; exact hs)
  have hh0 : (0 : ℝ) ≤ h := by linarith [hh.1]
  have hab : |y i 2 * y j 2 - -h ^ 2| ≤ 39 / 200000 * (2 * h + 39 / 200000) := by
    rcases hA.z_cases hh.1 i hia hib with ⟨hi0, hi1⟩ | ⟨hi0, hi1⟩
    · rcases hA.z_cases hh.1 j hja hjb with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · exact absurd (iff_of_true hi0 hj0) hs
      · have e : y i 2 * y j 2 - -h ^ 2 = -(y i 2 * -y j 2 - h ^ 2) := by ring
        rw [e, abs_neg]
        refine prod_near _ _ h hh0 hi1 ?_
        rw [show -y j 2 - h = -(y j 2 + h) by ring, abs_neg]
        exact hj1
    · rcases hA.z_cases hh.1 j hja hjb with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
      · have e : y i 2 * y j 2 - -h ^ 2 = -(-y i 2 * y j 2 - h ^ 2) := by ring
        rw [e, abs_neg]
        refine prod_near _ _ h hh0 ?_ hj1
        rw [show -y i 2 - h = -(y i 2 + h) by ring, abs_neg]
        exact hi1
      · exact absurd (iff_of_false hi0 hj0) hs
  have h3 : √3 / 2 ≤ 1 := by
    have : √3 ≤ √4 := Real.sqrt_le_sqrt (by norm_num)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith
  have h3' : 0 ≤ √3 / 2 := by positivity
  have hc1 : |c| ≤ 1 := by
    rcases hc with rfl | rfl | rfl
    · rw [abs_of_nonneg h3']
      exact h3
    · norm_num
    · rw [abs_neg, abs_of_nonneg h3']
      exact h3
  have key := cos_dev h (y i 2) (y j 2) (rho y i) (rho y j) (dot y i j) (-h ^ 2) c hh (rho_nonneg y i)
    (rho_nonneg y j) (hA.rho_sq_near hh.1 i hia hib) (hA.rho_sq_near hh.1 j hja hjb) hab hd hc1
  rw [hA.cdot hh i j hia hib hja hjb]
  rcases hc with rfl | rfl | rfl
  · left
    exact key
  · right
    left
    exact key
  · right
    right
    exact key

/-! ## The reference point -/

theorem rho_ref (hA : Adapted h y a b r) : y r 0 = rho y r := by
  have h1 := hA.sph3 r
  rw [hA.ref1] at h1
  have h2 := hA.rho_sq r
  have h0 := rho_nonneg y r
  have e : (y r 0 - rho y r) * (y r 0 + rho y r) = 0 := by
    have : (y r 0 - rho y r) * (y r 0 + rho y r) = y r 0 ^ 2 - rho y r ^ 2 := by ring
    rw [this]
    linarith
  rcases mul_eq_zero.mp e with h3 | h3
  · linarith
  · linarith [hA.ref0]

theorem cc_ref (hA : Adapted h y a b r) : cc y r = 1 := by
  unfold cc
  rw [← hA.rho_ref]
  exact div_self (ne_of_gt hA.ref0)

theorem ss_ref (hA : Adapted h y a b r) : ss y r = 0 := by
  unfold ss
  rw [hA.ref1, zero_div]

/-! ## The direction of a point -/

/-- **The direction of a point of the rings other than the reference point, and its deviation.** -/
theorem kd_spec (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) (hir : i ≠ r) :
    (kd y i % 2 = 0 ↔ 0 < y i 2) ∧ 1 ≤ kd y i ∧ kd y i < 12
      ∧ 249 / 250 ≤ c12 (kd y i) * cc y i + s12 (kd y i) * ss y i
      ∧ |c12 (kd y i) * ss y i - s12 (kd y i) * cc y i| ≤ 3 / 80
      ∧ (kd y i ≠ 6 → |c12 (kd y i) * ss y i - s12 (kd y i) * cc y i| ≤ 1053 / 625000) := by
  have hu := hA.cs_unit hh i hia hib
  have hcr : cc y i * cc y r + ss y i * ss y r = cc y i := by
    rw [hA.cc_ref, hA.ss_ref]
    ring
  by_cases hz : 0 < y i 2
  · have hopt := hA.cos_same hh i r hia hib hA.ra hA.rb hir (iff_of_true hz hA.up)
    rw [hcr] at hopt
    obtain ⟨h1, h2, h3, h4, h5⟩ := kdir_up (y i 2) (cc y i) (ss y i) hz hu hopt
    unfold kd
    refine ⟨iff_of_true h1 hz, h2, h3, h4, ?_, ?_⟩
    · by_cases h6 : kdir (y i 2) (cc y i) (ss y i) = 6
      · rw [if_pos h6] at h5
        exact h5
      · rw [if_neg h6] at h5
        linarith
    · intro hne
      rw [if_neg hne] at h5
      exact h5
  · have hopt := hA.cos_diff hh i r hia hib hA.ra hA.rb hir (fun hiff => hz (hiff.mpr hA.up))
    rw [hcr] at hopt
    obtain ⟨h1, h2, h3, h4, h5⟩ := kdir_low (y i 2) (cc y i) (ss y i) hz hu hopt
    unfold kd
    exact ⟨iff_of_false (by omega) hz, h2, h3, h4, by linarith, fun _ => h5⟩

/-! ## The labels -/

theorem gN_a : gN y a b r a = 0 := if_pos rfl

theorem gN_b (hA : Adapted h y a b r) : gN y a b r b = 1 := by
  unfold gN
  rw [if_neg (Ne.symm hA.tube.ne), if_pos rfl]

theorem gN_r (hA : Adapted h y a b r) : gN y a b r r = 2 := by
  unfold gN
  rw [if_neg hA.ra, if_neg hA.rb, if_pos rfl]

theorem gN_other (i : Fin 14) (hia : i ≠ a) (hib : i ≠ b) (hir : i ≠ r) : gN y a b r i = gidx (kd y i) := by
  unfold gN
  rw [if_neg hia, if_neg hib, if_neg hir]

theorem gN_ge (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) (hir : i ≠ r) : 3 ≤ gN y a b r i ∧ gN y a b r i < 14 := by
  rw [gN_other i hia hib hir]
  obtain ⟨_, h1, h2, _⟩ := hA.kd_spec hh i hia hib hir
  exact gidx_range _ h1 h2

theorem gN_lt (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) :
    gN y a b r i < 14 := by
  by_cases hia : i = a
  · rw [hia, gN_a]
    norm_num
  by_cases hib : i = b
  · rw [hib, hA.gN_b]
    norm_num
  by_cases hir : i = r
  · rw [hir, hA.gN_r]
    norm_num
  exact (hA.gN_ge hh i hia hib hir).2

/-- The points with the labels `0`, `1`, `2`. -/
theorem gN_small (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) :
    (gN y a b r i = 0 → i = a) ∧ (gN y a b r i = 1 → i = b) ∧ (gN y a b r i = 2 → i = r) := by
  by_cases hia : i = a
  · rw [hia, gN_a]
    exact ⟨fun _ => rfl, fun h => by omega, fun h => by omega⟩
  by_cases hib : i = b
  · rw [hib, hA.gN_b]
    exact ⟨fun h => by omega, fun _ => rfl, fun h => by omega⟩
  by_cases hir : i = r
  · rw [hir, hA.gN_r]
    exact ⟨fun h => by omega, fun h => by omega, fun _ => rfl⟩
  have := (hA.gN_ge hh i hia hib hir).1
  exact ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩

/-- Two different points of the rings other than the reference point have different directions. -/
theorem kd_ne (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i j : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) (hir : i ≠ r) (hja : j ≠ a) (hjb : j ≠ b) (hjr : j ≠ r) (hij : i ≠ j) : kd y i ≠ kd y j := by
  intro hk
  obtain ⟨hpi, _, hi12, hCi, hSi, _⟩ := hA.kd_spec hh i hia hib hir
  obtain ⟨hpj, _, _, hCj, hSj, _⟩ := hA.kd_spec hh j hja hjb hjr
  rw [← hk] at hpj hCj hSj
  have hw := c12_sq_add_s12_sq (kd y i) hi12
  have hclose := same_dir_close (c12 (kd y i)) (s12 (kd y i)) (cc y i) (ss y i) (cc y j) (ss y j) hw hCi hSi hCj
    hSj
  have hopt := hA.cos_same hh i j hia hib hja hjb hij (by rw [← hpi, ← hpj])
  rcases hopt with h1 | h1 | h1
  · have := (abs_le.mp h1).2
    linarith
  · have := (abs_le.mp h1).2
    linarith
  · have := (abs_le.mp h1).2
    linarith

/-- **The labels are an injective assignment** (row A8). -/
theorem gN_inj (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) :
    Function.Injective (gN y a b r) := by
  intro i j hij
  obtain ⟨i0, i1, i2⟩ := hA.gN_small hh i
  obtain ⟨j0, j1, j2⟩ := hA.gN_small hh j
  by_cases hia : i = a
  · rw [hia, gN_a] at hij
    rw [hia, j0 hij.symm]
  by_cases hib : i = b
  · rw [hib, hA.gN_b] at hij
    rw [hib, j1 hij.symm]
  by_cases hir : i = r
  · rw [hir, hA.gN_r] at hij
    rw [hir, j2 hij.symm]
  have hi3 := (hA.gN_ge hh i hia hib hir).1
  have hja : j ≠ a := by
    intro e
    rw [e, gN_a] at hij
    omega
  have hjb : j ≠ b := by
    intro e
    rw [e, hA.gN_b] at hij
    omega
  have hjr : j ≠ r := by
    intro e
    rw [e, hA.gN_r] at hij
    omega
  by_contra hne
  rw [gN_other i hia hib hir, gN_other j hja hjb hjr] at hij
  obtain ⟨_, a1, a2, _⟩ := hA.kd_spec hh i hia hib hir
  obtain ⟨_, b1, b2, _⟩ := hA.kd_spec hh j hja hjb hjr
  exact hA.kd_ne hh i j hia hib hir hja hjb hjr hne (gidx_inj _ _ a1 b1 hij a2 b2)

/-- **The relabelling.** -/
theorem exists_perm (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) :
    ∃ π : Equiv.Perm (Fin 14), ∀ n : Fin 14, gN y a b r (π n) = n.val := by
  obtain ⟨F, hF⟩ : ∃ F : Fin 14 → Fin 14, ∀ i, (F i).val = gN y a b r i :=
    ⟨fun i => ⟨gN y a b r i, hA.gN_lt hh i⟩, fun _ => rfl⟩
  have hinj : Function.Injective F := by
    intro i j hij
    apply hA.gN_inj hh
    rw [← hF i, ← hF j, hij]
  have hbij : Function.Bijective F := Finite.injective_iff_bijective.mp hinj
  refine ⟨(Equiv.ofBijective F hbij).symm, fun n => ?_⟩
  rw [← hF]
  exact congrArg Fin.val ((Equiv.ofBijective F hbij).apply_symm_apply n)

/-- **The points with the labels of the candidate.** -/
theorem perm_spec (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (π : Equiv.Perm (Fin 14))
    (hπ : ∀ n : Fin 14, gN y a b r (π n) = n.val) :
    π 0 = a ∧ π 1 = b ∧ π 2 = r ∧ ∀ n : Fin 14, 3 ≤ n.val →
      π n ≠ a ∧ π n ≠ b ∧ π n ≠ r ∧ kd y (π n) = ang n.val := by
  refine ⟨(hA.gN_small hh (π 0)).1 (hπ 0), (hA.gN_small hh (π 1)).2.1 (hπ 1), (hA.gN_small hh (π 2)).2.2 (hπ 2),
    fun n hn => ?_⟩
  have h0 := hπ n
  have hna : π n ≠ a := by
    intro e
    rw [e, gN_a] at h0
    omega
  have hnb : π n ≠ b := by
    intro e
    rw [e, hA.gN_b] at h0
    omega
  have hnr : π n ≠ r := by
    intro e
    rw [e, hA.gN_r] at h0
    omega
  rw [gN_other _ hna hnb hnr] at h0
  obtain ⟨_, k1, k2, _⟩ := hA.kd_spec hh (π n) hna hnb hnr
  exact ⟨hna, hnb, hnr, (ang_of_gidx _ _ k1 k2 h0).1⟩

end Adapted

end N14
