module

public import N14.Analytic.Rigidity
public import N14.Local.Global

/-!
# The theorem for 14 points, analytic part: the rigidity lemma, second part (row A9)

For a configuration `y` in the frame of the rigidity lemma (`Adapted hStar y a b r`) and the relabelling `σ` of
`N14/Analytic/Rigidity.lean`:

* `pole_A`, `pole_B`: the first two coordinates of the second pole are at most `2.8 τ` in absolute value;
* `dev_opposite`: the deviation of the point opposite to the reference point is at most `3.6 · 3.6 τ`;
* `disp`: the displacement of the gauge coordinates from those of the candidate; `gauge_eq`: the point `σ n` of
  the configuration is the point `n` of the configuration with the gauge coordinates `pStarN + disp`;
* `disp_le`, `nsq_disp`: the bounds for the displacement;
* `rigidity_adapted`, and `rigidity` (**Lemma 8.1 of the source at the radius of the tubes**): a configuration that
  satisfies `Tube hStar x p q` is, after an orthogonal map and a relabelling, a configuration in the gauge whose
  coordinates differ from those of the candidate by a displacement `D` with `|D|₂ ≤ 0.0075`.
-/

@[expose] public section

namespace N14

open Finset N14.Plane N14.Local

/-! ## The hypotheses of the rigidity lemma under symmetries -/

theorem Tube.symm {h : ℝ} {x : Fin 14 → Fin 3 → ℝ} {p q : Fin 14} (hh : 4553 / 10000 ≤ h) (T : Tube h x p q) :
    Tube h x q p := by
  have hsign : ∀ i, i ≠ p → i ≠ q → (0 < dot x q i ↔ ¬ 0 < dot x p i) := by
    intro i hip hiq
    rcases T.ring i hip hiq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 := abs_le.mp h1
      have a2 := abs_le.mp h2
      exact ⟨fun h0 => by linarith, fun h0 => absurd (by linarith : 0 < dot x p i) h0⟩
    · have a1 := abs_le.mp h1
      have a2 := abs_le.mp h2
      exact ⟨fun _ h0 => by linarith, fun _ => by linarith⟩
  refine ⟨T.ne.symm, by rw [dot_comm]; exact T.pole, ?_, ?_, ?_⟩
  · intro i hiq hip
    rcases T.ring i hip hiq with h1 | h1
    · exact Or.inr ⟨h1.2, h1.1⟩
    · exact Or.inl ⟨h1.2, h1.1⟩
  · intro i j hiq hip hjq hjp hij hs
    refine T.same i j hip hiq hjp hjq hij ?_
    rw [hsign i hip hiq, hsign j hjp hjq] at hs
    exact not_iff_not.mp hs
  · intro i j hiq hip hjq hjp hij hs
    refine T.diff i j hip hiq hjp hjq hij ?_
    intro hs'
    apply hs
    rw [hsign i hip hiq, hsign j hjp hjq]
    exact not_iff_not.mpr hs'

theorem Tube.congr {h : ℝ} {x y : Fin 14 → Fin 3 → ℝ} {p q : Fin 14} (hd : ∀ i j, dot y i j = dot x i j)
    (T : Tube h x p q) : Tube h y p q := by
  refine ⟨T.ne, by rw [hd]; exact T.pole, ?_, ?_, ?_⟩
  · intro i hip hiq
    rw [hd, hd]
    exact T.ring i hip hiq
  · intro i j hip hiq hjp hjq hij hs
    rw [hd, hd] at hs
    rw [hd]
    exact T.same i j hip hiq hjp hjq hij hs
  · intro i j hip hiq hjp hjq hij hs
    rw [hd, hd] at hs
    rw [hd]
    exact T.diff i j hip hiq hjp hjq hij hs

theorem exists_ring : ∀ p q : Fin 14, ∃ r : Fin 14, r ≠ p ∧ r ≠ q := by decide +kernel

/-! ## The second pole -/

namespace Adapted

variable {h : ℝ} {y : Fin 14 → Fin 3 → ℝ} {a b r : Fin 14}

/-- The inner product of the horizontal parts of the second pole and of a point of the rings. -/
theorem pole_xy (hA : Adapted h y a b r) (hh0 : 0 ≤ h) (i : Fin 14) (hia : i ≠ a) (hib : i ≠ b) :
    |y b 0 * y i 0 + y b 1 * y i 1| ≤ 39 / 200000 * (2 + h) := by
  have hb2 : dot y a b = y b 2 := hA.dot_north b
  have hp := abs_le.mp hA.tube.pole
  rw [hb2] at hp
  have hb2' : y b 2 ^ 2 ≤ 1 := by nlinarith [hA.sph3 b, sq_nonneg (y b 0), sq_nonneg (y b 1)]
  have hb2a : |y b 2| ≤ 1 := abs_le_one_of_sq_le_one hb2'
  have a2 : |h * (1 + y b 2)| ≤ h * (39 / 200000) := by
    rw [abs_mul, abs_of_nonneg hh0]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hh0
  have e := dot3 y b i
  rcases hA.heights i hia hib with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e2 : y b 0 * y i 0 + y b 1 * y i 1
        = (dot y b i + h) - y b 2 * (y i 2 - h) - h * (1 + y b 2) := by
      rw [e]
      ring
    have a1 : |y b 2 * (y i 2 - h)| ≤ 1 * (39 / 200000) := abs_mul_le_mul hb2a h1
    rw [e2]
    calc |(dot y b i + h) - y b 2 * (y i 2 - h) - h * (1 + y b 2)|
        ≤ |dot y b i + h| + |y b 2 * (y i 2 - h)| + |h * (1 + y b 2)| := abs_sub3 _ _ _
      _ ≤ 39 / 200000 * (2 + h) := by linarith
  · have e2 : y b 0 * y i 0 + y b 1 * y i 1
        = (dot y b i - h) - y b 2 * (y i 2 + h) - -(h * (1 + y b 2)) := by
      rw [e]
      ring
    have a1 : |y b 2 * (y i 2 + h)| ≤ 1 * (39 / 200000) := abs_mul_le_mul hb2a h1
    rw [e2]
    calc |(dot y b i - h) - y b 2 * (y i 2 + h) - -(h * (1 + y b 2))|
        ≤ |dot y b i - h| + |y b 2 * (y i 2 + h)| + |-(h * (1 + y b 2))| := abs_sub3 _ _ _
      _ ≤ 39 / 200000 * (2 + h) := by
          rw [abs_neg]
          linarith

/-- The first coordinate of the second pole. -/
theorem pole_A (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) :
    |y b 0| ≤ 273 / 500000 := by
  have h1 := hA.pole_xy (by linarith [hh.1]) r hA.ra hA.rb
  rw [hA.ref1, mul_zero, add_zero, abs_mul, abs_of_pos hA.ref0] at h1
  have hρ := hA.rho_ge hh r hA.ra hA.rb
  rw [← hA.rho_ref] at hρ
  have := mul_le_mul_of_nonneg_left hρ (abs_nonneg (y b 0))
  linarith [hh.2, abs_nonneg (y b 0)]

/-- The second coordinate of the second pole, from a point of the rings in the direction of 90 degrees. -/
theorem pole_B (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i : Fin 14) (hia : i ≠ a)
    (hib : i ≠ b) (hC : 249 / 250 ≤ ss y i) (hS : |cc y i| ≤ 1053 / 625000) : |y b 1| ≤ 273 / 500000 := by
  have h1 := hA.pole_xy (by linarith [hh.1]) i hia hib
  have hA0 := hA.pole_A hh
  have hρ := hA.rho_ge hh i hia hib
  have hρ1 := hA.rho_le_one i
  have hx : |y i 0| ≤ 1 * (1053 / 625000) := by
    rw [hA.x_eq hh i hia hib]
    exact abs_mul_le_mul (by rw [abs_of_nonneg (rho_nonneg y i)]; exact hρ1) hS
  have hy : 8901 / 10000 * (249 / 250) ≤ y i 1 := by
    rw [hA.y_eq hh i hia hib]
    exact mul_le_mul hρ hC (by norm_num) (rho_nonneg y i)
  have a1 : |y b 0 * y i 0| ≤ 273 / 500000 * (1 * (1053 / 625000)) := abs_mul_le_mul hA0 hx
  have e : y b 1 * y i 1 = (y b 0 * y i 0 + y b 1 * y i 1) - y b 0 * y i 0 := by ring
  have h2 : |y b 1 * y i 1| ≤ 39 / 200000 * (2 + h) + 273 / 500000 * (1 * (1053 / 625000)) := by
    rw [e]
    calc |(y b 0 * y i 0 + y b 1 * y i 1) - y b 0 * y i 0|
        ≤ |y b 0 * y i 0 + y b 1 * y i 1| + |y b 0 * y i 0| := abs_sub _ _
      _ ≤ 39 / 200000 * (2 + h) + 273 / 500000 * (1 * (1053 / 625000)) := by linarith
  have hy0 : (0 : ℝ) < y i 1 := by linarith
  rw [abs_mul, abs_of_pos hy0] at h2
  have := mul_le_mul_of_nonneg_left hy (abs_nonneg (y b 1))
  linarith [hh.2, abs_nonneg (y b 1)]

/-! ## The point opposite to the reference point -/

/-- **The deviation of the point opposite to the reference point**, from the point in the direction of 60
degrees. -/
theorem dev_opposite (hA : Adapted h y a b r) (hh : 4553 / 10000 ≤ h ∧ h ≤ 4554 / 10000) (i5 i3 : Fin 14)
    (h5a : i5 ≠ a) (h5b : i5 ≠ b) (h3a : i3 ≠ a) (h3b : i3 ≠ b) (hne : i5 ≠ i3) (up5 : 0 < y i5 2)
    (up3 : 0 < y i3 2) (hC5 : 249 / 250 ≤ c12 6 * cc y i5 + s12 6 * ss y i5)
    (hS5 : |c12 6 * ss y i5 - s12 6 * cc y i5| ≤ 3 / 80)
    (hC3 : 249 / 250 ≤ c12 2 * cc y i3 + s12 2 * ss y i3)
    (hS3 : |c12 2 * ss y i3 - s12 2 * cc y i3| ≤ 1053 / 625000) :
    |c12 6 * ss y i5 - s12 6 * cc y i5| ≤ 3159 / 1250000 := by
  have hopt := hA.cos_same hh i5 i3 h5a h5b h3a h3b hne (iff_of_true up5 up3)
  have u5 := hA.cs_unit hh i5 h5a h5b
  have u3 := hA.cs_unit hh i3 h3a h3b
  have d5 := dev_unit (c12 6) (s12 6) (cc y i5) (ss y i5) (c12_sq_add_s12_sq 6 (by norm_num)) u5
  have d3 := dev_unit (c12 2) (s12 2) (cc y i3) (ss y i3) (c12_sq_add_s12_sq 2 (by norm_num)) u3
  have hς : (√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
    rw [div_pow, sqrt3_sq]
    norm_num
  refine dev_refine (√3 / 2) _ _ _ _ hς d5 d3 hC5 hS5 hC3 hS3 (cc y i5 * cc y i3 + ss y i5 * ss y i3) ?_ hopt
  rw [c12_6, s12_6, c12_2, s12_2]
  linear_combination (-(cc y i5 * cc y i3 + ss y i5 * ss y i3) / 4) * sqrt3_sq

end Adapted

/-! ## The relabelled configuration and its displacement -/

/-- **The relabelling of a configuration in the frame**: `σ 0 = a`, `σ 1 = b`, `σ 2 = r`, and the point `σ n`,
`n ≥ 3`, is a point of the rings with the direction `ang n`. -/
structure Labelled (y : Fin 14 → Fin 3 → ℝ) (a b r : Fin 14) (σ : Equiv.Perm (Fin 14)) : Prop where
  p0 : σ 0 = a
  p1 : σ 1 = b
  p2 : σ 2 = r
  dir : ∀ n : Fin 14, 3 ≤ n.val → σ n ≠ a ∧ σ n ≠ b ∧ σ n ≠ r ∧ kd y (σ n) = ang n.val

/-- The point with the label `n`. -/
noncomputable def pt14 (σ : Equiv.Perm (Fin 14)) (n : ℕ) : Fin 14 := σ ⟨n % 14, Nat.mod_lt n (by norm_num)⟩

theorem pt14_eq (σ : Equiv.Perm (Fin 14)) (n : Fin 14) : pt14 σ n.val = σ n := by
  unfold pt14
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt n.isLt)

/-- **The displacement** of the gauge coordinates of the relabelled configuration from those of the candidate:
the two coordinates of the second pole, the heights of the twelve points of the rings minus `± hStar`, and the
angles of the deviations of eleven of them. -/
noncomputable def disp (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) (k : ℕ) : ℝ :=
  if k = 0 then y b 0 else if k = 1 then y b 1 else if k = 2 then y r 2 - hStar
  else if 25 ≤ k then 0
  else if k % 2 = 1 then y (pt14 σ ((k + 3) / 2)) 2 - zs ((k + 3) / 2) * hStar
  else Real.arcsin (c12 (ang ((k + 2) / 2)) * ss y (pt14 σ ((k + 2) / 2))
    - s12 (ang ((k + 2) / 2)) * cc y (pt14 σ ((k + 2) / 2)))

theorem disp_0 (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) : disp y b r σ 0 = y b 0 :=
  if_pos rfl

theorem disp_1 (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) : disp y b r σ 1 = y b 1 := by
  unfold disp
  rw [if_neg (by norm_num), if_pos rfl]

theorem disp_2 (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) :
    disp y b r σ 2 = y r 2 - hStar := by
  unfold disp
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem disp_z (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) (n : ℕ) (hn : 3 ≤ n)
    (hn' : n < 14) : disp y b r σ (2 * n - 3) = y (pt14 σ n) 2 - zs n * hStar := by
  unfold disp
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (2 * n - 3 + 3) / 2 = n by omega]

theorem disp_th (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) (n : ℕ) (hn : 3 ≤ n)
    (hn' : n < 14) : disp y b r σ (2 * n - 2)
      = Real.arcsin (c12 (ang n) * ss y (pt14 σ n) - s12 (ang n) * cc y (pt14 σ n)) := by
  unfold disp
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (2 * n - 2 + 2) / 2 = n by omega]

theorem supp_disp (y : Fin 14 → Fin 3 → ℝ) (b r : Fin 14) (σ : Equiv.Perm (Fin 14)) : Supp25 (disp y b r σ) := by
  intro k hk
  unfold disp
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hk]

theorem ang_even (n : ℕ) : ang n % 2 = 0 ↔ n < 8 := by
  unfold ang
  split_ifs <;> omega

namespace Adapted

variable {y : Fin 14 → Fin 3 → ℝ} {a b r : Fin 14}

/-- The deviation of the point with the label `n ≥ 3`. -/
theorem dev_label (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (n : Fin 14) (hn : 3 ≤ n.val) :
    (n.val < 8 ↔ 0 < y (σ n) 2) ∧ ang n.val < 12
      ∧ 249 / 250 ≤ c12 (ang n.val) * cc y (σ n) + s12 (ang n.val) * ss y (σ n)
      ∧ |c12 (ang n.val) * ss y (σ n) - s12 (ang n.val) * cc y (σ n)| ≤ 3 / 80
      ∧ (ang n.val ≠ 6 → |c12 (ang n.val) * ss y (σ n) - s12 (ang n.val) * cc y (σ n)| ≤ 1053 / 625000) := by
  obtain ⟨hna, hnb, hnr, hk⟩ := hL.dir n hn
  obtain ⟨h1, _, h3, h4, h5, h6⟩ := hA.kd_spec hh (σ n) hna hnb hnr
  rw [hk] at h1 h3 h4 h5 h6
  exact ⟨by rw [← ang_even]; exact h1, h3, h4, h5, h6⟩

/-- The deviation of every point with a label `n ≥ 3` is at most `3.6 · 3.6 τ`, and at most `2.4 · 3.6 τ` for
`n ≠ 5`. -/
theorem dev_small (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (n : Fin 14) (hn : 3 ≤ n.val) :
    |c12 (ang n.val) * ss y (σ n) - s12 (ang n.val) * cc y (σ n)|
      ≤ (if n.val = 5 then 3159 / 1250000 else 1053 / 625000) := by
  obtain ⟨_, _, hC, hS, hS'⟩ := hA.dev_label hh σ hL n hn
  by_cases h5 : n.val = 5
  · rw [if_pos h5]
    have e5 : n = 5 := Fin.ext h5
    subst e5
    obtain ⟨h5a, h5b, _, _⟩ := hL.dir 5 (by decide)
    obtain ⟨h3a, h3b, _, _⟩ := hL.dir 3 (by decide)
    obtain ⟨u5, _, hC5, hS5, _⟩ := hA.dev_label hh σ hL 5 (by decide)
    obtain ⟨u3, _, hC3, _, hS3⟩ := hA.dev_label hh σ hL 3 (by decide)
    have a5 : ang (5 : Fin 14).val = 6 := by decide
    have a3 : ang (3 : Fin 14).val = 2 := by decide
    rw [a5] at hC5 hS5 ⊢
    rw [a3] at hC3 hS3
    have hne : σ 5 ≠ σ 3 := fun e => absurd (σ.injective e) (by decide)
    exact hA.dev_opposite hh (σ 5) (σ 3) h5a h5b h3a h3b hne (u5.mp (by decide)) (u3.mp (by decide)) hC5 hS5
      hC3 (hS3 (by norm_num))
  · rw [if_neg h5]
    refine hS' ?_
    intro h6
    unfold ang at h6
    split_ifs at h6 <;> omega

/-! ## The configuration in the gauge -/

theorem gauge_north (hA : Adapted hStar y a b r) (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) :
    y (σ 0) = gaugeN (qOf (disp y b r σ)) 0 := by
  rw [hL.p0, gaugeN_0, hA.north]
  rfl

theorem gauge_pole (hA : Adapted hStar y a b r) (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) :
    y (σ 1) = gaugeN (qOf (disp y b r σ)) 1 := by
  rw [hL.p1, gaugeN_1]
  unfold qOf
  rw [disp_0, disp_1, pStarN_0, pStarN_1, add_zero, add_zero]
  unfold polePt
  have hb2 : dot y a b = y b 2 := hA.dot_north b
  have hp := abs_le.mp hA.tube.pole
  rw [hb2] at hp
  have hs := hA.sph3 b
  have e : √(1 + -(y b 0 * y b 0 + y b 1 * y b 1)) = -y b 2 := by
    rw [show 1 + -(y b 0 * y b 0 + y b 1 * y b 1) = (-y b 2) ^ 2 by linear_combination (-1 : ℝ) * hs]
    exact Real.sqrt_sq (by linarith)
  rw [e, neg_neg]
  exact vec3_eta _

theorem gauge_ref (hA : Adapted hStar y a b r) (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) :
    y (σ 2) = gaugeN (qOf (disp y b r σ)) 2 := by
  rw [hL.p2, gaugeN_2]
  unfold qOf
  rw [disp_2, pStarN_2, sub_add_cancel]
  unfold ringPt
  rw [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
  have hρ : √(1 + -(y r 2 * y r 2)) = rho y r := by
    unfold rho
    congr 1
    ring
  rw [hρ, ← hA.rho_ref]
  have := vec3_eta (y r)
  rw [hA.ref1] at this
  exact this

theorem gauge_ring (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (n : Fin 14) (hn : 3 ≤ n.val) :
    y (σ n) = gaugeN (qOf (disp y b r σ)) n.val := by
  obtain ⟨hna, hnb, _, _⟩ := hL.dir n hn
  obtain ⟨_, hk12, hC, _, _⟩ := hA.dev_label hh σ hL n hn
  have hu := hA.cs_unit hh (σ n) hna hnb
  have hw := c12_sq_add_s12_sq (ang n.val) hk12
  have hd := dev_unit _ _ _ _ hw hu
  have hC0 : 0 ≤ c12 (ang n.val) * cc y (σ n) + s12 (ang n.val) * ss y (σ n) := by linarith
  have e1 := (recon _ _ (cc y (σ n)) (ss y (σ n)) hw).1
  have e2 := (recon _ _ (cc y (σ n)) (ss y (σ n)) hw).2
  rw [gaugeN_ring _ n.val hn]
  unfold qOf
  rw [disp_z y b r σ n.val hn n.isLt, disp_th y b r σ n.val hn n.isLt, pStarN_z n.val hn, pStarN_th n.val hn,
    pt14_eq, sub_add_cancel]
  unfold ringPt
  rw [cos_gauge _ hk12 _ _ hd hC0, sin_gauge _ hk12 _ _ hd hC0, ← e1, ← e2]
  have hρ : √(1 + -(y (σ n) 2 * y (σ n) 2)) = rho y (σ n) := by
    unfold rho
    congr 1
    ring
  rw [hρ, ← hA.x_eq hh _ hna hnb, ← hA.y_eq hh _ hna hnb]
  exact vec3_eta _

/-- **The relabelled configuration is the configuration with the gauge coordinates `pStarN + disp`.** -/
theorem gauge_eq (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (n : Fin 14) :
    y (σ n) = gaugeN (qOf (disp y b r σ)) n.val := by
  by_cases h3 : 3 ≤ n.val
  · exact hA.gauge_ring hh σ hL n h3
  · have hn : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 := by omega
    rcases hn with h0 | h0 | h0
    · have e : n = 0 := Fin.ext h0
      subst e
      exact hA.gauge_north σ hL
    · have e : n = 1 := Fin.ext h0
      subst e
      exact hA.gauge_pole σ hL
    · have e : n = 2 := Fin.ext h0
      subst e
      exact hA.gauge_ref σ hL

/-! ## The bounds for the displacement -/

end Adapted

/-- The bounds for the coordinates of the displacement: `2.8 τ` for the second pole, `τ` for the heights, and
`1.001` times the bounds of the deviations for the angles. -/
noncomputable def dbnd (k : ℕ) : ℝ :=
  if k < 2 then 273 / 500000 else if k = 2 ∨ k % 2 = 1 then 39 / 200000
  else if k = 8 then 1001 / 1000 * (3159 / 1250000) else 1001 / 1000 * (1053 / 625000)

theorem dbnd_le (k : ℕ) : dbnd k ≤ 1 / 125 := by
  unfold dbnd
  split_ifs <;> norm_num

theorem dbnd_sum : ∑ k ∈ range 25, dbnd k ^ 2 ≤ (3 / 400 : ℝ) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, dbnd]
  norm_num

namespace Adapted

variable {y : Fin 14 → Fin 3 → ℝ} {a b r : Fin 14}

/-- The height of the point with the label `n ≥ 3`. -/
theorem height_label (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (n : Fin 14) (hn : 3 ≤ n.val) :
    |y (σ n) 2 - zs n.val * hStar| ≤ 39 / 200000 := by
  obtain ⟨hna, hnb, _, _⟩ := hL.dir n hn
  obtain ⟨hup, _⟩ := hA.dev_label hh σ hL n hn
  unfold zs
  rcases hA.z_cases hh.1 (σ n) hna hnb with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [if_pos (hup.mpr h0), one_mul]
    exact h1
  · rw [if_neg (fun h8 => h0 (hup.mp h8)), neg_one_mul, sub_neg_eq_add]
    exact h1

/-- **The bounds for the coordinates of the displacement.** -/
theorem disp_le (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (k : ℕ) (hk : k < 25) : |disp y b r σ k| ≤ dbnd k := by
  by_cases h0 : k = 0
  · subst h0
    rw [disp_0]
    unfold dbnd
    rw [if_pos (by norm_num)]
    exact hA.pole_A hh
  by_cases h1 : k = 1
  · subst h1
    rw [disp_1]
    unfold dbnd
    rw [if_pos (by norm_num)]
    obtain ⟨h9a, h9b, _, _⟩ := hL.dir 9 (by decide)
    obtain ⟨_, _, hC, _, hS⟩ := hA.dev_label hh σ hL 9 (by decide)
    have a9 : ang (9 : Fin 14).val = 3 := by decide
    rw [a9, c12_3, s12_3] at hC hS
    have hS' := hS (by norm_num)
    have e1 : (0 : ℝ) * cc y (σ 9) + 1 * ss y (σ 9) = ss y (σ 9) := by ring
    have e2 : (0 : ℝ) * ss y (σ 9) - 1 * cc y (σ 9) = -cc y (σ 9) := by ring
    rw [e1] at hC
    rw [e2, abs_neg] at hS'
    exact hA.pole_B hh (σ 9) h9a h9b hC hS'
  by_cases h2 : k = 2
  · subst h2
    rw [disp_2]
    unfold dbnd
    rw [if_neg (by norm_num), if_pos (Or.inl rfl)]
    rcases hA.z_cases hh.1 r hA.ra hA.rb with ⟨_, h3⟩ | ⟨h3, _⟩
    · exact h3
    · exact absurd hA.up h3
  by_cases hodd : k % 2 = 1
  · obtain ⟨n, hn3, hn14, rfl⟩ : ∃ n, 3 ≤ n ∧ n < 14 ∧ k = 2 * n - 3 := ⟨(k + 3) / 2, by omega, by omega, by omega⟩
    rw [disp_z y b r σ n hn3 hn14]
    unfold dbnd
    rw [if_neg (by omega), if_pos (Or.inr hodd)]
    have := hA.height_label hh σ hL ⟨n, hn14⟩ hn3
    rw [← pt14_eq σ ⟨n, hn14⟩] at this
    exact this
  · obtain ⟨n, hn3, hn14, rfl⟩ : ∃ n, 3 ≤ n ∧ n < 14 ∧ k = 2 * n - 2 := ⟨(k + 2) / 2, by omega, by omega, by omega⟩
    rw [disp_th y b r σ n hn3 hn14]
    unfold dbnd
    rw [if_neg (by omega), if_neg (by omega)]
    have hs := hA.dev_small hh σ hL ⟨n, hn14⟩ hn3
    rw [← pt14_eq σ ⟨n, hn14⟩] at hs
    by_cases h5 : n = 5
    · rw [if_pos (by omega)]
      rw [if_pos h5] at hs
      have := arcsin_abs_le _ (le_trans hs (by norm_num))
      nlinarith [abs_nonneg (c12 (ang n) * ss y (pt14 σ n) - s12 (ang n) * cc y (pt14 σ n))]
    · rw [if_neg (by omega)]
      rw [if_neg h5] at hs
      have := arcsin_abs_le _ (le_trans hs (by norm_num))
      nlinarith [abs_nonneg (c12 (ang n) * ss y (pt14 σ n) - s12 (ang n) * cc y (pt14 σ n))]

/-- **The Euclidean norm of the displacement is at most `0.0075`.** -/
theorem nsq_disp (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) : nsq (disp y b r σ) ≤ (3 / 400) ^ 2 := by
  unfold nsq
  refine le_trans (Finset.sum_le_sum fun k hk => ?_) dbnd_sum
  have h := hA.disp_le hh σ hL k (Finset.mem_range.mp hk)
  exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)

theorem disp_small (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (σ : Equiv.Perm (Fin 14)) (hL : Labelled y a b r σ) (k : ℕ) : |disp y b r σ k| ≤ 1 / 125 := by
  by_cases hk : k < 25
  · exact le_trans (hA.disp_le hh σ hL k hk) (dbnd_le k)
  · rw [supp_disp y b r σ k (by omega), abs_zero]
    norm_num

/-- **The rigidity lemma for a configuration in the frame.** -/
theorem rigidity_adapted (hA : Adapted hStar y a b r) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000) :
    ∃ (σ : Equiv.Perm (Fin 14)) (D : ℕ → ℝ), Supp25 D ∧ nsq D ≤ (3 / 400) ^ 2 ∧ (∀ k, |D k| ≤ 1 / 125)
      ∧ ∀ n : Fin 14, y (σ n) = gaugeN (qOf D) n.val := by
  obtain ⟨σ, hσ⟩ := hA.exists_perm hh
  obtain ⟨p0, p1, p2, hdir⟩ := hA.perm_spec hh σ hσ
  have hL : Labelled y a b r σ := ⟨p0, p1, p2, hdir⟩
  exact ⟨σ, disp y b r σ, supp_disp y b r σ, hA.nsq_disp hh σ hL, hA.disp_small hh σ hL, hA.gauge_eq hh σ hL⟩

end Adapted

/-! ## The rigidity lemma -/

/-- The rigidity lemma for a configuration with a reference point of the upper ring. -/
theorem rigidity_up (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (p q r : Fin 14) (T : Tube hStar x p q) (hrp : r ≠ p) (hrq : r ≠ q) (hup : 0 < dot x p r) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∃ (σ : Equiv.Perm (Fin 14)) (D : ℕ → ℝ), Supp25 D
      ∧ nsq D ≤ (3 / 400) ^ 2 ∧ (∀ k, |D k| ≤ 1 / 125)
      ∧ ∀ n : Fin 14, U.mulVec (x (σ n)) = gaugeN (qOf D) n.val := by
  have hz1 : (dot x p r) ^ 2 < 1 := by
    rcases T.ring r hrp hrq with ⟨h1, _⟩ | ⟨h1, _⟩
    · have := abs_le.mp h1
      nlinarith [hh.1, hh.2]
    · have := abs_le.mp h1
      nlinarith [hh.1, hh.2]
  obtain ⟨U, hU, hUp, hUr⟩ := exists_frame (x p) (x r) (hx p) (hx r) (dot x p r) rfl hz1
  have hd : ∀ i j, dot (fun i => U.mulVec (x i)) i j = dot x i j := dot_mulVec_config U hU x
  have hA : Adapted hStar (fun i => U.mulVec (x i)) p q r :=
    { sph := onSphere_mulVec U hU x hx
      tube := T.congr hd
      ra := hrp
      rb := hrq
      north := hUp
      ref1 := by
        show U.mulVec (x r) 1 = 0
        rw [hUr]
        rfl
      ref0 := by
        show 0 < U.mulVec (x r) 0
        rw [hUr]
        exact Real.sqrt_pos.mpr (by linarith)
      up := by
        show 0 < U.mulVec (x r) 2
        rw [hUr]
        exact hup }
  obtain ⟨σ, D, h1, h2, h3, h4⟩ := hA.rigidity_adapted hh
  exact ⟨U, hU, σ, D, h1, h2, h3, h4⟩

/-- **The rigidity lemma** (Lemma 8.1 of the source, at the radius of the tubes): a configuration that satisfies
the hypotheses `Tube hStar x p q` is, after an orthogonal map and a relabelling, the configuration with the gauge
coordinates `pStarN + D` for a displacement `D` with `|D|₂ ≤ 0.0075` and `|D_k| ≤ 0.008`. -/
theorem rigidity (x : Fin 14 → Fin 3 → ℝ) (hx : OnSphere x) (hh : 4553 / 10000 ≤ hStar ∧ hStar ≤ 4554 / 10000)
    (p q : Fin 14) (T : Tube hStar x p q) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∃ (σ : Equiv.Perm (Fin 14)) (D : ℕ → ℝ), Supp25 D
      ∧ nsq D ≤ (3 / 400) ^ 2 ∧ (∀ k, |D k| ≤ 1 / 125)
      ∧ ∀ n : Fin 14, U.mulVec (x (σ n)) = gaugeN (qOf D) n.val := by
  obtain ⟨r, hrp, hrq⟩ := exists_ring p q
  by_cases hup : 0 < dot x p r
  · exact rigidity_up x hx hh p q r T hrp hrq hup
  · have hup' : 0 < dot x q r := by
      rcases T.ring r hrp hrq with ⟨h1, _⟩ | ⟨_, h2⟩
      · have := abs_le.mp h1
        exact absurd (by linarith [hh.1] : 0 < dot x p r) hup
      · have := abs_le.mp h2
        linarith [hh.1]
    exact rigidity_up x hx hh q p r (T.symm hh.1) hrq hrp hup'

end N14
