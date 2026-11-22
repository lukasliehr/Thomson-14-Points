module

public import N14.Candidate
public import N14.Local.Forms

/-!
# Statement 7 of T7: the gauge coordinates and the energies of the pairs

The 25 gauge coordinates of the source (Section 9): the first pole is `(0, 0, 1)`, the second pole is
`(a, b, -√(1 - a² - b²))` (coordinates 0, 1), the first point of the upper hexagon is `(√(1 - z²), 0, z)`
(coordinate 2), and the point `n ≥ 3` is `(√(1 - z²) cos θ, √(1 - z²) sin θ, z)` with `z` the coordinate
`2 n - 3` and `θ` the coordinate `2 n - 2`. `gaugeN q n` is the point `n` for the coordinates `q`, and `pStarN`
are the coordinates of the candidate: `gauge_star`.

`pair_link`: for a displacement `D` of the coordinates with `|D_k| ≤ 1/125`, the function of the expression
`pairExpW i j wit` of the checker at the local point of the pair is the energy `1 / |x_i - x_j|` of the two
points of the configuration with the coordinates `pStarN + D`.

`energy_pairs`: the energy of a configuration of 14 points is the sum over the list `allPairs`.
-/

@[expose] public section

namespace N14.Local

open Real Finset N14.Jet

/-! ## Two points of the sphere -/

/-- The energy of two points given by their coordinates. -/
noncomputable def pe (u v : Fin 3 → ℝ) : ℝ := 1 / √(∑ k, (u k - v k) ^ 2)

theorem pe_unit (u v : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 = 1) (hv : ∑ k, v k ^ 2 = 1) (s : ℝ)
    (hs : ∑ k, u k * v k = s) : pe u v = (√(2 + -(s + s)))⁻¹ := by
  unfold pe
  have e : ∑ k, (u k - v k) ^ 2 = 2 + -(s + s) := by
    have e1 : ∀ k, (u k - v k) ^ 2 = u k ^ 2 + v k ^ 2 - 2 * (u k * v k) := fun k => by ring
    rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hu, hv, hs]
    ring
  rw [e, one_div]

/-- The first pole. -/
noncomputable def northPt : Fin 3 → ℝ := ![0, 0, 1]

/-- The second pole with the coordinates `a`, `b`. -/
noncomputable def polePt (a b : ℝ) : Fin 3 → ℝ := ![a, b, -√(1 + -(a * a + b * b))]

/-- A point with the height `z` and the angle `θ`. -/
noncomputable def ringPt (z θ : ℝ) : Fin 3 → ℝ := ![√(1 + -(z * z)) * cos θ, √(1 + -(z * z)) * sin θ, z]

theorem north_unit : ∑ k, northPt k ^ 2 = 1 := by
  rw [Fin.sum_univ_three]
  simp only [northPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

theorem pole_unit (a b : ℝ) (h : a * a + b * b ≤ 1) : ∑ k, polePt a b k ^ 2 = 1 := by
  have hs : √(1 + -(a * a + b * b)) ^ 2 = 1 + -(a * a + b * b) := Real.sq_sqrt (by linarith)
  rw [Fin.sum_univ_three]
  simp only [polePt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination hs

theorem ring_unit (z θ : ℝ) (h : z * z ≤ 1) : ∑ k, ringPt z θ k ^ 2 = 1 := by
  have hs : √(1 + -(z * z)) ^ 2 = 1 + -(z * z) := Real.sq_sqrt (by linarith)
  have hc := Real.cos_sq_add_sin_sq θ
  rw [Fin.sum_univ_three]
  simp only [ringPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (cos θ ^ 2 + sin θ ^ 2) * hs + (1 + -(z * z)) * hc

theorem dot_north_pole (a b : ℝ) : ∑ k, northPt k * polePt a b k = -√(1 + -(a * a + b * b)) := by
  rw [Fin.sum_univ_three]
  simp only [northPt, polePt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dot_north_ring (z θ : ℝ) : ∑ k, northPt k * ringPt z θ k = z := by
  rw [Fin.sum_univ_three]
  simp only [northPt, ringPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dot_pole_ring (a b z θ : ℝ) :
    ∑ k, polePt a b k * ringPt z θ k
      = √(1 + -(z * z)) * (a * cos θ + b * sin θ) + -(√(1 + -(a * a + b * b)) * z) := by
  rw [Fin.sum_univ_three]
  simp only [polePt, ringPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dot_ring_ring (z1 θ1 z2 θ2 : ℝ) :
    ∑ k, ringPt z1 θ1 k * ringPt z2 θ2 k
      = √(1 + -(z1 * z1)) * √(1 + -(z2 * z2)) * (cos θ1 * cos θ2 + sin θ1 * sin θ2) + z1 * z2 := by
  rw [Fin.sum_univ_three]
  simp only [ringPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-! ## The constants of the table -/

/-- The real constants of the expressions: `h, -h, 0, 1, -1, 1/2, -1/2, √3/2, -√3/2` for the stationary
height `h`. -/
noncomputable def rho (i : ℕ) : ℝ :=
  match i with
  | 0 => hStar
  | 1 => -hStar
  | 2 => 0
  | 3 => 1
  | 4 => -1
  | 5 => 1 / 2
  | 6 => -1 / 2
  | 7 => √3 / 2
  | 8 => -√3 / 2
  | _ => 0

theorem cond_blt {α : Type} (x y : ℕ) (p q : α) : cond (Nat.blt x y) p q = if x < y then p else q := by
  by_cases h : x < y
  · rw [if_pos h, Nat.blt_eq.mpr h]
    rfl
  · rw [if_neg h]
    have hb : Nat.blt x y = false := by
      cases hb : Nat.blt x y
      · rfl
      · exact absurd (Nat.blt_eq.mp hb) h
    rw [hb]
    rfl

theorem ang12_eq (n : ℕ) : ang12 n = ang n := cond_blt _ _ _ _

theorem rho_hI (n : ℕ) : rho (hI n) = zs n * hStar := by
  have e : hI n = if n < 8 then 0 else 1 := cond_blt _ _ _ _
  rw [e]
  unfold zs
  split_ifs
  · show hStar = 1 * hStar
    ring
  · show -hStar = -1 * hStar
    ring

theorem rho_cosI (k : ℕ) : rho (cosI k) = c12 k := by
  have h : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have e : cosI k = lgetD 0 [3, 7, 5, 2, 6, 8, 4, 8, 6, 2, 5, 7] (k % 12) := rfl
  rw [e]
  unfold c12
  generalize k % 12 = r at h
  interval_cases r <;> rfl

theorem rho_sinI (k : ℕ) : rho (sinI k) = s12 k := rho_cosI (k + 9)

theorem cosI_lt (k : ℕ) : cosI k < 9 := by
  have h : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have e : cosI k = lgetD 0 [3, 7, 5, 2, 6, 8, 4, 8, 6, 2, 5, 7] (k % 12) := rfl
  rw [e]
  generalize k % 12 = r at h
  interval_cases r <;> decide

theorem rho_negI (i : ℕ) (hi : i < 9) : rho (negI i) = -rho i := by
  interval_cases i
  · rw [show negI 0 = 1 from rfl]
    rfl
  · rw [show negI 1 = 0 from rfl]
    simp only [rho]
    ring
  · rw [show negI 2 = 2 from rfl]
    simp only [rho]
    ring
  · rw [show negI 3 = 4 from rfl]
    rfl
  · rw [show negI 4 = 3 from rfl]
    simp only [rho]
    ring
  · rw [show negI 5 = 6 from rfl]
    simp only [rho]
    ring
  · rw [show negI 6 = 5 from rfl]
    simp only [rho]
    ring
  · rw [show negI 7 = 8 from rfl]
    simp only [rho]
    ring
  · rw [show negI 8 = 7 from rfl]
    simp only [rho]
    ring

theorem trig_cos (k : ℕ) (hk : k < 12) (δ : ℝ) :
    rho (cosI k) * cos δ - rho (sinI k) * sin δ = cos (δ + (k : ℝ) * (π / 6)) := by
  rw [rho_cosI, rho_sinI, ← cos_tab k hk, ← sin_tab k hk, cos_add]
  ring

theorem trig_sin (k : ℕ) (hk : k < 12) (δ : ℝ) :
    rho (sinI k) * cos δ - rho (negI (cosI k)) * sin δ = sin (δ + (k : ℝ) * (π / 6)) := by
  rw [rho_sinI, rho_negI _ (cosI_lt k), rho_cosI, ← cos_tab k hk, ← sin_tab k hk, sin_add]
  ring

theorem lx_kf (xs : ℕ → ℝ) (k : ℕ) (hk : k ≤ 3) : lx xs (kf k) = xs k := by
  show xs (min k 3) = xs k
  rw [min_eq_left hk]

theorem lx_kf0 (xs : ℕ → ℝ) : lx xs (kf 0) = xs 0 := lx_kf xs 0 (by norm_num)

theorem lx_kf1 (xs : ℕ → ℝ) : lx xs (kf 1) = xs 1 := lx_kf xs 1 (by norm_num)

theorem lx_kf2 (xs : ℕ → ℝ) : lx xs (kf 2) = xs 2 := lx_kf xs 2 (by norm_num)

theorem lx_kf3 (xs : ℕ → ℝ) : lx xs (kf 3) = xs 3 := lx_kf xs 3 (by norm_num)

/-! ## The gauge -/

/-- The gauge coordinates of the candidate. -/
noncomputable def pStarN (k : ℕ) : ℝ :=
  if k < 2 then 0 else if k = 2 then hStar
  else if k % 2 = 1 then zs ((k + 3) / 2) * hStar else (ang ((k + 2) / 2) : ℝ) * (π / 6)

theorem pStarN_0 : pStarN 0 = 0 := if_pos (by norm_num)

theorem pStarN_1 : pStarN 1 = 0 := if_pos (by norm_num)

theorem pStarN_2 : pStarN 2 = hStar := by
  unfold pStarN
  rw [if_neg (by norm_num), if_pos rfl]

theorem pStarN_z (n : ℕ) (hn : 3 ≤ n) : pStarN (2 * n - 3) = zs n * hStar := by
  unfold pStarN
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (2 * n - 3 + 3) / 2 = n by omega]

theorem pStarN_th (n : ℕ) (hn : 3 ≤ n) : pStarN (2 * n - 2) = (ang n : ℝ) * (π / 6) := by
  unfold pStarN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * n - 2 + 2) / 2 = n by omega]

/-- The coordinates of the candidate, displaced by `D`. -/
noncomputable def qOf (D : ℕ → ℝ) (k : ℕ) : ℝ := D k + pStarN k

/-- **The point `n` of the configuration with the gauge coordinates `q`.** -/
noncomputable def gaugeN (q : ℕ → ℝ) (n : ℕ) : Fin 3 → ℝ :=
  if n = 0 then northPt
  else if n = 1 then polePt (q 0) (q 1)
  else if n = 2 then ringPt (q 2) 0
  else ringPt (q (2 * n - 3)) (q (2 * n - 2))

theorem gaugeN_0 (q : ℕ → ℝ) : gaugeN q 0 = northPt := if_pos rfl

theorem gaugeN_1 (q : ℕ → ℝ) : gaugeN q 1 = polePt (q 0) (q 1) := by
  unfold gaugeN
  rw [if_neg (by norm_num), if_pos rfl]

theorem gaugeN_2 (q : ℕ → ℝ) : gaugeN q 2 = ringPt (q 2) 0 := by
  unfold gaugeN
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem gaugeN_ring (q : ℕ → ℝ) (n : ℕ) (hn : 3 ≤ n) : gaugeN q n = ringPt (q (2 * n - 3)) (q (2 * n - 2)) := by
  unfold gaugeN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem own_ring (n : ℕ) (hn : 3 ≤ n) : own n = [2 * n - 3, 2 * n - 2] := by
  unfold own
  rw [cond_beq, if_neg (by omega), cond_beq, if_neg (by omega), cond_beq, if_neg (by omega)]
  rfl

/-- **The candidate in the gauge.** -/
theorem gauge_star (n : ℕ) (hn : n < 14) : gaugeN pStarN n = X14N hStar n := by
  have hsq : ∀ z : ℝ, √(1 + -(z * z)) = √(1 - z ^ 2) := fun z => by
    rw [show 1 + -(z * z) = 1 - z ^ 2 by ring]
  by_cases h3 : 3 ≤ n
  · rw [gaugeN_ring _ n h3, X14N_ring hStar n (by omega), pStarN_z n h3, pStarN_th n h3]
    unfold ringPt
    have hz : zs n * hStar * (zs n * hStar) = hStar * hStar := by
      have h1 : zs n * zs n = 1 := by
        unfold zs
        split_ifs <;> norm_num
      linear_combination (hStar * hStar) * h1
    rw [hz, hsq]
  · have hc : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · rw [gaugeN_0]
      unfold X14N northPt
      rw [if_pos rfl]
    · rw [gaugeN_1, pStarN_0, pStarN_1]
      unfold X14N polePt
      rw [if_neg (by norm_num), if_pos rfl]
      norm_num
    · rw [gaugeN_2, pStarN_2, X14N_ring hStar 2 (by norm_num)]
      unfold ringPt
      rw [hsq]
      norm_num [ang, zs]

/-! ## The link of the expressions with the energies of the pairs -/

theorem sq_small (x : ℝ) (h : |x| ≤ 1 / 125) : x * x ≤ 1 / 15625 := by
  have h1 := abs_le.mp h
  nlinarith [h1.1, h1.2]

/-- A height in the box around `±h` has absolute value below 1. -/
theorem z_small (x s : ℝ) (h : |x| ≤ 1 / 125) (hs : |s| ≤ 1 / 2) : (x + s) * (x + s) ≤ 1 := by
  have h1 := abs_le.mp h
  have h2 := abs_le.mp hs
  nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem zs_abs (n : ℕ) (hh : |hStar| ≤ 1 / 2) : |zs n * hStar| ≤ 1 / 2 := by
  unfold zs
  split_ifs
  · rw [one_mul]
    exact hh
  · rw [neg_one_mul, abs_neg]
    exact hh

theorem link_01 (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW 0 1 wit) (lx (fun v => D (lgetD 25 (gl 0 1) v)))
      = pe (gaugeN (qOf D) 0) (gaugeN (qOf D) 1) := by
  have hq0 : qOf D 0 = D 0 := by
    unfold qOf
    rw [pStarN_0, add_zero]
  have hq1 : qOf D 1 = D 1 := by
    unfold qOf
    rw [pStarN_1, add_zero]
  have hdom : D 0 * D 0 + D 1 * D 1 ≤ 1 := by
    have := sq_small _ (hD 0)
    have := sq_small _ (hD 1)
    linarith
  rw [gaugeN_0, gaugeN_1, hq0, hq1, pe_unit _ _ north_unit (pole_unit _ _ hdom) _ (dot_north_pole _ _)]
  show sem rho (.isqrt (.add (.nat 2) (.add (wE (wget wit 0)) (wE (wget wit 0)))) (wget wit 1).1
    (wget wit 1).2) (lx (fun v => D (lgetD 25 [0, 1] v))) = _
  simp only [sem, wE, lx_kf0, lx_kf1, Nat.cast_ofNat, Nat.cast_one]
  rw [show rho 2 = 0 from rfl, show lgetD 25 [0, 1] 0 = 0 from rfl, show lgetD 25 [0, 1] 1 = 1 from rfl,
    add_zero, add_zero]
  refine congrArg (fun t : ℝ => (√t)⁻¹) ?_
  ring

theorem link_02 (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW 0 2 wit) (lx (fun v => D (lgetD 25 (gl 0 2) v)))
      = pe (gaugeN (qOf D) 0) (gaugeN (qOf D) 2) := by
  have hq2 : qOf D 2 = D 2 + hStar := by
    unfold qOf
    rw [pStarN_2]
  rw [gaugeN_0, gaugeN_2, hq2,
    pe_unit _ _ north_unit (ring_unit _ _ (z_small _ _ (hD 2) hh)) _ (dot_north_ring _ _)]
  show sem rho (.isqrt (twoMinus (.var 0 (hI 2))) (wget wit 0).1 (wget wit 0).2)
    (lx (fun v => D (lgetD 25 [2] v))) = _
  simp only [sem, twoMinus, lx_kf0, Nat.cast_ofNat]
  rw [show rho (hI 2) = hStar from rfl, show lgetD 25 [2] 0 = 2 from rfl]

theorem link_0j (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (j : ℕ) (hj : 3 ≤ j)
    (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW 0 j wit) (lx (fun v => D (lgetD 25 (gl 0 j) v)))
      = pe (gaugeN (qOf D) 0) (gaugeN (qOf D) j) := by
  have hgl : gl 0 j = [2 * j - 3, 2 * j - 2] := own_ring j hj
  have hqz : qOf D (2 * j - 3) = D (2 * j - 3) + zs j * hStar := by
    unfold qOf
    rw [pStarN_z j hj]
  rw [gaugeN_0, gaugeN_ring _ j hj, hqz,
    pe_unit _ _ north_unit (ring_unit _ _ (z_small _ _ (hD _) (zs_abs j hh))) _ (dot_north_ring _ _)]
  unfold pairExpW
  rw [cond_beq, if_pos rfl, cond_beq, if_neg (by omega), hgl]
  simp only [sem, twoMinus, lx_kf0, Nat.cast_ofNat]
  rw [rho_hI, show lgetD 25 [2 * j - 3, 2 * j - 2] 0 = 2 * j - 3 from rfl]

theorem link_12 (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW 1 2 wit) (lx (fun v => D (lgetD 25 (gl 1 2) v)))
      = pe (gaugeN (qOf D) 1) (gaugeN (qOf D) 2) := by
  have hq0 : qOf D 0 = D 0 := by
    unfold qOf
    rw [pStarN_0, add_zero]
  have hq1 : qOf D 1 = D 1 := by
    unfold qOf
    rw [pStarN_1, add_zero]
  have hq2 : qOf D 2 = D 2 + hStar := by
    unfold qOf
    rw [pStarN_2]
  have hdom : D 0 * D 0 + D 1 * D 1 ≤ 1 := by
    have := sq_small _ (hD 0)
    have := sq_small _ (hD 1)
    linarith
  rw [gaugeN_1, gaugeN_2, hq0, hq1, hq2,
    pe_unit _ _ (pole_unit _ _ hdom) (ring_unit _ _ (z_small _ _ (hD 2) hh)) _ (dot_pole_ring _ _ _ _)]
  show sem rho (.isqrt (twoMinus (.add (.mul (.var 0 2) (rhoE (.var 2 0) (wget wit 1)))
    (.neg (.mul (wE (wget wit 0)) (.var 2 0))))) (wget wit 2).1 (wget wit 2).2)
    (lx (fun v => D (lgetD 25 [0, 1, 2] v))) = _
  simp only [sem, twoMinus, rhoE, wE, lx_kf0, lx_kf1, lx_kf2, Nat.cast_ofNat, Nat.cast_one]
  rw [show rho 2 = 0 from rfl, show rho 0 = hStar from rfl, show lgetD 25 [0, 1, 2] 0 = 0 from rfl,
    show lgetD 25 [0, 1, 2] 1 = 1 from rfl, show lgetD 25 [0, 1, 2] 2 = 2 from rfl, add_zero, add_zero,
    cos_zero, sin_zero]
  refine congrArg (fun t : ℝ => (√t)⁻¹) ?_
  ring

theorem link_1j (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (j : ℕ) (hj : 3 ≤ j)
    (hj14 : j < 14) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW 1 j wit) (lx (fun v => D (lgetD 25 (gl 1 j) v)))
      = pe (gaugeN (qOf D) 1) (gaugeN (qOf D) j) := by
  have hgl : gl 1 j = [0, 1, 2 * j - 3, 2 * j - 2] := by
    show [0, 1] ++ own j = _
    rw [own_ring j hj]
    rfl
  have hq0 : qOf D 0 = D 0 := by
    unfold qOf
    rw [pStarN_0, add_zero]
  have hq1 : qOf D 1 = D 1 := by
    unfold qOf
    rw [pStarN_1, add_zero]
  have hqz : qOf D (2 * j - 3) = D (2 * j - 3) + zs j * hStar := by
    unfold qOf
    rw [pStarN_z j hj]
  have hqt : qOf D (2 * j - 2) = D (2 * j - 2) + (ang j : ℝ) * (π / 6) := by
    unfold qOf
    rw [pStarN_th j hj]
  have hdom : D 0 * D 0 + D 1 * D 1 ≤ 1 := by
    have := sq_small _ (hD 0)
    have := sq_small _ (hD 1)
    linarith
  have hk : ang12 j < 12 := by
    rw [ang12_eq]
    exact ang_lt j (by omega) hj14
  rw [gaugeN_1, gaugeN_ring _ j hj, hq0, hq1, hqz, hqt,
    pe_unit _ _ (pole_unit _ _ hdom) (ring_unit _ _ (z_small _ _ (hD _) (zs_abs j hh))) _
      (dot_pole_ring _ _ _ _)]
  unfold pairExpW
  rw [cond_beq, if_neg (by norm_num), cond_beq, if_pos rfl, cond_beq, if_neg (by omega), hgl]
  simp only [sem, twoMinus, rhoE, wE, lx_kf0, lx_kf1, lx_kf2, lx_kf3, Nat.cast_ofNat, Nat.cast_one]
  rw [trig_cos _ hk, trig_sin _ hk, rho_hI, show rho 2 = 0 from rfl, ang12_eq,
    show lgetD 25 [0, 1, 2 * j - 3, 2 * j - 2] 0 = 0 from rfl,
    show lgetD 25 [0, 1, 2 * j - 3, 2 * j - 2] 1 = 1 from rfl,
    show lgetD 25 [0, 1, 2 * j - 3, 2 * j - 2] 2 = 2 * j - 3 from rfl,
    show lgetD 25 [0, 1, 2 * j - 3, 2 * j - 2] 3 = 2 * j - 2 from rfl, add_zero, add_zero]

theorem link_2j (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (j : ℕ) (hj : 3 ≤ j)
    (hj14 : j < 14) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW 2 j wit) (lx (fun v => D (lgetD 25 (gl 2 j) v)))
      = pe (gaugeN (qOf D) 2) (gaugeN (qOf D) j) := by
  have hgl : gl 2 j = [2, 2 * j - 3, 2 * j - 2] := by
    show [2] ++ own j = _
    rw [own_ring j hj]
    rfl
  have hq2 : qOf D 2 = D 2 + hStar := by
    unfold qOf
    rw [pStarN_2]
  have hqz : qOf D (2 * j - 3) = D (2 * j - 3) + zs j * hStar := by
    unfold qOf
    rw [pStarN_z j hj]
  have hqt : qOf D (2 * j - 2) = D (2 * j - 2) + (ang j : ℝ) * (π / 6) := by
    unfold qOf
    rw [pStarN_th j hj]
  have hk : ang12 j < 12 := by
    rw [ang12_eq]
    exact ang_lt j (by omega) hj14
  rw [gaugeN_2, gaugeN_ring _ j hj, hq2, hqz, hqt,
    pe_unit _ _ (ring_unit _ _ (z_small _ _ (hD 2) hh)) (ring_unit _ _ (z_small _ _ (hD _) (zs_abs j hh))) _
      (dot_ring_ring _ _ _ _)]
  unfold pairExpW
  rw [cond_beq, if_neg (by norm_num), cond_beq, if_neg (by norm_num), cond_beq, if_pos rfl, hgl]
  simp only [sem, twoMinus, rhoE, lx_kf0, lx_kf1, lx_kf2, Nat.cast_ofNat, Nat.cast_one]
  rw [trig_cos _ hk, rho_hI, show rho 0 = hStar from rfl, ang12_eq,
    show lgetD 25 [2, 2 * j - 3, 2 * j - 2] 0 = 2 from rfl,
    show lgetD 25 [2, 2 * j - 3, 2 * j - 2] 1 = 2 * j - 3 from rfl,
    show lgetD 25 [2, 2 * j - 3, 2 * j - 2] 2 = 2 * j - 2 from rfl, cos_zero, sin_zero]
  refine congrArg (fun t : ℝ => (√t)⁻¹) ?_
  ring

theorem link_ij (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (i j : ℕ) (hi : 3 ≤ i)
    (hij : i < j) (hj14 : j < 14) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW i j wit) (lx (fun v => D (lgetD 25 (gl i j) v)))
      = pe (gaugeN (qOf D) i) (gaugeN (qOf D) j) := by
  have hj : 3 ≤ j := by omega
  have hgl : gl i j = [2 * i - 3, 2 * i - 2, 2 * j - 3, 2 * j - 2] := by
    show own i ++ own j = _
    rw [own_ring i hi, own_ring j hj]
    rfl
  have hqzi : qOf D (2 * i - 3) = D (2 * i - 3) + zs i * hStar := by
    unfold qOf
    rw [pStarN_z i hi]
  have hqti : qOf D (2 * i - 2) = D (2 * i - 2) + (ang i : ℝ) * (π / 6) := by
    unfold qOf
    rw [pStarN_th i hi]
  have hqzj : qOf D (2 * j - 3) = D (2 * j - 3) + zs j * hStar := by
    unfold qOf
    rw [pStarN_z j hj]
  have hqtj : qOf D (2 * j - 2) = D (2 * j - 2) + (ang j : ℝ) * (π / 6) := by
    unfold qOf
    rw [pStarN_th j hj]
  have hki : ang12 i < 12 := by
    rw [ang12_eq]
    exact ang_lt i (by omega) (by omega)
  have hkj : ang12 j < 12 := by
    rw [ang12_eq]
    exact ang_lt j (by omega) hj14
  rw [gaugeN_ring _ i hi, gaugeN_ring _ j hj, hqzi, hqti, hqzj, hqtj,
    pe_unit _ _ (ring_unit _ _ (z_small _ _ (hD _) (zs_abs i hh)))
      (ring_unit _ _ (z_small _ _ (hD _) (zs_abs j hh))) _ (dot_ring_ring _ _ _ _)]
  unfold pairExpW
  rw [cond_beq, if_neg (by omega), cond_beq, if_neg (by omega), cond_beq, if_neg (by omega), hgl]
  simp only [sem, twoMinus, rhoE, lx_kf0, lx_kf1, lx_kf2, lx_kf3, Nat.cast_ofNat, Nat.cast_one]
  rw [trig_cos _ hki, trig_sin _ hki, trig_cos _ hkj, trig_sin _ hkj, rho_hI, rho_hI, ang12_eq, ang12_eq,
    show lgetD 25 [2 * i - 3, 2 * i - 2, 2 * j - 3, 2 * j - 2] 0 = 2 * i - 3 from rfl,
    show lgetD 25 [2 * i - 3, 2 * i - 2, 2 * j - 3, 2 * j - 2] 1 = 2 * i - 2 from rfl,
    show lgetD 25 [2 * i - 3, 2 * i - 2, 2 * j - 3, 2 * j - 2] 2 = 2 * j - 3 from rfl,
    show lgetD 25 [2 * i - 3, 2 * i - 2, 2 * j - 3, 2 * j - 2] 3 = 2 * j - 2 from rfl]

/-- **The expression of a pair is the energy of the two points** of the configuration with the coordinates
`pStarN + D`, for `|D_k| ≤ 1/125`. -/
theorem pair_link (D : ℕ → ℝ) (hD : ∀ k, |D k| ≤ 1 / 125) (hh : |hStar| ≤ 1 / 2) (i j : ℕ) (hij : i < j)
    (hj : j < 14) (wit : List (ℕ × ℕ)) :
    sem rho (pairExpW i j wit) (lx (fun v => D (lgetD 25 (gl i j) v)))
      = pe (gaugeN (qOf D) i) (gaugeN (qOf D) j) := by
  by_cases h3 : 3 ≤ i
  · exact link_ij D hD hh i j h3 hij hj wit
  · have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · by_cases hj3 : 3 ≤ j
      · exact link_0j D hD hh j hj3 wit
      · have hc2 : j = 1 ∨ j = 2 := by omega
        rcases hc2 with rfl | rfl
        · exact link_01 D hD wit
        · exact link_02 D hD hh wit
    · by_cases hj3 : 3 ≤ j
      · exact link_1j D hD hh j hj3 hj wit
      · obtain rfl : j = 2 := by omega
        exact link_12 D hD hh wit
    · exact link_2j D hD hh j (by omega) hj wit

/-! ## The energy as a sum over the pairs -/

/-- The pairs `i < j < 14`. -/
def allPairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13),
   (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, 3),
   (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, 4), (3, 5), (3, 6),
   (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10),
   (4, 11), (4, 12), (4, 13), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (6, 7),
   (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13),
   (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, 10), (9, 11), (9, 12), (9, 13), (10, 11), (10, 12),
   (10, 13), (11, 12), (11, 13), (12, 13)]

theorem allPairs_lt : ∀ t ∈ allPairs, t.1 < t.2 ∧ t.2 < 14 := by decide +kernel

/-- A sum over the pairs `i < j < 14`. -/
theorem sum_allPairs (h : ℕ → ℕ → ℝ) :
    ∑ i ∈ range 14, ∑ j ∈ range 14, (if i < j then h i j else 0) = (allPairs.map (fun t => h t.1 t.2)).sum := by
  simp [Finset.sum_range_succ, allPairs]
  ring

/-- **The energy of 14 points as a sum over the pairs.** -/
theorem energy_pairs (x : Fin 14 → Fin 3 → ℝ) (f : ℕ → Fin 3 → ℝ) (hf : ∀ n : Fin 14, x n = f n.val) :
    energy x = (allPairs.map (fun t => pe (f t.1) (f t.2))).sum := by
  rw [← sum_allPairs (fun i j => pe (f i) (f j))]
  unfold energy
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range 14, if i < j then pe (f i) (f j) else 0) 14]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => if i.val < j then pe (f i.val) (f j) else 0) 14, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · have h' : i.val < j.val := hij
    rw [if_pos hij, if_pos h', hf i, hf j]
    rfl
  · have h' : ¬ i.val < j.val := hij
    rw [if_neg hij, if_neg h']

end N14.Local
