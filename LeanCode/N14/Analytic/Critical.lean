module

public import N14.Analytic.Force
public import N14.Analytic.Cases
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The theorem for 14 points, analytic part: the candidate is a critical point (row A10, second part)

The source derives the criticality of the candidate from its symmetry group. Here it is a lower bound for the
energy that needs no derivative on the sphere.

* `pair_convex_dot`: the function `t ↦ (2 - 2t)^(-1/2)` lies above its tangents;
* `uc c`: the weight of a class of pairs of the candidate, the slope of the tangent at its inner product;
* `star_of_stationary`: the weights satisfy the relation `starc uc hStar = 0`. By the convexity, the energy of
  the family `X14 h` minus a polynomial of degree two in `h` has a local minimum at the stationary height, and
  the derivative vanishes there (the theorem of Fermat);
* `quad_lower`: for a symmetric matrix of weights `W` and a configuration `x` whose forces are multiples of its
  points, the form `∑ W i j ⟨y i, y j⟩` of a configuration `y = x + d` of the sphere differs from its value at
  `x` by at least `-K |d|²`;
* `energy_lower`: `energy Xstar - K |y - Xstar|² ≤ energy y` for every configuration `y` of the sphere with
  distinct points.
-/

@[expose] public section

namespace N14

open Finset N14.T7

/-! ## The convexity of the potential -/

/-- For `d, e > 0`: `1/e + (e² - d²)/2 · e⁻³ ≤ 1/d`. -/
theorem pair_convex (d e : ℝ) (hd : 0 < d) (he : 0 < e) : 1 / e + (e ^ 2 - d ^ 2) / 2 * e⁻¹ ^ 3 ≤ 1 / d := by
  rw [← sub_nonneg]
  have key : 1 / d - (1 / e + (e ^ 2 - d ^ 2) / 2 * e⁻¹ ^ 3) = (e - d) ^ 2 * (2 * e + d) / (2 * e ^ 3 * d) := by
    field_simp
    ring
  rw [key]
  positivity

/-- **The potential lies above its tangents.** For inner products `t, s < 1`. -/
theorem pair_convex_dot (t s : ℝ) (ht : t < 1) (hs : s < 1) :
    1 / √(2 - 2 * s) + (t - s) * (√(2 - 2 * s))⁻¹ ^ 3 ≤ 1 / √(2 - 2 * t) := by
  have hd : 0 < √(2 - 2 * t) := Real.sqrt_pos.mpr (by linarith)
  have he : 0 < √(2 - 2 * s) := Real.sqrt_pos.mpr (by linarith)
  have h := pair_convex _ _ hd he
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] at h
  have e : (2 - 2 * s - (2 - 2 * t)) / 2 = t - s := by ring
  rw [e] at h
  exact h

/-! ## The stationary height in terms of the weights -/

/-- The weight of a class of pairs of the candidate. -/
noncomputable def uc (c : ℕ) : ℝ := (√(2 - 2 * ipVal hStar c))⁻¹ ^ 3

/-- The sum over the nine classes of pairs, with the numbers of their pairs. -/
noncomputable def cls (g : ℕ → ℝ) : ℝ :=
  g 0 + 12 * g 1 + 12 * g 2 + 12 * g 3 + 12 * g 4 + 6 * g 5 + 12 * g 6 + 12 * g 7 + 12 * g 8

/-- The energy of the family as a sum over the classes. -/
theorem energy_X14_cls (h : ℝ) (h0 : 0 < h) (h1 : h < 1) :
    energy (X14 h) = cls (fun c => 1 / √(2 - 2 * ipVal h c)) := by
  have hh : h ^ 2 ≤ 1 := by nlinarith
  unfold energy
  have e2 : ∑ i : Fin 14, ∑ j with i < j, 1 / Real.sqrt (∑ k, (X14 h i k - X14 h j k) ^ 2)
      = ∑ i : Fin 14, ∑ j ∈ Finset.univ.filter (fun j : Fin 14 => i < j),
          1 / Real.sqrt (2 - 2 * ipVal h (pc i.val j.val)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => by
      have := sqdist_X14N h hh i.val j.val (Finset.mem_filter.1 hj).2 j.isLt
      unfold X14
      rw [this]
  rw [e2, CAP.sum_fin_pairs 14 (fun i j => 1 / Real.sqrt (2 - 2 * ipVal h (pc i j))),
    pair_count (fun c => 1 / Real.sqrt (2 - 2 * ipVal h c))]
  rfl

/-- The polynomial of degree two in the height that bounds the energy of the family from below. -/
noncomputable def gfam (h : ℝ) : ℝ := cls (fun c => (ipVal h c - ipVal hStar c) * uc c)

theorem energy_family_ge (h : ℝ) (h0 : 0 < h) (h1 : h < 1) (hs0 : 0 < hStar) (hs1 : hStar < 1) :
    energy (X14 hStar) + gfam h ≤ energy (X14 h) := by
  rw [energy_X14_cls h h0 h1, energy_X14_cls hStar hs0 hs1]
  have key : ∀ c : ℕ, 1 / √(2 - 2 * ipVal hStar c) + (ipVal h c - ipVal hStar c) * uc c
      ≤ 1 / √(2 - 2 * ipVal h c) := fun c =>
    pair_convex_dot _ _ (ipVal_lt_one h h0 h1 c) (ipVal_lt_one hStar hs0 hs1 c)
  unfold gfam cls
  beta_reduce
  linarith [key 0, key 1, key 2, key 3, key 4, key 5, key 6, key 7, key 8]

theorem gfam_eq (h : ℝ) : gfam h = 12 * (uc 1 - uc 2) * (h - hStar)
    + (h ^ 2 - hStar ^ 2)
      * (6 * uc 3 + 18 * uc 4 + 12 * uc 5 - (12 + 6 * √3) * uc 6 - 12 * uc 7 - (12 - 6 * √3) * uc 8) := by
  unfold gfam cls
  simp only [ipVal]
  ring

theorem hasDerivAt_gfam : HasDerivAt gfam (12 * starc uc hStar) hStar := by
  have e : gfam = fun h : ℝ => 12 * (uc 1 - uc 2) * (h - hStar) + (h ^ 2 - hStar ^ 2)
      * (6 * uc 3 + 18 * uc 4 + 12 * uc 5 - (12 + 6 * √3) * uc 6 - 12 * uc 7 - (12 - 6 * √3) * uc 8) :=
    funext gfam_eq
  rw [e]
  have h3 : HasDerivAt (fun h : ℝ => 12 * (uc 1 - uc 2) * (h - hStar) + (h ^ 2 - hStar ^ 2)
        * (6 * uc 3 + 18 * uc 4 + 12 * uc 5 - (12 + 6 * √3) * uc 6 - 12 * uc 7 - (12 - 6 * √3) * uc 8))
      (12 * (uc 1 - uc 2) * 1 + ((2 : ℕ) : ℝ) * hStar ^ (2 - 1) * 1
        * (6 * uc 3 + 18 * uc 4 + 12 * uc 5 - (12 + 6 * √3) * uc 6 - 12 * uc 7 - (12 - 6 * √3) * uc 8)) hStar :=
    (((hasDerivAt_id' hStar).sub_const hStar).const_mul (12 * (uc 1 - uc 2))).add
      ((((hasDerivAt_id' hStar).pow 2).sub_const (hStar ^ 2)).mul_const _)
  have e' : 12 * starc uc hStar = 12 * (uc 1 - uc 2) * 1 + ((2 : ℕ) : ℝ) * hStar ^ (2 - 1) * 1
      * (6 * uc 3 + 18 * uc 4 + 12 * uc 5 - (12 + 6 * √3) * uc 6 - 12 * uc 7 - (12 - 6 * √3) * uc 8) := by
    unfold starc
    norm_num
    ring
  rw [e']
  exact h3

/-- The stationary height is a stationary height. -/
theorem stationary_hStar (H : CAP) : StationaryHeight hStar := by
  have hex : ∃ h, StationaryHeight h := H.height.exists
  unfold hStar
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- **The relation between the weights of the candidate**, from the stationarity of the height. -/
theorem star_of_stationary (hst : StationaryHeight hStar) (hs0 : 0 < hStar) (hs1 : hStar < 1) :
    starc uc hStar = 0 := by
  have hd : HasDerivAt (fun t => energy (X14 t) - gfam t) (0 - 12 * starc uc hStar) hStar :=
    hst.2.sub hasDerivAt_gfam
  have hmin : IsLocalMin (fun t => energy (X14 t) - gfam t) hStar := by
    have hnh : Set.Ioo (0 : ℝ) 1 ∈ nhds hStar := Ioo_mem_nhds hs0 hs1
    filter_upwards [hnh] with h hh
    have h1 := energy_family_ge h hh.1 hh.2 hs0 hs1
    have e0 : gfam hStar = 0 := by
      rw [gfam_eq]
      ring
    rw [e0]
    linarith
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-! ## A quadratic form at a configuration with radial forces -/

/-- For unit vectors `y`, `x`: the inner product of `y - x` with `x`. -/
theorem delta_dot {N : ℕ} (x y : Fin N → Fin 3 → ℝ) (hx : OnSphere x) (hy : OnSphere y) (i : Fin N) :
    ∑ k, (y i k - x i k) * x i k = -(1 / 2) * ∑ k, (y i k - x i k) ^ 2 := by
  have h1 := hx i
  have h2 := hy i
  have e : ∑ k, ((y i k - x i k) * x i k + 1 / 2 * (y i k - x i k) ^ 2)
      = ∑ k, (1 / 2 * y i k ^ 2 - 1 / 2 * x i k ^ 2) := Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1,
    h2] at e
  linarith

theorem cross_le {N : ℕ} (d : Fin N → Fin 3 → ℝ) (i j : Fin N) :
    |∑ k, d i k * d j k| ≤ (∑ k, d i k ^ 2 + ∑ k, d j k ^ 2) / 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, abs_le]
  constructor
  · nlinarith [sq_nonneg (d i 0 + d j 0), sq_nonneg (d i 1 + d j 1), sq_nonneg (d i 2 + d j 2)]
  · nlinarith [sq_nonneg (d i 0 - d j 0), sq_nonneg (d i 1 - d j 1), sq_nonneg (d i 2 - d j 2)]

/-- The first-order part of the form: it is of second order because the forces are radial. -/
theorem quad_first {N : ℕ} (W : Fin N → Fin N → ℝ) (cf : Fin N → ℝ) (x d : Fin N → Fin 3 → ℝ)
    (hF : ∀ i k, ∑ j, W i j * x j k = cf i * x i k)
    (hd : ∀ i, ∑ k, d i k * x i k = -(1 / 2) * ∑ k, d i k ^ 2) :
    ∑ i, ∑ j, ∑ k, d i k * (W i j * x j k) = -(1 / 2) * ∑ i, cf i * ∑ k, d i k ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have e : ∀ k, ∑ j, d i k * (W i j * x j k) = cf i * (d i k * x i k) := by
    intro k
    rw [← Finset.mul_sum, hF i k]
    ring
  rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, hd i]
  ring

theorem quad_second {N : ℕ} (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i) (x d : Fin N → Fin 3 → ℝ) :
    ∑ i, ∑ j, ∑ k, d j k * (W i j * x i k) = ∑ i, ∑ j, ∑ k, d i k * (W i j * x j k) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
    rw [hW j i]

/-- The second-order part of the form. -/
theorem quad_third {N : ℕ} (W : Fin N → Fin N → ℝ) (d : Fin N → Fin 3 → ℝ) :
    -(∑ i, ∑ j, |W i j|) * (∑ i, ∑ k, d i k ^ 2) ≤ ∑ i, ∑ j, W i j * ∑ k, d i k * d j k := by
  have hn : ∀ i, 0 ≤ ∑ k, d i k ^ 2 := fun i => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnN : ∀ i, ∑ k, d i k ^ 2 ≤ ∑ i, ∑ k, d i k ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i => ∑ k, d i k ^ 2) (fun i _ => hn i) (Finset.mem_univ i)
  have e : -(∑ i, ∑ j, |W i j|) * (∑ i, ∑ k, d i k ^ 2)
      = ∑ i, ∑ j, -(|W i j| * ∑ i, ∑ k, d i k ^ 2) := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [e]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := cross_le d i j
  have h2 : |∑ k, d i k * d j k| ≤ ∑ i, ∑ k, d i k ^ 2 := by linarith [hnN i, hnN j]
  have h3 : |W i j * ∑ k, d i k * d j k| ≤ |W i j| * ∑ i, ∑ k, d i k ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  linarith [neg_abs_le (W i j * ∑ k, d i k * d j k)]

/-- **The quadratic form at a configuration with radial forces.** Let `W` be a symmetric matrix of weights, `x` a
configuration with `∑ j, W i j • x j = cf i • x i`, and `d` a displacement with `⟨d i, x i⟩ = -|d i|²/2` (which
holds if `x i` and `x i + d i` are unit vectors). Then the form of `x + d` minus the form of `x` is at least
`-K |d|²`. -/
theorem quad_lower {N : ℕ} (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i) (cf : Fin N → ℝ)
    (x d : Fin N → Fin 3 → ℝ) (hF : ∀ i k, ∑ j, W i j * x j k = cf i * x i k)
    (hd : ∀ i, ∑ k, d i k * x i k = -(1 / 2) * ∑ k, d i k ^ 2) :
    -(∑ i, |cf i| + ∑ i, ∑ j, |W i j|) * (∑ i, ∑ k, d i k ^ 2)
      ≤ ∑ i, ∑ j, W i j * ∑ k, ((x i k + d i k) * (x j k + d j k) - x i k * x j k) := by
  have e0 : ∀ i j, W i j * ∑ k, ((x i k + d i k) * (x j k + d j k) - x i k * x j k)
      = ∑ k, d i k * (W i j * x j k) + ∑ k, d j k * (W i j * x i k) + W i j * ∑ k, d i k * d j k := by
    intro i j
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∑ i, ∑ j, W i j * ∑ k, ((x i k + d i k) * (x j k + d j k) - x i k * x j k)
      = ∑ i, ∑ j, ∑ k, d i k * (W i j * x j k) + ∑ i, ∑ j, ∑ k, d j k * (W i j * x i k)
        + ∑ i, ∑ j, W i j * ∑ k, d i k * d j k := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => e0 i j
  rw [e1, quad_second W hW x d, quad_first W cf x d hF hd]
  have h3 := quad_third W d
  have hn : ∀ i, 0 ≤ ∑ k, d i k ^ 2 := fun i => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnN : ∀ i, ∑ k, d i k ^ 2 ≤ ∑ i, ∑ k, d i k ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i => ∑ k, d i k ^ 2) (fun i _ => hn i) (Finset.mem_univ i)
  have h4 : ∑ i, cf i * ∑ k, d i k ^ 2 ≤ (∑ i, |cf i|) * ∑ i, ∑ k, d i k ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    calc cf i * ∑ k, d i k ^ 2 ≤ |cf i| * ∑ k, d i k ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (hn i)
      _ ≤ |cf i| * ∑ i, ∑ k, d i k ^ 2 := mul_le_mul_of_nonneg_left (hnN i) (abs_nonneg _)
  linarith

/-! ## The energy near the candidate -/

theorem sqdist_dot {N : ℕ} (y : Fin N → Fin 3 → ℝ) (hy : OnSphere y) (i j : Fin N) :
    ∑ k, (y i k - y j k) ^ 2 = 2 - 2 * dot y i j := by
  have h1 := hy i
  have h2 := hy j
  have e : ∑ k, (y i k - y j k) ^ 2 = ∑ k, y i k ^ 2 + ∑ k, y j k ^ 2 - 2 * ∑ k, y i k * y j k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, h1, h2]
  unfold dot
  ring

/-- The symmetric matrix of the weights of the candidate. -/
noncomputable def wmat (i j : Fin 14) : ℝ := if j.val = i.val then 0 else uc (pcS i.val j.val)

theorem wmat_symm (i j : Fin 14) : wmat i j = wmat j i := by
  unfold wmat
  by_cases e : j.val = i.val
  · rw [if_pos e, if_pos e.symm]
  · rw [if_neg e, if_neg (fun e' => e e'.symm), pcS_comm i.val j.val (fun e' => e e'.symm)]

/-- The energy of a configuration of the sphere with distinct points, compared with the candidate: the
convexity of the potential for every pair. -/
theorem energy_ge_form (H : CAP) (y : Fin 14 → Fin 3 → ℝ) (hy : OnSphere y)
    (hlt : ∀ i j, i ≠ j → dot y i j < 1) :
    energy Xstar + ∑ i : Fin 14, ∑ j ∈ univ.filter (fun j => i < j), wmat i j * (dot y i j - dot Xstar i j)
      ≤ energy y := by
  have hb := hStar_bounds H
  have hs0 : 0 < hStar := by linarith [hb.1]
  have hs1 : hStar < 1 := by linarith [hb.2]
  unfold energy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hne : i ≠ j := ne_of_lt hij
  rw [sqdist_dot y hy, sqdist_dot Xstar H.candidate.1]
  have hv : dot Xstar i j = ipVal hStar (pcS i.val j.val) := H.values i j hne
  have hw : wmat i j = (√(2 - 2 * dot Xstar i j))⁻¹ ^ 3 := by
    unfold wmat uc
    rw [if_neg (fun e => hne (Fin.ext e.symm)), hv]
  rw [hw]
  have hX : dot Xstar i j < 1 := by
    rw [hv]
    exact ipVal_lt_one hStar hs0 hs1 _
  have := pair_convex_dot (dot y i j) (dot Xstar i j) (hlt i j hne) hX
  linarith

/-- **The energy near the candidate.** There is a number `K ≥ 0` such that every configuration `y` of 14 points
of the sphere whose inner products are smaller than `1` satisfies
`energy Xstar - K ∑ |y i - Xstar i|² ≤ energy y`. -/
theorem energy_lower (H : CAP) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Fin 14 → Fin 3 → ℝ, OnSphere y →
    (∀ i j, i ≠ j → dot y i j < 1) →
    energy Xstar - K * ∑ i : Fin 14, ∑ k, (y i k - Xstar i k) ^ 2 ≤ energy y := by
  have hb := hStar_bounds H
  have hs0 : 0 < hStar := by linarith [hb.1]
  have hs1 : hStar < 1 := by linarith [hb.2]
  have hstar := star_of_stationary (stationary_hStar H) hs0 hs1
  have hF : ∀ (i : Fin 14) (k : Fin 3), ∑ j, wmat i j * Xstar j k = cfc uc hStar i.val * Xstar i k :=
    fun i k => force_vector uc hStar hs0 hs1 hstar i k
  refine ⟨(∑ i : Fin 14, |cfc uc hStar i.val| + ∑ i : Fin 14, ∑ j, |wmat i j|) / 2,
    div_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)) (by norm_num), fun y hy hlt => ?_⟩
  have h1 := energy_ge_form H y hy hlt
  -- the sum over the pairs as half of the sum over all ordered pairs
  have h2 := sum_all_eq (fun i j : Fin 14 => wmat i j * (dot y i j - dot Xstar i j))
    (fun i j => by rw [wmat_symm i j, dot_comm y i j, dot_comm Xstar i j])
    (fun i => by
      unfold wmat
      rw [if_pos rfl, zero_mul])
  -- the quadratic form
  have h3 := quad_lower wmat wmat_symm (fun i => cfc uc hStar i.val) Xstar (fun i k => y i k - Xstar i k) hF
    (fun i => delta_dot Xstar y H.candidate.1 hy i)
  have e : ∀ i j : Fin 14, ∑ k, ((Xstar i k + (y i k - Xstar i k)) * (Xstar j k + (y j k - Xstar j k))
      - Xstar i k * Xstar j k) = dot y i j - dot Xstar i j := by
    intro i j
    unfold dot
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h3' : -(∑ i : Fin 14, |cfc uc hStar i.val| + ∑ i : Fin 14, ∑ j, |wmat i j|)
      * ∑ i : Fin 14, ∑ k, (y i k - Xstar i k) ^ 2 ≤ ∑ i : Fin 14, ∑ j, wmat i j * (dot y i j - dot Xstar i j) := by
    refine le_trans h3 (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [e i j]
  linarith

end N14
