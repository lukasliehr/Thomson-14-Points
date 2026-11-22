module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CAP.Schema.ThreePoint.Kernels
public import CAP.Schema.ThreePoint.Weights

/-!
# Schema S2: the three-point bound on the sphere

**Theorem** (`sphere_energy_bound`). Let the data of a certificate satisfy

* the three-point identity `symm6 (ZZ P mrows sos Hp cp) = 0`;
* the matrices of all blocks are positive definite (`MomentPD`, `SosPD`);
* the weight of every block is `1`, `1 - u ^ 2` or the Gram determinant;
* `Ĥ t ≤ Dn / √(2 - 2 t)` for `-1 ≤ t < 1`.

Then every configuration of `N` distinct points on the unit sphere of `ℝ³` has the Coulomb energy
at least `(cp / Dn) N (N - 1) / 2`.

The proof applies `three_point_sum` to the inner products `a i j = ⟪x i, x j⟫`. For the kernels, a
point `x i` is the first vector of an orthonormal basis; with the coordinates `p`, `q` of the
other points along the two further vectors, the complex numbers `w j = p j + q j I` satisfy
`Re (w j conj (w m)) = a j m - a i j a i m` and `|w j|² = 1 - (a i j)²`, which are the hypotheses of
`moment_kernel_nonneg`. The Gram determinant of three unit vectors is `(p j q m - q j p m)²`.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-- A unit vector of `ℝ³` is the first vector of an orthonormal basis. -/
theorem exists_frame (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)), b 0 = x := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict fun _ => x) :=
    ⟨fun _ => hx, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

/-- The inner product in coordinates with respect to a unit vector `x`: its own direction, and two
coordinates `p`, `q` orthogonal to it. -/
theorem frame_coords (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    ∃ p q : EuclideanSpace ℝ (Fin 3) → ℝ, ∀ y z : EuclideanSpace ℝ (Fin 3),
      inner ℝ y z = inner ℝ x y * inner ℝ x z + p y * p z + q y * q z := by
  obtain ⟨b, hb⟩ := exists_frame x hx
  refine ⟨fun y => inner ℝ (b 1) y, fun y => inner ℝ (b 2) y, fun y z => ?_⟩
  have h := b.sum_inner_mul_inner y z
  rw [Fin.sum_univ_three, hb] at h
  have e0 : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  have e1 : inner ℝ y (b 1) = inner ℝ (b 1) y := real_inner_comm _ _
  have e2 : inner ℝ y (b 2) = inner ℝ (b 2) y := real_inner_comm _ _
  rw [e0, e1, e2] at h
  exact h.symm

/-- The Gram determinant of three unit vectors is nonnegative. -/
theorem gram_nonneg (x y z : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ 1 + 2 * inner ℝ x y * inner ℝ x z * inner ℝ y z - inner ℝ x y ^ 2 - inner ℝ x z ^ 2
      - inner ℝ y z ^ 2 := by
  obtain ⟨p, q, hpq⟩ := frame_coords x hx
  have hyy := hpq y y
  have hzz := hpq z z
  have hyz := hpq y z
  rw [real_inner_self_eq_norm_sq, hy, one_pow] at hyy
  rw [real_inner_self_eq_norm_sq, hz, one_pow] at hzz
  have e : 1 + 2 * inner ℝ x y * inner ℝ x z * inner ℝ y z - inner ℝ x y ^ 2 - inner ℝ x z ^ 2
      - inner ℝ y z ^ 2 = (p y * q z - q y * p z) ^ 2 := by
    rw [hyz]
    linear_combination (1 - inner ℝ x z ^ 2) * hyy + (p y * p y + q y * q y) * hzz
  rw [e]
  positivity

theorem eq_of_inner_eq_one {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : inner ℝ x y = (1 : ℝ)) : x = y := by
  have h2 : ‖x - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hx, hy, h]
    norm_num
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h2))

/-- The identity, the positive definite matrices and the weights give the bound for the sum of
`Ĥ` over the pairs of distinct points. -/
theorem sphere_sum_bound (P : Params) (rows : ℕ) (l : List ℕ) (sos : List Sos) (Hp cp : ℕ)
    (hid : symm6 (ZZ P (rows :: l) sos Hp cp) = 0)
    (hM : MomentPD P (rows :: l) 0) (hS : SosPD P sos)
    (hw : ∀ B ∈ sos, polyZ P B.gT B.weight = 1 ∨ polyZ P B.gT B.weight = 1 - X 0 ^ 2
      ∨ polyZ P B.gT B.weight = 1 + 2 * X 0 * X 1 * X 2 - X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2)
    (hN3 : 3 ≤ P.N) (x : Fin P.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) :
    (P.N : ℝ) * ((P.N : ℝ) - 1) * cp
      ≤ ∑ i, ∑ j, if i ≠ j then evR (inner ℝ (x i) (x j)) 0 0 (HZ P Hp) else 0 := by
  have ha : ∀ i j, inner ℝ (x i) (x j) = inner ℝ (x j) (x i) := fun i j => real_inner_comm _ _
  have ha1 : ∀ i, inner ℝ (x i) (x i) = (1 : ℝ) := fun i => by
    rw [real_inner_self_eq_norm_sq, hx i, one_pow]
  have hle : ∀ i j, inner ℝ (x i) (x j) ^ 2 ≤ (1 : ℝ) := by
    intro i j
    have habs := abs_real_inner_le_norm (x i) (x j)
    rw [hx i, hx j, mul_one] at habs
    have h := abs_le.mp habs
    nlinarith [h.1, h.2]
  -- the kernels are positive definite
  have hMk : ∀ i, 0 ≤ ∑ j, ∑ k, evR (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k))
      (momentZ P (rows :: l) 0) := by
    intro i
    obtain ⟨p, q, hpq⟩ := frame_coords (x i) (hx i)
    have hsq : ∀ j, p (x j) * p (x j) + q (x j) * q (x j) = 1 - inner ℝ (x i) (x j) ^ 2 := by
      intro j
      have h := hpq (x j) (x j)
      rw [ha1 j] at h
      rw [sq]
      linarith
    refine moment_kernel_nonneg P (fun j => inner ℝ (x i) (x j)) (fun j m => inner ℝ (x j) (x m))
      (fun j => ⟨p (x j), q (x j)⟩) ?_ ?_ (rows :: l) 0 hM
    · intro j m
      show ((⟨p (x j), q (x j)⟩ : ℂ) * (starRingEnd ℂ) ⟨p (x m), q (x m)⟩).re
        = inner ℝ (x j) (x m) - inner ℝ (x i) (x j) * inner ℝ (x i) (x m)
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hpq (x j) (x m)]
      ring
    · intro j m
      show Complex.normSq ((⟨p (x j), q (x j)⟩ : ℂ) * (starRingEnd ℂ) ⟨p (x m), q (x m)⟩)
        = (1 - inner ℝ (x i) (x j) ^ 2) * (1 - inner ℝ (x i) (x m) ^ 2)
      rw [map_mul, Complex.normSq_conj, Complex.normSq_mk, Complex.normSq_mk, hsq j, hsq m]
  -- the sums of squares are nonnegative
  have hGk : ∀ i j k, 0 ≤ evR (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k))
      (sosSumZ P sos) := by
    intro i j k
    refine evR_sosSumZ_nonneg P _ _ _ sos hS fun B hB => ?_
    rcases hw B hB with h | h | h
    · rw [h, map_one]
      exact zero_le_one
    · rw [h]
      simp only [map_sub, map_one, map_pow, evR_X0]
      linarith [hle i j]
    · rw [h]
      simp only [map_add, map_sub, map_mul, map_one, map_pow, map_ofNat, evR_X0, evR_X1, evR_X2]
      exact gram_nonneg (x i) (x j) (x k) (hx i) (hx j) (hx k)
  -- the identity
  have key : ∀ u v t, Zf (Fintype.card (Fin P.N)) (fun u v t => evR u v t (momentZ P (rows :: l) 0))
      (fun u v t => evR u v t (sosSumZ P sos)) (fun u => evR u 0 0 (HZ P Hp)) (x0Z P rows : ℝ) (cp : ℝ) u v t
      = evR u v t (ZZ P (rows :: l) sos Hp cp) := by
    intro u v t
    rw [Fintype.card_fin]
    exact (evR_ZZ P (rows :: l) sos Hp cp u v t).symm
  have h := three_point_sum (fun i j => inner ℝ (x i) (x j)) ha ha1
    (fun u v t => evR u v t (momentZ P (rows :: l) 0)) (fun u v t => evR u v t (sosSumZ P sos))
    (fun u => evR u 0 0 (HZ P Hp)) (x0Z P rows : ℝ) (cp : ℝ) (by rw [Fintype.card_fin]; exact hN3)
    (fun u v t => by rw [key, key, key, key, key, key, ← evR_symm6, hid, map_zero])
    hMk hGk (evR_one_moment_zero P rows l)
  rw [Fintype.card_fin] at h
  exact h

/-- **The three-point bound on the sphere.** See the head of this file. -/
theorem sphere_energy_bound (P : Params) (rows : ℕ) (l : List ℕ) (sos : List Sos) (Hp cp Dn : ℕ)
    (hid : symm6 (ZZ P (rows :: l) sos Hp cp) = 0)
    (hM : MomentPD P (rows :: l) 0) (hS : SosPD P sos)
    (hw : ∀ B ∈ sos, polyZ P B.gT B.weight = 1 ∨ polyZ P B.gT B.weight = 1 - X 0 ^ 2
      ∨ polyZ P B.gT B.weight = 1 + 2 * X 0 * X 1 * X 2 - X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2)
    (hN3 : 3 ≤ P.N) (hDn : 0 < Dn)
    (hH : ∀ t : ℝ, -1 ≤ t → t < 1 → evR t 0 0 (HZ P Hp) ≤ Dn / Real.sqrt (2 - 2 * t))
    (x : Fin P.N → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x) :
    (cp : ℝ) / Dn * ((P.N : ℝ) * ((P.N : ℝ) - 1) / 2)
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have h1 := sphere_sum_bound P rows l sos Hp cp hid hM hS hw hN3 x hx
  have h2 : ∀ i j, (if i ≠ j then evR (inner ℝ (x i) (x j)) 0 0 (HZ P Hp) else 0)
      ≤ if i ≠ j then (Dn : ℝ) * (1 / dist (x i) (x j)) else 0 := by
    intro i j
    by_cases hij : i = j
    · rw [if_neg (not_not.mpr hij), if_neg (not_not.mpr hij)]
    · rw [if_pos hij, if_pos hij]
      have habs := abs_real_inner_le_norm (x i) (x j)
      rw [hx i, hx j, mul_one] at habs
      have hle := abs_le.mp habs
      have hne : inner ℝ (x i) (x j) ≠ (1 : ℝ) := fun h =>
        hij (hinj (eq_of_inner_eq_one (hx i) (hx j) h))
      have hlt : inner ℝ (x i) (x j) < (1 : ℝ) := lt_of_le_of_ne hle.2 hne
      have hd : dist (x i) (x j) = Real.sqrt (2 - 2 * inner ℝ (x i) (x j)) := by
        rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (x i - x j)), norm_sub_sq_real, hx i, hx j]
        congr 1
        ring
      rw [hd, mul_one_div]
      exact hH _ hle.1 hlt
  have h3 : (∑ i, ∑ j, if i ≠ j then evR (inner ℝ (x i) (x j)) 0 0 (HZ P Hp) else 0)
      ≤ ∑ i, ∑ j, if i ≠ j then (Dn : ℝ) * (1 / dist (x i) (x j)) else 0 :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => h2 i j
  have h4 := sum_ne_eq_two_mul_sum_lt (fun i j => (Dn : ℝ) * (1 / dist (x i) (x j)))
    (fun i j => by rw [dist_comm])
  rw [h4] at h3
  have h5 := h1.trans h3
  simp only [← mul_sum] at h5
  have hDn' : (0 : ℝ) < Dn := by exact_mod_cast hDn
  rw [div_mul_eq_mul_div, div_le_iff₀ hDn']
  linarith

end CAP.ThreePoint
