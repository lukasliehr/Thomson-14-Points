module

public import N14.Statement
public import CAP.Core.PairSum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.IntervalCases

/-!
# The theorem for 14 points: the family `X14 h` and its inner products

The configuration `X14 h` (`N14/Statement.lean`) consists of the two poles and of two regular
hexagons at the heights `h` and `-h`. This file proves, for `h² ≤ 1`:

* `cos_tab`, `sin_tab`: the cosine and the sine of the multiples of 30 degrees;
* `inner_X14N`: the inner product of two points is one of nine values, `ipVal h (pc i j)`; the class
  `pc i j` of a pair is the function `pair` of `Certificates/common/audit_geometry.py` of the source,
  and the values are its list `values`;
* `onSphere_X14`, `sqdist_X14N`, `injective_X14`;
* `energy_X14`: the energy of `X14 h` is the function `Efam h` of formula (1.1) of the source, for
  `0 < h < 1`. The terms of `Efam` are written like the expression of the certificate of statement 1
  (`certgen/n14_height.py`), so that the two functions are equal by definition.
-/

@[expose] public section

namespace N14

open Real Finset

theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `cos (k π / 6)`. -/
noncomputable def c12 (k : ℕ) : ℝ :=
  match k % 12 with
  | 0 => 1
  | 1 => √3 / 2
  | 2 => 1 / 2
  | 3 => 0
  | 4 => -1 / 2
  | 5 => -√3 / 2
  | 6 => -1
  | 7 => -√3 / 2
  | 8 => -1 / 2
  | 9 => 0
  | 10 => 1 / 2
  | _ => √3 / 2

/-- `sin (k π / 6)`. -/
noncomputable def s12 (k : ℕ) : ℝ := c12 (k + 9)

theorem c12_add (k : ℕ) : c12 (k + 12) = c12 k := by
  unfold c12
  rw [Nat.add_mod_right]

theorem cos_tab : ∀ k : ℕ, k < 12 → cos ((k : ℝ) * (π / 6)) = c12 k := by
  intro k hk
  interval_cases k
  · simp [c12]
  · simp [c12]
  · rw [show ((2 : ℕ) : ℝ) * (π / 6) = π / 3 by push_cast; ring, cos_pi_div_three]
    simp [c12]
  · rw [show ((3 : ℕ) : ℝ) * (π / 6) = π / 2 by push_cast; ring, cos_pi_div_two]
    simp [c12]
  · rw [show ((4 : ℕ) : ℝ) * (π / 6) = π - π / 3 by push_cast; ring, cos_pi_sub, cos_pi_div_three]
    norm_num [c12]
  · rw [show ((5 : ℕ) : ℝ) * (π / 6) = π - π / 6 by push_cast; ring, cos_pi_sub, cos_pi_div_six]
    norm_num [c12]
    ring
  · rw [show ((6 : ℕ) : ℝ) * (π / 6) = π by push_cast; ring, cos_pi]
    simp [c12]
  · rw [show ((7 : ℕ) : ℝ) * (π / 6) = π / 6 + π by push_cast; ring, cos_add_pi, cos_pi_div_six]
    norm_num [c12]
    ring
  · rw [show ((8 : ℕ) : ℝ) * (π / 6) = π / 3 + π by push_cast; ring, cos_add_pi, cos_pi_div_three]
    norm_num [c12]
  · rw [show ((9 : ℕ) : ℝ) * (π / 6) = π / 2 + π by push_cast; ring, cos_add_pi, cos_pi_div_two]
    simp [c12]
  · rw [show ((10 : ℕ) : ℝ) * (π / 6) = 2 * π - π / 3 by push_cast; ring, cos_two_pi_sub, cos_pi_div_three]
    simp [c12]
  · rw [show ((11 : ℕ) : ℝ) * (π / 6) = 2 * π - π / 6 by push_cast; ring, cos_two_pi_sub, cos_pi_div_six]
    simp [c12]

theorem sin_tab : ∀ k : ℕ, k < 12 → sin ((k : ℝ) * (π / 6)) = s12 k := by
  intro k hk
  interval_cases k
  · simp [s12, c12]
  · simp [s12, c12]
  · rw [show ((2 : ℕ) : ℝ) * (π / 6) = π / 3 by push_cast; ring, sin_pi_div_three]
    simp [s12, c12]
  · rw [show ((3 : ℕ) : ℝ) * (π / 6) = π / 2 by push_cast; ring, sin_pi_div_two]
    simp [s12, c12]
  · rw [show ((4 : ℕ) : ℝ) * (π / 6) = π - π / 3 by push_cast; ring, sin_pi_sub, sin_pi_div_three]
    simp [s12, c12]
  · rw [show ((5 : ℕ) : ℝ) * (π / 6) = π - π / 6 by push_cast; ring, sin_pi_sub, sin_pi_div_six]
    simp [s12, c12]
  · rw [show ((6 : ℕ) : ℝ) * (π / 6) = π by push_cast; ring, sin_pi]
    simp [s12, c12]
  · rw [show ((7 : ℕ) : ℝ) * (π / 6) = π / 6 + π by push_cast; ring, sin_add_pi, sin_pi_div_six]
    norm_num [s12, c12]
  · rw [show ((8 : ℕ) : ℝ) * (π / 6) = π / 3 + π by push_cast; ring, sin_add_pi, sin_pi_div_three]
    norm_num [s12, c12]
    ring
  · rw [show ((9 : ℕ) : ℝ) * (π / 6) = π / 2 + π by push_cast; ring, sin_add_pi, sin_pi_div_two]
    simp [s12, c12]
  · rw [show ((10 : ℕ) : ℝ) * (π / 6) = 2 * π - π / 3 by push_cast; ring, sin_two_pi_sub, sin_pi_div_three]
    norm_num [s12, c12]
    ring
  · rw [show ((11 : ℕ) : ℝ) * (π / 6) = 2 * π - π / 6 by push_cast; ring, sin_two_pi_sub, sin_pi_div_six]
    norm_num [s12, c12]

/-- The cosine of the difference of two multiples of 30 degrees. -/
theorem cos_diff (a b : ℕ) (ha : a < 12) (hb : b < 12) :
    cos ((b : ℝ) * (π / 6) - (a : ℝ) * (π / 6)) = c12 (b + 12 - a) := by
  by_cases hab : a ≤ b
  · have e : (b : ℝ) * (π / 6) - (a : ℝ) * (π / 6) = ((b - a : ℕ) : ℝ) * (π / 6) := by
      rw [Nat.cast_sub hab]
      ring
    rw [e, cos_tab (b - a) (by omega), show b + 12 - a = (b - a) + 12 by omega, c12_add]
  · have e : (b : ℝ) * (π / 6) - (a : ℝ) * (π / 6) = ((b + 12 - a : ℕ) : ℝ) * (π / 6) - 2 * π := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [e, cos_sub_two_pi, cos_tab (b + 12 - a) (by omega)]

/-! ## The points of the hexagons -/

/-- The angle of a point of a hexagon, in units of 30 degrees. -/
def ang (n : ℕ) : ℕ := if n < 8 then 2 * (n - 2) else 2 * (n - 8) + 1

/-- The sign of the height of a point of a hexagon. -/
noncomputable def zs (n : ℕ) : ℝ := if n < 8 then 1 else -1

theorem ang_lt (n : ℕ) (h2 : 2 ≤ n) (h14 : n < 14) : ang n < 12 := by
  unfold ang
  split_ifs <;> omega

theorem X14N_ring (h : ℝ) (n : ℕ) (h2 : 2 ≤ n) :
    X14N h n = ![√(1 - h ^ 2) * cos ((ang n : ℝ) * (π / 6)), √(1 - h ^ 2) * sin ((ang n : ℝ) * (π / 6)),
      zs n * h] := by
  unfold X14N ang zs
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases h8 : n < 8
  · rw [if_pos h8, if_pos h8, if_pos h8]
    have e : ((2 * (n - 2) : ℕ) : ℝ) * (π / 6) = ((n - 2 : ℕ) : ℝ) * (π / 3) := by
      push_cast
      ring
    rw [e, one_mul]
  · rw [if_neg h8, if_neg h8, if_neg h8]
    have e : ((2 * (n - 8) + 1 : ℕ) : ℝ) * (π / 6) = ((n - 8 : ℕ) : ℝ) * (π / 3) + π / 6 := by
      push_cast
      ring
    rw [e, neg_one_mul]

/-- The class of a pair `i < j` of points: the function `pair` of `audit_geometry.py`. -/
def pc (i j : ℕ) : ℕ :=
  if i = 0 then (if j = 1 then 0 else if j < 8 then 1 else 2)
  else if i = 1 then (if j < 8 then 2 else 1)
  else if j < 8 ∨ 8 ≤ i then min ((j - i) % 6) ((i + 6 - j) % 6) + 2
  else
    match (2 * (j - 8) + 13 - 2 * (i - 2)) % 12 with
    | 1 => 6
    | 3 => 7
    | 5 => 8
    | 7 => 8
    | 9 => 7
    | _ => 6

/-- The nine inner products of the configuration `X14 h`: the list `values` of `audit_geometry.py`. -/
noncomputable def ipVal (h : ℝ) (c : ℕ) : ℝ :=
  match c with
  | 0 => -1
  | 1 => h
  | 2 => -h
  | 3 => (1 + h ^ 2) / 2
  | 4 => (3 * h ^ 2 - 1) / 2
  | 5 => 2 * h ^ 2 - 1
  | 6 => -h ^ 2 + √3 / 2 * (1 - h ^ 2)
  | 7 => -h ^ 2
  | _ => -h ^ 2 - √3 / 2 * (1 - h ^ 2)

theorem ring_inner (h : ℝ) (hh : h ^ 2 ≤ 1) (i j : ℕ) (hi : 2 ≤ i) (hi14 : i < 14) (hj : 2 ≤ j)
    (hj14 : j < 14) :
    ∑ k, X14N h i k * X14N h j k = (1 - h ^ 2) * c12 (ang j + 12 - ang i) + zs i * zs j * h ^ 2 := by
  rw [X14N_ring h i hi, X14N_ring h j hj, Fin.sum_univ_three,
    ← cos_diff (ang i) (ang j) (ang_lt i hi hi14) (ang_lt j hj hj14), cos_sub]
  have hr : √(1 - h ^ 2) ^ 2 = 1 - h ^ 2 := Real.sq_sqrt (by linarith)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (cos ((ang j : ℝ) * (π / 6)) * cos ((ang i : ℝ) * (π / 6))
    + sin ((ang j : ℝ) * (π / 6)) * sin ((ang i : ℝ) * (π / 6))) * hr

theorem ring_class (h : ℝ) : ∀ i j : ℕ, 2 ≤ i → i < j → j < 14 →
    (1 - h ^ 2) * c12 (ang j + 12 - ang i) + zs i * zs j * h ^ 2 = ipVal h (pc i j) := by
  intro i j hi hij hj
  have hj3 : 3 ≤ j := by omega
  interval_cases j <;> interval_cases i <;> first
    | omega
    | (norm_num [ang, zs, pc, ipVal, c12]; try ring)

/-- **The inner products of the family.** -/
theorem inner_X14N (h : ℝ) (hh : h ^ 2 ≤ 1) (i j : ℕ) (hij : i < j) (hj : j < 14) :
    ∑ k, X14N h i k * X14N h j k = ipVal h (pc i j) := by
  by_cases hi2 : 2 ≤ i
  · rw [ring_inner h hh i j hi2 (by omega) (by omega) hj, ring_class h i j hi2 hij hj]
  · by_cases hj2 : 2 ≤ j
    · rw [X14N_ring h j hj2, Fin.sum_univ_three]
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · by_cases h8 : j < 8
        · have hp : pc 0 j = 1 := by
            unfold pc
            rw [if_pos rfl, if_neg (by omega), if_pos h8]
          simp [X14N, zs, h8, hp, ipVal]
        · have hp : pc 0 j = 2 := by
            unfold pc
            rw [if_pos rfl, if_neg (by omega), if_neg h8]
          simp [X14N, zs, h8, hp, ipVal]
      · by_cases h8 : j < 8
        · have hp : pc 1 j = 2 := by
            unfold pc
            rw [if_neg (by omega), if_pos rfl, if_pos h8]
          simp [X14N, zs, h8, hp, ipVal]
        · have hp : pc 1 j = 1 := by
            unfold pc
            rw [if_neg (by omega), if_pos rfl, if_neg h8]
          simp [X14N, zs, h8, hp, ipVal]
    · obtain rfl : i = 0 := by omega
      obtain rfl : j = 1 := by omega
      simp [X14N, pc, ipVal, Fin.sum_univ_three]

/-- **The points of `X14 h` lie on the unit sphere.** -/
theorem norm_X14N (h : ℝ) (hh : h ^ 2 ≤ 1) (n : ℕ) : ∑ k, X14N h n k ^ 2 = 1 := by
  by_cases h2 : 2 ≤ n
  · rw [X14N_ring h n h2, Fin.sum_univ_three]
    have hr : √(1 - h ^ 2) ^ 2 = 1 - h ^ 2 := Real.sq_sqrt (by linarith)
    have hz : zs n ^ 2 = 1 := by
      unfold zs
      split_ifs <;> norm_num
    have hc := Real.cos_sq_add_sin_sq ((ang n : ℝ) * (π / 6))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination (cos ((ang n : ℝ) * (π / 6)) ^ 2 + sin ((ang n : ℝ) * (π / 6)) ^ 2) * hr
      + (1 - h ^ 2) * hc + h ^ 2 * hz
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;> simp [X14N, Fin.sum_univ_three]

theorem onSphere_X14 (h : ℝ) (hh : h ^ 2 ≤ 1) : OnSphere (X14 h) := fun i => norm_X14N h hh i.val

/-- The squared distance of two points of the family. -/
theorem sqdist_X14N (h : ℝ) (hh : h ^ 2 ≤ 1) (i j : ℕ) (hij : i < j) (hj : j < 14) :
    ∑ k, (X14N h i k - X14N h j k) ^ 2 = 2 - 2 * ipVal h (pc i j) := by
  have e : ∑ k, (X14N h i k - X14N h j k) ^ 2
      = ∑ k, X14N h i k ^ 2 + ∑ k, X14N h j k ^ 2 - 2 * ∑ k, X14N h i k * X14N h j k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, norm_X14N h hh i, norm_X14N h hh j, inner_X14N h hh i j hij hj]
  ring

/-- The nine inner products are smaller than `1` for `0 < h < 1`. -/
theorem ipVal_lt_one (h : ℝ) (h0 : 0 < h) (h1 : h < 1) (c : ℕ) : ipVal h c < 1 := by
  have hs : (√3 : ℝ) < 2 := by
    have := sqrt3_sq
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hq : h ^ 2 < 1 := by nlinarith
  unfold ipVal
  split <;> nlinarith [sq_nonneg h]

/-- **The points of `X14 h` are distinct** for `0 < h < 1`. -/
theorem injective_X14 (h : ℝ) (h0 : 0 < h) (h1 : h < 1) : Function.Injective (X14 h) := by
  have hh : h ^ 2 ≤ 1 := by nlinarith
  have key : ∀ a b : Fin 14, a < b → X14 h a ≠ X14 h b := by
    intro a b hab e
    have h1' := sqdist_X14N h hh a.val b.val hab b.isLt
    have e' : X14N h a.val = X14N h b.val := e
    rw [e'] at h1'
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1'
    linarith [ipVal_lt_one h h0 h1 (pc a.val b.val)]
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i j hlt hij
  · exact key j i hlt hij.symm

/-! ## The energy of the family -/

/-- **Formula (1.1) of the source**: the energy of `X14 h`. The terms are written in the order of the
operations of the program of the certificate of statement 1. -/
noncomputable def Efam (h : ℝ) : ℝ :=
  2⁻¹ + 12 * (Real.sqrt (2 - 2 * h))⁻¹ + 12 * (Real.sqrt (2 + 2 * h))⁻¹
    + (15 + 12 * (Real.sqrt 3)⁻¹) * (Real.sqrt (1 - h * h))⁻¹
    + 12 * (Real.sqrt (2 * (1 - h * h) * (1 - Real.sqrt 3 * 2⁻¹) + 4 * (h * h)))⁻¹
    + 12 * (Real.sqrt (2 * (1 - h * h) * 1 + 4 * (h * h)))⁻¹
    + 12 * (Real.sqrt (2 * (1 - h * h) * (1 + Real.sqrt 3 * 2⁻¹) + 4 * (h * h)))⁻¹

/-- The numbers of the pairs of the nine classes: `1, 12, 12, 12, 12, 6, 12, 12, 12`. -/
theorem pair_count (g : ℕ → ℝ) : ∑ j ∈ range 14, ∑ i ∈ range j, g (pc i j)
    = g 0 + 12 * g 1 + 12 * g 2 + 12 * g 3 + 12 * g 4 + 6 * g 5 + 12 * g 6 + 12 * g 7 + 12 * g 8 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [pc]
  ring

/-- **The energy of the family** (formula (1.1) of the source). -/
theorem energy_X14 (h : ℝ) (h0 : 0 < h) (h1 : h < 1) : energy (X14 h) = Efam h := by
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
  have hr : (0 : ℝ) ≤ 1 - h * h := by nlinarith
  have e0 : Real.sqrt (2 - 2 * ipVal h 0) = 2 := by
    rw [show (2 : ℝ) - 2 * ipVal h 0 = 2 ^ 2 by norm_num [ipVal], Real.sqrt_sq (by norm_num)]
  have e1 : (2 : ℝ) - 2 * ipVal h 1 = 2 - 2 * h := by simp [ipVal]
  have e2' : (2 : ℝ) - 2 * ipVal h 2 = 2 + 2 * h := by
    simp [ipVal]
  have e3 : (2 : ℝ) - 2 * ipVal h 3 = 1 - h * h := by
    simp only [ipVal]
    ring
  have e4 : Real.sqrt (2 - 2 * ipVal h 4) = Real.sqrt 3 * Real.sqrt (1 - h * h) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    simp only [ipVal]
    ring
  have e5 : Real.sqrt (2 - 2 * ipVal h 5) = 2 * Real.sqrt (1 - h * h) := by
    rw [show (2 : ℝ) - 2 * ipVal h 5 = 2 ^ 2 * (1 - h * h) by simp only [ipVal]; ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have e6 : (2 : ℝ) - 2 * ipVal h 6
      = 2 * (1 - h * h) * (1 - Real.sqrt 3 * 2⁻¹) + 4 * (h * h) := by
    simp only [ipVal]
    ring
  have e7 : (2 : ℝ) - 2 * ipVal h 7 = 2 * (1 - h * h) * 1 + 4 * (h * h) := by
    simp only [ipVal]
    ring
  have e8 : (2 : ℝ) - 2 * ipVal h 8
      = 2 * (1 - h * h) * (1 + Real.sqrt 3 * 2⁻¹) + 4 * (h * h) := by
    simp only [ipVal]
    ring
  rw [e0, e1, e2', e3, e4, e5, e6, e7, e8]
  unfold Efam
  have hs3 : Real.sqrt 3 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt this
  have hr' : Real.sqrt (1 - h * h) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (1 - h * h) := Real.sqrt_pos.mpr (by nlinarith)
    exact ne_of_gt this
  field_simp
  ring

end N14
