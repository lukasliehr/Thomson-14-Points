module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import CAP.UniPos.Packed
public import CAP.Subdivision.BernArray

/-!
# E11, arrays in three coordinates: weights, columns, the binomial array

* `W3 m ω`: the weight of the entry `e` is the product of the weights `ω a` of its three digits.
  `Phi m ω f` is the weighted sum of the array `f`.
* `Phi_act`: a table that acts on the digit of the coordinate `a` acts on the weights of this
  coordinate (`dualW`).
* The columns of the tables of the checker are the polynomials
  `(a + b * X) ^ k * (a' + b' * X) ^ (n - k)` (`col2`). For the weights `u ^ (n - j) * v ^ j` (`hw`)
  the table acts by the substitution `(u, v) ↦ (a' * u + b' * v, a * u + b * v)` (`dualW_col2`).
* `cJ`: the array of the products of three binomial coefficients; `Phi_cJ` is its weighted sum.
-/

@[expose] public section

namespace CAP.Bernstein

open Finset Polynomial

/-! ## Coordinates -/

/-- The distance of the digits of the coordinate `a` (`0`, `1`; otherwise the third one), in slots. -/
def stride (m a : ℕ) : ℕ := if a = 0 then 1 else if a = 1 then m else m * m

/-- The number of repetitions of the digits of the coordinate `a`. -/
def reps (m a : ℕ) : ℕ := if a = 0 then m * m else if a = 1 then m else 1

theorem stride_mul (m a : ℕ) : stride m a * (m * reps m a) = m * m * m := by
  unfold stride reps
  split_ifs <;> ring

theorem stride_pos (m a : ℕ) (hm : 0 < m) : 0 < stride m a := by
  unfold stride
  split_ifs
  · exact Nat.one_pos
  · exact hm
  · exact Nat.mul_pos hm hm

/-- The weights `ω` with those of the coordinate `a` replaced by `ω'`. -/
def upd {R : Type*} (ω : ℕ → ℕ → R) (a : ℕ) (ω' : ℕ → R) : ℕ → ℕ → R := fun b => if b = a then ω' else ω b

theorem upd_self {R : Type*} (ω : ℕ → ℕ → R) (a : ℕ) (ω' : ℕ → R) : upd ω a ω' a = ω' := if_pos rfl

theorem upd_ne {R : Type*} (ω : ℕ → ℕ → R) (a b : ℕ) (ω' : ℕ → R) (h : b ≠ a) : upd ω a ω' b = ω b :=
  if_neg h

theorem upd_eq_self {R : Type*} (ω : ℕ → ℕ → R) (a : ℕ) : upd ω a (ω a) = ω := by
  funext b
  by_cases h : b = a
  · rw [h, upd_self]
  · rw [upd_ne _ _ _ _ h]

/-- The weight of the entry `e`: the product of the weights of its digits. -/
def W3 {R : Type*} [CommSemiring R] (m : ℕ) (ω : ℕ → ℕ → R) (e : ℕ) : R :=
  ω 0 (e % m) * ω 1 (e / m % m) * ω 2 (e / (m * m))

theorem W3_upd0 {R : Type*} [CommSemiring R] (m : ℕ) (ω : ℕ → ℕ → R) (ω' : ℕ → R) (e : ℕ) :
    W3 m (upd ω 0 ω') e = ω' (e % m) * ω 1 (e / m % m) * ω 2 (e / (m * m)) := by
  unfold W3
  rw [upd_self, upd_ne _ _ _ _ (by decide : (1 : ℕ) ≠ 0), upd_ne _ _ _ _ (by decide : (2 : ℕ) ≠ 0)]

theorem W3_upd1 {R : Type*} [CommSemiring R] (m : ℕ) (ω : ℕ → ℕ → R) (ω' : ℕ → R) (e : ℕ) :
    W3 m (upd ω 1 ω') e = ω 0 (e % m) * ω' (e / m % m) * ω 2 (e / (m * m)) := by
  unfold W3
  rw [upd_self, upd_ne _ _ _ _ (by decide : (0 : ℕ) ≠ 1), upd_ne _ _ _ _ (by decide : (2 : ℕ) ≠ 1)]

theorem W3_upd2 {R : Type*} [CommSemiring R] (m : ℕ) (ω : ℕ → ℕ → R) (ω' : ℕ → R) (e : ℕ) :
    W3 m (upd ω 2 ω') e = ω 0 (e % m) * ω 1 (e / m % m) * ω' (e / (m * m)) := by
  unfold W3
  rw [upd_self, upd_ne _ _ _ _ (by decide : (0 : ℕ) ≠ 2), upd_ne _ _ _ _ (by decide : (1 : ℕ) ≠ 2)]

/-- In the coordinate `a` the weight of an entry is a product of a factor that does not depend on
the digit of this coordinate and the weight of this digit. -/
theorem W3_factor {R : Type*} [CommSemiring R] (m a : ℕ) (ha : a ≤ 2) (ω : ℕ → ℕ → R) :
    ∃ ν : ℕ → ℕ → R, ∀ (ω' : ℕ → R) (lo k hi : ℕ), lo < stride m a → k < m → hi < reps m a →
      W3 m (upd ω a ω') (lo + stride m a * (k + m * hi)) = ν lo hi * ω' k := by
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  · refine ⟨fun _ hi => ω 1 (hi % m) * ω 2 (hi / m), fun ω' lo k hi hlo hk _ => ?_⟩
    have hm : 0 < m := Nat.zero_lt_of_lt hk
    have hs : stride m 0 = 1 := if_pos rfl
    rw [hs] at hlo ⊢
    have hlo0 : lo = 0 := by omega
    subst hlo0
    rw [W3_upd0, zero_add, one_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hk, zero_add]
    ring
  · refine ⟨fun lo hi => ω 0 lo * ω 2 hi, fun ω' lo k hi hlo hk _ => ?_⟩
    have hm : 0 < m := Nat.zero_lt_of_lt hk
    have hs : stride m 1 = m := by unfold stride; rw [if_neg (by decide), if_pos rfl]
    rw [hs] at hlo ⊢
    rw [W3_upd1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hlo, zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hk, zero_add]
    ring
  · refine ⟨fun lo _ => ω 0 (lo % m) * ω 1 (lo / m % m), fun ω' lo k hi hlo hk hhi => ?_⟩
    have hm : 0 < m := Nat.zero_lt_of_lt hk
    have hs : stride m 2 = m * m := by unfold stride; rw [if_neg (by decide), if_neg (by decide)]
    have hr : reps m 2 = 1 := by unfold reps; rw [if_neg (by decide), if_neg (by decide)]
    rw [hs] at hlo ⊢
    rw [hr] at hhi
    have hhi0 : hi = 0 := by omega
    subst hhi0
    have e1 : lo + m * m * (k + m * 0) = lo + m * (m * k) := by ring
    have e2 : lo + m * m * (k + m * 0) = lo + m * m * k := by ring
    rw [W3_upd2]
    rw [show (lo + m * m * (k + m * 0)) % m = lo % m by rw [e1, Nat.add_mul_mod_self_left]]
    rw [show (lo + m * m * (k + m * 0)) / m % m = lo / m % m by
      rw [e1, Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left]]
    rw [show (lo + m * m * (k + m * 0)) / (m * m) = k by
      rw [e2, Nat.add_mul_div_left _ _ (Nat.mul_pos hm hm), Nat.div_eq_of_lt hlo, zero_add]]

/-- Every index of an array is `lo + s * (k + m * hi)` for the coordinate `a`. -/
theorem decomp (m a e : ℕ) (hm : 0 < m) (he : e < m * m * m) :
    ∃ lo k hi, lo < stride m a ∧ k < m ∧ hi < reps m a ∧ e = lo + stride m a * (k + m * hi) := by
  have hs := stride_pos m a hm
  refine ⟨e % stride m a, e / stride m a % m, e / stride m a / m, Nat.mod_lt _ hs, Nat.mod_lt _ hm, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hm, Nat.div_lt_iff_lt_mul hs]
    calc e < m * m * m := he
      _ = reps m a * m * stride m a := by rw [← stride_mul m a]; ring
  · rw [Nat.mod_add_div, Nat.mod_add_div]

/-! ## Weighted sums -/

/-- The weighted sum of an array. -/
def Phi (m : ℕ) (ω : ℕ → ℕ → ℝ) (f : ℕ → ℕ) : ℝ := ∑ e ∈ range (m * m * m), (f e : ℝ) * W3 m ω e

/-- The action of a table on the weights of one coordinate. -/
def dualW (m : ℕ) (τ : ℕ → ℕ → ℕ) (ω : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range m, (τ k j : ℝ) * ω j

/-- A table that acts on the digit of the coordinate `a` acts on the weights of this coordinate. -/
theorem Phi_act (m a : ℕ) (ha : a ≤ 2) (τ : ℕ → ℕ → ℕ) (ω : ℕ → ℕ → ℝ) (f : ℕ → ℕ) :
    Phi m ω (act (stride m a) m τ f) = Phi m (upd ω a (dualW m τ (ω a))) f := by
  obtain ⟨ν, hν⟩ := W3_factor m a ha ω
  unfold Phi
  rw [← stride_mul m a]
  refine act_adjoint (stride m a) m (reps m a) τ f _ _ ν (ω a) (fun lo k hi h1 h2 h3 => ?_)
    (fun lo k hi h1 h2 h3 => hν _ lo k hi h1 h2 h3)
  have h := hν (ω a) lo k hi h1 h2 h3
  rwa [upd_eq_self] at h

theorem Phi_add (m : ℕ) (ω : ℕ → ℕ → ℝ) (f g : ℕ → ℕ) :
    Phi m ω (fun e => f e + g e) = Phi m ω f + Phi m ω g := by
  unfold Phi
  rw [← sum_add_distrib]
  exact sum_congr rfl fun e _ => by push_cast; ring

theorem Phi_smul (m : ℕ) (ω : ℕ → ℕ → ℝ) (c : ℕ) (f : ℕ → ℕ) :
    Phi m ω (fun e => c * f e) = c * Phi m ω f := by
  unfold Phi
  rw [mul_sum]
  exact sum_congr rfl fun e _ => by push_cast; ring

theorem Phi_congr (m : ℕ) (ω : ℕ → ℕ → ℝ) {f g : ℕ → ℕ} (h : ∀ e, e < m * m * m → f e = g e) :
    Phi m ω f = Phi m ω g :=
  sum_congr rfl fun e he => by rw [h e (mem_range.mp he)]

theorem Phi_mono (m : ℕ) (ω : ℕ → ℕ → ℝ) (hω : ∀ e, 0 ≤ W3 m ω e) {f g : ℕ → ℕ}
    (h : ∀ e, e < m * m * m → f e ≤ g e) : Phi m ω f ≤ Phi m ω g :=
  sum_le_sum fun e he => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h e (mem_range.mp he))) (hω e)

theorem Phi_sub (m : ℕ) (ω : ℕ → ℕ → ℝ) {f g : ℕ → ℕ} (h : ∀ e, e < m * m * m → g e ≤ f e) :
    Phi m ω (fun e => f e - g e) = Phi m ω f - Phi m ω g := by
  unfold Phi
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e he => ?_
  rw [Nat.cast_sub (h e (mem_range.mp he))]
  ring

theorem Phi_upd_sub (m a : ℕ) (ha : a ≤ 2) (ω : ℕ → ℕ → ℝ) (α β : ℕ → ℝ) (f : ℕ → ℕ) :
    Phi m (upd ω a (fun k => α k - β k)) f = Phi m (upd ω a α) f - Phi m (upd ω a β) f := by
  unfold Phi
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  · rw [W3_upd0, W3_upd0, W3_upd0]; ring
  · rw [W3_upd1, W3_upd1, W3_upd1]; ring
  · rw [W3_upd2, W3_upd2, W3_upd2]; ring

/-! ## The action of a table on an array that is a product -/

/-- The action of a table on the entries of one coordinate of a product. -/
def fwd (m : ℕ) (τ : ℕ → ℕ → ℕ) (ω : ℕ → ℕ) (j : ℕ) : ℕ := ∑ k ∈ range m, ω k * τ k j

theorem act_W3 (m a : ℕ) (ha : a ≤ 2) (hm : 0 < m) (τ : ℕ → ℕ → ℕ) (ω : ℕ → ℕ → ℕ) (e : ℕ)
    (he : e < m * m * m) :
    act (stride m a) m τ (W3 m ω) e = W3 m (upd ω a (fwd m τ (ω a))) e := by
  obtain ⟨ν, hν⟩ := W3_factor m a ha ω
  obtain ⟨lo, j, hi, hlo, hj, hhi, rfl⟩ := decomp m a e hm he
  rw [act_at' _ _ _ _ lo j hi hlo hj, hν _ lo j hi hlo hj hhi]
  unfold fwd
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have h := hν (ω a) lo k hi hlo (mem_range.mp hk) hhi
  rw [upd_eq_self] at h
  rw [h]
  ring

/-! ## Homogeneous weights and the columns of the tables -/

/-- The weight `u ^ (n - j) * v ^ j` of the digit `j`. -/
def hw (n : ℕ) (u v : ℝ) (j : ℕ) : ℝ := u ^ (n - j) * v ^ j

/-- The homogeneous value of a polynomial of degree at most `d`. -/
def homE (d : ℕ) (F : ℕ[X]) (u v : ℝ) : ℝ := ∑ j ∈ range (d + 1), (F.coeff j : ℝ) * (u ^ (d - j) * v ^ j)

/-- The table whose columns are the coefficients of polynomials. -/
def tab (col : ℕ → ℕ[X]) (k j : ℕ) : ℕ := (col k).coeff j

theorem dualW_tab (n : ℕ) (col : ℕ → ℕ[X]) (u v : ℝ) (k : ℕ) :
    dualW (n + 1) (tab col) (hw n u v) k = homE n (col k) u v := rfl

/-- The linear form `a + b * X`. -/
noncomputable def linP (a b : ℕ) : ℕ[X] := C a + C b * X

theorem natDegree_linP (a b : ℕ) : (linP a b).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_C]; exact Nat.zero_le 1
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le

theorem homE_add (d : ℕ) (F G : ℕ[X]) (u v : ℝ) : homE d (F + G) u v = homE d F u v + homE d G u v := by
  unfold homE
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by rw [coeff_add]; push_cast; ring

theorem homE_one (u v : ℝ) : homE 0 1 u v = 1 := by
  unfold homE
  simp

/-- The homogeneous value of a product with a linear form. -/
theorem homE_mul_lin (d : ℕ) (F : ℕ[X]) (hF : F.natDegree ≤ d) (a b : ℕ) (u v : ℝ) :
    homE (d + 1) (F * linP a b) u v = homE d F u v * (a * u + b * v) := by
  have hc : ∀ j, (F * linP a b).coeff (j + 1) = F.coeff (j + 1) * a + F.coeff j * b := by
    intro j
    unfold linP
    rw [mul_add, coeff_add, coeff_mul_C, ← mul_assoc, coeff_mul_X, coeff_mul_C]
  have hc0 : (F * linP a b).coeff 0 = F.coeff 0 * a := by
    unfold linP
    rw [mul_add, coeff_add, coeff_mul_C, ← mul_assoc, coeff_mul_X_zero, add_zero]
  have hd : F.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hF)
  unfold homE
  rw [sum_range_succ' _ (d + 1), hc0]
  have e1 : ∑ j ∈ range (d + 1), ((F * linP a b).coeff (j + 1) : ℝ) * (u ^ (d + 1 - (j + 1)) * v ^ (j + 1))
      = ∑ j ∈ range (d + 1), (F.coeff (j + 1) : ℝ) * a * (u ^ (d - j) * v ^ (j + 1))
        + ∑ j ∈ range (d + 1), (F.coeff j : ℝ) * b * (u ^ (d - j) * v ^ (j + 1)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [hc, Nat.add_sub_add_right]
    push_cast
    ring
  have e2 : ∑ j ∈ range (d + 1), (F.coeff (j + 1) : ℝ) * a * (u ^ (d - j) * v ^ (j + 1))
      = ∑ j ∈ range d, (F.coeff (j + 1) : ℝ) * a * (u ^ (d - j) * v ^ (j + 1)) := by
    rw [sum_range_succ, hd]
    simp
  have e3 : (∑ j ∈ range (d + 1), (F.coeff j : ℝ) * (u ^ (d - j) * v ^ j)) * (a * u)
      = ∑ j ∈ range d, (F.coeff (j + 1) : ℝ) * a * (u ^ (d - j) * v ^ (j + 1))
        + (F.coeff 0 : ℝ) * a * (u ^ (d + 1) * v ^ 0) := by
    rw [sum_range_succ' _ d, add_mul, sum_mul]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have hj' : j < d := mem_range.mp hj
      have e : d - j = d - (j + 1) + 1 := by omega
      rw [e, pow_succ]
      ring
    · rw [Nat.sub_zero, pow_succ]
      ring
  rw [e1, e2, mul_add, e3, sum_mul]
  push_cast
  have e4 : ∑ j ∈ range (d + 1), (F.coeff j : ℝ) * b * (u ^ (d - j) * v ^ (j + 1))
      = ∑ j ∈ range (d + 1), (F.coeff j : ℝ) * (u ^ (d - j) * v ^ j) * (b * v) :=
    sum_congr rfl fun j _ => by rw [pow_succ]; ring
  rw [e4]
  ring

/-- The homogeneous value of a product with a power of a linear form. -/
theorem homE_mul_pow (k : ℕ) (F : ℕ[X]) (hF : F.natDegree ≤ k) (a b : ℕ) (u v : ℝ) : ∀ l : ℕ,
    (F * linP a b ^ l).natDegree ≤ k + l ∧ homE (k + l) (F * linP a b ^ l) u v = homE k F u v * (a * u + b * v) ^ l
  | 0 => by
    rw [pow_zero, mul_one, pow_zero, mul_one]
    exact ⟨hF, rfl⟩
  | l + 1 => by
    obtain ⟨h1, h2⟩ := homE_mul_pow k F hF a b u v l
    have e : F * linP a b ^ (l + 1) = F * linP a b ^ l * linP a b := by rw [pow_succ, mul_assoc]
    rw [e, ← Nat.add_assoc]
    refine ⟨natDegree_mul_le.trans (Nat.add_le_add h1 (natDegree_linP a b)), ?_⟩
    rw [homE_mul_lin (k + l) _ h1, h2, pow_succ]
    ring

/-- The column `k` of a table: `(a + b * X) ^ k * (a' + b' * X) ^ (n - k)`. -/
noncomputable def col2 (a b a' b' n k : ℕ) : ℕ[X] := linP a b ^ k * linP a' b' ^ (n - k)

theorem natDegree_pow_linP (a b k : ℕ) (u v : ℝ) :
    (linP a b ^ k).natDegree ≤ k ∧ homE k (linP a b ^ k) u v = (a * u + b * v) ^ k := by
  have h := homE_mul_pow 0 1 (by simp) a b u v k
  rw [one_mul, zero_add, homE_one, one_mul] at h
  exact h

theorem col2_spec (a b a' b' n k : ℕ) (hk : k ≤ n) (u v : ℝ) :
    (col2 a b a' b' n k).natDegree ≤ n ∧
      homE n (col2 a b a' b' n k) u v = (a * u + b * v) ^ k * (a' * u + b' * v) ^ (n - k) := by
  obtain ⟨h1, h2⟩ := natDegree_pow_linP a b k u v
  have h := homE_mul_pow k (linP a b ^ k) h1 a' b' u v (n - k)
  rw [Nat.add_sub_of_le hk, h2] at h
  exact h

theorem col2_eval (a b a' b' n k y : ℕ) :
    (col2 a b a' b' n k).eval y = (a + b * y) ^ k * (a' + b' * y) ^ (n - k) := by
  unfold col2 linP
  simp only [eval_mul, eval_pow, eval_add, eval_C, eval_X]

/-- The action of the table of `col2` on homogeneous weights is a substitution. -/
theorem dualW_col2 (a b a' b' n k : ℕ) (hk : k ≤ n) (u v : ℝ) :
    dualW (n + 1) (tab (col2 a b a' b' n)) (hw n u v) k = hw n (a' * u + b' * v) (a * u + b * v) k := by
  rw [dualW_tab, (col2_spec a b a' b' n k hk u v).2]
  unfold hw
  ring

/-! ## The binomial array -/

/-- The array of the products of three binomial coefficients. -/
def cJ (n : ℕ) : ℕ → ℕ := W3 (n + 1) (fun _ => n.choose)

theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · rw [← Nat.sum_range_choose n]
    exact single_le_sum (f := fun m => n.choose m) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt (not_le.mp hk)]
    exact Nat.zero_le _

theorem cJ_le (n e : ℕ) : cJ n e ≤ 2 ^ (3 * n) := by
  unfold cJ W3
  calc n.choose (e % (n + 1)) * n.choose (e / (n + 1) % (n + 1)) * n.choose (e / ((n + 1) * (n + 1)))
      ≤ 2 ^ n * 2 ^ n * 2 ^ n :=
        Nat.mul_le_mul (Nat.mul_le_mul (choose_le_two_pow _ _) (choose_le_two_pow _ _)) (choose_le_two_pow _ _)
    _ = 2 ^ (3 * n) := by ring

/-- `(1 + c * 2 ^ W) ^ n` is the packed number of the binomial coefficients times powers of `c`. -/
theorem one_add_pow_packSum (W n : ℕ) :
    (1 + 2 ^ W) ^ n = packSum W (n + 1) n.choose := by
  rw [add_comm, add_pow]
  unfold packSum
  refine sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, ← pow_mul, Nat.cast_id, mul_comm]

/-- The number of the binomial array. -/
theorem binom_packSum (V n : ℕ) :
    (1 + 2 ^ V) ^ n * (1 + 2 ^ (V * (n + 1))) ^ n * (1 + 2 ^ (V * (n + 1) * (n + 1))) ^ n
      = packSum V ((n + 1) * (n + 1) * (n + 1)) (cJ n) := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  rw [one_add_pow_packSum, one_add_pow_packSum, one_add_pow_packSum]
  -- the first two coordinates
  have h12 : packSum V (n + 1) n.choose * packSum (V * (n + 1)) (n + 1) n.choose
      = packSum V ((n + 1) * (n + 1)) (fun e => n.choose (e % (n + 1)) * n.choose (e / (n + 1))) := by
    rw [← packSum_flat V (n + 1) (n + 1), ← packSum_mul]
    refine packSum_congr _ _ fun i _ => ?_
    rw [← packSum_mul_right]
    refine packSum_congr _ _ fun lo hlo => ?_
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hlo,
      zero_add]
  rw [h12, mul_assoc V, ← packSum_flat V ((n + 1) * (n + 1)) (n + 1), ← packSum_mul]
  refine packSum_congr _ _ fun i _ => ?_
  rw [← packSum_mul_right]
  refine packSum_congr _ _ fun lo hlo => ?_
  unfold cJ W3
  have e1 : (lo + (n + 1) * (n + 1) * i) % (n + 1) = lo % (n + 1) := by
    rw [mul_assoc, Nat.add_mul_mod_self_left]
  have e2 : (lo + (n + 1) * (n + 1) * i) / (n + 1) % (n + 1) = lo / (n + 1) % (n + 1) := by
    rw [mul_assoc, Nat.add_mul_div_left _ _ hm, Nat.add_mul_mod_self_left]
  have e3 : (lo + (n + 1) * (n + 1) * i) / ((n + 1) * (n + 1)) = i := by
    rw [Nat.add_mul_div_left _ _ (Nat.mul_pos hm hm), Nat.div_eq_of_lt hlo, zero_add]
  have e4 : lo / (n + 1) % (n + 1) = lo / (n + 1) :=
    Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hm).mpr hlo)
  rw [e1, e2, e3, e4]

/-- The weights of homogeneous coordinates. -/
def hwω (n : ℕ) (u v : ℕ → ℝ) : ℕ → ℕ → ℝ := fun a => hw n (u a) (v a)

theorem W3_hw_nonneg (n : ℕ) (u v : ℕ → ℝ) (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) (e : ℕ) :
    0 ≤ W3 (n + 1) (hwω n u v) e := by
  unfold W3 hwω hw
  have h : ∀ a j, 0 ≤ u a ^ (n - j) * v a ^ j := fun a j =>
    mul_nonneg (pow_nonneg (hu a) _) (pow_nonneg (hv a) _)
  exact mul_nonneg (mul_nonneg (h 0 _) (h 1 _)) (h 2 _)

/-- The sum over an array as a sum over the three digits. -/
theorem sum_cube {R : Type*} [AddCommMonoid R] (m : ℕ) (g : ℕ → R) :
    ∑ e ∈ range (m * m * m), g e
      = ∑ e3 ∈ range m, ∑ e2 ∈ range m, ∑ e1 ∈ range m, g (e1 + m * (e2 + m * e3)) := by
  rw [show m * m * m = m * (m * m) by ring, sum_range_mul' m (m * m), sum_range_mul' m m]

theorem W3_at {R : Type*} [CommSemiring R] (m : ℕ) (ω : ℕ → ℕ → R) (e1 e2 e3 : ℕ) (h1 : e1 < m) (h2 : e2 < m) :
    W3 m ω (e1 + m * (e2 + m * e3)) = ω 0 e1 * ω 1 e2 * ω 2 e3 := by
  have hm : 0 < m := Nat.zero_lt_of_lt h1
  unfold W3
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hm,
    Nat.div_eq_of_lt h1, zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2, Nat.add_mul_div_left _ _ hm,
    Nat.div_eq_of_lt h2, zero_add]

/-- The weighted sum as a sum over the three digits. -/
theorem Phi_cube (m : ℕ) (ω : ℕ → ℕ → ℝ) (f : ℕ → ℕ) :
    Phi m ω f = ∑ e3 ∈ range m, ∑ e2 ∈ range m, ∑ e1 ∈ range m,
      (f (e1 + m * (e2 + m * e3)) : ℝ) * (ω 0 e1 * ω 1 e2 * ω 2 e3) := by
  unfold Phi
  rw [sum_cube]
  refine sum_congr rfl fun e3 _ => sum_congr rfl fun e2 h2 => sum_congr rfl fun e1 h1 => ?_
  rw [W3_at m ω e1 e2 e3 (mem_range.mp h1) (mem_range.mp h2)]

theorem prod3_sum (m : ℕ) (a b c : ℕ → ℝ) :
    (∑ i ∈ range m, a i) * (∑ j ∈ range m, b j) * (∑ k ∈ range m, c k)
      = ∑ k ∈ range m, ∑ j ∈ range m, ∑ i ∈ range m, a i * b j * c k := by
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_mul, sum_mul]

theorem sum_choose_hw (n : ℕ) (u v : ℝ) : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * hw n u v j = (u + v) ^ n := by
  rw [add_comm u v, add_pow]
  exact sum_congr rfl fun j _ => by unfold hw; ring

/-- The weighted sum of the binomial array. -/
theorem Phi_cJ (n : ℕ) (u v : ℕ → ℝ) :
    Phi (n + 1) (hwω n u v) (cJ n) = (u 0 + v 0) ^ n * (u 1 + v 1) ^ n * (u 2 + v 2) ^ n := by
  rw [Phi_cube, ← sum_choose_hw n (u 0) (v 0), ← sum_choose_hw n (u 1) (v 1), ← sum_choose_hw n (u 2) (v 2),
    prod3_sum]
  refine sum_congr rfl fun e3 _ => sum_congr rfl fun e2 h2 => sum_congr rfl fun e1 h1 => ?_
  unfold cJ
  rw [W3_at _ _ e1 e2 e3 (mem_range.mp h1) (mem_range.mp h2)]
  unfold hwω
  push_cast
  ring

end CAP.Bernstein
