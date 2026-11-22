module

public import N14.Jet.Sem
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

/-!
# Jets: a function with a polynomial of degree five and a bound of order six

`Rep r F c κ`: the sequence `c` vanishes outside the valid slots, and `|F x - pev c x| ≤ κ m⁶` for all `x` and
`m` with `|x_k| ≤ m ≤ r`. The rules:

* `Rep.const`, `Rep.var`, `Rep.trig`: a constant, a variable plus a constant, `a cos x_k - b sin x_k`;
* `Rep.add`, `Rep.neg`, `Rep.smul`: sums and multiples;
* `Rep.mul`: the product, with the convolution of the sequences and the bound
  `H + PB₁ κ₂ + κ₁ (PB₂ + κ₂ ρ⁶)`, where `PB_i = ∑ n_i(d) ρ^d` bounds the polynomial `i` on the box and
  `H = ∑_{d₁ + d₂ ≥ 6} n₁(d₁) n₂(d₂) ρ^(d₁ + d₂ - 6)` the terms of degree at least 6 of the product; `n_i(d)` are
  bounds for the sums of the absolute values of the coefficients of degree `d`, and `ρ ≥ r`;
* `Rep.perturb`: a function that differs from `F` by at most `ε m⁶`.
-/

@[expose] public section

namespace N14.Jet

open Finset

/-- A function with its polynomial of degree 5 and its bound of order six on the box of radius `r`. -/
structure Rep (r : ℝ) (F : (Fin 4 → ℝ) → ℝ) (c : ℕ → ℝ) (κ : ℝ) : Prop where
  supp : Supp c
  bound : ∀ x m, (∀ k, |x k| ≤ m) → m ≤ r → |F x - pev c x| ≤ κ * m ^ 6

theorem pev_abs_le (c : ℕ → ℝ) (hc : Supp c) (x : Fin 4 → ℝ) (m : ℝ) (hx : ∀ k, |x k| ≤ m) :
    |pev c x| ≤ ∑ d ∈ range 6, nrm c d * m ^ d := by
  rw [pev_eq_blk]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_le_sum fun d _ => blk_abs_le c hc d x m hx)

/-- The polynomial on the box, from bounds `n d` for the sums of the absolute values of its coefficients. -/
theorem pev_abs_le' (c : ℕ → ℝ) (hc : Supp c) (n : ℕ → ℝ) (hn : ∀ d, d < 6 → nrm c d ≤ n d)
    (x : Fin 4 → ℝ) (m ρ : ℝ) (hx : ∀ k, |x k| ≤ m) (hm : m ≤ ρ) :
    |pev c x| ≤ ∑ d ∈ range 6, n d * ρ ^ d := by
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  refine le_trans (pev_abs_le c hc x m hx) (sum_le_sum fun d hd => ?_)
  have h1 := hn d (mem_range.mp hd)
  exact mul_le_mul h1 (pow_le_pow_left₀ hm0 hm d) (pow_nonneg hm0 d) (le_trans (nrm_nonneg c d) h1)

theorem pev_add (c c' : ℕ → ℝ) (x : Fin 4 → ℝ) : pev (fun e => c e + c' e) x = pev c x + pev c' x := by
  unfold pev
  rw [← Finset.sum_add_distrib]
  exact sum_congr rfl fun e _ => by ring

theorem pev_smul (a : ℝ) (c : ℕ → ℝ) (x : Fin 4 → ℝ) : pev (fun e => a * c e) x = a * pev c x := by
  unfold pev
  rw [Finset.mul_sum]
  exact sum_congr rfl fun e _ => by ring

/-- The polynomial with one coefficient. -/
theorem pev_single (e0 : ℕ) (he0 : e0 < 1296) (a : ℝ) (x : Fin 4 → ℝ) :
    pev (fun e => if e = e0 then a else 0) x = a * mval e0 x := by
  unfold pev
  rw [Finset.sum_eq_single e0]
  · show (if e0 = e0 then a else 0) * mval e0 x = a * mval e0 x
    rw [if_pos rfl]
  · intro e _ hne
    show (if e = e0 then a else 0) * mval e x = 0
    rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (mem_range.mpr he0) h

namespace Rep

variable {r : ℝ} {F F1 F2 : (Fin 4 → ℝ) → ℝ} {c c1 c2 : ℕ → ℝ} {κ κ1 κ2 : ℝ}

theorem const (r a : ℝ) : Rep r (fun _ => a) (fun e => if e = 0 then a else 0) 0 := by
  refine ⟨fun e he => ?_, fun x m _ _ => ?_⟩
  · have h0 : e ≠ 0 := fun h => he (h ▸ valid_zero)
    rw [if_neg h0]
  · rw [pev_single 0 (by norm_num) a x, mval_zero]
    simp

theorem add (h1 : Rep r F1 c1 κ1) (h2 : Rep r F2 c2 κ2) :
    Rep r (fun x => F1 x + F2 x) (fun e => c1 e + c2 e) (κ1 + κ2) := by
  refine ⟨fun e he => ?_, fun x m hx hm => ?_⟩
  · rw [h1.supp e he, h2.supp e he, add_zero]
  · rw [pev_add]
    have a1 := h1.bound x m hx hm
    have a2 := h2.bound x m hx hm
    have e : F1 x + F2 x - (pev c1 x + pev c2 x) = (F1 x - pev c1 x) + (F2 x - pev c2 x) := by ring
    rw [e]
    calc |F1 x - pev c1 x + (F2 x - pev c2 x)| ≤ |F1 x - pev c1 x| + |F2 x - pev c2 x| := abs_add_le _ _
      _ ≤ κ1 * m ^ 6 + κ2 * m ^ 6 := add_le_add a1 a2
      _ = (κ1 + κ2) * m ^ 6 := by ring

theorem smul (a : ℝ) (h : Rep r F c κ) : Rep r (fun x => a * F x) (fun e => a * c e) (|a| * κ) := by
  refine ⟨fun e he => ?_, fun x m hx hm => ?_⟩
  · rw [h.supp e he, mul_zero]
  · rw [pev_smul, ← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.bound x m hx hm) (abs_nonneg a)

theorem neg (h : Rep r F c κ) : Rep r (fun x => -F x) (fun e => -c e) κ := by
  have h1 := smul (-1) h
  simp only [neg_mul, one_mul, abs_neg, abs_one] at h1
  exact h1

/-- A function that differs from `F` by at most `ε m⁶`. -/
theorem perturb (h : Rep r F c κ) (G : (Fin 4 → ℝ) → ℝ) (ε : ℝ)
    (hG : ∀ x m, (∀ k, |x k| ≤ m) → m ≤ r → |G x - F x| ≤ ε * m ^ 6) : Rep r G c (κ + ε) := by
  refine ⟨h.supp, fun x m hx hm => ?_⟩
  have a1 := h.bound x m hx hm
  have a2 := hG x m hx hm
  have e : G x - pev c x = (G x - F x) + (F x - pev c x) := by ring
  rw [e]
  calc |G x - F x + (F x - pev c x)| ≤ |G x - F x| + |F x - pev c x| := abs_add_le _ _
    _ ≤ ε * m ^ 6 + κ * m ^ 6 := add_le_add a2 a1
    _ = (κ + ε) * m ^ 6 := by ring

/-- A larger bound. -/
theorem mono (h : Rep r F c κ) (κ' : ℝ) (hκ : κ ≤ κ') : Rep r F c κ' := by
  refine ⟨h.supp, fun x m hx hm => ?_⟩
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  exact le_trans (h.bound x m hx hm) (mul_le_mul_of_nonneg_right hκ (pow_nonneg hm0 6))

/-- The same function, written differently. -/
theorem congr (h : Rep r F c κ) (G : (Fin 4 → ℝ) → ℝ) (hG : ∀ x, G x = F x) : Rep r G c κ :=
  ⟨h.supp, fun x m hx hm => by rw [hG]; exact h.bound x m hx hm⟩

/-- The bound of a function on the box. -/
theorem abs_le (h : Rep r F c κ) (n : ℕ → ℝ) (hn : ∀ d, d < 6 → nrm c d ≤ n d) (ρ : ℝ) (hr : r ≤ ρ)
    (hκ : 0 ≤ κ) (x : Fin 4 → ℝ) (m : ℝ) (hx : ∀ k, |x k| ≤ m) (hm : m ≤ r) :
    |F x| ≤ (∑ d ∈ range 6, n d * ρ ^ d) + κ * ρ ^ 6 := by
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  have a1 := h.bound x m hx hm
  have a2 := pev_abs_le' c h.supp n hn x m ρ hx (le_trans hm hr)
  have a3 : κ * m ^ 6 ≤ κ * ρ ^ 6 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 (le_trans hm hr) 6) hκ
  have e : F x = (F x - pev c x) + pev c x := by ring
  rw [e]
  calc |F x - pev c x + pev c x| ≤ |F x - pev c x| + |pev c x| := abs_add_le _ _
    _ ≤ κ * m ^ 6 + ∑ d ∈ range 6, n d * ρ ^ d := add_le_add a1 a2
    _ ≤ (∑ d ∈ range 6, n d * ρ ^ d) + κ * ρ ^ 6 := by linarith

/-- **The product.** -/
theorem mul (h1 : Rep r F1 c1 κ1) (h2 : Rep r F2 c2 κ2) (n1 n2 : ℕ → ℝ)
    (hn1 : ∀ d, d < 6 → nrm c1 d ≤ n1 d) (hn2 : ∀ d, d < 6 → nrm c2 d ≤ n2 d) (ρ : ℝ) (hr : r ≤ ρ)
    (hκ1 : 0 ≤ κ1) (hκ2 : 0 ≤ κ2) :
    Rep r (fun x => F1 x * F2 x) (cmul c1 c2)
      ((∑ d1 ∈ range 6, ∑ d2 ∈ range 6, if 6 ≤ d1 + d2 then n1 d1 * n2 d2 * ρ ^ (d1 + d2 - 6) else 0)
        + (∑ d ∈ range 6, n1 d * ρ ^ d) * κ2 + κ1 * ((∑ d ∈ range 6, n2 d * ρ ^ d) + κ2 * ρ ^ 6)) := by
  refine ⟨cmul_supp c1 c2 h1.supp h2.supp, fun x m hx hm => ?_⟩
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  have hmρ : m ≤ ρ := le_trans hm hr
  have hρ0 : 0 ≤ ρ := le_trans hm0 hmρ
  have hm6 : 0 ≤ m ^ 6 := pow_nonneg hm0 6
  have a1 := h1.bound x m hx hm
  have a2 := h2.bound x m hx hm
  have b1 := pev_abs_le' c1 h1.supp n1 hn1 x m ρ hx hmρ
  have bF2 := abs_le h2 n2 hn2 ρ hr hκ2 x m hx hm
  have hn1' : ∀ d, d < 6 → 0 ≤ n1 d := fun d hd => le_trans (nrm_nonneg c1 d) (hn1 d hd)
  have hn2' : ∀ d, d < 6 → 0 ≤ n2 d := fun d hd => le_trans (nrm_nonneg c2 d) (hn2 d hd)
  -- the terms of degree at least 6
  have hH : |pev c1 x * pev c2 x - pev (cmul c1 c2) x|
      ≤ (∑ d1 ∈ range 6, ∑ d2 ∈ range 6, if 6 ≤ d1 + d2 then n1 d1 * n2 d2 * ρ ^ (d1 + d2 - 6) else 0)
        * m ^ 6 := by
    rw [pev_mul c1 c2 h1.supp h2.supp x, Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_le_sum fun d1 hd1 => ?_)
    rw [Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_le_sum fun d2 hd2 => ?_)
    have g1 := hn1 d1 (mem_range.mp hd1)
    have g2 := hn2 d2 (mem_range.mp hd2)
    have q1 := hn1' d1 (mem_range.mp hd1)
    have q2 := hn2' d2 (mem_range.mp hd2)
    by_cases hs : 6 ≤ d1 + d2
    · rw [if_pos hs, if_pos hs, abs_mul]
      have t1 : |blk c1 d1 x| ≤ n1 d1 * m ^ d1 :=
        le_trans (blk_abs_le c1 h1.supp d1 x m hx) (mul_le_mul_of_nonneg_right g1 (pow_nonneg hm0 d1))
      have t2 : |blk c2 d2 x| ≤ n2 d2 * m ^ d2 :=
        le_trans (blk_abs_le c2 h2.supp d2 x m hx) (mul_le_mul_of_nonneg_right g2 (pow_nonneg hm0 d2))
      have t3 : m ^ d1 * m ^ d2 ≤ ρ ^ (d1 + d2 - 6) * m ^ 6 := by
        rw [← pow_add, show d1 + d2 = (d1 + d2 - 6) + 6 by omega, pow_add,
          show d1 + d2 - 6 + 6 - 6 = d1 + d2 - 6 by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hmρ _) hm6
      calc |blk c1 d1 x| * |blk c2 d2 x| ≤ (n1 d1 * m ^ d1) * (n2 d2 * m ^ d2) :=
            mul_le_mul t1 t2 (abs_nonneg _) (mul_nonneg q1 (pow_nonneg hm0 d1))
        _ = n1 d1 * n2 d2 * (m ^ d1 * m ^ d2) := by ring
        _ ≤ n1 d1 * n2 d2 * (ρ ^ (d1 + d2 - 6) * m ^ 6) :=
            mul_le_mul_of_nonneg_left t3 (mul_nonneg q1 q2)
        _ = n1 d1 * n2 d2 * ρ ^ (d1 + d2 - 6) * m ^ 6 := by ring
    · rw [if_neg hs, if_neg hs]
      simp
  have e : F1 x * F2 x - pev (cmul c1 c2) x
      = (F1 x - pev c1 x) * F2 x + pev c1 x * (F2 x - pev c2 x)
        + (pev c1 x * pev c2 x - pev (cmul c1 c2) x) := by ring
  rw [e]
  have s1 : |(F1 x - pev c1 x) * F2 x| ≤ κ1 * m ^ 6 * ((∑ d ∈ range 6, n2 d * ρ ^ d) + κ2 * ρ ^ 6) := by
    rw [abs_mul]
    exact mul_le_mul a1 bF2 (abs_nonneg _) (mul_nonneg hκ1 hm6)
  have s2 : |pev c1 x * (F2 x - pev c2 x)| ≤ (∑ d ∈ range 6, n1 d * ρ ^ d) * (κ2 * m ^ 6) := by
    rw [abs_mul]
    exact mul_le_mul b1 a2 (abs_nonneg _) (le_trans (abs_nonneg _) b1)
  calc |(F1 x - pev c1 x) * F2 x + pev c1 x * (F2 x - pev c2 x)
          + (pev c1 x * pev c2 x - pev (cmul c1 c2) x)|
      ≤ |(F1 x - pev c1 x) * F2 x + pev c1 x * (F2 x - pev c2 x)|
          + |pev c1 x * pev c2 x - pev (cmul c1 c2) x| := abs_add_le _ _
    _ ≤ |(F1 x - pev c1 x) * F2 x| + |pev c1 x * (F2 x - pev c2 x)|
          + |pev c1 x * pev c2 x - pev (cmul c1 c2) x| := by
        have := abs_add_le ((F1 x - pev c1 x) * F2 x) (pev c1 x * (F2 x - pev c2 x))
        linarith
    _ ≤ κ1 * m ^ 6 * ((∑ d ∈ range 6, n2 d * ρ ^ d) + κ2 * ρ ^ 6)
          + (∑ d ∈ range 6, n1 d * ρ ^ d) * (κ2 * m ^ 6)
          + (∑ d1 ∈ range 6, ∑ d2 ∈ range 6, if 6 ≤ d1 + d2 then n1 d1 * n2 d2 * ρ ^ (d1 + d2 - 6) else 0)
            * m ^ 6 := by linarith
    _ = _ := by ring

end Rep

/-! ## Variables and the trigonometric functions of a variable -/

theorem uk_val (k : Fin 4) : uk k.val = 216 + (if k.val = 0 then 0 else if k.val = 1 then 1
    else if k.val = 2 then 6 else 36) := by
  fin_cases k <;> rfl

theorem uk_pos (k : Fin 4) : 0 < uk k.val := by
  fin_cases k <;> decide

theorem valid_pow (k : Fin 4) (j : ℕ) (hj : j < 6) : Valid (j * uk k.val) := by
  fin_cases k <;> interval_cases j <;> decide

theorem mval_pow_aux (x : Fin 4 → ℝ) (j : ℕ) (hj : j < 6) :
    mval (j * 216) x = x 0 ^ j ∧ mval (j * 217) x = x 1 ^ j ∧ mval (j * 222) x = x 2 ^ j
      ∧ mval (j * 252) x = x 3 ^ j := by
  interval_cases j <;> norm_num [mval, sdeg, sa1, sa2, sa3]

theorem mval_pow (k : Fin 4) (j : ℕ) (hj : j < 6) (x : Fin 4 → ℝ) : mval (j * uk k.val) x = x k ^ j := by
  have h := mval_pow_aux x j hj
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- The polynomial of a finite sum of sequences. -/
theorem pev_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (x : Fin 4 → ℝ) :
    pev (fun e => ∑ j ∈ s, f j e) x = ∑ j ∈ s, pev (f j) x := by
  unfold pev
  rw [Finset.sum_comm]
  exact sum_congr rfl fun e _ => by rw [Finset.sum_mul]

/-- The polynomial `∑_{j < 6} t j * x_k ^ j`. -/
theorem pev_powers (k : Fin 4) (t : ℕ → ℝ) (x : Fin 4 → ℝ) :
    pev (fun e => ∑ j ∈ range 6, if e = j * uk k.val then t j else 0) x = ∑ j ∈ range 6, t j * x k ^ j := by
  rw [pev_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [pev_single (j * uk k.val) (valid_pow k j hj').1, mval_pow k j hj']

/-- The coefficient of a slot in the polynomial `∑_{j < 6} t j * x_k ^ j`. -/
theorem powers_coef (k : Fin 4) (t : ℕ → ℝ) (e : ℕ) :
    (∑ j ∈ range 6, if e = j * uk k.val then t j else 0)
      = if e % uk k.val = 0 ∧ e / uk k.val < 6 then t (e / uk k.val) else 0 := by
  have hu := uk_pos k
  by_cases h : e % uk k.val = 0 ∧ e / uk k.val < 6
  · rw [if_pos h]
    have he : e = e / uk k.val * uk k.val := by
      have := Nat.div_add_mod e (uk k.val)
      rw [h.1, add_zero, mul_comm] at this
      exact this.symm
    have hc : ∀ j : ℕ, (e = j * uk k.val) ↔ (e / uk k.val = j) := by
      intro j
      constructor
      · intro hj
        rw [hj, Nat.mul_div_cancel _ hu]
      · intro hj
        rw [← hj]
        exact he
    simp only [hc]
    rw [Finset.sum_ite_eq (range 6) (e / uk k.val), if_pos (mem_range.mpr h.2)]
  · rw [if_neg h]
    refine sum_eq_zero fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [if_neg]
    intro hej
    apply h
    rw [hej, Nat.mul_mod_left, Nat.mul_div_cancel _ hu]
    exact ⟨rfl, hj'⟩

theorem powers_supp (k : Fin 4) (t : ℕ → ℝ) :
    Supp (fun e => ∑ j ∈ range 6, if e = j * uk k.val then t j else 0) := by
  intro e he
  refine sum_eq_zero fun j hj => ?_
  rw [if_neg]
  intro hej
  exact he (hej ▸ valid_pow k j (mem_range.mp hj))

namespace Rep

/-- A variable plus a constant. -/
theorem var (r : ℝ) (k : Fin 4) (a : ℝ) :
    Rep r (fun x => x k + a) (fun e => ∑ j ∈ range 6, if e = j * uk k.val then
      (if j = 0 then a else if j = 1 then 1 else 0) else 0) 0 := by
  refine ⟨powers_supp k _, fun x m _ _ => ?_⟩
  rw [pev_powers]
  simp [Finset.sum_range_succ]
  ring

/-- The coefficients of `a cos t - b sin t` up to degree 5. -/
noncomputable def tcoef (a b : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then a else if j = 1 then -b else if j = 2 then -a / 2 else if j = 3 then b / 6
  else if j = 4 then a / 24 else if j = 5 then -b / 120 else 0

/-- **The trigonometric functions of a variable**: `a cos x_k - b sin x_k`. -/
theorem trig (r ρ : ℝ) (hr : r ≤ ρ) (hρ : ρ ≤ 1) (k : Fin 4) (a b : ℝ) :
    Rep r (fun x => a * Real.cos (x k) - b * Real.sin (x k))
      (fun e => ∑ j ∈ range 6, if e = j * uk k.val then tcoef a b j else 0)
      (|a| * (7 / 4320) + |b| * (ρ / 4410)) := by
  refine ⟨powers_supp k _, fun x m hx hm => ?_⟩
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  have ht : |x k| ≤ m := hx k
  have ht1 : |x k| ≤ 1 := le_trans ht (le_trans hm (le_trans hr hρ))
  have hc := cos_bound6 ht1
  have hs := sin_bound7 ht1
  rw [pev_powers]
  have e : (∑ j ∈ range 6, tcoef a b j * x k ^ j)
      = a * (1 - x k ^ 2 / 2 + x k ^ 4 / 24) - b * (x k - x k ^ 3 / 6 + x k ^ 5 / 120) := by
    simp [Finset.sum_range_succ, tcoef]
    ring
  rw [e]
  have e2 : a * Real.cos (x k) - b * Real.sin (x k)
      - (a * (1 - x k ^ 2 / 2 + x k ^ 4 / 24) - b * (x k - x k ^ 3 / 6 + x k ^ 5 / 120))
      = a * (Real.cos (x k) - (1 - x k ^ 2 / 2 + x k ^ 4 / 24))
        - b * (Real.sin (x k) - (x k - x k ^ 3 / 6 + x k ^ 5 / 120)) := by ring
  rw [e2]
  have p6 : |x k| ^ 6 ≤ m ^ 6 := pow_le_pow_left₀ (abs_nonneg _) ht 6
  have p7 : |x k| ^ 7 ≤ m ^ 6 * ρ := by
    calc |x k| ^ 7 = |x k| ^ 6 * |x k| := by ring
      _ ≤ m ^ 6 * ρ := mul_le_mul p6 (le_trans ht (le_trans hm hr)) (abs_nonneg _) (pow_nonneg hm0 6)
  have t1 : |a * (Real.cos (x k) - (1 - x k ^ 2 / 2 + x k ^ 4 / 24))| ≤ |a| * (m ^ 6 * (7 / 4320)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (le_trans hc ?_) (abs_nonneg a)
    exact mul_le_mul_of_nonneg_right p6 (by norm_num)
  have t2 : |b * (Real.sin (x k) - (x k - x k ^ 3 / 6 + x k ^ 5 / 120))| ≤ |b| * (m ^ 6 * ρ / 4410) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (le_trans hs ?_) (abs_nonneg b)
    exact div_le_div_of_nonneg_right p7 (by norm_num)
  calc |a * (Real.cos (x k) - (1 - x k ^ 2 / 2 + x k ^ 4 / 24))
          - b * (Real.sin (x k) - (x k - x k ^ 3 / 6 + x k ^ 5 / 120))|
      ≤ |a * (Real.cos (x k) - (1 - x k ^ 2 / 2 + x k ^ 4 / 24))|
        + |b * (Real.sin (x k) - (x k - x k ^ 3 / 6 + x k ^ 5 / 120))| := abs_sub _ _
    _ ≤ |a| * (m ^ 6 * (7 / 4320)) + |b| * (m ^ 6 * ρ / 4410) := add_le_add t1 t2
    _ = (|a| * (7 / 4320) + |b| * (ρ / 4410)) * m ^ 6 := by ring

end Rep

end N14.Jet
