module

public import CAP.Subdivision.BernWeight
public import CAP.Subdivision.BernKernel

/-!
# E11, the sign of a polynomial on a box: the passes of the checker

Each pass of `CAP/Subdivision/BernKernel.lean` is Horner's rule on the slices of one coordinate.

* `half_eq`, `halfR_eq`, `asc_eq`, `desc_eq`: the loops in closed form, as sums of slices times
  powers of linear forms at `2 ^ Vs`.
* `half_rep`, `halfR_rep`, `asc_rep`, `desc_rep`: for a number that represents an array with entries
  below `2 ^ V`, the pass gives the number of the array on which the table of the pass has acted.
* `Phi_col2`, `Phi_actP`: the weighted sum with homogeneous weights after a pass is the weighted
  sum before it at the substituted point.
* `act_le`, `actP_le`, `act_mono`: bounds for the entries.
-/

@[expose] public section

namespace CAP.Bernstein

open Finset Polynomial

/-! ## The loops in closed form -/

/-- The slice `k` of a number. -/
def sl (Vs msk X k : ℕ) : ℕ := (X >>> (Vs * k)) &&& msk

theorem halfGo_succ (Vs msk X k S : ℕ) :
    halfGo Vs msk X (k + 1) S = halfGo Vs msk X k (S + S <<< (Vs + 1) + sl Vs msk X k) := rfl

theorem halfGo_eq (Vs msk X : ℕ) : ∀ (cnt S : ℕ),
    halfGo Vs msk X cnt S
      = S * (1 + 2 * 2 ^ Vs) ^ cnt + ∑ k ∈ range cnt, sl Vs msk X k * (1 + 2 * 2 ^ Vs) ^ k
  | 0, S => by
    rw [pow_zero, mul_one, range_zero, sum_empty, add_zero]
    rfl
  | cnt + 1, S => by
    rw [halfGo_succ, halfGo_eq Vs msk X cnt, sum_range_succ, Nat.shiftLeft_eq, pow_succ, pow_succ]
    ring

theorem half_eq (n Vs msk X : ℕ) :
    half n Vs msk X = ∑ k ∈ range (n + 1), sl Vs msk X k * (1 + 2 * 2 ^ Vs) ^ k := by
  show halfGo Vs msk X (n + 1) 0 = _
  rw [halfGo_eq, zero_mul, zero_add]

theorem halfRGo_succ (Vs msk X k : ℕ) :
    halfRGo Vs msk X (k + 1)
      = halfRGo Vs msk X k + halfRGo Vs msk X k <<< (Vs + 1) + sl Vs msk X k := rfl

theorem halfRGo_eq (Vs msk X : ℕ) : ∀ cnt : ℕ,
    halfRGo Vs msk X cnt = ∑ k ∈ range cnt, sl Vs msk X k * (1 + 2 * 2 ^ Vs) ^ (cnt - 1 - k)
  | 0 => by
    rw [range_zero, sum_empty]
    rfl
  | cnt + 1 => by
    have e : ∀ k ∈ range cnt, sl Vs msk X k * (1 + 2 * 2 ^ Vs) ^ (cnt + 1 - 1 - k)
        = sl Vs msk X k * (1 + 2 * 2 ^ Vs) ^ (cnt - 1 - k) * (1 + 2 * 2 ^ Vs) := by
      intro k hk
      have hk' := mem_range.mp hk
      have e' : cnt + 1 - 1 - k = cnt - 1 - k + 1 := by omega
      rw [e', pow_succ]
      ring
    rw [halfRGo_succ, halfRGo_eq Vs msk X cnt, sum_range_succ, sum_congr rfl e, ← sum_mul, Nat.shiftLeft_eq,
      Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_succ]
    ring

theorem halfR_eq (n Vs msk X : ℕ) :
    halfR n Vs msk X = ∑ k ∈ range (n + 1), sl Vs msk X k * (1 + 2 * 2 ^ Vs) ^ (n - k) := by
  show halfRGo Vs msk X (n + 1) = _
  rw [halfRGo_eq]
  rfl

theorem ascGo_succ (Vs msk X c S sh : ℕ) :
    ascGo Vs msk X (c + 1) S sh = ascGo Vs msk X c (S + S <<< Vs + (X &&& (msk <<< sh))) (sh + Vs) := rfl

theorem ascGo_eq (Vs msk X : ℕ) : ∀ (cnt S sh : ℕ),
    ascGo Vs msk X cnt S sh
      = S * (1 + 2 ^ Vs) ^ cnt
        + ∑ i ∈ range cnt, (X &&& (msk <<< (sh + Vs * i))) * (1 + 2 ^ Vs) ^ (cnt - 1 - i)
  | 0, S, sh => by
    rw [pow_zero, mul_one, range_zero, sum_empty, add_zero]
    rfl
  | cnt + 1, S, sh => by
    have e : ∀ i ∈ range cnt, (X &&& (msk <<< (sh + Vs + Vs * i))) * (1 + 2 ^ Vs) ^ (cnt - 1 - i)
        = (X &&& (msk <<< (sh + Vs * (i + 1)))) * (1 + 2 ^ Vs) ^ (cnt + 1 - 1 - (i + 1)) := by
      intro i _
      have e1 : sh + Vs + Vs * i = sh + Vs * (i + 1) := by ring
      have e2 : cnt + 1 - 1 - (i + 1) = cnt - 1 - i := by omega
      rw [e1, e2]
    rw [ascGo_succ, ascGo_eq Vs msk X cnt, sum_range_succ', sum_congr rfl e, Nat.shiftLeft_eq, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero, pow_succ]
    ring_nf

theorem asc_eq (n Vs msk X : ℕ) :
    asc n Vs msk X = ∑ i ∈ range (n + 1), (X &&& (msk <<< (Vs * i))) * (1 + 2 ^ Vs) ^ (n - i) := by
  show ascGo Vs msk X (n + 1) 0 0 = _
  rw [ascGo_eq, zero_mul, zero_add]
  exact sum_congr rfl fun i _ => by rw [zero_add, Nat.add_sub_cancel]

theorem lin_eq (a X Y : ℕ) : lin a X Y = a * X + Y := by
  cases a with
  | zero =>
    show Y = 0 * X + Y
    rw [zero_mul, zero_add]
  | succ a => rfl

/-- The powers of `c' - off` as pairs (positive part, negative part). -/
def pwN (c' off : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 => (c' * (pwN c' off j).1 + off * (pwN c' off j).2, c' * (pwN c' off j).2 + off * (pwN c' off j).1)

theorem descGo_succ (Vs msk c w off q Xp Xn k Sp Sn gp : ℕ) :
    descGo Vs msk c w off q Xp Xn (k + 1) Sp Sn gp =
      descGo Vs msk c w off q Xp Xn k (c * Sp + (off * Sn + (w * (Sp <<< Vs) + sl Vs msk Xp k * gp)))
        (c * Sn + (off * Sp + (w * (Sn <<< Vs) + sl Vs msk Xn k * gp))) (gp * q) := by
  rw [← lin_eq off Sn, ← lin_eq c Sp, ← lin_eq off Sp, ← lin_eq c Sn]
  rfl

theorem descGo_eq (Vs msk c w off q Xp Xn : ℕ) : ∀ (k Sp Sn gp : ℕ),
    descGo Vs msk c w off q Xp Xn k Sp Sn gp =
      (Sp * (pwN (c + w * 2 ^ Vs) off k).1 + Sn * (pwN (c + w * 2 ^ Vs) off k).2
          + ∑ i ∈ range k, gp * q ^ (k - 1 - i) * (sl Vs msk Xp i * (pwN (c + w * 2 ^ Vs) off i).1
              + sl Vs msk Xn i * (pwN (c + w * 2 ^ Vs) off i).2),
        Sn * (pwN (c + w * 2 ^ Vs) off k).1 + Sp * (pwN (c + w * 2 ^ Vs) off k).2
          + ∑ i ∈ range k, gp * q ^ (k - 1 - i) * (sl Vs msk Xp i * (pwN (c + w * 2 ^ Vs) off i).2
              + sl Vs msk Xn i * (pwN (c + w * 2 ^ Vs) off i).1))
  | 0, Sp, Sn, gp => by
    show (Sp, Sn) = _
    simp [pwN]
  | k + 1, Sp, Sn, gp => by
    have hs : ∀ T : ℕ → ℕ, ∑ i ∈ range k, gp * q * q ^ (k - 1 - i) * T i
        = ∑ i ∈ range k, gp * q ^ (k + 1 - 1 - i) * T i := fun T =>
      sum_congr rfl fun i hi => by
        have hi' := mem_range.mp hi
        have e' : k + 1 - 1 - i = k - 1 - i + 1 := by omega
        rw [e', pow_succ]
        ring
    rw [descGo_succ, descGo_eq Vs msk c w off q Xp Xn k, hs, hs, sum_range_succ, sum_range_succ,
      Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.shiftLeft_eq, Nat.shiftLeft_eq, pwN]
    congr 1 <;> ring

theorem desc_eq (n Vs msk c w off q : ℕ) (X : ℕ × ℕ) :
    desc n Vs msk c w off q X =
      (∑ i ∈ range (n + 1), q ^ (n - i) * (sl Vs msk X.1 i * (pwN (c + w * 2 ^ Vs) off i).1
          + sl Vs msk X.2 i * (pwN (c + w * 2 ^ Vs) off i).2),
        ∑ i ∈ range (n + 1), q ^ (n - i) * (sl Vs msk X.1 i * (pwN (c + w * 2 ^ Vs) off i).2
          + sl Vs msk X.2 i * (pwN (c + w * 2 ^ Vs) off i).1)) := by
  show descGo Vs msk c w off q X.1 X.2 (n + 1) 0 0 1 = _
  rw [descGo_eq]
  simp only [zero_mul, zero_add, one_mul, Nat.add_sub_cancel]

/-! ## The columns of `desc` -/

theorem linP_eval (a b y : ℕ) : (linP a b).eval y = a + b * y := by
  unfold linP
  simp only [eval_add, eval_mul, eval_C, eval_X]

/-- The powers of `c + w * X - off` as pairs of polynomials. -/
noncomputable def pwP (c w off : ℕ) : ℕ → ℕ[X] × ℕ[X]
  | 0 => (1, 0)
  | j + 1 => ((pwP c w off j).1 * linP c w + (pwP c w off j).2 * linP off 0,
      (pwP c w off j).2 * linP c w + (pwP c w off j).1 * linP off 0)

theorem pwN_eq (c w off Vs : ℕ) : ∀ j : ℕ,
    pwN (c + w * 2 ^ Vs) off j = ((pwP c w off j).1.eval (2 ^ Vs), (pwP c w off j).2.eval (2 ^ Vs))
  | 0 => by simp [pwN, pwP]
  | j + 1 => by
    rw [pwN, pwN_eq c w off Vs j, pwP]
    simp only [eval_add, eval_mul, linP_eval, zero_mul, add_zero]
    congr 1 <;> ring

theorem pwP_spec (c w off : ℕ) (u v : ℝ) : ∀ j : ℕ,
    (pwP c w off j).1.natDegree ≤ j ∧ (pwP c w off j).2.natDegree ≤ j ∧
      homE j (pwP c w off j).1 u v - homE j (pwP c w off j).2 u v = ((c : ℝ) * u + w * v - off * u) ^ j ∧
      (pwP c w off j).1.eval 1 + (pwP c w off j).2.eval 1 = (c + w + off) ^ j
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [pwP]
    · simp [pwP]
    · simp [pwP, homE]
    · simp [pwP]
  | j + 1 => by
    obtain ⟨d1, d2, h, hs⟩ := pwP_spec c w off u v j
    have dl : ∀ (F : ℕ[X]), F.natDegree ≤ j → ∀ a b : ℕ, (F * linP a b).natDegree ≤ j + 1 := fun F hF a b =>
      natDegree_mul_le.trans (Nat.add_le_add hF (natDegree_linP a b))
    rw [pwP]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (natDegree_add_le _ _).trans (max_le (dl _ d1 _ _) (dl _ d2 _ _))
    · exact (natDegree_add_le _ _).trans (max_le (dl _ d2 _ _) (dl _ d1 _ _))
    · rw [homE_add, homE_add, homE_mul_lin j _ d1 c w, homE_mul_lin j _ d2 off 0, homE_mul_lin j _ d2 c w,
        homE_mul_lin j _ d1 off 0, pow_succ, ← h]
      push_cast
      ring
    · simp only [eval_add, eval_mul, linP_eval]
      rw [pow_succ, ← hs]
      ring

/-- The columns of the positive part of `desc`. -/
noncomputable def colDP (c w off q n k : ℕ) : ℕ[X] := (pwP c w off k).1 * linP q 0 ^ (n - k)

/-- The columns of the negative part of `desc`. -/
noncomputable def colDN (c w off q n k : ℕ) : ℕ[X] := (pwP c w off k).2 * linP q 0 ^ (n - k)

theorem colD_spec (c w off q n k : ℕ) (hk : k ≤ n) (u v : ℝ) :
    (colDP c w off q n k).natDegree ≤ n ∧ (colDN c w off q n k).natDegree ≤ n ∧
      homE n (colDP c w off q n k) u v - homE n (colDN c w off q n k) u v
        = ((q : ℝ) * u) ^ (n - k) * ((c : ℝ) * u + w * v - off * u) ^ k := by
  obtain ⟨d1, d2, h, _⟩ := pwP_spec c w off u v k
  have h1 := homE_mul_pow k _ d1 q 0 u v (n - k)
  have h2 := homE_mul_pow k _ d2 q 0 u v (n - k)
  rw [Nat.add_sub_of_le hk] at h1 h2
  refine ⟨h1.1, h2.1, ?_⟩
  unfold colDP colDN
  rw [h1.2, h2.2, ← h]
  push_cast
  ring

theorem colD_eval (c w off q n k Vs : ℕ) :
    (colDP c w off q n k).eval (2 ^ Vs) = q ^ (n - k) * (pwN (c + w * 2 ^ Vs) off k).1 ∧
      (colDN c w off q n k).eval (2 ^ Vs) = q ^ (n - k) * (pwN (c + w * 2 ^ Vs) off k).2 := by
  unfold colDP colDN
  rw [pwN_eq]
  simp only [eval_mul, eval_pow, linP_eval, zero_mul, add_zero]
  exact ⟨mul_comm _ _, mul_comm _ _⟩

/-- The sum of the entries of the row `j` of the two tables of `desc`. -/
theorem colD_sum (c w off q n : ℕ) (j : ℕ) :
    ∑ k ∈ range (n + 1), (tab (colDP c w off q n) k j + tab (colDN c w off q n) k j)
      ≤ ∑ k ∈ range (n + 1), (c + w + off) ^ k * q ^ (n - k) := by
  refine sum_le_sum fun k _ => ?_
  obtain ⟨_, _, _, hs⟩ := pwP_spec c w off 0 0 k
  calc tab (colDP c w off q n) k j + tab (colDN c w off q n) k j
      ≤ (colDP c w off q n k).eval 1 + (colDN c w off q n k).eval 1 :=
        Nat.add_le_add (UniPos.coeff_le_eval_one _ j) (UniPos.coeff_le_eval_one _ j)
    _ = (c + w + off) ^ k * q ^ (n - k) := by
        unfold colDP colDN
        simp only [eval_mul, eval_pow, linP_eval, zero_mul, add_zero]
        rw [← add_mul, hs]

/-- The loop `gsum`. -/
theorem gsum_eq (a b : ℕ) : ∀ n : ℕ,
    gsum a b n = (∑ k ∈ range (n + 1), a ^ k * b ^ (n - k), b ^ n)
  | 0 => by
    show ((1 : ℕ), (1 : ℕ)) = _
    simp
  | n + 1 => by
    have e : gsum a b (n + 1) = ((gsum a b n).1 * a + (gsum a b n).2 * b, (gsum a b n).2 * b) := rfl
    rw [e, gsum_eq a b n]
    have e1 : ∑ k ∈ range (n + 1 + 1), a ^ k * b ^ (n + 1 - k)
        = (∑ k ∈ range (n + 1), a ^ k * b ^ (n - k)) * a + b ^ n * b := by
      rw [sum_range_succ' _ (n + 1), sum_mul, pow_zero, one_mul, Nat.sub_zero, pow_succ]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [e1, pow_succ]

theorem gsum_pos (a b n : ℕ) (hb : 1 ≤ b) : 1 ≤ (gsum a b n).1 := by
  rw [gsum_eq]
  calc 1 ≤ a ^ 0 * b ^ (n - 0) := by
        rw [pow_zero, one_mul]
        exact Nat.one_le_pow _ _ hb
    _ ≤ ∑ k ∈ range (n + 1), a ^ k * b ^ (n - k) :=
        single_le_sum (f := fun k => a ^ k * b ^ (n - k)) (fun _ _ => Nat.zero_le _)
          (mem_range.mpr (Nat.succ_pos n))

theorem sum_two_pow_le : ∀ n : ℕ, ∑ k ∈ range (n + 1), 2 ^ (n - k) ≤ 2 ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have e : ∑ k ∈ range (n + 1), 2 ^ (n + 1 - (k + 1)) = ∑ k ∈ range (n + 1), 2 ^ (n - k) :=
      sum_congr rfl fun k _ => by rw [Nat.add_sub_add_right]
    have h := sum_two_pow_le n
    have e2 : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [pow_succ 2 (n + 1)]; ring
    rw [sum_range_succ' _ (n + 1), Nat.sub_zero, e]
    omega

/-- The sum of the entries of the row `j` of the table of `asc`. -/
theorem colA_sum (n j : ℕ) : ∑ k ∈ range (n + 1), tab (col2 0 1 1 1 n) k j ≤ 2 ^ (n + 1) := by
  refine le_trans (sum_le_sum fun k _ => ?_) (sum_two_pow_le n)
  calc tab (col2 0 1 1 1 n) k j ≤ (col2 0 1 1 1 n k).eval 1 := UniPos.coeff_le_eval_one _ j
    _ = 2 ^ (n - k) := by
      rw [col2_eval]
      simp

/-! ## Slices of the number of an array -/

theorem idx_lt (m a lo k hi : ℕ) (hlo : lo < stride m a) (hk : k < m) (hhi : hi < reps m a) :
    lo + stride m a * (k + m * hi) < m * m * m := by
  have h1 : k + m * hi + 1 ≤ m * reps m a := by
    calc k + m * hi + 1 ≤ m + m * hi := by omega
      _ = m * (hi + 1) := by ring
      _ ≤ m * reps m a := Nat.mul_le_mul_left m hhi
  calc lo + stride m a * (k + m * hi) < stride m a + stride m a * (k + m * hi) := Nat.add_lt_add_right hlo _
    _ = stride m a * (k + m * hi + 1) := by ring
    _ ≤ stride m a * (m * reps m a) := Nat.mul_le_mul_left _ h1
    _ = m * m * m := stride_mul m a

/-- The mask of the slices of the coordinate `a`. -/
def mskA (V m a : ℕ) : ℕ := mask (V * stride m a) * ones (V * stride m a * m) (reps m a)

theorem superslot_lt (V m a : ℕ) (f : ℕ → ℕ) (hf : ∀ e, e < m * m * m → f e < 2 ^ V) (i : ℕ)
    (hi : i < m * reps m a) : packSum V (stride m a) (fun lo => f (lo + stride m a * i)) < 2 ^ (V * stride m a) := by
  refine packSum_lt V _ _ fun lo hlo => hf _ ?_
  calc lo + stride m a * i < stride m a + stride m a * i := Nat.add_lt_add_right hlo _
    _ = stride m a * (i + 1) := by ring
    _ ≤ stride m a * (m * reps m a) := Nat.mul_le_mul_left _ hi
    _ = m * m * m := stride_mul m a

theorem sl_packSum (V m a : ℕ) (hV : 0 < V) (hm : 0 < m) (f : ℕ → ℕ) (hf : ∀ e, e < m * m * m → f e < 2 ^ V)
    (k : ℕ) (hk : k < m) :
    sl (V * stride m a) (mskA V m a) (packSum V (m * m * m) f) k
      = packSum (V * stride m a * m) (reps m a)
          (fun hi => packSum V (stride m a) (fun lo => f (lo + stride m a * (k + m * hi)))) := by
  have h := shiftRight_and_sliceMask (V * stride m a) m (reps m a) k
    (fun i => packSum V (stride m a) (fun lo => f (lo + stride m a * i)))
    (Nat.mul_pos hV (stride_pos m a hm)) hm hk (superslot_lt V m a f hf)
  rw [packSum_flat V (stride m a) (m * reps m a) f, stride_mul] at h
  exact h

theorem placed_packSum (V m a : ℕ) (hV : 0 < V) (hm : 0 < m) (f : ℕ → ℕ) (hf : ∀ e, e < m * m * m → f e < 2 ^ V)
    (k : ℕ) (hk : k < m) :
    packSum V (m * m * m) f &&& (mskA V m a <<< (V * stride m a * k))
      = 2 ^ (V * stride m a * k) * sl (V * stride m a) (mskA V m a) (packSum V (m * m * m) f) k := by
  rw [sl_packSum V m a hV hm f hf k hk]
  have h := and_sliceMask (V * stride m a) m (reps m a) k
    (fun i => packSum V (stride m a) (fun lo => f (lo + stride m a * i)))
    (Nat.mul_pos hV (stride_pos m a hm)) hm hk (superslot_lt V m a f hf)
  rw [packSum_flat V (stride m a) (m * reps m a) f, stride_mul] at h
  exact h

/-- The sum of the slices times the values of the columns at `2 ^ Vs` is the number of the array
on which the table has acted. -/
theorem pass_cols (V m a : ℕ) (hV : 0 < V) (hm : 0 < m) (f : ℕ → ℕ) (hf : ∀ e, e < m * m * m → f e < 2 ^ V)
    (col : ℕ → ℕ[X]) (hcol : ∀ k, k < m → (col k).natDegree < m) :
    ∑ k ∈ range m, sl (V * stride m a) (mskA V m a) (packSum V (m * m * m) f) k
        * (col k).eval (2 ^ (V * stride m a))
      = packSum V (m * m * m) (act (stride m a) m (tab col) f) := by
  have h := pass_packSum V (stride m a) m (reps m a) (tab col) f
  rw [stride_mul] at h
  rw [← h]
  refine sum_congr rfl fun k hk => ?_
  rw [sl_packSum V m a hV hm f hf k (mem_range.mp hk),
    UniPos.eval_two_pow (V * stride m a) m (col k) (hcol k (mem_range.mp hk))]
  rfl

/-! ## The passes on the number of an array -/

theorem half_rep (V n a : ℕ) (hV : 0 < V) (f : ℕ → ℕ)
    (hf : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → f e < 2 ^ V) :
    half n (V * stride (n + 1) a) (mskA V (n + 1) a) (packSum V ((n + 1) * (n + 1) * (n + 1)) f)
      = packSum V ((n + 1) * (n + 1) * (n + 1)) (act (stride (n + 1) a) (n + 1) (tab (col2 1 2 1 0 n)) f) := by
  rw [half_eq, ← pass_cols V (n + 1) a hV (Nat.succ_pos n) f hf (col2 1 2 1 0 n)
    (fun k hk => Nat.lt_succ_of_le (col2_spec 1 2 1 0 n k (Nat.lt_succ_iff.mp hk) 0 0).1)]
  refine sum_congr rfl fun k _ => ?_
  rw [col2_eval, zero_mul, add_zero, one_pow, mul_one]

theorem halfR_rep (V n a : ℕ) (hV : 0 < V) (f : ℕ → ℕ)
    (hf : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → f e < 2 ^ V) :
    halfR n (V * stride (n + 1) a) (mskA V (n + 1) a) (packSum V ((n + 1) * (n + 1) * (n + 1)) f)
      = packSum V ((n + 1) * (n + 1) * (n + 1)) (act (stride (n + 1) a) (n + 1) (tab (col2 1 0 1 2 n)) f) := by
  rw [halfR_eq, ← pass_cols V (n + 1) a hV (Nat.succ_pos n) f hf (col2 1 0 1 2 n)
    (fun k hk => Nat.lt_succ_of_le (col2_spec 1 0 1 2 n k (Nat.lt_succ_iff.mp hk) 0 0).1)]
  refine sum_congr rfl fun k _ => ?_
  rw [col2_eval, zero_mul, add_zero, one_pow, one_mul]

theorem asc_rep (V n a : ℕ) (hV : 0 < V) (f : ℕ → ℕ)
    (hf : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → f e < 2 ^ V) :
    asc n (V * stride (n + 1) a) (mskA V (n + 1) a) (packSum V ((n + 1) * (n + 1) * (n + 1)) f)
      = packSum V ((n + 1) * (n + 1) * (n + 1)) (act (stride (n + 1) a) (n + 1) (tab (col2 0 1 1 1 n)) f) := by
  rw [asc_eq, ← pass_cols V (n + 1) a hV (Nat.succ_pos n) f hf (col2 0 1 1 1 n)
    (fun k hk => Nat.lt_succ_of_le (col2_spec 0 1 1 1 n k (Nat.lt_succ_iff.mp hk) 0 0).1)]
  refine sum_congr rfl fun k hk => ?_
  rw [placed_packSum V (n + 1) a hV (Nat.succ_pos n) f hf k (mem_range.mp hk), col2_eval, zero_add, one_mul,
    ← pow_mul]
  ring

/-- The pair of arrays after `desc`. -/
def actP (s m : ℕ) (τP τN : ℕ → ℕ → ℕ) (f g : ℕ → ℕ) (e : ℕ) : ℕ := act s m τP f e + act s m τN g e

theorem desc_rep (V n a : ℕ) (hV : 0 < V) (c w off q : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → f e < 2 ^ V)
    (hg : ∀ e, e < (n + 1) * (n + 1) * (n + 1) → g e < 2 ^ V) :
    desc n (V * stride (n + 1) a) (mskA V (n + 1) a) c w off q
        (packSum V ((n + 1) * (n + 1) * (n + 1)) f, packSum V ((n + 1) * (n + 1) * (n + 1)) g)
      = (packSum V ((n + 1) * (n + 1) * (n + 1))
            (actP (stride (n + 1) a) (n + 1) (tab (colDP c w off q n)) (tab (colDN c w off q n)) f g),
          packSum V ((n + 1) * (n + 1) * (n + 1))
            (actP (stride (n + 1) a) (n + 1) (tab (colDN c w off q n)) (tab (colDP c w off q n)) f g)) := by
  have hcP : ∀ k, k < n + 1 → (colDP c w off q n k).natDegree < n + 1 := fun k hk =>
    Nat.lt_succ_of_le (colD_spec c w off q n k (Nat.lt_succ_iff.mp hk) 0 0).1
  have hcN : ∀ k, k < n + 1 → (colDN c w off q n k).natDegree < n + 1 := fun k hk =>
    Nat.lt_succ_of_le (colD_spec c w off q n k (Nat.lt_succ_iff.mp hk) 0 0).2.1
  have hm : 0 < n + 1 := Nat.succ_pos n
  rw [desc_eq]
  unfold actP
  rw [packSum_add, packSum_add, ← pass_cols V (n + 1) a hV hm f hf _ hcP, ← pass_cols V (n + 1) a hV hm g hg _ hcN,
    ← pass_cols V (n + 1) a hV hm f hf _ hcN, ← pass_cols V (n + 1) a hV hm g hg _ hcP, ← sum_add_distrib,
    ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [(colD_eval c w off q n k _).1, (colD_eval c w off q n k _).2]
    ring
  · refine sum_congr rfl fun k _ => ?_
    rw [(colD_eval c w off q n k _).1, (colD_eval c w off q n k _).2]
    ring

/-! ## Bounds for the entries -/

theorem act_smul (s m c : ℕ) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (e : ℕ) :
    act s m τ (fun e => c * f e) e = c * act s m τ f e := by
  unfold act
  rw [mul_sum]
  exact sum_congr rfl fun k _ => by ring

theorem act_mono (m a : ℕ) (hm : 0 < m) (τ : ℕ → ℕ → ℕ) (f g : ℕ → ℕ) (h : ∀ e, e < m * m * m → f e ≤ g e)
    (e : ℕ) (he : e < m * m * m) : act (stride m a) m τ f e ≤ act (stride m a) m τ g e := by
  obtain ⟨lo, j, hi, hlo, hj, hhi, rfl⟩ := decomp m a e hm he
  rw [act_at' _ _ _ _ lo j hi hlo hj, act_at' _ _ _ _ lo j hi hlo hj]
  exact sum_le_sum fun k hk => Nat.mul_le_mul_right _ (h _ (idx_lt m a lo k hi hlo (mem_range.mp hk) hhi))

theorem actP_le (m a : ℕ) (hm : 0 < m) (τP τN : ℕ → ℕ → ℕ) (f g : ℕ → ℕ) (B Γ : ℕ)
    (hf : ∀ e, e < m * m * m → f e ≤ B) (hg : ∀ e, e < m * m * m → g e ≤ B)
    (hΓ : ∀ j, ∑ k ∈ range m, (τP k j + τN k j) ≤ Γ) (e : ℕ) (he : e < m * m * m) :
    actP (stride m a) m τP τN f g e ≤ B * Γ := by
  obtain ⟨lo, j, hi, hlo, hj, hhi, rfl⟩ := decomp m a e hm he
  unfold actP
  rw [act_at' _ _ _ _ lo j hi hlo hj, act_at' _ _ _ _ lo j hi hlo hj, ← sum_add_distrib]
  refine le_trans (sum_le_sum fun k hk => ?_) (le_trans (le_of_eq (mul_sum _ _ _).symm) (Nat.mul_le_mul_left B (hΓ j)))
  have h1 := hf _ (idx_lt m a lo k hi hlo (mem_range.mp hk) hhi)
  have h2 := hg _ (idx_lt m a lo k hi hlo (mem_range.mp hk) hhi)
  calc f (lo + stride m a * (k + m * hi)) * τP k j + g (lo + stride m a * (k + m * hi)) * τN k j
      ≤ B * τP k j + B * τN k j := Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_right _ h2)
    _ = B * (τP k j + τN k j) := by ring

theorem act_le (m a : ℕ) (hm : 0 < m) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (B Γ : ℕ)
    (hf : ∀ e, e < m * m * m → f e ≤ B) (hΓ : ∀ j, ∑ k ∈ range m, τ k j ≤ Γ) (e : ℕ) (he : e < m * m * m) :
    act (stride m a) m τ f e ≤ B * Γ := by
  obtain ⟨lo, j, hi, hlo, hj, hhi, rfl⟩ := decomp m a e hm he
  rw [act_at' _ _ _ _ lo j hi hlo hj]
  refine le_trans (sum_le_sum fun k hk => ?_) (le_trans (le_of_eq (mul_sum _ _ _).symm) (Nat.mul_le_mul_left B (hΓ j)))
  exact Nat.mul_le_mul_right _ (hf _ (idx_lt m a lo k hi hlo (mem_range.mp hk) hhi))

/-! ## Weighted sums with homogeneous weights -/

/-- The coordinates `u` with that of the index `a` replaced by `x`. -/
def updR (u : ℕ → ℝ) (a : ℕ) (x : ℝ) : ℕ → ℝ := fun b => if b = a then x else u b

theorem updR_self (u : ℕ → ℝ) (a : ℕ) (x : ℝ) : updR u a x a = x := if_pos rfl

theorem updR_ne (u : ℕ → ℝ) (a b : ℕ) (x : ℝ) (h : b ≠ a) : updR u a x b = u b := if_neg h

/-- The weighted sum depends on the weights of the digits below `m` only. -/
theorem Phi_congr_weight (m : ℕ) (ω ω' : ℕ → ℕ → ℝ) (f : ℕ → ℕ) (h : ∀ b k, b ≤ 2 → k < m → ω b k = ω' b k) :
    Phi m ω f = Phi m ω' f := by
  rw [Phi_cube, Phi_cube]
  refine sum_congr rfl fun e3 h3 => sum_congr rfl fun e2 h2 => sum_congr rfl fun e1 h1 => ?_
  rw [h 0 e1 (by decide) (mem_range.mp h1), h 1 e2 (by decide) (mem_range.mp h2),
    h 2 e3 (by decide) (mem_range.mp h3)]

/-- A pass whose columns are `col2`: the weighted sum with homogeneous weights is that of the old
array at the substituted point. -/
theorem Phi_col2 (n a : ℕ) (ha : a ≤ 2) (α β α' β' : ℕ) (u v : ℕ → ℝ) (f : ℕ → ℕ) :
    Phi (n + 1) (hwω n u v) (act (stride (n + 1) a) (n + 1) (tab (col2 α β α' β' n)) f)
      = Phi (n + 1) (hwω n (updR u a (α' * u a + β' * v a)) (updR v a (α * u a + β * v a))) f := by
  rw [Phi_act (n + 1) a ha]
  refine Phi_congr_weight _ _ _ _ fun b k _ hk => ?_
  by_cases hb : b = a
  · subst hb
    rw [upd_self]
    unfold hwω
    rw [dualW_col2 α β α' β' n k (Nat.lt_succ_iff.mp hk), updR_self, updR_self]
  · rw [upd_ne _ _ _ _ hb]
    unfold hwω
    rw [updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb]

/-- The pass `desc`: the difference of the weighted sums of the two parts. -/
theorem Phi_actP (n a : ℕ) (ha : a ≤ 2) (c w off q : ℕ) (u v : ℕ → ℝ) (f g : ℕ → ℕ) :
    Phi (n + 1) (hwω n u v)
        (actP (stride (n + 1) a) (n + 1) (tab (colDP c w off q n)) (tab (colDN c w off q n)) f g)
      - Phi (n + 1) (hwω n u v)
        (actP (stride (n + 1) a) (n + 1) (tab (colDN c w off q n)) (tab (colDP c w off q n)) f g)
      = Phi (n + 1) (hwω n (updR u a (q * u a)) (updR v a (c * u a + w * v a - off * u a))) f
        - Phi (n + 1) (hwω n (updR u a (q * u a)) (updR v a (c * u a + w * v a - off * u a))) g := by
  have key : ∀ h : ℕ → ℕ,
      Phi (n + 1) (hwω n u v) (act (stride (n + 1) a) (n + 1) (tab (colDP c w off q n)) h)
        - Phi (n + 1) (hwω n u v) (act (stride (n + 1) a) (n + 1) (tab (colDN c w off q n)) h)
      = Phi (n + 1) (hwω n (updR u a (q * u a)) (updR v a (c * u a + w * v a - off * u a))) h := by
    intro h
    rw [Phi_act (n + 1) a ha, Phi_act (n + 1) a ha, ← Phi_upd_sub (n + 1) a ha]
    refine Phi_congr_weight _ _ _ _ fun b k _ hk => ?_
    by_cases hb : b = a
    · subst hb
      rw [upd_self]
      unfold hwω
      rw [dualW_tab, dualW_tab, (colD_spec c w off q n k (Nat.lt_succ_iff.mp hk) (u b) (v b)).2.2, updR_self,
        updR_self]
      rfl
    · rw [upd_ne _ _ _ _ hb]
      unfold hwω
      rw [updR_ne _ _ _ _ hb, updR_ne _ _ _ _ hb]
  unfold actP
  rw [Phi_add, Phi_add, ← key f, ← key g]
  ring

end CAP.Bernstein
