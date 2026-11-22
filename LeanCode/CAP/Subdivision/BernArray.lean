module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import CAP.Core.PackedLemmas

/-!
# E11, arrays in three coordinates as packed numbers

An array is a function `f : ℕ → ℕ`; its number is `packSum w N f`. For a coordinate whose digits
have the distance `s` in slots, with `m` values of the digit and `r` repetitions, the index of an
entry is `lo + s * (k + m * hi)` with `lo < s`, the digit `k < m` and `hi < r`.

* `packSum_flat`: a packed number whose slots are packed numbers.
* `and_sliceMask`, `shiftRight_and_sliceMask`: the mask with a periodic pattern cuts out the slice
  of a digit.
* `floor_packSum`: division of all slots by a power of two.
* `act`: a table `τ` acts on the digit of one coordinate; `pass_packSum`: the sum of the slices
  times the numbers of the columns of the table is the number of the new array.
* `act_adjoint`: the sum of the new array with weights that are products is the sum of the old
  array with new weights.
-/

@[expose] public section

namespace CAP

open Finset

/-! ## Sums over a range of products -/

theorem sum_range_mul' {R : Type*} [AddCommMonoid R] (s : ℕ) : ∀ (M : ℕ) (g : ℕ → R),
    ∑ e ∈ range (s * M), g e = ∑ i ∈ range M, ∑ lo ∈ range s, g (lo + s * i)
  | 0, g => by simp
  | M + 1, g => by
    rw [Nat.mul_succ, sum_range_add, sum_range_succ, sum_range_mul' s M g]
    congr 1
    exact sum_congr rfl fun lo _ => by rw [Nat.add_comm]

theorem packSum_succ_last (w m : ℕ) (f : ℕ → ℕ) :
    packSum w (m + 1) f = packSum w m f + f m * 2 ^ (w * m) :=
  sum_range_succ _ _

theorem packSum_mul_right (w m c : ℕ) (f : ℕ → ℕ) :
    packSum w m (fun j => f j * c) = packSum w m f * c := by
  rw [mul_comm, ← packSum_mul]
  exact packSum_congr w m fun j _ => mul_comm _ _

/-- A packed number whose slots of width `w * s` are packed numbers with `s` slots of width `w`. -/
theorem packSum_flat (w s M : ℕ) (g : ℕ → ℕ) :
    packSum (w * s) M (fun i => packSum w s (fun lo => g (lo + s * i))) = packSum w (s * M) g := by
  unfold packSum
  rw [sum_range_mul' s M]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun lo _ => ?_
  rw [mul_assoc, ← pow_add]
  congr 2
  ring

/-- A packed number with one slot that is not zero. -/
theorem packSum_single (w m k c : ℕ) (hk : k < m) :
    packSum w m (fun j => if j = k then c else 0) = c * 2 ^ (w * k) := by
  unfold packSum
  rw [sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (mem_range.mpr hk) h

/-! ## Slices -/

/-- The mask of the slices, moved to the digit `k`, as a packed number. -/
theorem sliceMask_shift (W m r k : ℕ) (hW : 0 < W) (hm : 0 < m) (hk : k < m) :
    (mask W * ones (W * m) r) * 2 ^ (W * k)
      = packSum W (m * r) (fun i => if i % m = k then 2 ^ W - 1 else 0) := by
  rw [mask_eq, ones_eq (W * m) r (Nat.mul_pos hW hm),
    ← packSum_flat W m r (fun i => if i % m = k then 2 ^ W - 1 else 0)]
  have inner : ∀ i, packSum W m (fun lo => if (lo + m * i) % m = k then 2 ^ W - 1 else 0)
      = (2 ^ W - 1) * 2 ^ (W * k) := by
    intro i
    rw [← packSum_single W m k (2 ^ W - 1) hk]
    refine packSum_congr W m fun j hj => ?_
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [packSum_congr (W * m) r (fun i _ => inner i), packSum_const (W * m) r ((2 ^ W - 1) * 2 ^ (W * k))]
  ring

/-- The slice of the digit `k` at its place: the conjunction with the mask moved to this digit. -/
theorem and_sliceMask (W m r k : ℕ) (F : ℕ → ℕ) (hW : 0 < W) (hm : 0 < m) (hk : k < m)
    (hF : ∀ i, i < m * r → F i < 2 ^ W) :
    packSum W (m * r) F &&& ((mask W * ones (W * m) r) <<< (W * k))
      = 2 ^ (W * k) * packSum (W * m) r (fun hi => F (k + m * hi)) := by
  have hlt : ∀ i, i < m * r → (if i % m = k then 2 ^ W - 1 else 0) < 2 ^ W := by
    intro i _
    split_ifs
    · exact Nat.sub_lt (Nat.two_pow_pos W) Nat.one_pos
    · exact Nat.two_pow_pos W
  rw [Nat.shiftLeft_eq, sliceMask_shift W m r k hW hm hk, packSum_and W (m * r) F _ hF hlt,
    ← packSum_flat W m r (fun i => F i &&& if i % m = k then 2 ^ W - 1 else 0), ← packSum_mul]
  refine packSum_congr (W * m) r fun hi hhi => ?_
  rw [mul_comm (2 ^ (W * k)), ← packSum_single W m k (F (k + m * hi)) hk]
  refine packSum_congr W m fun j hj => ?_
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  by_cases hjk : j = k
  · subst hjk
    have hb : j + m * hi < m * r := by
      calc j + m * hi < m + m * hi := Nat.add_lt_add_right hj _
        _ = m * (hi + 1) := by ring
        _ ≤ m * r := Nat.mul_le_mul_left m hhi
    rw [if_pos rfl, if_pos rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hF _ hb)]
  · rw [if_neg hjk, if_neg hjk, Nat.and_zero]

/-- The slice of the digit `k`, moved to the digit `0`. -/
theorem shiftRight_and_sliceMask (W m r k : ℕ) (F : ℕ → ℕ) (hW : 0 < W) (hm : 0 < m) (hk : k < m)
    (hF : ∀ i, i < m * r → F i < 2 ^ W) :
    (packSum W (m * r) F >>> (W * k)) &&& (mask W * ones (W * m) r)
      = packSum (W * m) r (fun hi => F (k + m * hi)) := by
  have e : (packSum W (m * r) F >>> (W * k)) &&& (mask W * ones (W * m) r)
      = (packSum W (m * r) F &&& ((mask W * ones (W * m) r) <<< (W * k))) >>> (W * k) := by
    rw [Nat.shiftRight_and_distrib, Nat.shiftLeft_shiftRight]
  rw [e, and_sliceMask W m r k F hW hm hk hF, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- Division of every slot by `2 ^ n`, rounded down. -/
theorem floor_packSum (w n N : ℕ) (f : ℕ → ℕ) (hn : n ≤ w) (hw : 0 < w) (hf : ∀ j, j < N → f j < 2 ^ w) :
    (packSum w N f &&& ((2 ^ w - 2 ^ n) * ones w N)) >>> n = packSum w N (fun j => f j / 2 ^ n) := by
  have h1 : packSum w N (fun j => f j &&& (2 ^ w - 2 ^ n)) = 2 ^ n * packSum w N (fun j => f j / 2 ^ n) := by
    rw [← packSum_mul]
    exact packSum_congr w N fun j hj => and_hi w n (f j) hn (hf j hj)
  rw [ones_eq w N hw, ← packSum_const,
    packSum_and w N f _ hf (fun _ _ => Nat.sub_lt (Nat.two_pow_pos w) (Nat.two_pow_pos n)), h1,
    Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos n)]

/-! ## The action of a table on the digits of one coordinate -/

/-- The table `τ` acts on the digit of the coordinate with distance `s` and `m` values: the entry
with the digit `j` of the new array is `∑ k, (entry with the digit k) * τ k j`. -/
def act (s m : ℕ) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (e : ℕ) : ℕ :=
  ∑ k ∈ range m, f (e % s + s * (k + m * (e / s / m))) * τ k (e / s % m)

theorem act_at (s m : ℕ) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (lo i : ℕ) (hlo : lo < s) :
    act s m τ f (lo + s * i) = ∑ k ∈ range m, f (lo + s * (k + m * (i / m))) * τ k (i % m) := by
  unfold act
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hlo),
    Nat.div_eq_of_lt hlo, zero_add]

theorem act_at' (s m : ℕ) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (lo j hi : ℕ) (hlo : lo < s) (hj : j < m) :
    act s m τ f (lo + s * (j + m * hi)) = ∑ k ∈ range m, f (lo + s * (k + m * hi)) * τ k j := by
  rw [act_at s m τ f lo _ hlo, Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hj), Nat.div_eq_of_lt hj, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

/-- The sum of the slices times the numbers of the columns is the number of the new array. -/
theorem pass_packSum (w s m r : ℕ) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range m, packSum (w * s * m) r (fun hi => packSum w s (fun lo => f (lo + s * (k + m * hi))))
        * packSum (w * s) m (τ k)
      = packSum w (s * (m * r)) (act s m τ f) := by
  rw [← packSum_flat w s (m * r), ← packSum_flat (w * s) m r]
  have h1 : ∀ hi, packSum (w * s) m (fun j => packSum w s (fun lo => act s m τ f (lo + s * (j + m * hi))))
      = ∑ k ∈ range m, packSum w s (fun lo => f (lo + s * (k + m * hi))) * packSum (w * s) m (τ k) := by
    intro hi
    have h2 : ∀ j, j < m → packSum w s (fun lo => act s m τ f (lo + s * (j + m * hi)))
        = ∑ k ∈ range m, packSum w s (fun lo => f (lo + s * (k + m * hi))) * τ k j := by
      intro j hj
      rw [packSum_congr w s (fun lo hlo => act_at' s m τ f lo j hi hlo hj), packSum_sum]
      exact sum_congr rfl fun k _ => packSum_mul_right w s _ _
    rw [packSum_congr (w * s) m h2, packSum_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [packSum_mul]
  rw [packSum_congr (w * s * m) r (fun hi _ => h1 hi), packSum_sum]
  exact sum_congr rfl fun k _ => (packSum_mul_right _ _ _ _).symm

/-- Weights that are products in the coordinate: the weighted sum of the new array is the weighted
sum of the old array for the weights on which the table has acted. -/
theorem act_adjoint (s m r : ℕ) (τ : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (wgt wgt' : ℕ → ℝ) (ν : ℕ → ℕ → ℝ)
    (ω : ℕ → ℝ)
    (h1 : ∀ lo k hi, lo < s → k < m → hi < r → wgt (lo + s * (k + m * hi)) = ν lo hi * ω k)
    (h2 : ∀ lo k hi, lo < s → k < m → hi < r →
      wgt' (lo + s * (k + m * hi)) = ν lo hi * ∑ j ∈ range m, (τ k j : ℝ) * ω j) :
    ∑ e ∈ range (s * (m * r)), (act s m τ f e : ℝ) * wgt e
      = ∑ e ∈ range (s * (m * r)), (f e : ℝ) * wgt' e := by
  rw [sum_range_mul' s (m * r), sum_range_mul' m r, sum_range_mul' s (m * r), sum_range_mul' m r]
  refine sum_congr rfl fun hi hhi => ?_
  have hhi' := mem_range.mp hhi
  calc ∑ j ∈ range m, ∑ lo ∈ range s, (act s m τ f (lo + s * (j + m * hi)) : ℝ) * wgt (lo + s * (j + m * hi))
      = ∑ j ∈ range m, ∑ lo ∈ range s, ∑ k ∈ range m,
          (f (lo + s * (k + m * hi)) : ℝ) * (ν lo hi * ((τ k j : ℝ) * ω j)) := by
        refine sum_congr rfl fun j hj => sum_congr rfl fun lo hlo => ?_
        rw [act_at' s m τ f lo j hi (mem_range.mp hlo) (mem_range.mp hj),
          h1 lo j hi (mem_range.mp hlo) (mem_range.mp hj) hhi', Nat.cast_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        push_cast
        ring
    _ = ∑ k ∈ range m, ∑ lo ∈ range s, ∑ j ∈ range m,
          (f (lo + s * (k + m * hi)) : ℝ) * (ν lo hi * ((τ k j : ℝ) * ω j)) := by
        exact (sum_comm.trans (sum_congr rfl fun lo _ => sum_comm)).trans sum_comm
    _ = ∑ k ∈ range m, ∑ lo ∈ range s, (f (lo + s * (k + m * hi)) : ℝ) * wgt' (lo + s * (k + m * hi)) := by
        refine sum_congr rfl fun k hk => sum_congr rfl fun lo hlo => ?_
        rw [h2 lo k hi (mem_range.mp hlo) (mem_range.mp hk) hhi', ← mul_sum, ← mul_sum]

end CAP
