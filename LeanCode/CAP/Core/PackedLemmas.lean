module

public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.GeomSum
public import CAP.Core.Packed

/-!
# Packed natural numbers: lemmas

The semantics of `CAP.Core.Packed`. A packed vector with slot width `w` and slots
`f 0, …, f (m - 1)` is the number `packSum w m f = ∑ j < m, f j * 2 ^ (w * j)`. This equation needs
no bound on the slots, and it is preserved by sums and by products with scalars. Bounds on the
slots are needed only when slots are read: if all slots are below `2 ^ w`, then `slot` returns
them, shifts and masks select ranges of slots, and bitwise operations act slot by slot.
-/

@[expose] public section

namespace CAP

open Finset

/-! ## The definitions in standard notation -/

theorem mask_eq (w : ℕ) : mask w = 2 ^ w - 1 := by
  show (1 <<< w) - 1 = 2 ^ w - 1
  rw [Nat.one_shiftLeft]

theorem slot_eq (w x j : ℕ) : slot w x j = x / 2 ^ (w * j) % 2 ^ w := by
  show (x >>> (w * j)) &&& mask w = _
  rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem two_pow_pred {k : ℕ} (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_comm]

/-! ## Packed sums -/

/-- The number with the slots `f 0, …, f (m - 1)` of width `w`. -/
def packSum (w m : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ range m, f j * 2 ^ (w * j)

@[simp] theorem packSum_zero (w : ℕ) (f : ℕ → ℕ) : packSum w 0 f = 0 := by simp [packSum]

theorem packSum_succ (w m : ℕ) (f : ℕ → ℕ) :
    packSum w (m + 1) f = f 0 + 2 ^ w * packSum w m (fun j => f (j + 1)) := by
  unfold packSum
  rw [sum_range_succ', mul_sum, add_comm]
  congr 1
  · simp
  · refine sum_congr rfl fun j _ => ?_
    rw [show w * (j + 1) = w + w * j by ring, pow_add]
    ring

theorem packSum_congr (w m : ℕ) {f g : ℕ → ℕ} (h : ∀ j, j < m → f j = g j) :
    packSum w m f = packSum w m g :=
  sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

theorem packSum_add (w m : ℕ) (f g : ℕ → ℕ) :
    packSum w m (fun j => f j + g j) = packSum w m f + packSum w m g := by
  simp [packSum, add_mul, sum_add_distrib]

theorem packSum_mul (w m c : ℕ) (f : ℕ → ℕ) :
    packSum w m (fun j => c * f j) = c * packSum w m f := by
  simp [packSum, mul_sum, mul_assoc]

/-- If the slots are below `2 ^ w`, the packed number is below `2 ^ (w * m)`. -/
theorem packSum_lt (w : ℕ) : ∀ (m : ℕ) (f : ℕ → ℕ), (∀ j, j < m → f j < 2 ^ w) →
    packSum w m f < 2 ^ (w * m)
  | 0, f, _ => by simp
  | m + 1, f, h => by
    rw [packSum_succ]
    have h0 := h 0 (Nat.succ_pos m)
    have ih := packSum_lt w m (fun j => f (j + 1)) (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
    calc f 0 + 2 ^ w * packSum w m (fun j => f (j + 1))
        < 2 ^ w + 2 ^ w * packSum w m (fun j => f (j + 1)) := by omega
      _ = 2 ^ w * (packSum w m (fun j => f (j + 1)) + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * m) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt ih)
      _ = 2 ^ (w * (m + 1)) := by rw [← pow_add]; congr 1; ring

theorem packSum_succ_mod (w m : ℕ) (f : ℕ → ℕ) (h0 : f 0 < 2 ^ w) :
    packSum w (m + 1) f % 2 ^ w = f 0 := by
  rw [packSum_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem packSum_succ_div (w m : ℕ) (f : ℕ → ℕ) (h0 : f 0 < 2 ^ w) :
    packSum w (m + 1) f / 2 ^ w = packSum w m (fun j => f (j + 1)) := by
  rw [packSum_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt h0, zero_add]

/-- Splitting a packed number after `k` slots. -/
theorem packSum_split (w k m : ℕ) (f : ℕ → ℕ) (hk : k ≤ m) :
    packSum w m f = packSum w k f + 2 ^ (w * k) * packSum w (m - k) (fun j => f (j + k)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold packSum
  rw [sum_range_add, Nat.add_sub_cancel_left, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  show f (k + j) * 2 ^ (w * (k + j)) = 2 ^ (w * k) * (f (j + k) * 2 ^ (w * j))
  rw [mul_add, pow_add, add_comm j k]
  ring

/-- Dropping the first `k` slots. -/
theorem packSum_div (w k m : ℕ) (f : ℕ → ℕ) (hk : k ≤ m) (h : ∀ j, j < k → f j < 2 ^ w) :
    packSum w m f / 2 ^ (w * k) = packSum w (m - k) (fun j => f (j + k)) := by
  rw [packSum_split w k m f hk, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (w * k)),
    Nat.div_eq_of_lt (packSum_lt w k f h), zero_add]

/-- Keeping the first `k` slots. -/
theorem packSum_mod (w k m : ℕ) (f : ℕ → ℕ) (hk : k ≤ m) (h : ∀ j, j < k → f j < 2 ^ w) :
    packSum w m f % 2 ^ (w * k) = packSum w k f := by
  rw [packSum_split w k m f hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (packSum_lt w k f h)]

/-- Reading a slot. -/
theorem slot_packSum (w m : ℕ) (f : ℕ → ℕ) (h : ∀ j, j < m → f j < 2 ^ w) (j : ℕ) (hj : j < m) :
    slot w (packSum w m f) j = f j := by
  rw [slot_eq, packSum_div w j m f hj.le (fun i hi => h i (hi.trans hj))]
  obtain ⟨d, hd⟩ : ∃ d, m - j = d + 1 := ⟨m - j - 1, by omega⟩
  rw [hd, packSum_succ_mod _ _ _ (by simpa using h j hj)]
  simp

/-- Two packed numbers with slots below `2 ^ w` are equal only if their slots are equal. -/
theorem packSum_injective (w m : ℕ) (f g : ℕ → ℕ) (hf : ∀ j, j < m → f j < 2 ^ w)
    (hg : ∀ j, j < m → g j < 2 ^ w) (h : packSum w m f = packSum w m g) (j : ℕ) (hj : j < m) :
    f j = g j := by
  rw [← slot_packSum w m f hf j hj, h, slot_packSum w m g hg j hj]

/-- Slot-wise subtraction without borrow. -/
theorem packSum_sub (w m : ℕ) (f g : ℕ → ℕ) (h : ∀ j, j < m → g j ≤ f j) :
    packSum w m f - packSum w m g = packSum w m (fun j => f j - g j) := by
  have : packSum w m f = packSum w m (fun j => f j - g j) + packSum w m g := by
    rw [← packSum_add]
    exact packSum_congr w m fun j hj => (Nat.sub_add_cancel (h j hj)).symm
  omega

theorem packSum_sum {ι : Type*} (w m : ℕ) (r : Finset ι) (f : ι → ℕ → ℕ) :
    packSum w m (fun j => ∑ k ∈ r, f k j) = ∑ k ∈ r, packSum w m (f k) := by
  unfold packSum
  simp only [sum_mul]
  exact sum_comm

theorem packSum_const (w m c : ℕ) : packSum w m (fun _ => c) = c * packSum w m (fun _ => 1) := by
  rw [← packSum_mul]
  simp

theorem packSum_add_const (w m c : ℕ) (f : ℕ → ℕ) :
    packSum w m (fun s => f s + c) = packSum w m f + c * packSum w m (fun _ => 1) :=
  (packSum_add w m f (fun _ => c)).trans
    (congrArg (fun x => packSum w m f + x) (packSum_const w m c))

/-! ## Reading slots of an arbitrary number -/

theorem slot_lt (w x j : ℕ) : slot w x j < 2 ^ w := by
  rw [slot_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Slot `s` of `x` without its first `o` slots is slot `o + s` of `x`. -/
theorem slot_div (w x o s : ℕ) : slot w (x / 2 ^ (w * o)) s = slot w x (o + s) := by
  rw [slot_eq, slot_eq, Nat.div_div_eq_div_mul, ← pow_add, ← mul_add]

/-- The first `m` slots of `x % 2 ^ (w * m)` are those of `x`. -/
theorem slot_mod (w x m s : ℕ) (hs : s < m) : slot w (x % 2 ^ (w * m)) s = slot w x s := by
  obtain ⟨d, rfl⟩ : ∃ d, m = s + (d + 1) := ⟨m - s - 1, by omega⟩
  rw [slot_eq, slot_eq, mul_add, pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_mul_of_pos_right w (Nat.succ_pos d)))

/-- A number below `2 ^ (w * m)` is the packed vector of its first `m` slots. -/
theorem packSum_slot (w : ℕ) : ∀ (m x : ℕ), x < 2 ^ (w * m) → packSum w m (slot w x) = x
  | 0, x, h => by
    have hx : x = 0 := by simpa using h
    simp [hx]
  | m + 1, x, h => by
    have hx : x / 2 ^ w < 2 ^ (w * m) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), ← pow_add]
      have : w * m + w = w * (m + 1) := by ring
      rw [this]
      exact h
    have hs : (fun j => slot w x (j + 1)) = slot w (x / 2 ^ w) := by
      funext j
      have h1 := slot_div w x 1 j
      rw [mul_one] at h1
      rw [h1, add_comm]
    rw [packSum_succ, hs, packSum_slot w m _ hx, slot_eq, mul_zero, pow_zero, Nat.div_one]
    exact Nat.mod_add_div x (2 ^ w)

/-! ## Blocks of slots -/

/-- The first `n` slots of a number below `2 ^ (w * n)` that is extended by a block. -/
theorem slot_add_mul_lo (w n R v s : ℕ) (hR : R < 2 ^ (w * n)) (hs : s < n) :
    slot w (R + v * 2 ^ (w * n)) s = slot w R s := by
  rw [← slot_mod w _ n s hs, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR]

/-- The slots of the block by which a number below `2 ^ (w * n)` is extended. -/
theorem slot_add_mul_hi (w n R v s : ℕ) (hR : R < 2 ^ (w * n)) :
    slot w (R + v * 2 ^ (w * n)) (n + s) = slot w v s := by
  rw [← slot_div, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hR, Nat.zero_add]

theorem add_mul_lt_two_pow (w n m R v : ℕ) (hR : R < 2 ^ (w * n)) (hv : v < 2 ^ (w * m)) :
    R + v * 2 ^ (w * n) < 2 ^ (w * (n + m)) := by
  rw [Nat.mul_add, pow_add]
  calc R + v * 2 ^ (w * n) < 2 ^ (w * n) + v * 2 ^ (w * n) := by omega
    _ = (v + 1) * 2 ^ (w * n) := by ring
    _ ≤ 2 ^ (w * m) * 2 ^ (w * n) := Nat.mul_le_mul_right _ hv
    _ = 2 ^ (w * n) * 2 ^ (w * m) := Nat.mul_comm _ _

theorem slot_zero_of_lt (w a : ℕ) (ha : a < 2 ^ w) : slot w a 0 = a := by
  rw [slot_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt ha]

/-- The lowest slot of `a + rest * 2 ^ w`. -/
theorem slot_cons_zero (w a rest : ℕ) (ha : a < 2 ^ w) : slot w (a + rest * 2 ^ w) 0 = a := by
  have h1 : a < 2 ^ (w * 1) := by rwa [Nat.mul_one]
  have h := slot_add_mul_lo w 1 a rest 0 h1 Nat.zero_lt_one
  rw [Nat.mul_one] at h
  rw [h, slot_zero_of_lt w a ha]

/-- The higher slots of `a + rest * 2 ^ w`. -/
theorem slot_cons_succ (w a rest s : ℕ) (ha : a < 2 ^ w) :
    slot w (a + rest * 2 ^ w) (s + 1) = slot w rest s := by
  have h1 : a < 2 ^ (w * 1) := by rwa [Nat.mul_one]
  have h := slot_add_mul_hi w 1 a rest s h1
  rw [Nat.mul_one, Nat.add_comm 1 s] at h
  exact h

theorem cons_lt_two_pow (w m a rest : ℕ) (ha : a < 2 ^ w) (hrest : rest < 2 ^ (w * m)) :
    a + rest * 2 ^ w < 2 ^ (w * (m + 1)) := by
  have h1 : a < 2 ^ (w * 1) := by rwa [Nat.mul_one]
  have h := add_mul_lt_two_pow w 1 m a rest h1 hrest
  rw [Nat.mul_one, Nat.add_comm 1 m] at h
  exact h

/-- Two numbers whose disjunction is below `2 ^ w` are below `2 ^ w`. -/
theorem lt_of_lor_lt {w a b : ℕ} (h : a ||| b < 2 ^ w) : a < 2 ^ w ∧ b < 2 ^ w :=
  ⟨lt_of_le_of_lt Nat.left_le_or h, lt_of_le_of_lt Nat.right_le_or h⟩

theorem lt_of_shiftRight_eq_zero {w a : ℕ} (h : a >>> w = 0) : a < 2 ^ w := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos w)).mp h

/-! ## Bitwise conjunction -/

/-- Conjunction acts separately on the bits below and above position `k`. -/
theorem and_split (k a b c d : ℕ) (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (b + 2 ^ k * a) &&& (d + 2 ^ k * c) = (b &&& d) + 2 ^ k * (a &&& c) := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have h1 : ((b + 2 ^ k * a) &&& (d + 2 ^ k * c)) / 2 ^ k = a &&& c := by
    rw [Nat.and_div_two_pow, Nat.add_mul_div_left _ _ hk, Nat.add_mul_div_left _ _ hk,
      Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hd, zero_add, zero_add]
  have h2 : ((b + 2 ^ k * a) &&& (d + 2 ^ k * c)) % 2 ^ k = b &&& d := by
    rw [Nat.and_mod_two_pow, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd]
  rw [← Nat.mod_add_div ((b + 2 ^ k * a) &&& (d + 2 ^ k * c)) (2 ^ k), h1, h2]

/-- Conjunction of packed numbers acts slot by slot. -/
theorem packSum_and (w : ℕ) : ∀ (m : ℕ) (f g : ℕ → ℕ), (∀ j, j < m → f j < 2 ^ w) →
    (∀ j, j < m → g j < 2 ^ w) →
    packSum w m f &&& packSum w m g = packSum w m (fun j => f j &&& g j)
  | 0, f, g, _, _ => by simp
  | m + 1, f, g, hf, hg => by
    rw [packSum_succ w m f, packSum_succ w m g, packSum_succ w m (fun j => f j &&& g j),
      and_split w _ _ _ _ (hf 0 (Nat.succ_pos m)) (hg 0 (Nat.succ_pos m)),
      packSum_and w m _ _ (fun j hj => hf (j + 1) (Nat.succ_lt_succ hj))
        (fun j hj => hg (j + 1) (Nat.succ_lt_succ hj))]

/-- The bits `k, …, w - 1` of a number below `2 ^ w`. -/
theorem and_hi (w k z : ℕ) (hk : k ≤ w) (hz : z < 2 ^ w) :
    z &&& (2 ^ w - 2 ^ k) = 2 ^ k * (z / 2 ^ k) := by
  have hw : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  have h1 : 2 ^ w - 2 ^ k = 0 + 2 ^ k * (2 ^ (w - k) - 1) := by
    rw [zero_add, Nat.mul_sub_one, ← hw]
  have h2 : z / 2 ^ k < 2 ^ (w - k) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), mul_comm, ← hw]
    exact hz
  have h3 := and_split k (z / 2 ^ k) (z % 2 ^ k) (2 ^ (w - k) - 1) 0
    (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.two_pow_pos k)
  rw [Nat.mod_add_div, ← h1, Nat.and_zero, zero_add, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt h2] at h3
  exact h3

/-- If the bits `k, …, w - 1` of `z < 2 ^ w` vanish, then `z < 2 ^ k`. -/
theorem lt_of_and_hi_eq_zero (w k z : ℕ) (hk : k ≤ w) (hz : z < 2 ^ w)
    (h : z &&& (2 ^ w - 2 ^ k) = 0) : z < 2 ^ k := by
  rw [and_hi w k z hk hz] at h
  have h0 : z / 2 ^ k = 0 := by
    rcases Nat.mul_eq_zero.mp h with h | h
    · exact absurd h (Nat.two_pow_pos k).ne'
    · exact h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).mp h0

/-- If the bits `k, …, w - 1` of `z < 2 ^ w` are those of `c`, a multiple of `2 ^ k`, then
`c ≤ z < c + 2 ^ k`. -/
theorem bounds_of_and_hi_eq (w k z c : ℕ) (hk : k ≤ w) (hz : z < 2 ^ w)
    (h : z &&& (2 ^ w - 2 ^ k) = c) : c ≤ z ∧ z < c + 2 ^ k := by
  rw [and_hi w k z hk hz] at h
  have h1 := Nat.mod_add_div z (2 ^ k)
  have h2 := Nat.mod_lt z (Nat.two_pow_pos k)
  omega

/-- If no slot of a packed number has a bit in the positions `k, …, w - 1`, then all slots are
below `2 ^ k`. -/
theorem slots_lt_of_and_hi (w k m : ℕ) (f : ℕ → ℕ) (hk : k ≤ w) (hf : ∀ j, j < m → f j < 2 ^ w)
    (h : packSum w m f &&& ((2 ^ w - 2 ^ k) * packSum w m (fun _ => 1)) = 0) :
    ∀ j, j < m → f j < 2 ^ k := by
  intro j hj
  have hc : 2 ^ w - 2 ^ k < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (Nat.two_pow_pos k)
  rw [← packSum_const, packSum_and w m f _ hf (fun _ _ => hc)] at h
  have h0 : packSum w m (fun _ => 0) = 0 := by simp [packSum]
  have h1 := packSum_injective w m _ _ (fun j hj => lt_of_le_of_lt Nat.and_le_left (hf j hj))
    (fun _ _ => Nat.two_pow_pos w) (h.trans h0.symm) j hj
  exact lt_of_and_hi_eq_zero w k (f j) hk (hf j hj) h1

/-- If in every slot of a packed number the bits `k, …, w - 1` are those of `c`, then every slot
lies in `[c, c + 2 ^ k)`. -/
theorem slots_bounds_of_and_hi (w k m c : ℕ) (f : ℕ → ℕ) (hk : k ≤ w) (hc : c < 2 ^ w)
    (hf : ∀ j, j < m → f j < 2 ^ w)
    (h : packSum w m f &&& ((2 ^ w - 2 ^ k) * packSum w m (fun _ => 1))
      = c * packSum w m (fun _ => 1)) :
    ∀ j, j < m → c ≤ f j ∧ f j < c + 2 ^ k := by
  intro j hj
  have hc' : 2 ^ w - 2 ^ k < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (Nat.two_pow_pos k)
  rw [← packSum_const, ← packSum_const, packSum_and w m f _ hf (fun _ _ => hc')] at h
  have h1 := packSum_injective w m _ _ (fun j hj => lt_of_le_of_lt Nat.and_le_left (hf j hj))
    (fun _ _ => hc) h j hj
  exact bounds_of_and_hi_eq w k (f j) c hk (hf j hj) h1

/-! ## The vector of ones -/

/-- The packed vector `(1, …, 1)`. -/
theorem ones_eq (w n : ℕ) (hw : 0 < w) : ones w n = packSum w n (fun _ => 1) := by
  show ((1 <<< (w * n)) - 1) / mask w = _
  rw [mask_eq, Nat.one_shiftLeft]
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have h := Nat.geomSum_eq h2 n
  simp only [packSum, one_mul]
  rw [pow_mul, ← h]
  exact sum_congr rfl fun j _ => by rw [pow_mul]

/-- Dropping the first `i` slots of the vector of ones. -/
theorem ones_div (w n i : ℕ) (hw : 0 < w) (hi : i ≤ n) :
    ones w n / 2 ^ (w * i) = packSum w (n - i) (fun _ => 1) := by
  rw [ones_eq w n hw, packSum_div w i n _ hi (fun _ _ => Nat.one_lt_two_pow hw.ne')]

end CAP
