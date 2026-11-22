module

public import N14.Energy.PD
public import N14.Ident.KerVecKernel
public import N14.Ident.Sem

/-!
# T7, a singular block of the cap: its quadratic form is nonnegative

In the certificate of the cap 13 of the 22 kernel matrices are singular (`F = N G Nᵀ` in the source, with a
matrix `N` that has one column less than rows). The positivity of the kernels needs that the quadratic form of
every block is nonnegative (`QuadNN`). For a singular block this follows from two facts that the kernel verifies:

* a kernel vector `v` of the symmetric matrix `S` of the block, with `v i ≠ 0` (`kerVecOk`);
* the block in which a number `c` is added to the stored diagonal entry `i` is positive definite (`CAP.PSD`).

**Proof** (`quadNN_of_kernel`). For a vector `α` put `β = α - (α i / v i) v`. Then `β i = 0`, and the quadratic
form `q` of `S` satisfies `q (β) = q (α)`, since `S v = 0` and `S` is symmetric (`quad_shift`). The form `q'` of
the changed block is `q + 2 c β i ^ 2` (`quad_bump`), so `q (α) = q (β) = q' (β) ≥ 0`.

`kv_rows`: the checker `kvAll` is sound. `triEnt_bump`, `symEnt_bump`: the entries of the changed block.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Ident Finset

/-- The vector of a certificate of a kernel vector. -/
noncomputable def kvVec (wv Vp Vn : ℕ) (j : ℕ) : ℝ := (slot wv Vp j : ℝ) - slot wv Vn j

/-! ## The entries of the symmetric matrix -/

theorem entZ_cast (P : Params) (n rows i s : ℕ) :
    (entZ P n rows i s : ℝ) = (triEnt P.w n rows i s : ℝ) - 2 ^ (P.a - 1) := by
  unfold entZ
  push_cast
  ring

theorem symEnt_lt (P : Params) (n rows : ℕ) {a b : ℕ} (h : a < b) :
    symEnt P n rows a b = (entZ P n rows a (b - a) : ℝ) := by
  unfold symEnt
  rw [if_neg h.ne, if_pos h]

theorem symEnt_self (P : Params) (n rows a : ℕ) : symEnt P n rows a a = 2 * (entZ P n rows a 0 : ℝ) := by
  unfold symEnt
  rw [if_pos rfl]

theorem symEnt_gt (P : Params) (n rows : ℕ) {a b : ℕ} (h : b < a) :
    symEnt P n rows a b = (entZ P n rows b (a - b) : ℝ) := by
  unfold symEnt
  rw [if_neg h.ne', if_neg (not_lt.mpr h.le)]

theorem symEnt_comm (P : Params) (n rows a b : ℕ) : symEnt P n rows a b = symEnt P n rows b a := by
  rcases lt_trichotomy a b with h | h | h
  · rw [symEnt_lt P n rows h, symEnt_gt P n rows h]
  · rw [h]
  · rw [symEnt_gt P n rows h, symEnt_lt P n rows h]

theorem kvEnt_eq (P : Params) (n rows k j : ℕ) :
    kvEnt P n rows k j = if k ≤ j then triEnt P.w n rows k (j - k) else triEnt P.w n rows j (k - j) := by
  unfold kvEnt triEnt
  by_cases h : k ≤ j
  · rw [Nat.ble_eq_true_of_le h, if_pos h, ← triOffK_eq]
    rfl
  · have hb : Nat.ble k j = false := Bool.eq_false_iff.mpr fun hb => h (Nat.le_of_ble_eq_true hb)
    rw [hb, if_neg h, ← triOffK_eq]
    rfl

theorem kvMul_self (k : ℕ) : kvMul k k = 2 := by
  unfold kvMul
  rw [Nat.beq_refl]

theorem kvMul_ne {k j : ℕ} (h : k ≠ j) : kvMul k j = 1 := by
  unfold kvMul
  rw [Bool.eq_false_iff.mpr fun hb => h (Nat.eq_of_beq_eq_true hb)]

/-- The entry of the symmetric matrix through the functions of the checker. -/
theorem symEnt_kv (P : Params) (n rows k j : ℕ) :
    symEnt P n rows k j = (kvMul k j : ℝ) * ((kvEnt P n rows k j : ℝ) - 2 ^ (P.a - 1)) := by
  rw [kvEnt_eq]
  rcases lt_trichotomy k j with h | h | h
  · rw [symEnt_lt P n rows h, kvMul_ne h.ne, if_pos h.le, entZ_cast]
    push_cast
    ring
  · subst h
    rw [symEnt_self, kvMul_self, if_pos (le_refl k), Nat.sub_self, entZ_cast]
    push_cast
    ring
  · rw [symEnt_gt P n rows h, kvMul_ne h.ne', if_neg (not_le.mpr h), entZ_cast]
    push_cast
    ring

/-! ## Soundness of the checker of a kernel vector -/

theorem kvRow_succ (P : Params) (n rows wv Vp Vn k j : ℕ) :
    kvRow P n rows wv Vp Vn k (j + 1)
      = ((kvRow P n rows wv Vp Vn k j).1
          + kvMul k j * (kvEnt P n rows k j * slot wv Vp j + 1 <<< (P.a - 1) * slot wv Vn j),
        (kvRow P n rows wv Vp Vn k j).2
          + kvMul k j * (kvEnt P n rows k j * slot wv Vn j + 1 <<< (P.a - 1) * slot wv Vp j)) := rfl

theorem kvRow_eq (P : Params) (n rows wv Vp Vn k : ℕ) : ∀ cnt : ℕ,
    ((kvRow P n rows wv Vp Vn k cnt).1 : ℝ) - (kvRow P n rows wv Vp Vn k cnt).2
      = ∑ j ∈ range cnt, symEnt P n rows k j * kvVec wv Vp Vn j
  | 0 => by
    show ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) = _
    simp
  | cnt + 1 => by
    rw [kvRow_succ, sum_range_succ, ← kvRow_eq P n rows wv Vp Vn k cnt, symEnt_kv, Nat.one_shiftLeft]
    unfold kvVec
    push_cast
    ring

theorem kvAll_sound (P : Params) (n rows wv Vp Vn : ℕ) : ∀ cnt : ℕ, kvAll P n rows wv Vp Vn cnt = true →
    ∀ k, k < cnt → (kvRow P n rows wv Vp Vn k n).1 = (kvRow P n rows wv Vp Vn k n).2
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | cnt + 1, h, k, hk => by
    have h' : (kvAll P n rows wv Vp Vn cnt
        && Nat.beq (kvRow P n rows wv Vp Vn cnt n).1 (kvRow P n rows wv Vp Vn cnt n).2) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact kvAll_sound P n rows wv Vp Vn cnt h'.1 k hlt
    · exact Nat.eq_of_beq_eq_true h'.2

/-- **The rows of `S v` vanish.** -/
theorem kv_rows (P : Params) (n rows wv Vp Vn : ℕ) (h : kvAll P n rows wv Vp Vn n = true) (k : ℕ)
    (hk : k < n) : ∑ j ∈ range n, symEnt P n rows k j * kvVec wv Vp Vn j = 0 := by
  rw [← kvRow_eq, kvAll_sound P n rows wv Vp Vn n h k hk, sub_self]

/-! ## The block with a changed diagonal entry -/

theorem triOff_le (n : ℕ) {a b : ℕ} (h : a ≤ b) : triOff n a ≤ triOff n b := by
  unfold triOff
  exact sum_le_sum_of_subset (range_mono h)

theorem tri_idx_lt (n r s : ℕ) (hr : r < n) (hs : s < n - r) : triOff n r + s < triOff n n := by
  have h1 := triOff_le n (Nat.succ_le_of_lt hr)
  rw [triOff_succ] at h1
  omega

theorem tri_idx_inj (n r s i : ℕ) (hr : r < n) (hs : s < n - r) (hi : i < n) :
    triOff n r + s = triOff n i ↔ r = i ∧ s = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy r i with h1 | h1 | h1
    · have h2 := triOff_le n (Nat.succ_le_of_lt h1)
      rw [triOff_succ] at h2
      omega
    · subst h1
      exact ⟨rfl, by omega⟩
    · have h2 := triOff_le n (Nat.succ_le_of_lt h1)
      rw [triOff_succ] at h2
      omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem packSum_unit (w m k c : ℕ) (hk : k < m) :
    packSum w m (fun j => if j = k then c else 0) = c * 2 ^ (w * k) := by
  unfold packSum
  rw [sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (mem_range.mpr hk) h

/-- The stored entries of the block in which `c` is added to the diagonal entry `i`. -/
theorem triEnt_bump (w n rows i c : ℕ) (hi : i < n) (hrows : rows < 2 ^ (w * triOff n n))
    (hroom : slot w rows (triOff n i) + c < 2 ^ w) (r s : ℕ) (hr : r < n) (hs : s < n - r) :
    triEnt w n (rows + c * 2 ^ (w * triOff n i)) r s
      = triEnt w n rows r s + (if r = i ∧ s = 0 then c else 0) := by
  have hK : triOff n i < triOff n n := by
    have := tri_idx_lt n i 0 hi (by omega)
    omega
  have e : rows + c * 2 ^ (w * triOff n i)
      = packSum w (triOff n n) (fun j => slot w rows j + (if j = triOff n i then c else 0)) := by
    rw [packSum_add, packSum_slot w (triOff n n) rows hrows, packSum_unit w (triOff n n) (triOff n i) c hK]
  have hf : ∀ j, j < triOff n n → slot w rows j + (if j = triOff n i then c else 0) < 2 ^ w := by
    intro j _
    split_ifs with hj
    · rw [hj]
      exact hroom
    · have := slot_lt w rows j
      omega
  unfold triEnt
  rw [e, slot_packSum w (triOff n n) _ hf _ (tri_idx_lt n r s hr hs)]
  show slot w rows (triOff n r + s) + (if triOff n r + s = triOff n i then c else 0) = _
  congr 1
  by_cases h : r = i ∧ s = 0
  · rw [if_pos h, if_pos ((tri_idx_inj n r s i hr hs hi).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((tri_idx_inj n r s i hr hs hi).mp h'))]

/-- The entries of the symmetric matrix of the changed block. -/
theorem symEnt_bump (P : Params) (n rows i c : ℕ) (hi : i < n) (hrows : rows < 2 ^ (P.w * triOff n n))
    (hroom : slot P.w rows (triOff n i) + c < 2 ^ P.w) (a b : ℕ) (ha : a < n) (hb : b < n) :
    symEnt P n (rows + c * 2 ^ (P.w * triOff n i)) a b
      = symEnt P n rows a b + (if a = i ∧ b = i then 2 * (c : ℝ) else 0) := by
  have hz : ∀ r s, r < n → s < n - r → (entZ P n (rows + c * 2 ^ (P.w * triOff n i)) r s : ℝ)
      = (entZ P n rows r s : ℝ) + (if r = i ∧ s = 0 then (c : ℝ) else 0) := by
    intro r s hr hs
    rw [entZ_cast, entZ_cast, triEnt_bump P.w n rows i c hi hrows hroom r s hr hs]
    split_ifs
    · push_cast
      ring
    · push_cast
      ring
  rcases lt_trichotomy a b with h | h | h
  · rw [symEnt_lt P n _ h, symEnt_lt P n _ h, hz a (b - a) ha (by omega),
      if_neg (show ¬(a = i ∧ b - a = 0) from fun h' => by omega),
      if_neg (show ¬(a = i ∧ b = i) from fun h' => by omega)]
  · subst h
    rw [symEnt_self, symEnt_self, hz a 0 ha (by omega)]
    by_cases h' : a = i
    · rw [if_pos ⟨h', rfl⟩, if_pos ⟨h', h'⟩]
      ring
    · rw [if_neg (fun h2 => h' h2.1), if_neg (fun h2 => h' h2.1)]
      ring
  · rw [symEnt_gt P n _ h, symEnt_gt P n _ h, hz b (a - b) hb (by omega),
      if_neg (show ¬(b = i ∧ a - b = 0) from fun h' => by omega),
      if_neg (show ¬(a = i ∧ b = i) from fun h' => by omega)]

/-! ## Quadratic forms of symmetric arrays -/

/-- The quadratic form of a symmetric array does not change along a kernel vector. -/
theorem quad_shift (n : ℕ) (S : ℕ → ℕ → ℝ) (hS : ∀ i j, S i j = S j i) (v : ℕ → ℝ)
    (hv : ∀ k, k < n → ∑ j ∈ range n, S k j * v j = 0) (α : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, S i j * ((α i + t * v i) * (α j + t * v j))
      = ∑ i ∈ range n, ∑ j ∈ range n, S i j * (α i * α j) := by
  have h1 : ∑ i ∈ range n, ∑ j ∈ range n, α i * (S i j * v j) = 0 :=
    sum_eq_zero fun i hi => by rw [← mul_sum, hv i (mem_range.mp hi), mul_zero]
  have h2 : ∑ i ∈ range n, ∑ j ∈ range n, α j * (S j i * v i) = 0 := by
    rw [sum_comm]
    exact h1
  have h3 : ∑ i ∈ range n, ∑ j ∈ range n, v i * (S i j * v j) = 0 :=
    sum_eq_zero fun i hi => by rw [← mul_sum, hv i (mem_range.mp hi), mul_zero]
  have e : ∀ i j, S i j * ((α i + t * v i) * (α j + t * v j))
      = S i j * (α i * α j) + t * (α i * (S i j * v j)) + t * (α j * (S j i * v i))
        + t ^ 2 * (v i * (S i j * v j)) := by
    intro i j
    rw [hS j i]
    ring
  calc ∑ i ∈ range n, ∑ j ∈ range n, S i j * ((α i + t * v i) * (α j + t * v j))
      = ∑ i ∈ range n, ∑ j ∈ range n, (S i j * (α i * α j) + t * (α i * (S i j * v j))
          + t * (α j * (S j i * v i)) + t ^ 2 * (v i * (S i j * v j))) :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => e i j
    _ = (∑ i ∈ range n, ∑ j ∈ range n, S i j * (α i * α j))
          + t * (∑ i ∈ range n, ∑ j ∈ range n, α i * (S i j * v j))
          + t * (∑ i ∈ range n, ∑ j ∈ range n, α j * (S j i * v i))
          + t ^ 2 * (∑ i ∈ range n, ∑ j ∈ range n, v i * (S i j * v j)) := by
        simp only [sum_add_distrib, mul_sum]
    _ = ∑ i ∈ range n, ∑ j ∈ range n, S i j * (α i * α j) := by
        rw [h1, h2, h3]
        ring

/-- The quadratic form of an array that differs from another one in the diagonal entry `i`. -/
theorem quad_bump (n i : ℕ) (hi : i < n) (S S' : ℕ → ℕ → ℝ) (c : ℝ)
    (h : ∀ a b, a < n → b < n → S' a b = S a b + (if a = i ∧ b = i then c else 0)) (β : ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, S' a b * (β a * β b)
      = (∑ a ∈ range n, ∑ b ∈ range n, S a b * (β a * β b)) + c * (β i * β i) := by
  have e : ∀ a ∈ range n, ∀ b ∈ range n, S' a b * (β a * β b)
      = S a b * (β a * β b) + (if a = i then (if b = i then c * (β i * β i) else 0) else 0) := by
    intro a ha b hb
    rw [h a b (mem_range.mp ha) (mem_range.mp hb)]
    by_cases h1 : a = i
    · by_cases h2 : b = i
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, h1, h2]
        ring
      · rw [if_neg (fun h' => h2 h'.2), if_pos h1, if_neg h2]
        ring
    · rw [if_neg (fun h' => h1 h'.1), if_neg h1]
      ring
  have e2 : ∑ a ∈ range n, ∑ b ∈ range n, (if a = i then (if b = i then c * (β i * β i) else 0) else 0)
      = c * (β i * β i) := by
    rw [sum_eq_single i (fun a _ ha => by simp [ha]) (fun h => absurd (mem_range.mpr hi) h)]
    simp [hi]
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => e a ha b hb]
  simp only [sum_add_distrib]
  rw [e2]

/-! ## The theorem -/

/-- **The quadratic form of a block with a verified kernel vector is nonnegative**, if the block with `c` added
to the stored diagonal entry `i` is positive definite. `K` is the place of this entry, `triOffK n i`. -/
theorem quadNN_of_kernel (P : Params) (n rows wv Vp Vn i c K : ℕ) (hK : triOffK n i = K)
    (h : kerVecOk P n rows wv Vp Vn i c = true)
    (hPD : (symMat P n (rows + c * 2 ^ (P.w * K))).PosDef) : QuadNN P n rows := by
  subst hK
  rw [triOffK_eq] at hPD
  have h' : (kvAll P n rows wv Vp Vn n && Nat.blt i n && !(Nat.beq (slot wv Vp i) (slot wv Vn i)) &&
      Nat.blt rows (1 <<< (P.w * triOffK n n)) && Nat.blt (slot P.w rows (triOffK n i) + c) (1 <<< P.w))
      = true := h
  simp only [Bool.and_eq_true, Nat.one_shiftLeft, Nat.blt_eq, Bool.not_eq_true', triOffK_eq] at h'
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h'
  have hne : slot wv Vp i ≠ slot wv Vn i := Nat.ne_of_beq_eq_false a3
  have hvi : kvVec wv Vp Vn i ≠ 0 := by
    unfold kvVec
    exact sub_ne_zero.mpr (fun hc => hne (Nat.cast_injective hc))
  intro α
  set v := kvVec wv Vp Vn with hv
  set t : ℝ := -(α i) / v i with ht
  have hβ : α i + t * v i = 0 := by
    rw [ht]
    field_simp
    ring
  have s1 : ∑ a ∈ range n, ∑ b ∈ range n, symEnt P n rows a b * (α a * α b)
      = 2 * ∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (α r * α (r + s)) :=
    sym_sum P n rows (fun a b => α a * α b) (fun a b => mul_comm _ _)
  have s2 : ∑ a ∈ range n, ∑ b ∈ range n, symEnt P n rows a b * ((α a + t * v a) * (α b + t * v b))
      = ∑ a ∈ range n, ∑ b ∈ range n, symEnt P n rows a b * (α a * α b) :=
    quad_shift n (symEnt P n rows) (symEnt_comm P n rows) v (kv_rows P n rows wv Vp Vn a1) α t
  have s3 : ∑ a ∈ range n, ∑ b ∈ range n,
        symEnt P n (rows + c * 2 ^ (P.w * triOff n i)) a b * ((α a + t * v a) * (α b + t * v b))
      = (∑ a ∈ range n, ∑ b ∈ range n, symEnt P n rows a b * ((α a + t * v a) * (α b + t * v b)))
        + 2 * (c : ℝ) * ((α i + t * v i) * (α i + t * v i)) :=
    quad_bump n i a2 (symEnt P n rows) (symEnt P n (rows + c * 2 ^ (P.w * triOff n i))) (2 * (c : ℝ))
      (fun a b ha hb => symEnt_bump P n rows i c a2 a4 a5 a b ha hb) (fun j => α j + t * v j)
  have s4 : ∑ a ∈ range n, ∑ b ∈ range n,
        symEnt P n (rows + c * 2 ^ (P.w * triOff n i)) a b * ((α a + t * v a) * (α b + t * v b))
      = 2 * ∑ r ∈ range n, ∑ s ∈ range (n - r),
          (entZ P n (rows + c * 2 ^ (P.w * triOff n i)) r s : ℝ)
            * ((α r + t * v r) * (α (r + s) + t * v (r + s))) :=
    sym_sum P n (rows + c * 2 ^ (P.w * triOff n i)) (fun a b => (α a + t * v a) * (α b + t * v b))
      (fun a b => mul_comm _ _)
  have s5 : 0 ≤ ∑ r ∈ range n, ∑ s ∈ range (n - r),
      (entZ P n (rows + c * 2 ^ (P.w * triOff n i)) r s : ℝ)
        * ((α r + t * v r) * (α (r + s) + t * v (r + s))) :=
    quad_nonneg P n (rows + c * 2 ^ (P.w * triOff n i)) hPD (fun j => α j + t * v j)
  rw [hβ] at s3
  linarith

end N14.Energy
