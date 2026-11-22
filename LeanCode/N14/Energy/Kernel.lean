module

public import CAP.Schema.ThreePoint.Sphere
public import N14.Ident.Val

/-!
# T7, the kernels of a certificate with two types of points are positive definite

A block of a kernel is a symmetric matrix whose rows and columns belong to basis functions: the first `n0` are
the functions `u ^ i` on the points of the type `0`, the others the functions `u ^ i` on the points of the type
`1` (every type other than `0`). `bas` is the value of a basis function, `phiR` the function `φ` of a block for
two points with their types, `kerR` the kernel `∑ₖ φₖ * Qₖ`.

* `phiR_eq`, `kerR_eq`: these functions are the values of the polynomials of the checker (`partZ`, `kernZ`) for
  the part that the two types select; for the types `1`, `0` in this order the function is zero, since only the
  upper triangle of the matrix is stored.
* `block_nonneg`, `kerR_nonneg`: the kernel of positive definite blocks is positive definite, for numbers
  `u j` and complex numbers `w j` as in `CAP.ThreePoint.moment_kernel_nonneg`.
* `kerR_sphere`: for points of the unit sphere of `ℝ³` and a root point, the sum of the kernel over all pairs of
  points is nonnegative.
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Ident MvPolynomial Finset

/-- The value of the basis function with the number `r` at a point of the type `σ` whose inner product with the
root point is `u`. -/
noncomputable def bas (n0 σ r : ℕ) (u : ℝ) : ℝ :=
  if r < n0 then (if σ = 0 then u ^ r else 0) else (if σ = 0 then 0 else u ^ (r - n0))

theorem bas_lt0 {n0 r : ℕ} (u : ℝ) (h : r < n0) : bas n0 0 r u = u ^ r := by
  unfold bas
  rw [if_pos h, if_pos rfl]

theorem bas_ge0 {n0 r : ℕ} (u : ℝ) (h : ¬ r < n0) : bas n0 0 r u = 0 := by
  unfold bas
  rw [if_neg h, if_pos rfl]

theorem bas_lt1 {n0 σ r : ℕ} (u : ℝ) (hσ : σ ≠ 0) (h : r < n0) : bas n0 σ r u = 0 := by
  unfold bas
  rw [if_pos h, if_neg hσ]

theorem bas_ge1 {n0 σ r : ℕ} (u : ℝ) (hσ : σ ≠ 0) (h : ¬ r < n0) : bas n0 σ r u = u ^ (r - n0) := by
  unfold bas
  rw [if_neg h, if_neg hσ]

/-- The function `φ` of a block for two points of the types `σ`, `σ'`. -/
noncomputable def phiR (P : Params) (B : Blk) (σ σ' : ℕ) (u v : ℝ) : ℝ :=
  ∑ r ∈ range B.N, ∑ s ∈ range (B.N - r),
    (entZ P B.N B.rows r s : ℝ) * (bas B.n0 σ r u * bas B.n0 σ' (r + s) v)

/-- The part of a block that two types select. -/
def selOf (σ σ' : ℕ) : ℕ := if σ = 0 then (if σ' = 0 then 0 else 1) else 2

theorem evR_phi00Z (P : Params) (N n0 rows : ℕ) (u v t : ℝ) :
    evR u v t (phi00Z P N n0 rows)
      = ∑ i ∈ range n0, ∑ s ∈ range (n0 - i), (entZ P N rows i s : ℝ) * (u ^ i * v ^ (i + s)) := by
  unfold phi00Z
  simp only [map_sum, map_mul, map_pow, evR_C, evR_X0, evR_X1]

theorem evR_phi01Z (P : Params) (N n0 rows : ℕ) (u v t : ℝ) :
    evR u v t (phi01Z P N n0 rows)
      = ∑ i ∈ range n0, ∑ j ∈ range (N - n0), (entZ P N rows i (n0 - i + j) : ℝ) * (u ^ i * v ^ j) := by
  unfold phi01Z
  simp only [map_sum, map_mul, map_pow, evR_C, evR_X0, evR_X1]

theorem triOff_add (N a i : ℕ) : triOff N (a + i) = triOff N a + triOff (N - a) i := by
  unfold triOff
  rw [sum_range_add]
  congr 1
  exact sum_congr rfl fun t _ => by omega

/-- The entries of the last rows of a block are those of a block for the rest of the data. -/
theorem entZ_tail (P : Params) (N n0 rows i s : ℕ) :
    entZ P (N - n0) (rows / 2 ^ (P.w * triOff N n0)) i s = entZ P N rows (n0 + i) s := by
  unfold entZ triEnt
  rw [slot_div, triOff_add, Nat.add_assoc]

/-- The function `φ` for two types is the value of the part that they select. -/
theorem phiR_eq (P : Params) (B : Blk) (h : B.n0 ≤ B.N) (σ σ' : ℕ) (u v t : ℝ) :
    phiR P B σ σ' u v = if σ ≠ 0 ∧ σ' = 0 then 0 else evR u v t (partZ P B (selOf σ σ')) := by
  unfold phiR
  by_cases hσ : σ = 0
  · subst hσ
    rw [if_neg (fun hh => hh.1 rfl)]
    have hsub : range B.n0 ⊆ range B.N := range_subset_range.mpr h
    by_cases hσ' : σ' = 0
    · -- both types are `0`
      subst hσ'
      have e : selOf 0 0 = 0 := rfl
      rw [e]
      unfold partZ
      rw [if_pos rfl, evR_phi00Z, ← sum_subset hsub]
      · refine sum_congr rfl fun r hr => ?_
        have hr' := mem_range.mp hr
        have hsub2 : range (B.n0 - r) ⊆ range (B.N - r) := range_subset_range.mpr (by omega)
        rw [← sum_subset hsub2]
        · refine sum_congr rfl fun s hs => ?_
          have hs' := mem_range.mp hs
          rw [bas_lt0 u hr', bas_lt0 v (by omega : r + s < B.n0)]
        · intro s _ hs
          have hs' : ¬ s < B.n0 - r := fun hh => hs (mem_range.mpr hh)
          rw [bas_ge0 v (by omega : ¬ r + s < B.n0), mul_zero, mul_zero]
      · intro r _ hr
        have hr' : ¬ r < B.n0 := fun hh => hr (mem_range.mpr hh)
        refine sum_eq_zero fun s _ => ?_
        rw [bas_ge0 u hr', zero_mul, mul_zero]
    · -- the types `0` and `1`
      have e : selOf 0 σ' = 1 := by simp [selOf, hσ']
      rw [e]
      unfold partZ
      rw [if_neg (by norm_num), if_pos rfl, evR_phi01Z, ← sum_subset hsub]
      · refine sum_congr rfl fun r hr => ?_
        have hr' := mem_range.mp hr
        have hN : B.N - r = (B.n0 - r) + (B.N - B.n0) := by omega
        rw [hN, sum_range_add]
        have hz : ∑ s ∈ range (B.n0 - r),
            (entZ P B.N B.rows r s : ℝ) * (bas B.n0 0 r u * bas B.n0 σ' (r + s) v) = 0 := by
          refine sum_eq_zero fun s hs => ?_
          have hs' := mem_range.mp hs
          rw [bas_lt1 v hσ' (by omega : r + s < B.n0), mul_zero, mul_zero]
        rw [hz, zero_add]
        refine sum_congr rfl fun j _ => ?_
        rw [bas_lt0 u hr', bas_ge1 v hσ' (by omega : ¬ r + (B.n0 - r + j) < B.n0)]
        have ej : r + (B.n0 - r + j) - B.n0 = j := by omega
        rw [ej]
      · intro r _ hr
        have hr' : ¬ r < B.n0 := fun hh => hr (mem_range.mpr hh)
        refine sum_eq_zero fun s _ => ?_
        rw [bas_ge0 u hr', zero_mul, mul_zero]
  · by_cases hσ' : σ' = 0
    · -- the types `1` and `0`: no entry of the upper triangle
      subst hσ'
      rw [if_pos ⟨hσ, rfl⟩]
      refine sum_eq_zero fun r _ => sum_eq_zero fun s _ => ?_
      by_cases hr : r < B.n0
      · rw [bas_lt1 u hσ hr, zero_mul, mul_zero]
      · rw [bas_ge0 v (by omega : ¬ r + s < B.n0), mul_zero, mul_zero]
    · -- both types are `1`
      rw [if_neg (fun hh => hσ' hh.2)]
      have e : selOf σ σ' = 2 := by simp [selOf, hσ]
      rw [e]
      unfold partZ
      rw [if_neg (by norm_num), if_neg (by norm_num), evR_phiZ]
      have hsplit : ∑ r ∈ range B.N, ∑ s ∈ range (B.N - r),
            (entZ P B.N B.rows r s : ℝ) * (bas B.n0 σ r u * bas B.n0 σ' (r + s) v)
          = ∑ i ∈ range (B.N - B.n0), ∑ s ∈ range (B.N - (B.n0 + i)),
            (entZ P B.N B.rows (B.n0 + i) s : ℝ)
              * (bas B.n0 σ (B.n0 + i) u * bas B.n0 σ' (B.n0 + i + s) v) := by
        have hsr : ∀ f : ℕ → ℝ, ∑ r ∈ range B.N, f r
            = ∑ r ∈ range B.n0, f r + ∑ i ∈ range (B.N - B.n0), f (B.n0 + i) := by
          intro f
          rw [← sum_range_add, Nat.add_sub_of_le h]
        have hz : ∑ r ∈ range B.n0, ∑ s ∈ range (B.N - r),
            (entZ P B.N B.rows r s : ℝ) * (bas B.n0 σ r u * bas B.n0 σ' (r + s) v) = 0 := by
          refine sum_eq_zero fun r hr => sum_eq_zero fun s _ => ?_
          rw [bas_lt1 u hσ (mem_range.mp hr), zero_mul, mul_zero]
        rw [hsr, hz, zero_add]
      rw [hsplit]
      refine sum_congr rfl fun i _ => ?_
      have hi : B.N - (B.n0 + i) = B.N - B.n0 - i := by omega
      rw [hi]
      refine sum_congr rfl fun s _ => ?_
      rw [entZ_tail, bas_ge1 u hσ (by omega : ¬ B.n0 + i < B.n0),
        bas_ge1 v hσ' (by omega : ¬ B.n0 + i + s < B.n0)]
      have e1 : B.n0 + i - B.n0 = i := by omega
      have e2 : B.n0 + i + s - B.n0 = i + s := by omega
      rw [e1, e2]

/-- The kernel `∑ φₖ * Qₖ` of the blocks of `l`, the first of which has the index `k`, for two points of the
types `σ`, `σ'`. -/
noncomputable def kerR (P : Params) : List Blk → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _, _ => 0
  | B :: l, k, σ, σ', u, v, t => phiR P B σ σ' u v * evR u v t (QZ k) + kerR P l (k + 1) σ σ' u v t

/-- The kernel for two types is the value of the kernel of the part that they select. -/
theorem kerR_eq (P : Params) (σ σ' : ℕ) (u v t : ℝ) : ∀ (l : List Blk) (k : ℕ), (∀ B ∈ l, B.n0 ≤ B.N) →
    kerR P l k σ σ' u v t = if σ ≠ 0 ∧ σ' = 0 then 0 else evR u v t (kernZFrom P (selOf σ σ') l k)
  | [], _, _ => by simp [kerR, kernZFrom]
  | B :: l, k, h => by
    have ih := kerR_eq P σ σ' u v t l (k + 1) (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    rw [kerR, ih, phiR_eq P B (h B List.mem_cons_self) σ σ' u v t]
    split_ifs
    · ring
    · rw [kernZFrom, map_add, map_mul]

theorem blocksOk_n0 (m : ℕ) : ∀ (l : List Blk) (k : ℕ), blocksOk m l k = true → ∀ B ∈ l, B.n0 ≤ B.N
  | [], _, _ => fun _ hB => absurd hB List.not_mem_nil
  | B :: l, k, h => by
    rw [blocksOk_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    intro B' hB'
    rcases List.mem_cons.mp hB' with rfl | hl
    · exact Nat.le_of_ble_eq_true h.1.1.1
    · exact blocksOk_n0 m l (k + 1) h.2 B' hl

/-! ## Positivity -/

/-- The quadratic form of a block, written with the stored upper triangle, is nonnegative. This is what the
positivity of the kernels uses; it holds if the matrix of the block is positive definite
(`CAP.ThreePoint.quad_nonneg`), and for the singular blocks of the cap by `quadNN_of_kernel`. -/
def QuadNN (P : Params) (n rows : ℕ) : Prop :=
  ∀ α : ℕ → ℝ, 0 ≤ ∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (α r * α (r + s))

/-- The kernel of a block with a nonnegative quadratic form is positive definite, for arbitrary basis
functions. -/
theorem gen_block_nonneg {ι : Type*} [Fintype ι] (P : Params) (n rows k : ℕ)
    (h : QuadNN P n rows) (β : ℕ → ι → ℝ) (w : ι → ℂ) :
    0 ≤ ∑ j, ∑ l,
      (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (β r j * β (r + s) l))
        * ((w j * (starRingEnd ℂ) (w l)) ^ k).re := by
  have hre : ∀ j l, ((w j * (starRingEnd ℂ) (w l)) ^ k).re
      = (w j ^ k).re * (w l ^ k).re + (w j ^ k).im * (w l ^ k).im := by
    intro j l
    rw [mul_pow, ← map_pow, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have key : ∀ A : ι → ℝ,
      (∑ j, ∑ l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (β r j * β (r + s) l))
        * (A j * A l))
      = ∑ r ∈ range n, ∑ s ∈ range (n - r),
          (entZ P n rows r s : ℝ) * ((∑ j, β r j * A j) * (∑ j, β (r + s) j * A j)) := by
    intro A
    have e1 : ∀ j l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (β r j * β (r + s) l))
          * (A j * A l)
        = ∑ r ∈ range n, ∑ s ∈ range (n - r),
            (entZ P n rows r s : ℝ) * ((β r j * A j) * (β (r + s) l * A l)) := by
      intro j l
      rw [sum_mul]
      refine sum_congr rfl fun r _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun s _ => ?_
      ring
    rw [sum_congr rfl fun j _ => sum_congr rfl fun l _ => e1 j l,
      sum4_reorder n (fun r => n - r)
        (fun j l r s => (entZ P n rows r s : ℝ) * ((β r j * A j) * (β (r + s) l * A l)))]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
  have hA := h (fun r => ∑ j, β r j * (w j ^ k).re)
  have hB := h (fun r => ∑ j, β r j * (w j ^ k).im)
  have e : (∑ j, ∑ l,
      (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (β r j * β (r + s) l))
        * ((w j * (starRingEnd ℂ) (w l)) ^ k).re)
      = (∑ j, ∑ l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (β r j * β (r + s) l))
          * ((w j ^ k).re * (w l ^ k).re))
        + ∑ j, ∑ l, (∑ r ∈ range n, ∑ s ∈ range (n - r), (entZ P n rows r s : ℝ) * (β r j * β (r + s) l))
          * ((w j ^ k).im * (w l ^ k).im) := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
    rw [hre, mul_add]
  rw [e, key (fun j => (w j ^ k).re), key (fun j => (w j ^ k).im)]
  exact add_nonneg hA hB

/-- The quadratic forms of the blocks of a list are nonnegative. -/
def BlkPD (P : Params) (l : List Blk) : Prop := ∀ B ∈ l, QuadNN P B.N B.rows

/-- **The kernels of a certificate with two types are positive definite.** -/
theorem kerR_nonneg {ι : Type*} [Fintype ι] (P : Params) (τ : ι → ℕ) (u : ι → ℝ) (tt : ι → ι → ℝ) (w : ι → ℂ)
    (h1 : ∀ j m, (w j * (starRingEnd ℂ) (w m)).re = tt j m - u j * u m)
    (h2 : ∀ j m, Complex.normSq (w j * (starRingEnd ℂ) (w m)) = (1 - u j ^ 2) * (1 - u m ^ 2)) :
    ∀ (l : List Blk) (k : ℕ), BlkPD P l → 0 ≤ ∑ j, ∑ m, kerR P l k (τ j) (τ m) (u j) (u m) (tt j m)
  | [], _, _ => by simp [kerR]
  | B :: l, k, h => by
    have ih := kerR_nonneg P τ u tt w h1 h2 l (k + 1) (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    have hb := gen_block_nonneg P B.N B.rows k (h B List.mem_cons_self) (fun r j => bas B.n0 (τ j) r (u j)) w
    have e : ∀ j m, kerR P (B :: l) k (τ j) (τ m) (u j) (u m) (tt j m)
        = (∑ r ∈ range B.N, ∑ s ∈ range (B.N - r),
              (entZ P B.N B.rows r s : ℝ) * (bas B.n0 (τ j) r (u j) * bas B.n0 (τ m) (r + s) (u m)))
            * ((w j * (starRingEnd ℂ) (w m)) ^ k).re
          + kerR P l (k + 1) (τ j) (τ m) (u j) (u m) (tt j m) := by
      intro j m
      rw [kerR, (evR_QZ (u j) (u m) (tt j m) _ (h1 j m) (h2 j m) k).1]
      rfl
    simp only [e, sum_add_distrib]
    exact add_nonneg hb ih

/-- **The kernels on the sphere.** For points of the unit sphere of `ℝ³` with types and a root point `x i`, the
sum of the kernel over all pairs of points is nonnegative. -/
theorem kerR_sphere {ι : Type*} [Fintype ι] (P : Params) (l : List Blk) (hl : BlkPD P l) (τ : ι → ℕ)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1) (i : ι) :
    0 ≤ ∑ j, ∑ m, kerR P l 0 (τ j) (τ m) (inner ℝ (x i) (x j)) (inner ℝ (x i) (x m)) (inner ℝ (x j) (x m)) := by
  have ha1 : ∀ j, inner ℝ (x j) (x j) = (1 : ℝ) := fun j => by
    rw [real_inner_self_eq_norm_sq, hx j, one_pow]
  obtain ⟨p, q, hpq⟩ := frame_coords (x i) (hx i)
  have hsq : ∀ j, p (x j) * p (x j) + q (x j) * q (x j) = 1 - inner ℝ (x i) (x j) ^ 2 := by
    intro j
    have h := hpq (x j) (x j)
    rw [ha1 j] at h
    rw [sq]
    linarith
  refine kerR_nonneg P τ (fun j => inner ℝ (x i) (x j)) (fun j m => inner ℝ (x j) (x m))
    (fun j => ⟨p (x j), q (x j)⟩) ?_ ?_ l 0 hl
  · intro j m
    show ((⟨p (x j), q (x j)⟩ : ℂ) * (starRingEnd ℂ) ⟨p (x m), q (x m)⟩).re
      = inner ℝ (x j) (x m) - inner ℝ (x i) (x j) * inner ℝ (x i) (x m)
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hpq (x j) (x m)]
    ring
  · intro j m
    show Complex.normSq ((⟨p (x j), q (x j)⟩ : ℂ) * (starRingEnd ℂ) ⟨p (x m), q (x m)⟩)
      = (1 - inner ℝ (x i) (x j) ^ 2) * (1 - inner ℝ (x i) (x m) ^ 2)
    rw [map_mul, Complex.normSq_conj, Complex.normSq_mk, Complex.normSq_mk, hsq j, hsq m]

end N14.Energy
