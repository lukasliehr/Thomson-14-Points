module

public import CAP.Schema.ThreePoint.Bounds
public import N14.Ident.Sem

/-!
# T7, the energy identity: the integer polynomials of the kernels, and their degrees

* `partZ`, `kernZ`: the polynomials with integer coefficients of the parts of a block and of the kernels
  (`val_partP`, `val_kernP`): the value of a pair is the positive part minus the negative part.
* `DegB`, `DegP`: every variable has degree at most `d`. A kernel whose blocks pass `blocksOk (n + 1)` has
  degree at most `n` in each variable (`degP_kernP`) and total degree at most `2 * n` (`degLe_kernP`).
* The values at the point `(1, 1, 1)` are the sums of the coefficients (`kern_zero`).
-/

@[expose] public section

namespace N14.Ident

open CAP CAP.ThreePoint MvPolynomial Finset

/-! ## Integer polynomials -/

/-- `∑_{i ≤ j < n0} X i j • u ^ i * v ^ j` with the integer entries of a block of order `N`. -/
noncomputable def phi00Z (P : Params) (N n0 rows : ℕ) : PolyZ :=
  ∑ i ∈ range n0, ∑ s ∈ range (n0 - i), C (entZ P N rows i s) * (X 0 ^ i * X 1 ^ (i + s))

/-- `∑_{i < n0, j < N - n0} X i (n0 + j) • u ^ i * v ^ j`. -/
noncomputable def phi01Z (P : Params) (N n0 rows : ℕ) : PolyZ :=
  ∑ i ∈ range n0, ∑ j ∈ range (N - n0), C (entZ P N rows i (n0 - i + j)) * (X 0 ^ i * X 1 ^ j)

theorem val_phi00P (P : Params) (N n0 rows : ℕ) : val (phi00P P N n0 rows) = phi00Z P N n0 rows := by
  unfold CAP.ThreePoint.val phi00P phi00Z
  simp only [map_sum, map_mul, map_pow, toZ_C, toZ_X]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  unfold entZ
  rw [map_sub, sub_mul]
  simp only [Nat.cast_ofNat, map_pow]

theorem val_phi01P (P : Params) (N n0 rows : ℕ) : val (phi01P P N n0 rows) = phi01Z P N n0 rows := by
  unfold CAP.ThreePoint.val phi01P phi01Z
  simp only [map_sum, map_mul, map_pow, toZ_C, toZ_X]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  unfold entZ
  rw [map_sub, sub_mul]
  simp only [Nat.cast_ofNat, map_pow]

/-- The polynomial `φ` of the part of a block that `sel` selects. -/
noncomputable def partZ (P : Params) (B : Blk) (sel : ℕ) : PolyZ :=
  if sel = 0 then phi00Z P B.N B.n0 B.rows
  else if sel = 1 then phi01Z P B.N B.n0 B.rows
  else phiZ P (B.N - B.n0) (B.rows / 2 ^ (P.w * triOff B.N B.n0))

theorem val_partP (P : Params) (B : Blk) (sel : ℕ) : val (partP P B sel) = partZ P B sel := by
  unfold partP partZ
  split_ifs
  · exact val_phi00P P _ _ _
  · exact val_phi01P P _ _ _
  · exact val_phiP P _ _

/-- `∑ φₖ * Qₖ` over the blocks of `l`, the first of which has the index `k`. -/
noncomputable def kernZFrom (P : Params) (sel : ℕ) : List Blk → ℕ → PolyZ
  | [], _ => 0
  | B :: l, k => partZ P B sel * QZ k + kernZFrom P sel l (k + 1)

/-- The kernel `∑ₖ φₖ * Qₖ` of a part. -/
noncomputable def kernZ (P : Params) (sel : ℕ) (blocks : List Blk) : PolyZ := kernZFrom P sel blocks 0

theorem val_kernFrom (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel : ℕ) : ∀ (l : List Blk) (k : ℕ),
    val (kernFrom P sel l k) = kernZFrom P sel l k
  | [], _ => val_zero
  | B :: l, k => by
    rw [kernFrom, val_add, val_pmul, val_partP, (val_qP P heb hcb k).1, val_kernFrom P heb hcb sel l, kernZFrom]

theorem val_kernP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel : ℕ) (blocks : List Blk) :
    val (kernP P sel blocks) = kernZ P sel blocks := val_kernFrom P heb hcb sel blocks 0

/-! ## The degree in each variable -/

/-- Every variable has degree at most `d`. -/
def DegB (F : Poly) (d : ℕ) : Prop := ∀ i : Fin 3, degreeOf i F ≤ d

/-- Both parts of a pair have degree at most `d` in every variable. -/
def DegP (a : Poly × Poly) (d : ℕ) : Prop := DegB a.1 d ∧ DegB a.2 d

theorem degB_zero (d : ℕ) : DegB 0 d := fun i => by simp

theorem degB_mono {F : Poly} {d e : ℕ} (h : DegB F d) (hd : d ≤ e) : DegB F e := fun i => (h i).trans hd

theorem degB_add {F G : Poly} {d : ℕ} (hF : DegB F d) (hG : DegB G d) : DegB (F + G) d :=
  fun i => (degreeOf_add_le i F G).trans (max_le (hF i) (hG i))

theorem degB_mul {F G : Poly} {d e : ℕ} (hF : DegB F d) (hG : DegB G e) : DegB (F * G) (d + e) :=
  fun i => (degreeOf_mul_le i F G).trans (add_le_add (hF i) (hG i))

theorem degB_sum {ι : Type*} (s : Finset ι) (f : ι → Poly) (d : ℕ) (h : ∀ j ∈ s, DegB (f j) d) :
    DegB (∑ j ∈ s, f j) d :=
  fun i => (degreeOf_sum_le i s f).trans (Finset.sup_le fun j hj => h j hj i)

theorem degB_one (d : ℕ) : DegB (1 : Poly) d := fun i => by
  have h : (1 : Poly) = C 1 := rfl
  rw [h, degreeOf_C]
  exact Nat.zero_le d

theorem degreeOf_X_pow_le (k i : Fin 3) (e : ℕ) :
    degreeOf k ((X i : Poly) ^ e) ≤ if k = i then e else 0 := by
  refine (degreeOf_pow_le k _ e).trans ?_
  rw [degreeOf_X]
  split_ifs <;> simp

theorem degB_var (i : Fin 3) : DegB (X i : Poly) 1 := fun k => by
  have h := degreeOf_X_pow_le k i 1
  rw [pow_one] at h
  refine h.trans ?_
  split_ifs <;> simp

/-- A monomial `u ^ i * v ^ j`. -/
theorem degB_uv (i j d : ℕ) (hi : i ≤ d) (hj : j ≤ d) : DegB (X 0 ^ i * X 1 ^ j : Poly) d := by
  intro k
  refine (degreeOf_mul_le k _ _).trans ?_
  have h0 := degreeOf_X_pow_le k 0 i
  have h1 := degreeOf_X_pow_le k 1 j
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl] at h0
    rw [if_neg (by decide)] at h1
    omega
  · rw [if_neg hk] at h0
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl] at h1
      omega
    · rw [if_neg hk1] at h1
      omega

/-- A term `c • u ^ i * v ^ j`. -/
theorem degB_C_uv (c i j d : ℕ) (hi : i ≤ d) (hj : j ≤ d) : DegB (C c * (X 0 ^ i * X 1 ^ j) : Poly) d :=
  fun k => (degreeOf_C_mul_le _ k c).trans (degB_uv i j d hi hj k)

theorem degP_zero (d : ℕ) : DegP (0, 0) d := ⟨degB_zero d, degB_zero d⟩

theorem degP_mono {a : Poly × Poly} {d e : ℕ} (h : DegP a d) (hd : d ≤ e) : DegP a e :=
  ⟨degB_mono h.1 hd, degB_mono h.2 hd⟩

theorem degP_add {a b : Poly × Poly} {d : ℕ} (ha : DegP a d) (hb : DegP b d) : DegP (a + b) d :=
  ⟨degB_add ha.1 hb.1, degB_add ha.2 hb.2⟩

theorem degP_pmul {a b : Poly × Poly} {d e : ℕ} (ha : DegP a d) (hb : DegP b e) : DegP (pmul a b) (d + e) :=
  ⟨degB_add (degB_mul ha.1 hb.1) (degB_mul ha.2 hb.2), degB_add (degB_mul ha.1 hb.2) (degB_mul ha.2 hb.1)⟩

section kernels
variable (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb)
include heb hcb

theorem degP_tuvP : DegP (tuvP P) 1 := by
  rw [tuvP_eq P heb hcb]
  refine ⟨degB_var 2, ?_⟩
  have h := degB_uv 1 1 1 (le_refl 1) (le_refl 1)
  rw [pow_one, pow_one] at h
  exact h

theorem degP_wuvP : DegP (wuvP P) 2 := by
  rw [wuvP_eq P heb hcb]
  have hx0 : DegB ((X 0 : Poly) ^ 2) 2 := fun k => by
    refine (degreeOf_X_pow_le k 0 2).trans ?_
    split_ifs <;> simp
  have hx1 : DegB ((X 1 : Poly) ^ 2) 2 := fun k => by
    refine (degreeOf_X_pow_le k 1 2).trans ?_
    split_ifs <;> simp
  exact ⟨degB_add (degB_one 2) (degB_uv 2 2 2 (le_refl 2) (le_refl 2)), degB_add hx0 hx1⟩

theorem degP_qNextP {cur prev : Poly × Poly} {k : ℕ} (hc : DegP cur (k + 1)) (hp : DegP prev k) :
    DegP (qNextP P cur prev) (k + 2) := by
  have h1 := degP_pmul (degP_tuvP P heb hcb) hc
  have h2 := degP_pmul (degP_wuvP P heb hcb) hp
  have e1 : 1 + (k + 1) = k + 2 := by ring
  have e2 : 2 + k = k + 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  unfold qNextP
  refine ⟨?_, ?_⟩
  · show DegB (2 * (pmul (tuvP P) cur).1 + (pmul (wuvP P) prev).2) _
    rw [two_mul]
    exact degB_add (degB_add h1.1 h1.1) h2.2
  · show DegB (2 * (pmul (tuvP P) cur).2 + (pmul (wuvP P) prev).1) _
    rw [two_mul]
    exact degB_add (degB_add h1.2 h1.2) h2.1

theorem degP_qP : ∀ k, DegP (qP P k) k ∧ DegP (qP P (k + 1)) (k + 1)
  | 0 => by
    have h : DegP ((1, 0) : Poly × Poly) 0 := ⟨degB_one 0, degB_zero 0⟩
    have h1 : DegP (pmul (tuvP P) (1, 0)) (1 + 0) := degP_pmul (degP_tuvP P heb hcb) h
    exact ⟨h, h1⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := degP_qP k
    exact ⟨h2, degP_qNextP P heb hcb h2 h1⟩

end kernels

theorem degP_phi00P (P : Params) (N n0 rows d : ℕ) (h : n0 ≤ d + 1) : DegP (phi00P P N n0 rows) d := by
  refine ⟨?_, ?_⟩ <;>
  · refine degB_sum _ _ _ fun i hi => degB_sum _ _ _ fun s hs => degB_C_uv _ _ _ _ ?_ ?_
    · have := mem_range.mp hi
      omega
    · have := mem_range.mp hi
      have := mem_range.mp hs
      omega

theorem degP_phi01P (P : Params) (N n0 rows d : ℕ) (h : n0 ≤ d + 1) (h1 : N - n0 ≤ d + 1) :
    DegP (phi01P P N n0 rows) d := by
  refine ⟨?_, ?_⟩ <;>
  · refine degB_sum _ _ _ fun i hi => degB_sum _ _ _ fun s hs => degB_C_uv _ _ _ _ ?_ ?_
    · have := mem_range.mp hi
      omega
    · have := mem_range.mp hs
      omega

theorem degP_phiP (P : Params) (n rows d : ℕ) (h : n ≤ d + 1) : DegP (phiP P n rows) d := by
  refine ⟨?_, ?_⟩ <;>
  · refine degB_sum _ _ _ fun i hi => degB_sum _ _ _ fun s hs => degB_C_uv _ _ _ _ ?_ ?_
    · have := mem_range.mp hi
      omega
    · have := mem_range.mp hi
      have := mem_range.mp hs
      omega

theorem degP_partP (P : Params) (B : Blk) (sel d : ℕ) (h0 : B.n0 ≤ d + 1) (h1 : B.N - B.n0 ≤ d + 1) :
    DegP (partP P B sel) d := by
  unfold partP
  split_ifs
  · exact degP_phi00P P _ _ _ d h0
  · exact degP_phi01P P _ _ _ d h0 h1
  · exact degP_phiP P _ _ d h1

/-! ## The blocks of a kernel -/

theorem blocksOk_nil (m k : ℕ) : blocksOk m [] k = Nat.ble k m := rfl

theorem blocksOk_cons (m : ℕ) (B : Blk) (l : List Blk) (k : ℕ) :
    blocksOk m (B :: l) k = (Nat.ble B.n0 B.N && Nat.ble (B.n0 + k) m && Nat.ble (B.N - B.n0 + k) m
      && blocksOk m l (k + 1)) := rfl

theorem blocksOk_le (m : ℕ) : ∀ (l : List Blk) (k : ℕ), blocksOk m l k = true → k ≤ m
  | [], k, h => Nat.le_of_ble_eq_true h
  | B :: l, k, h => by
    rw [blocksOk_cons, Bool.and_eq_true] at h
    have := blocksOk_le m l (k + 1) h.2
    omega

/-- A kernel whose blocks pass the test has degree at most `n` in each variable. -/
theorem degP_kernFrom (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel n : ℕ) : ∀ (l : List Blk) (k : ℕ),
    blocksOk (n + 1) l k = true → DegP (kernFrom P sel l k) n
  | [], _, _ => degP_zero n
  | B :: l, k, h => by
    rw [blocksOk_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, h1⟩, h2⟩, h3⟩ := h
    have hk := blocksOk_le (n + 1) l (k + 1) h3
    have h1' := Nat.le_of_ble_eq_true h1
    have h2' := Nat.le_of_ble_eq_true h2
    rw [kernFrom]
    refine degP_add ?_ (degP_kernFrom P heb hcb sel n l (k + 1) h3)
    have hp := degP_pmul (degP_partP P B sel (n - k) (by omega) (by omega)) (degP_qP P heb hcb k).1
    exact degP_mono hp (by omega)

theorem degP_kernP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel n : ℕ) (blocks : List Blk)
    (h : blocksOk (n + 1) blocks 0 = true) : DegP (kernP P sel blocks) n :=
  degP_kernFrom P heb hcb sel n blocks 0 h

/-! ## The total degree -/

theorem degLe_phi00P (P : Params) (N n0 rows d : ℕ) (h : n0 ≤ d + 1) : degLe (phi00P P N n0 rows) (2 * d) := by
  refine ⟨?_, ?_⟩ <;>
  · refine totalDegree_sum_le _ _ _ fun i hi => totalDegree_sum_le _ _ _ fun s hs =>
      (totalDegree_uv_le _ _ _).trans ?_
    have := mem_range.mp hi
    have := mem_range.mp hs
    omega

theorem degLe_phi01P (P : Params) (N n0 rows d : ℕ) (h : n0 ≤ d + 1) (h1 : N - n0 ≤ d + 1) :
    degLe (phi01P P N n0 rows) (2 * d) := by
  refine ⟨?_, ?_⟩ <;>
  · refine totalDegree_sum_le _ _ _ fun i hi => totalDegree_sum_le _ _ _ fun s hs =>
      (totalDegree_uv_le _ _ _).trans ?_
    have := mem_range.mp hi
    have := mem_range.mp hs
    omega

theorem degLe_partP (P : Params) (B : Blk) (sel d : ℕ) (h0 : B.n0 ≤ d + 1) (h1 : B.N - B.n0 ≤ d + 1) :
    degLe (partP P B sel) (2 * d) := by
  unfold partP
  split_ifs
  · exact degLe_phi00P P _ _ _ d h0
  · exact degLe_phi01P P _ _ _ d h0 h1
  · exact degLe_mono (degLe_phiP P _ _) (by omega)

/-- A kernel whose blocks pass the test has total degree at most `2 * n`. -/
theorem degLe_kernFrom (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel n : ℕ) : ∀ (l : List Blk) (k : ℕ),
    blocksOk (n + 1) l k = true → degLe (kernFrom P sel l k) (2 * n)
  | [], _, _ => degLe_zero _
  | B :: l, k, h => by
    rw [blocksOk_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨_, h1⟩, h2⟩, h3⟩ := h
    have hk := blocksOk_le (n + 1) l (k + 1) h3
    have h1' := Nat.le_of_ble_eq_true h1
    have h2' := Nat.le_of_ble_eq_true h2
    rw [kernFrom]
    refine degLe_add ?_ (degLe_kernFrom P heb hcb sel n l (k + 1) h3)
    have hp := degLe_pmul (degLe_partP P B sel (n - k) (by omega) (by omega)) (degLe_qP P heb hcb k).1
    exact degLe_mono hp (by omega)

theorem degLe_kernP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (sel n : ℕ) (blocks : List Blk)
    (h : blocksOk (n + 1) blocks 0 = true) : degLe (kernP P sel blocks) (2 * n) :=
  degLe_kernFrom P heb hcb sel n blocks 0 h

/-! ## The sums of the coefficients -/

/-- At the point `(1, 1, 1)` the checker computes the sums of the coefficients of the two parts. -/
theorem kern_zero (P : Params) (sel : ℕ) (blocks : List Blk) :
    kern P ⟨0, 0, 0⟩ sel blocks = (csum (kernP P sel blocks).1, csum (kernP P sel blocks).2) := by
  rw [kern_eq]
  simp only [evp, ev_zero]

end N14.Ident
