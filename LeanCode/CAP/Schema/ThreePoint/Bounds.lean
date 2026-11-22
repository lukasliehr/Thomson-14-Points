module

public import CAP.Schema.ThreePoint.Sos
public import CAP.Schema.ThreePoint.Decode

/-!
# Schema S2, soundness: sums of coefficients and degrees

Two properties of the pairs of polynomials are needed when their coefficients are read as digits.

* **Sums of coefficients.** `nrm a` is the sum of the coefficients of both parts of the pair `a`,
  that is, the value at `(1, 1, 1)`. It is additive and multiplicative, it bounds every
  coefficient (`coeff_le_csum`), and for the sum of the blocks it is at most the bound that the
  checker computes (`nrm_sosSum_le`).
* **Degrees.** `degLe a d` states that both parts have total degree at most `d`. For the moment
  part and for the blocks whose flags hold, the degree is at most `2 * D` (`degLe_momentFrom`,
  `degLe_sosSum`).
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-! ## Sums of coefficients -/

/-- The sum of the coefficients of a polynomial with natural coefficients: its value at
`(1, 1, 1)`. -/
noncomputable def csum : Poly →+* ℕ := eval (fun _ => 1)

theorem csum_C (c : ℕ) : csum (C c) = c := eval_C c

theorem csum_X (i : Fin 3) : csum (X i) = 1 := eval_X i

theorem pval_zero (P : Params) : pval P ⟨0, 0, 0⟩ = fun _ => 1 := by
  funext i
  fin_cases i <;> simp [pval]

theorem ev_zero (P : Params) (F : Poly) : ev P ⟨0, 0, 0⟩ F = csum F := by
  unfold ev csum
  rw [pval_zero]

theorem coeff_le_csum (F : Poly) (m : Fin 3 →₀ ℕ) : coeff m F ≤ csum F := by
  unfold csum
  rw [eval_eq']
  simp only [one_pow, Finset.prod_const_one, mul_one]
  by_cases hm : m ∈ F.support
  · exact Finset.single_le_sum (f := fun d => coeff d F) (fun _ _ => Nat.zero_le _) hm
  · rw [notMem_support_iff.mp hm]
    exact Nat.zero_le _

/-- The sum of the coefficients of both parts of a pair. -/
noncomputable def nrm (a : Poly × Poly) : ℕ := csum a.1 + csum a.2

theorem nrm_zero : nrm ((0, 0) : Poly × Poly) = 0 := by simp [nrm]

theorem nrm_add (a b : Poly × Poly) : nrm (a + b) = nrm a + nrm b := by
  simp only [nrm, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem nrm_pmul (a b : Poly × Poly) : nrm (pmul a b) = nrm a * nrm b := by
  simp only [nrm, pmul, map_add, map_mul]
  ring

theorem nrm_smul (c : ℕ) (a : Poly × Poly) : nrm (C c * a.1, C c * a.2) = c * nrm a := by
  simp only [nrm, map_mul, csum_C]
  ring

theorem csum_tMono (P : Params) (f : ℕ) : csum (tMono P f) = 1 := by
  simp [tMono, csum_X]

theorem nrm_tPair (P : Params) (f : ℕ) : nrm (tPair P f) = tCoef P f := by
  unfold tPair
  split <;> simp [nrm, csum_tMono]

theorem nrm_polyOf (P : Params) : ∀ (T tf : ℕ), nrm (polyOf P T tf) = coefSum P T tf
  | 0, _ => nrm_zero
  | T + 1, tf => by rw [polyOf, nrm_add, nrm_tPair, nrm_polyOf P T, coefSum]

/-! ## The flags of a block -/

/-- If the flag of the matrix data holds, the slots of the rows are below `2 ^ a`. -/
theorem sosFlags_bound (P : Params) (B : Sos) (ha : P.a ≤ P.w) (hw : 0 < P.w) : ∀ (cnt i : ℕ),
    sosFlags P B cnt i = true → ∀ r, r < cnt → ∀ s, s < B.n - (i + r) →
      triEnt P.w B.n B.rows (i + r) s < 2 ^ P.a
  | 0, _, _, r, hr, _, _ => absurd hr (Nat.not_lt_zero r)
  | cnt + 1, i, hf, r, hr, s, hs => by
    rw [sosFlags, Bool.and_eq_true] at hf
    rcases r with _ | r
    · have h1 := Nat.eq_of_beq_eq_true hf.1
      rw [triRow_eq, ones_eq P.w _ hw] at h1
      exact slots_lt_of_and_hi P.w P.a (B.n - i) _ ha (fun j _ => triEnt_lt P.w B.n B.rows i j) h1 s hs
    · have e : i + 1 + r = i + (r + 1) := by ring
      have h2 := sosFlags_bound P B ha hw cnt (i + 1) hf.2 r (by omega) s (by rw [e]; exact hs)
      rwa [e] at h2

theorem basisFlag_mem (P : Params) (B : Sos) : ∀ l : List ℕ, basisFlag P B l = true →
    ∀ F ∈ l, degOk P B.dz B.T F = true ∧ coefSum P B.T F ≤ B.cmax
  | [], _, F, hF => absurd hF List.not_mem_nil
  | G :: l, h, F, hF => by
    rw [basisFlag, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hF with rfl | hF'
    · exact ⟨h.1.1, Nat.le_of_ble_eq_true h.1.2⟩
    · exact basisFlag_mem P B l h.2 F hF'

/-! ## The bound of a block -/

theorem nrm_sumP_le (P : Params) (B : Sos) : ∀ l : List ℕ, (∀ F ∈ l, coefSum P B.T F ≤ B.cmax) →
    nrm (sumP P B l) ≤ l.length * B.cmax
  | [], _ => by simp [sumP, nrm_zero]
  | F :: l, h => by
    have h1 := h F List.mem_cons_self
    have h2 := nrm_sumP_le P B l (fun G hG => h G (List.mem_cons_of_mem _ hG))
    have e : (l.length + 1) * B.cmax = l.length * B.cmax + B.cmax := by ring
    rw [sumP, nrm_add, nrm_polyOf, List.length_cons, e]
    omega

theorem nrm_rowP_le (P : Params) (B : Sos) (K : ℕ) : ∀ (l : List ℕ) (ξ : ℕ → ℕ),
    (∀ F ∈ l, coefSum P B.T F ≤ B.cmax) → (∀ j, j < l.length → ξ j ≤ K) →
    nrm (rowP P B l ξ) ≤ l.length * (K * B.cmax)
  | [], ξ, _, _ => by simp [rowP, nrm_zero]
  | F :: l, ξ, h, hξ => by
    have h1 := h F List.mem_cons_self
    have h0 := hξ 0 (by simp)
    have h2 := nrm_rowP_le P B K l (fun j => ξ (j + 1)) (fun G hG => h G (List.mem_cons_of_mem _ hG))
      (fun j hj => hξ (j + 1) (by simpa using hj))
    have h3 : ξ 0 * coefSum P B.T F ≤ K * B.cmax := Nat.mul_le_mul h0 h1
    have e : (l.length + 1) * (K * B.cmax) = l.length * (K * B.cmax) + K * B.cmax := by ring
    rw [rowP, nrm_add, nrm_smul, nrm_polyOf, List.length_cons, e]
    omega

theorem nrm_rowPair (P : Params) (B : Sos) (l : List ℕ) (i : ℕ) :
    nrm (rowPair P B l i) = 2 ^ (P.a - 1) * nrm (sumP P B l) + nrm (rowP P B l (triEnt P.w B.n B.rows i)) := by
  simp only [nrm, rowPair, map_add, map_mul, csum_C]
  ring

theorem nrm_rowPair_le (P : Params) (B : Sos) (ha1 : 1 ≤ P.a) (l : List ℕ) (i : ℕ)
    (hc : ∀ F ∈ l, coefSum P B.T F ≤ B.cmax)
    (hx : ∀ j, j < l.length → triEnt P.w B.n B.rows i j < 2 ^ P.a) :
    nrm (rowPair P B l i) ≤ l.length * B.cmax * 2 ^ (P.a + 1) := by
  have h1 := nrm_sumP_le P B l hc
  have h2 := nrm_rowP_le P B (2 ^ P.a) l _ hc (fun j hj => (hx j hj).le)
  have e1 : 2 ^ P.a = 2 * 2 ^ (P.a - 1) := two_pow_pred ha1
  have e2 : 2 ^ (P.a + 1) = 4 * 2 ^ (P.a - 1) := by rw [pow_succ, e1]; ring
  rw [nrm_rowPair]
  calc 2 ^ (P.a - 1) * nrm (sumP P B l) + nrm (rowP P B l (triEnt P.w B.n B.rows i))
      ≤ 2 ^ (P.a - 1) * (l.length * B.cmax) + l.length * (2 ^ P.a * B.cmax) :=
        add_le_add (Nat.mul_le_mul_left _ h1) h2
    _ = 3 * (2 ^ (P.a - 1) * (l.length * B.cmax)) := by rw [e1]; ring
    _ ≤ 4 * (2 ^ (P.a - 1) * (l.length * B.cmax)) := Nat.mul_le_mul_right _ (by norm_num)
    _ = l.length * B.cmax * 2 ^ (P.a + 1) := by rw [e2]; ring

theorem nrm_sosFrom_le (P : Params) (B : Sos) (ha1 : 1 ≤ P.a) : ∀ (l : List ℕ) (i : ℕ),
    i + l.length = B.n → (∀ F ∈ l, coefSum P B.T F ≤ B.cmax) →
    (∀ i', i ≤ i' → i' < B.n → ∀ s, s < B.n - i' → triEnt P.w B.n B.rows i' s < 2 ^ P.a) →
    nrm (sosFrom P B l i) ≤ l.length * (B.cmax * (B.n * B.cmax * 2 ^ (P.a + 1)))
  | [], i, _, _, _ => by simp [sosFrom, nrm_zero]
  | F :: l, i, h, hc, hx => by
    rw [List.length_cons] at h
    have h1 : coefSum P B.T F ≤ B.cmax := hc F List.mem_cons_self
    have h2 : nrm (rowPair P B (F :: l) i) ≤ (F :: l).length * B.cmax * 2 ^ (P.a + 1) :=
      nrm_rowPair_le P B ha1 (F :: l) i hc (fun j hj => hx i le_rfl (by omega) j (by
        rw [List.length_cons] at hj
        omega))
    have h3 : (F :: l).length ≤ B.n := by
      rw [List.length_cons]
      omega
    have h4 := nrm_sosFrom_le P B ha1 l (i + 1) (by omega) (fun G hG => hc G (List.mem_cons_of_mem _ hG))
      (fun i' hi' => hx i' (by omega))
    have h5 : coefSum P B.T F * nrm (rowPair P B (F :: l) i) ≤ B.cmax * (B.n * B.cmax * 2 ^ (P.a + 1)) :=
      Nat.mul_le_mul h1 (h2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)))
    have e : (l.length + 1) * (B.cmax * (B.n * B.cmax * 2 ^ (P.a + 1)))
        = l.length * (B.cmax * (B.n * B.cmax * 2 ^ (P.a + 1))) + B.cmax * (B.n * B.cmax * 2 ^ (P.a + 1)) := by
      ring
    rw [sosFrom, nrm_add, nrm_pmul, nrm_polyOf, List.length_cons, e]
    omega

/-- If the flag of a block holds, the sum of the coefficients of `f_B * G_B` is at most the bound
of the block. -/
theorem nrm_sosP_le (P : Params) (B : Sos) (ha1 : 1 ≤ P.a) (ha : P.a ≤ P.w) (h : blockFlag P B = true) :
    B.f * nrm (sosP P B) ≤ blockBound P B := by
  simp only [blockFlag, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hrows, hbasis⟩, -⟩, -⟩, -⟩ := h
  have hlen := basisFields_length P B B.n B.basis
  have hmem := basisFlag_mem P B _ hbasis
  have hent := sosFlags_bound P B ha (by omega) B.n 0 hrows
  have h1 := nrm_sosFrom_le P B ha1 (basisFields P B B.n B.basis) 0 (by rw [hlen, zero_add])
    (fun F hF => (hmem F hF).2) (fun i' _ hi' s hs => by
      have := hent i' hi' s (by rw [zero_add]; exact hs)
      rwa [zero_add] at this)
  rw [hlen] at h1
  unfold sosP blockBound
  rw [nrm_pmul, nrm_polyOf]
  calc B.f * (coefSum P B.gT B.weight * nrm (sosFrom P B (basisFields P B B.n B.basis) 0))
      ≤ B.f * (coefSum P B.gT B.weight * (B.n * (B.cmax * (B.n * B.cmax * 2 ^ (P.a + 1))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
    _ = B.f * coefSum P B.gT B.weight * (B.cmax * B.cmax) * B.n * B.n * 2 ^ (P.a + 1) := by ring

theorem nrm_sosSum_le (P : Params) (ha1 : 1 ≤ P.a) (ha : P.a ≤ P.w) : ∀ l : List Sos,
    flagAll P l = true → nrm (sosSum P l) ≤ boundSum P l
  | [], _ => by simp [sosSum, boundSum, nrm_zero]
  | B :: l, h => by
    rw [flagAll, Bool.and_eq_true] at h
    have h1 := nrm_sosP_le P B ha1 ha h.1
    have h2 := nrm_sosSum_le P ha1 ha l h.2
    rw [sosSum, nrm_add, nrm_smul, boundSum]
    omega

/-! ## Degrees -/

/-- Both parts of a pair have total degree at most `d`. -/
def degLe (a : Poly × Poly) (d : ℕ) : Prop := a.1.totalDegree ≤ d ∧ a.2.totalDegree ≤ d

theorem degLe_zero (d : ℕ) : degLe (0, 0) d := ⟨by simp, by simp⟩

theorem degLe_mono {a : Poly × Poly} {d d' : ℕ} (h : degLe a d) (hd : d ≤ d') : degLe a d' :=
  ⟨h.1.trans hd, h.2.trans hd⟩

theorem degLe_add {a b : Poly × Poly} {d : ℕ} (ha : degLe a d) (hb : degLe b d) : degLe (a + b) d :=
  ⟨(totalDegree_add a.1 b.1).trans (max_le ha.1 hb.1), (totalDegree_add a.2 b.2).trans (max_le ha.2 hb.2)⟩

theorem degLe_pmul {a b : Poly × Poly} {da db : ℕ} (ha : degLe a da) (hb : degLe b db) :
    degLe (pmul a b) (da + db) :=
  ⟨(totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (add_le_add ha.1 hb.1))
      ((totalDegree_mul _ _).trans (add_le_add ha.2 hb.2))),
    (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (add_le_add ha.1 hb.2))
      ((totalDegree_mul _ _).trans (add_le_add ha.2 hb.1)))⟩

theorem totalDegree_C_mul_le (c : ℕ) (F : Poly) : (C c * F).totalDegree ≤ F.totalDegree := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]

theorem degLe_smul (c : ℕ) {a : Poly × Poly} {d : ℕ} (h : degLe a d) : degLe (C c * a.1, C c * a.2) d :=
  ⟨(totalDegree_C_mul_le c a.1).trans h.1, (totalDegree_C_mul_le c a.2).trans h.2⟩

theorem totalDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → Poly) (d : ℕ)
    (h : ∀ i ∈ s, (f i).totalDegree ≤ d) : (∑ i ∈ s, f i).totalDegree ≤ d :=
  (totalDegree_finsetSum s f).trans (Finset.sup_le h)

theorem totalDegree_tMono (P : Params) (f : ℕ) : (tMono P f).totalDegree ≤ tDeg P f := by
  unfold tMono
  rw [tDeg_eq]
  exact (totalDegree_mul _ _).trans (add_le_add ((totalDegree_mul _ _).trans
    (add_le_add (totalDegree_X_pow 0 _).le (totalDegree_X_pow 1 _).le)) (totalDegree_X_pow 2 _).le)

theorem degLe_tPair (P : Params) (f : ℕ) : degLe (tPair P f) (tDeg P f) := by
  unfold tPair
  split
  · exact ⟨by simp, (totalDegree_C_mul_le _ _).trans (totalDegree_tMono P f)⟩
  · exact ⟨(totalDegree_C_mul_le _ _).trans (totalDegree_tMono P f), by simp⟩

theorem degLe_polyOf (P : Params) (dz : ℕ) : ∀ (T tf : ℕ), degOk P dz T tf = true →
    degLe (polyOf P T tf) dz
  | 0, _, _ => degLe_zero dz
  | T + 1, tf, h => by
    rw [degOk, Bool.and_eq_true] at h
    rw [polyOf]
    exact degLe_add (degLe_mono (degLe_tPair P _) (Nat.le_of_ble_eq_true h.1)) (degLe_polyOf P dz T _ h.2)

/-! ### The blocks -/

theorem degLe_sumP (P : Params) (B : Sos) : ∀ l : List ℕ, (∀ F ∈ l, degOk P B.dz B.T F = true) →
    degLe (sumP P B l) B.dz
  | [], _ => degLe_zero _
  | F :: l, h => by
    rw [sumP]
    exact degLe_add (degLe_polyOf P B.dz B.T F (h F List.mem_cons_self))
      (degLe_sumP P B l (fun G hG => h G (List.mem_cons_of_mem _ hG)))

theorem degLe_rowP (P : Params) (B : Sos) : ∀ (l : List ℕ) (ξ : ℕ → ℕ),
    (∀ F ∈ l, degOk P B.dz B.T F = true) → degLe (rowP P B l ξ) B.dz
  | [], _, _ => degLe_zero _
  | F :: l, ξ, h => by
    rw [rowP]
    exact degLe_add (degLe_smul _ (degLe_polyOf P B.dz B.T F (h F List.mem_cons_self)))
      (degLe_rowP P B l _ (fun G hG => h G (List.mem_cons_of_mem _ hG)))

theorem degLe_rowPair (P : Params) (B : Sos) (l : List ℕ) (i : ℕ)
    (h : ∀ F ∈ l, degOk P B.dz B.T F = true) : degLe (rowPair P B l i) B.dz := by
  have h1 := degLe_sumP P B l h
  have h2 := degLe_rowP P B l (triEnt P.w B.n B.rows i) h
  exact ⟨(totalDegree_add _ _).trans (max_le ((totalDegree_C_mul_le _ _).trans h1.2) h2.1),
    (totalDegree_add _ _).trans (max_le ((totalDegree_C_mul_le _ _).trans h1.1) h2.2)⟩

theorem degLe_sosFrom (P : Params) (B : Sos) : ∀ (l : List ℕ) (i : ℕ),
    (∀ F ∈ l, degOk P B.dz B.T F = true) → degLe (sosFrom P B l i) (B.dz + B.dz)
  | [], _, _ => degLe_zero _
  | F :: l, i, h => by
    rw [sosFrom]
    exact degLe_add (degLe_pmul (degLe_polyOf P B.dz B.T F (h F List.mem_cons_self))
        (degLe_rowPair P B (F :: l) i h))
      (degLe_sosFrom P B l (i + 1) (fun G hG => h G (List.mem_cons_of_mem _ hG)))

/-- If the flag of a block holds, the degree of `G_B` is at most `2 * D`. -/
theorem degLe_sosP (P : Params) (B : Sos) (h : blockFlag P B = true) : degLe (sosP P B) (2 * P.D) := by
  simp only [blockFlag, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hbasis⟩, hg⟩, hd⟩, -⟩ := h
  have hmem := basisFlag_mem P B _ hbasis
  have h1 := degLe_sosFrom P B (basisFields P B B.n B.basis) 0 (fun F hF => (hmem F hF).1)
  have h2 := degLe_polyOf P B.gdeg B.gT B.weight hg
  have h3 : B.gdeg + (B.dz + B.dz) ≤ 2 * P.D := by
    have := Nat.le_of_ble_eq_true hd
    omega
  exact degLe_mono (degLe_pmul h2 h1) h3

theorem degLe_sosSum (P : Params) : ∀ l : List Sos, flagAll P l = true → degLe (sosSum P l) (2 * P.D)
  | [], _ => degLe_zero _
  | B :: l, h => by
    rw [flagAll, Bool.and_eq_true] at h
    rw [sosSum]
    exact degLe_add (degLe_smul _ (degLe_sosP P B h.1)) (degLe_sosSum P l h.2)

/-! ### The moment part -/

theorem totalDegree_uv_le (c i j : ℕ) : (C c * (X 0 ^ i * X 1 ^ j) : Poly).totalDegree ≤ i + j :=
  (totalDegree_C_mul_le _ _).trans ((totalDegree_mul _ _).trans
    (add_le_add (totalDegree_X_pow 0 i).le (totalDegree_X_pow 1 j).le))

theorem degLe_phiP (P : Params) (n rows : ℕ) : degLe (phiP P n rows) (2 * (n - 1)) := by
  constructor
  · refine totalDegree_sum_le _ _ _ fun i hi => totalDegree_sum_le _ _ _ fun s hs => ?_
    have h1 := mem_range.mp hi
    have h2 := mem_range.mp hs
    exact (totalDegree_uv_le _ _ _).trans (by omega)
  · refine totalDegree_sum_le _ _ _ fun i hi => totalDegree_sum_le _ _ _ fun s hs => ?_
    have h1 := mem_range.mp hi
    have h2 := mem_range.mp hs
    exact (totalDegree_uv_le _ _ _).trans (by omega)

theorem phiP_zero (P : Params) (rows : ℕ) : phiP P 0 rows = (0, 0) := by simp [phiP]

theorem pmul_zero_left (b : Poly × Poly) : pmul (0, 0) b = (0, 0) := by simp [pmul]

section kernels
variable (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb)
include heb hcb

theorem degLe_tuvP : degLe (tuvP P) 2 := by
  rw [tuvP_eq P heb hcb]
  refine ⟨?_, ?_⟩
  · show (X 2 : Poly).totalDegree ≤ 2
    rw [totalDegree_X]
    norm_num
  · show (X 0 * X 1 : Poly).totalDegree ≤ 2
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]

theorem degLe_wuvP : degLe (wuvP P) 4 := by
  rw [wuvP_eq P heb hcb]
  refine ⟨?_, ?_⟩
  · show (1 + X 0 ^ 2 * X 1 ^ 2 : Poly).totalDegree ≤ 4
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X_pow, totalDegree_X_pow]
  · show (X 0 ^ 2 + X 1 ^ 2 : Poly).totalDegree ≤ 4
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_X_pow]
      norm_num
    · rw [totalDegree_X_pow]
      norm_num

theorem degLe_qNextP {cur prev : Poly × Poly} {k : ℕ} (hc : degLe cur (2 * (k + 1))) (hp : degLe prev (2 * k)) :
    degLe (qNextP P cur prev) (2 * (k + 2)) := by
  have h1 := degLe_pmul (degLe_tuvP P heb hcb) hc
  have h2 := degLe_pmul (degLe_wuvP P heb hcb) hp
  have e1 : 2 + 2 * (k + 1) = 2 * (k + 2) := by ring
  have e2 : 4 + 2 * k = 2 * (k + 2) := by ring
  rw [e1] at h1
  rw [e2] at h2
  unfold qNextP
  refine ⟨?_, ?_⟩
  · show (2 * (pmul (tuvP P) cur).1 + (pmul (wuvP P) prev).2).totalDegree ≤ _
    rw [two_mul]
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le h1.1 h1.1)) h2.2)
  · show (2 * (pmul (tuvP P) cur).2 + (pmul (wuvP P) prev).1).totalDegree ≤ _
    rw [two_mul]
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le h1.2 h1.2)) h2.1)

theorem degLe_qP : ∀ k, degLe (qP P k) (2 * k) ∧ degLe (qP P (k + 1)) (2 * (k + 1))
  | 0 => by
    refine ⟨⟨by simp [qP], by simp [qP]⟩, ?_⟩
    have h : degLe ((1, 0) : Poly × Poly) 0 := ⟨by simp, by simp⟩
    have h2 := degLe_pmul (degLe_tuvP P heb hcb) h
    exact h2
  | k + 1 => by
    obtain ⟨h1, h2⟩ := degLe_qP k
    exact ⟨h2, degLe_qNextP P heb hcb h2 h1⟩

/-- The degree of `∑ₖ φₖ * Qₖ` is at most `2 * D`. -/
theorem degLe_momentFrom : ∀ (l : List ℕ) (k : ℕ), degLe (momentFrom P l k) (2 * P.D)
  | [], _ => degLe_zero _
  | rows :: l, k => by
    rw [momentFrom]
    refine degLe_add ?_ (degLe_momentFrom l (k + 1))
    by_cases hk : k ≤ P.D
    · have h := degLe_pmul (degLe_phiP P (P.D + 1 - k) rows) (degLe_qP P heb hcb k).1
      exact degLe_mono h (by omega)
    · have e : P.D + 1 - k = 0 := by omega
      rw [e, phiP_zero, pmul_zero_left]
      exact degLe_zero _

end kernels

end CAP.ThreePoint
