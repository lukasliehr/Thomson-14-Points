module

public import CAP.Schema.ThreePoint.Kernels
public import CAP.Subdivision.BernWeight
public import N14.Box.Cell
public import N14.Ident.Val

/-!
# T7, the energy identity: soundness of the checker of the identity of a run

**Theorem** (`id3_sound`). If `id3Ok P I = true`, then for all real `u`, `v`, `t`

  `cM * M (u, v, t) + cK * ∑ terms (u, v, t) = B₀ (u) + B₁ (v) + B₂ (t) + cp - cn`,

where `M` is the polynomial whose coefficients are the slots of `I.PpM` minus the bias (`mixR`; for the number
`PpM` of a run this is the polynomial of `N14.Box.slackFn`), a term is the kernel `∑ₖ φₖ * Qₖ` of a part of a
list of blocks with the three variables in the order of the term (`termR`), and `B_a` are the polynomials of one
variable of the data (`uniR`).

**Proof.** Both sides of the equation of the checker are values, at the Kronecker point of the layout, of
polynomials with natural coefficients (`Lp`, `Rp`). Their exponents are at most `n` (`degB_…`) and the sums of
their coefficients are below `2 ^ W` (the tests of the checker, with the sums computed at the point `(1, 1, 1)`),
so the two polynomials are equal (`poly_eq_of_ev`, from `CAP.slot_eval_kpt`). Evaluation at a real point gives the
statement.
-/

@[expose] public section

namespace N14.Ident

open CAP CAP.ThreePoint MvPolynomial Finset

/-! ## Two polynomials with the same value at a Kronecker point -/

/-- Polynomials with exponents below `q` and sums of coefficients below `2 ^ W` are determined by their values
at the Kronecker point. -/
theorem poly_eq_of_ev (W q : ℕ) (A B : Poly) (hA : ∀ m ∈ A.support, ∀ i, m i < q)
    (hB : ∀ m ∈ B.support, ∀ i, m i < q) (cA : csum A < 2 ^ W) (cB : csum B < 2 ^ W)
    (h : eval (kpt W q) A = eval (kpt W q) B) : A = B := by
  ext m
  by_cases hm : ∀ i, m i < q
  · have a := slot_eval_kpt W q A hA (fun m => lt_of_le_of_lt (coeff_le_csum A m) cA) (hm 0) (hm 1) (hm 2)
    have b := slot_eval_kpt W q B hB (fun m => lt_of_le_of_lt (coeff_le_csum B m) cB) (hm 0) (hm 1) (hm 2)
    rw [expo_eta] at a b
    rw [← a, ← b, h]
  · push Not at hm
    obtain ⟨i, hi⟩ := hm
    have ha : m ∉ A.support := fun hmem => absurd (hA m hmem i) (not_lt.mpr hi)
    have hb : m ∉ B.support := fun hmem => absurd (hB m hmem i) (not_lt.mpr hi)
    rw [notMem_support_iff.mp ha, notMem_support_iff.mp hb]

theorem support_lt_of_degB {F : Poly} {n : ℕ} (h : DegB F n) : ∀ m ∈ F.support, ∀ i, m i < n + 1 :=
  fun m hm i => (degreeOf_lt_iff (Nat.succ_pos n)).mp (Nat.lt_succ_of_le (h i)) m hm

/-- The value of a polynomial with natural coefficients at a real point. -/
noncomputable def evN (u v t : ℝ) : Poly →+* ℝ := (evR u v t).toRingHom.comp toZ

theorem evN_C (u v t : ℝ) (c : ℕ) : evN u v t (C c) = c := by
  show evR u v t (toZ (C c)) = c
  rw [toZ_C, evR_C]
  simp

theorem evN_X0 (u v t : ℝ) : evN u v t (X 0) = u := by
  show evR u v t (toZ (X 0)) = u
  rw [toZ_X, evR_X0]

theorem evN_X1 (u v t : ℝ) : evN u v t (X 1) = v := by
  show evR u v t (toZ (X 1)) = v
  rw [toZ_X, evR_X1]

theorem evN_X2 (u v t : ℝ) : evN u v t (X 2) = t := by
  show evR u v t (toZ (X 2)) = t
  rw [toZ_X, evR_X2]

theorem evN_sub (u v t : ℝ) (a : Poly × Poly) :
    evN u v t a.1 - evN u v t a.2 = evR u v t (ThreePoint.val a) := by
  show evR u v t (toZ a.1) - evR u v t (toZ a.2) = evR u v t (toZ a.1 - toZ a.2)
  rw [map_sub]

/-! ## The point of the layout of a run -/

/-- The Kronecker point of the layout of a run with `m = n + 1`. -/
def runPt (m : ℕ) : Pt := ⟨1, m, m * m⟩

theorem pval_runPt (P : Params) (m : ℕ) : pval P (runPt m) = kpt P.W m := by
  unfold pval runPt kpt
  rw [mul_one]

theorem ev_runPt (P : Params) (m : ℕ) (F : Poly) : ev P (runPt m) F = eval (kpt P.W m) F := by
  unfold ev
  rw [pval_runPt]

/-- The variable with the number `s`: `0` is `u`, `1` is `v`, every other number is `t`. -/
def fin3 (s : ℕ) : Fin 3 := if s = 0 then 0 else if s = 1 then 1 else 2

/-- The renaming of the variables of a term. -/
def tsig (T : Term) : Fin 3 → Fin 3 := ![fin3 T.s0, fin3 T.s1, fin3 T.s2]

theorem pval_fin3 (P : Params) (m s : ℕ) : pval P (runPt m) (fin3 s) = 2 ^ (P.W * wt m s) := by
  rcases s with _ | _ | s
  · show (2 : ℕ) ^ (P.W * 1) = 2 ^ (P.W * 1)
    rfl
  · show (2 : ℕ) ^ (P.W * m) = 2 ^ (P.W * m)
    rfl
  · have e : fin3 (s + 1 + 1) = 2 := by simp [fin3]
    rw [e]
    show (2 : ℕ) ^ (P.W * (m * m)) = 2 ^ (P.W * (m * m))
    rfl

theorem pval_tpt (P : Params) (m : ℕ) (T : Term) : pval P (tpt m T) = pval P (runPt m) ∘ tsig T := by
  funext i
  fin_cases i
  · exact (pval_fin3 P m T.s0).symm
  · exact (pval_fin3 P m T.s1).symm
  · exact (pval_fin3 P m T.s2).symm

theorem ev_tpt (P : Params) (m : ℕ) (T : Term) (F : Poly) :
    ev P (tpt m T) F = ev P (runPt m) (rename (tsig T) F) := by
  unfold ev
  rw [pval_tpt, eval_rename]

theorem csum_rename (σ : Fin 3 → Fin 3) (F : Poly) : csum (rename σ F) = csum F := by
  unfold csum
  rw [eval_rename]
  rfl

/-! ## The terms -/

/-- The pair of a term: the kernel with renamed variables. -/
noncomputable def termP (P : Params) (T : Term) : Poly × Poly :=
  (rename (tsig T) (kernP P T.sel T.blocks).1, rename (tsig T) (kernP P T.sel T.blocks).2)

/-- The pair of the sum of the terms. -/
noncomputable def termsP (P : Params) : List Term → Poly × Poly
  | [] => (0, 0)
  | T :: l => termP P T + termsP P l

theorem termsGo_nil (P : Params) (f : Term → Pt) (Sp Sn : ℕ) : termsGo P f [] Sp Sn = (Sp, Sn) := rfl

theorem termsGo_cons (P : Params) (f : Term → Pt) (T : Term) (l : List Term) (Sp Sn : ℕ) :
    termsGo P f (T :: l) Sp Sn =
      termsGo P f l (Sp + (kern P (f T) T.sel T.blocks).1) (Sn + (kern P (f T) T.sel T.blocks).2) := rfl

theorem termsGo_eq (P : Params) (m : ℕ) : ∀ (l : List Term) (Sp Sn : ℕ),
    termsGo P (tpt m) l Sp Sn = (Sp + ev P (runPt m) (termsP P l).1, Sn + ev P (runPt m) (termsP P l).2)
  | [], Sp, Sn => by simp [termsGo_nil, termsP]
  | T :: l, Sp, Sn => by
    rw [termsGo_cons, termsGo_eq P m l, kern_eq]
    simp only [termsP, termP, evp, ev_tpt, Prod.fst_add, Prod.snd_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem termsGo_zero (P : Params) : ∀ (l : List Term) (Sp Sn : ℕ),
    termsGo P (fun _ => ⟨0, 0, 0⟩) l Sp Sn = (Sp + csum (termsP P l).1, Sn + csum (termsP P l).2)
  | [], Sp, Sn => by simp [termsGo_nil, termsP]
  | T :: l, Sp, Sn => by
    rw [termsGo_cons, termsGo_zero P l, kern_zero]
    simp only [termsP, termP, csum_rename, Prod.fst_add, Prod.snd_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-- The real variable with the number `s`. -/
def pick (s : ℕ) (u v t : ℝ) : ℝ := if s = 0 then u else if s = 1 then v else t

/-- The value of a term: the kernel with the three variables in the order of the term. -/
noncomputable def termR (P : Params) (T : Term) (u v t : ℝ) : ℝ :=
  evR (pick T.s0 u v t) (pick T.s1 u v t) (pick T.s2 u v t) (kernZ P T.sel T.blocks)

/-- The sum of the values of the terms. -/
noncomputable def termsR (P : Params) : List Term → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | T :: l, u, v, t => termR P T u v t + termsR P l u v t

theorem vec_fin3 (s : ℕ) (u v t : ℝ) : (![u, v, t] : Fin 3 → ℝ) (fin3 s) = pick s u v t := by
  rcases s with _ | _ | s
  · rfl
  · rfl
  · have e : fin3 (s + 1 + 1) = 2 := by simp [fin3]
    rw [e]
    simp [pick]

theorem evR_rename_tsig (T : Term) (F : PolyZ) (u v t : ℝ) :
    evR u v t (rename (tsig T) F) = evR (pick T.s0 u v t) (pick T.s1 u v t) (pick T.s2 u v t) F := by
  have e : (![u, v, t] : Fin 3 → ℝ) ∘ tsig T = ![pick T.s0 u v t, pick T.s1 u v t, pick T.s2 u v t] := by
    funext i
    fin_cases i
    · exact vec_fin3 T.s0 u v t
    · exact vec_fin3 T.s1 u v t
    · exact vec_fin3 T.s2 u v t
  unfold evR
  rw [aeval_rename, e]

theorem val_termP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (T : Term) :
    ThreePoint.val (termP P T) = rename (tsig T) (kernZ P T.sel T.blocks) := by
  rw [← val_kernP P heb hcb]
  unfold ThreePoint.val termP ThreePoint.toZ
  simp only [map_rename, map_sub]

theorem evR_termsP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (u v t : ℝ) : ∀ l : List Term,
    evR u v t (ThreePoint.val (termsP P l)) = termsR P l u v t
  | [] => by simp [termsP, termsR, val_zero]
  | T :: l => by
    rw [termsP, val_add, map_add, evR_termsP P heb hcb u v t l, val_termP P heb hcb, evR_rename_tsig]
    rfl

/-! ## The terms pass the tests -/

theorem termsOk_nil (m : ℕ) : termsOk m [] = true := rfl

theorem termsOk_cons (m : ℕ) (T : Term) (l : List Term) :
    termsOk m (T :: l) = (blocksOk m T.blocks 0 && Nat.ble T.s0 2 && Nat.ble T.s1 2 && Nat.ble T.s2 2 &&
      (Nat.blt T.s0 T.s1 || Nat.blt T.s1 T.s0) && (Nat.blt T.s0 T.s2 || Nat.blt T.s2 T.s0) &&
      (Nat.blt T.s1 T.s2 || Nat.blt T.s2 T.s1) && termsOk m l) := rfl

theorem lt_of_blt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem ne_of_blt_or {a b : ℕ} (h : (Nat.blt a b || Nat.blt b a) = true) : a ≠ b := by
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (lt_of_blt h).ne
  · exact (lt_of_blt h).ne'

/-- The numbers `0`, `1`, `2` in some order give a permutation of the variables. -/
theorem tsig_surj (T : Term) (h0 : T.s0 ≤ 2) (h1 : T.s1 ≤ 2) (h2 : T.s2 ≤ 2) (d01 : T.s0 ≠ T.s1)
    (d02 : T.s0 ≠ T.s2) (d12 : T.s1 ≠ T.s2) : Function.Injective (tsig T) := by
  obtain ⟨blocks, sel, s0, s1, s2⟩ := T
  simp only at h0 h1 h2 d01 d02 d12
  unfold tsig
  simp only
  interval_cases s0 <;> interval_cases s1 <;> interval_cases s2 <;> first | omega | decide

theorem degB_rename {σ : Fin 3 → Fin 3} (hσ : Function.Injective σ) {F : Poly} {n : ℕ} (h : DegB F n) :
    DegB (rename σ F) n := by
  intro j
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hσ j
  rw [degreeOf_rename_of_injective hσ]
  exact h i

theorem degP_termsP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (n : ℕ) : ∀ l : List Term,
    termsOk (n + 1) l = true → DegP (termsP P l) n
  | [], _ => degP_zero n
  | T :: l, h => by
    rw [termsOk_cons] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hb, h0⟩, h1⟩, h2⟩, d01⟩, d02⟩, d12⟩, hl⟩ := h
    have hσ := tsig_surj T (Nat.le_of_ble_eq_true h0) (Nat.le_of_ble_eq_true h1) (Nat.le_of_ble_eq_true h2)
      (ne_of_blt_or d01) (ne_of_blt_or d02) (ne_of_blt_or d12)
    have hk := degP_kernP P heb hcb T.sel n T.blocks hb
    rw [termsP]
    exact degP_add ⟨degB_rename hσ hk.1, degB_rename hσ hk.2⟩ (degP_termsP P heb hcb n l hl)

/-! ## Polynomials whose coefficients are the entries of an array of the layout -/

/-- The monomial `u ^ e₁ * v ^ e₂ * t ^ e₃`. -/
noncomputable def mono3 (e1 e2 e3 : ℕ) : Poly := X 0 ^ e1 * X 1 ^ e2 * X 2 ^ e3

/-- The polynomial whose coefficient of `u ^ e₁ * v ^ e₂ * t ^ e₃` is `c (e₁ + m * (e₂ + m * e₃))`. -/
noncomputable def cubeP (m : ℕ) (c : ℕ → ℕ) : Poly :=
  ∑ e3 ∈ range m, ∑ e2 ∈ range m, ∑ e1 ∈ range m, C (c (e1 + m * (e2 + m * e3))) * mono3 e1 e2 e3

theorem ev_mono3 (P : Params) (m e1 e2 e3 : ℕ) :
    ev P (runPt m) (mono3 e1 e2 e3) = 2 ^ (P.W * (e1 + m * (e2 + m * e3))) := by
  unfold ev mono3
  simp only [map_mul, map_pow, eval_X]
  show (2 ^ (P.W * 1)) ^ e1 * (2 ^ (P.W * m)) ^ e2 * (2 ^ (P.W * (m * m))) ^ e3 = _
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

theorem ev_cubeP (P : Params) (m : ℕ) (c : ℕ → ℕ) : ev P (runPt m) (cubeP m c) = packSum P.W (m * m * m) c := by
  unfold cubeP packSum
  rw [CAP.Bernstein.sum_cube m (fun p => c p * 2 ^ (P.W * p))]
  simp only [map_sum, map_mul, ev_C, ev_mono3]

theorem csum_mono3 (e1 e2 e3 : ℕ) : csum (mono3 e1 e2 e3) = 1 := by
  simp [mono3, csum_X]

theorem csum_cubeP (m : ℕ) (c : ℕ → ℕ) : csum (cubeP m c) = ∑ p ∈ range (m * m * m), c p := by
  unfold cubeP
  rw [CAP.Bernstein.sum_cube m c]
  simp only [map_sum, map_mul, csum_C, csum_mono3, mul_one]

theorem csum_cubeP_le (m : ℕ) (c : ℕ → ℕ) (B : ℕ) (h : ∀ p, p < m * m * m → c p ≤ B) :
    csum (cubeP m c) ≤ m * m * m * B := by
  rw [csum_cubeP]
  have := Finset.sum_le_card_nsmul (range (m * m * m)) c B (fun p hp => h p (mem_range.mp hp))
  rwa [card_range, smul_eq_mul] at this

theorem degB_mono3 (e1 e2 e3 d : ℕ) (h1 : e1 ≤ d) (h2 : e2 ≤ d) (h3 : e3 ≤ d) : DegB (mono3 e1 e2 e3) d := by
  intro k
  unfold mono3
  refine (degreeOf_mul_le k _ _).trans ?_
  have h12 := (degreeOf_mul_le k ((X 0 : Poly) ^ e1) (X 1 ^ e2))
  have a0 := degreeOf_X_pow_le k 0 e1
  have a1 := degreeOf_X_pow_le k 1 e2
  have a2 := degreeOf_X_pow_le k 2 e3
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl] at a0
    rw [if_neg (by decide)] at a1 a2
    omega
  · rw [if_neg hk0] at a0
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl] at a1
      rw [if_neg (by decide)] at a2
      omega
    · rw [if_neg hk1] at a1
      split_ifs at a2 <;> omega

theorem degB_cubeP (m : ℕ) (c : ℕ → ℕ) (d : ℕ) (h : m ≤ d + 1) : DegB (cubeP m c) d := by
  refine degB_sum _ _ _ fun e3 h3 => degB_sum _ _ _ fun e2 h2 => degB_sum _ _ _ fun e1 h1 => ?_
  have := mem_range.mp h1
  have := mem_range.mp h2
  have := mem_range.mp h3
  exact fun k => (degreeOf_C_mul_le _ k _).trans (degB_mono3 e1 e2 e3 d (by omega) (by omega) (by omega) k)

theorem evN_cubeP (m : ℕ) (c : ℕ → ℕ) (u v t : ℝ) :
    evN u v t (cubeP m c) = ∑ e3 ∈ range m, ∑ e2 ∈ range m, ∑ e1 ∈ range m,
      (c (e1 + m * (e2 + m * e3)) : ℝ) * (u ^ e1 * v ^ e2 * t ^ e3) := by
  unfold cubeP mono3
  simp only [map_sum, map_mul, map_pow, evN_C, evN_X0, evN_X1, evN_X2]

/-! ## Polynomials of one variable on an axis of the layout -/

/-- The polynomial `∑ d < m, c d • x_a ^ d`. -/
noncomputable def axP (a : Fin 3) (m : ℕ) (c : ℕ → ℕ) : Poly := ∑ d ∈ range m, C (c d) * X a ^ d

theorem ev_axP (P : Params) (m : ℕ) (a : Fin 3) (k : ℕ) (hk : pval P (runPt m) a = 2 ^ k) (c : ℕ → ℕ) :
    ev P (runPt m) (axP a m c) = ∑ d ∈ range m, c d * 2 ^ (k * d) := by
  unfold axP ev
  simp only [map_sum, map_mul, map_pow, eval_C, eval_X, hk, ← pow_mul]

theorem csum_axP (a : Fin 3) (m : ℕ) (c : ℕ → ℕ) : csum (axP a m c) = ∑ d ∈ range m, c d := by
  simp [axP, csum_X]

theorem csum_axP_le (a : Fin 3) (m : ℕ) (c : ℕ → ℕ) (B : ℕ) (h : ∀ d, d < m → c d ≤ B) :
    csum (axP a m c) ≤ m * B := by
  rw [csum_axP]
  have := Finset.sum_le_card_nsmul (range m) c B (fun p hp => h p (mem_range.mp hp))
  rwa [card_range, smul_eq_mul] at this

theorem degB_axP (a : Fin 3) (m : ℕ) (c : ℕ → ℕ) (d : ℕ) (h : m ≤ d + 1) : DegB (axP a m c) d := by
  refine degB_sum _ _ _ fun e he => ?_
  have := mem_range.mp he
  intro k
  refine (degreeOf_C_mul_le _ k _).trans ((degreeOf_X_pow_le k a e).trans ?_)
  split_ifs <;> omega

theorem evN_axP (a : Fin 3) (m : ℕ) (c : ℕ → ℕ) (u v t : ℝ) :
    evN u v t (axP a m c) = ∑ d ∈ range m, (c d : ℝ) * (evN u v t (X a)) ^ d := by
  unfold axP
  simp only [map_sum, map_mul, map_pow, evN_C]

theorem place_axis (wB k B m : ℕ) : N14.Box.place wB k B m = ∑ d ∈ range m, slot wB B d * 2 ^ (k * d) :=
  N14.Box.place_eq wB k B m

theorem ones_axis (k m : ℕ) (hk : 0 < k) : ones k m = ∑ d ∈ range m, (fun _ => 1) d * 2 ^ (k * d) := by
  rw [ones_eq k m hk]
  rfl

/-! ## The functions of the statement -/

/-- The polynomial whose coefficients are the slots of `PpM` minus the bias `2 ^ (aH - 1)`, in the layout with
`(n + 1) ^ 3` slots of width `W`. -/
noncomputable def mixR (W n aH PpM : ℕ) (u v t : ℝ) : ℝ :=
  ∑ e3 ∈ range (n + 1), ∑ e2 ∈ range (n + 1), ∑ e1 ∈ range (n + 1),
    ((slot W PpM (e1 + (n + 1) * (e2 + (n + 1) * e3)) : ℝ) - 2 ^ (aH - 1)) * (u ^ e1 * v ^ e2 * t ^ e3)

/-- The polynomial of one variable whose coefficients are the slots of `B` (width `wB`) minus the bias
`2 ^ (aB - 1)`, of degree at most `n`. -/
noncomputable def uniR (wB aB n B : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ range (n + 1), ((slot wB B d : ℝ) - 2 ^ (aB - 1)) * x ^ d

/-- The left side of the equation of the checker as a polynomial. -/
noncomputable def Lp (P : Params) (I : Id3) : Poly :=
  C I.cM * cubeP (I.n + 1) (slot P.W I.PpM) + C I.cK * (termsP P I.terms).1
    + C (2 ^ (I.aB - 1)) * (axP 0 (I.n + 1) (fun _ => 1) + axP 1 (I.n + 1) (fun _ => 1)
      + axP 2 (I.n + 1) (fun _ => 1)) + C I.cn

/-- The right side of the equation of the checker as a polynomial. -/
noncomputable def Rp (P : Params) (I : Id3) : Poly :=
  axP 0 (I.n + 1) (slot I.wB I.B0) + axP 1 (I.n + 1) (slot I.wB I.B1) + axP 2 (I.n + 1) (slot I.wB I.B2)
    + C I.cp + C (I.cM * 2 ^ (I.aH - 1)) * cubeP (I.n + 1) (fun _ => 1) + C I.cK * (termsP P I.terms).2

/-- What the checker of the identity of a run tests. -/
structure Facts3 (P : Params) (I : Id3) : Prop where
  hW : 1 ≤ P.W
  heb : 2 ≤ P.eb
  hcb : 1 ≤ P.cb
  haH : I.aH ≤ P.W
  haB : I.aB ≤ I.wB
  hwB : I.wB ≤ P.W
  hterms : termsOk (I.n + 1) I.terms = true
  hPpM : I.PpM < 2 ^ (P.W * ((I.n + 1) * (I.n + 1) * (I.n + 1)))
  hbits : I.PpM &&& ((2 ^ P.W - 2 ^ I.aH) * ones P.W ((I.n + 1) * (I.n + 1) * (I.n + 1))) = 0
  hL : I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1)) * 2 ^ I.aH
      + I.cK * (termsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).1 + 3 * (I.n + 1) * 2 ^ I.aB + I.cn < 2 ^ P.W
  hR : 3 * (I.n + 1) * 2 ^ I.wB + I.cp + I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1)) * 2 ^ I.aH
      + I.cK * (termsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).2 < 2 ^ P.W
  heq : I.cM * I.PpM + I.cK * (termsGo P (tpt (I.n + 1)) I.terms 0 0).1
      + 2 ^ (I.aB - 1) * (ones P.W (I.n + 1) + ones (P.W * (I.n + 1)) (I.n + 1)
        + ones (P.W * (I.n + 1) * (I.n + 1)) (I.n + 1)) + I.cn
    = N14.Box.place I.wB P.W I.B0 (I.n + 1) + N14.Box.place I.wB (P.W * (I.n + 1)) I.B1 (I.n + 1)
      + N14.Box.place I.wB (P.W * (I.n + 1) * (I.n + 1)) I.B2 (I.n + 1) + I.cp
      + I.cM * 2 ^ (I.aH - 1) * ones P.W ((I.n + 1) * (I.n + 1) * (I.n + 1))
      + I.cK * (termsGo P (tpt (I.n + 1)) I.terms 0 0).2

theorem facts3_of_ok {P : Params} {I : Id3} (h : id3Ok P I = true) : Facts3 P I := by
  have h' : (Nat.ble 1 P.W && Nat.ble 2 P.eb && Nat.ble 1 P.cb && Nat.ble 1 I.aH && Nat.ble I.aH P.W &&
      Nat.ble 1 I.aB && Nat.ble I.aB I.wB && Nat.ble I.wB P.W && termsOk (I.n + 1) I.terms &&
      Nat.blt I.PpM (1 <<< (P.W * ((I.n + 1) * (I.n + 1) * (I.n + 1)))) &&
      Nat.beq (I.PpM &&& ((1 <<< P.W - 1 <<< I.aH) * ones P.W ((I.n + 1) * (I.n + 1) * (I.n + 1)))) 0 &&
      Nat.blt (I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1)) * 1 <<< I.aH
        + I.cK * (termsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).1 + 3 * (I.n + 1) * 1 <<< I.aB + I.cn)
        (1 <<< P.W) &&
      Nat.blt (3 * (I.n + 1) * 1 <<< I.wB + I.cp + I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1)) * 1 <<< I.aH
        + I.cK * (termsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).2) (1 <<< P.W) &&
      Nat.beq (I.cM * I.PpM + I.cK * (termsGo P (tpt (I.n + 1)) I.terms 0 0).1
          + 1 <<< (I.aB - 1) * (ones P.W (I.n + 1) + ones (P.W * (I.n + 1)) (I.n + 1)
            + ones (P.W * (I.n + 1) * (I.n + 1)) (I.n + 1)) + I.cn)
        (N14.Box.place I.wB P.W I.B0 (I.n + 1) + N14.Box.place I.wB (P.W * (I.n + 1)) I.B1 (I.n + 1)
          + N14.Box.place I.wB (P.W * (I.n + 1) * (I.n + 1)) I.B2 (I.n + 1) + I.cp
          + I.cM * 1 <<< (I.aH - 1) * ones P.W ((I.n + 1) * (I.n + 1) * (I.n + 1))
          + I.cK * (termsGo P (tpt (I.n + 1)) I.terms 0 0).2)) = true := h
  simp only [Bool.and_eq_true, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, a5⟩, _⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩ := h'
  exact ⟨Nat.le_of_ble_eq_true a1, Nat.le_of_ble_eq_true a2, Nat.le_of_ble_eq_true a3,
    Nat.le_of_ble_eq_true a5, Nat.le_of_ble_eq_true a7, Nat.le_of_ble_eq_true a8, a9,
    lt_of_blt a10, Nat.eq_of_beq_eq_true a11, lt_of_blt a12,
    lt_of_blt a13, Nat.eq_of_beq_eq_true a14⟩

/-- The values of the two sides at the point of the layout are the two sides of the equation of the checker. -/
theorem ev_Lp (P : Params) (I : Id3) (F : Facts3 P I) :
    ev P (runPt (I.n + 1)) (Lp P I) = I.cM * I.PpM + I.cK * (termsGo P (tpt (I.n + 1)) I.terms 0 0).1
      + 2 ^ (I.aB - 1) * (ones P.W (I.n + 1) + ones (P.W * (I.n + 1)) (I.n + 1)
        + ones (P.W * (I.n + 1) * (I.n + 1)) (I.n + 1)) + I.cn := by
  have hW : 0 < P.W := F.hW
  have h0 : pval P (runPt (I.n + 1)) 0 = 2 ^ P.W := by simp [pval, runPt]
  have h1 : pval P (runPt (I.n + 1)) 1 = 2 ^ (P.W * (I.n + 1)) := by simp [pval, runPt]
  have h2 : pval P (runPt (I.n + 1)) 2 = 2 ^ (P.W * (I.n + 1) * (I.n + 1)) := by
    simp [pval, runPt, mul_assoc]
  unfold Lp
  simp only [map_add, map_mul, ev_C]
  rw [ev_cubeP, packSum_slot P.W _ I.PpM F.hPpM, termsGo_eq, ev_axP P _ 0 _ h0, ev_axP P _ 1 _ h1,
    ev_axP P _ 2 _ h2, ← ones_axis P.W _ hW, ← ones_axis _ _ (Nat.mul_pos hW (Nat.succ_pos _)),
    ← ones_axis _ _ (Nat.mul_pos (Nat.mul_pos hW (Nat.succ_pos _)) (Nat.succ_pos _))]
  simp only [zero_add]

theorem ev_Rp (P : Params) (I : Id3) (F : Facts3 P I) :
    ev P (runPt (I.n + 1)) (Rp P I) = N14.Box.place I.wB P.W I.B0 (I.n + 1)
      + N14.Box.place I.wB (P.W * (I.n + 1)) I.B1 (I.n + 1)
      + N14.Box.place I.wB (P.W * (I.n + 1) * (I.n + 1)) I.B2 (I.n + 1) + I.cp
      + I.cM * 2 ^ (I.aH - 1) * ones P.W ((I.n + 1) * (I.n + 1) * (I.n + 1))
      + I.cK * (termsGo P (tpt (I.n + 1)) I.terms 0 0).2 := by
  have hW : 0 < P.W := F.hW
  have h0 : pval P (runPt (I.n + 1)) 0 = 2 ^ P.W := by simp [pval, runPt]
  have h1 : pval P (runPt (I.n + 1)) 1 = 2 ^ (P.W * (I.n + 1)) := by simp [pval, runPt]
  have h2 : pval P (runPt (I.n + 1)) 2 = 2 ^ (P.W * (I.n + 1) * (I.n + 1)) := by
    simp [pval, runPt, mul_assoc]
  unfold Rp
  simp only [map_add, map_mul, ev_C]
  rw [ev_cubeP, termsGo_eq, ev_axP P _ 0 _ h0, ev_axP P _ 1 _ h1, ev_axP P _ 2 _ h2, place_axis, place_axis,
    place_axis, ones_eq P.W _ hW]
  simp only [zero_add]

/-- **Soundness of the checker of the identity of a run.** -/
theorem id3_sound (P : Params) (I : Id3) (h : id3Ok P I = true) (u v t : ℝ) :
    (I.cM : ℝ) * mixR P.W I.n I.aH I.PpM u v t + (I.cK : ℝ) * termsR P I.terms u v t
      = uniR I.wB I.aB I.n I.B0 u + uniR I.wB I.aB I.n I.B1 v + uniR I.wB I.aB I.n I.B2 t
        + ((I.cp : ℝ) - I.cn) := by
  have F := facts3_of_ok h
  have hW : 0 < P.W := F.hW
  have hz := termsGo_zero P I.terms 0 0
  simp only [zero_add] at hz
  have hdeg := degP_termsP P F.heb F.hcb I.n I.terms F.hterms
  -- the slots of `PpM` are below `2 ^ aH`
  have hslot : ∀ p, p < (I.n + 1) * (I.n + 1) * (I.n + 1) → slot P.W I.PpM p ≤ 2 ^ I.aH := by
    have hb := F.hbits
    rw [← packSum_slot P.W _ I.PpM F.hPpM, ones_eq P.W _ hW] at hb
    exact fun p hp => (slots_lt_of_and_hi P.W I.aH _ (slot P.W I.PpM) F.haH (fun j _ => slot_lt P.W I.PpM j) hb
      p hp).le
  have hpow : (2 : ℕ) ^ (I.aB - 1) ≤ 2 ^ I.aB := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hpowH : (2 : ℕ) ^ (I.aH - 1) ≤ 2 ^ I.aH := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  -- the two polynomials are equal
  have hLR : Lp P I = Rp P I := by
    refine poly_eq_of_ev P.W (I.n + 1) _ _ ?_ ?_ ?_ ?_ ?_
    · refine support_lt_of_degB ?_
      unfold Lp
      refine degB_add (degB_add (degB_add ?_ ?_) ?_) ?_
      · exact fun k => (degreeOf_C_mul_le _ k _).trans (degB_cubeP _ _ I.n (le_refl _) k)
      · exact fun k => (degreeOf_C_mul_le _ k _).trans (hdeg.1 k)
      · exact fun k => (degreeOf_C_mul_le _ k _).trans
          (degB_add (degB_add (degB_axP 0 _ _ I.n (le_refl _)) (degB_axP 1 _ _ I.n (le_refl _)))
            (degB_axP 2 _ _ I.n (le_refl _)) k)
      · exact fun k => by rw [degreeOf_C]; exact Nat.zero_le _
    · refine support_lt_of_degB ?_
      unfold Rp
      refine degB_add (degB_add (degB_add (degB_add (degB_add ?_ ?_) ?_) ?_) ?_) ?_
      · exact degB_axP 0 _ _ I.n (le_refl _)
      · exact degB_axP 1 _ _ I.n (le_refl _)
      · exact degB_axP 2 _ _ I.n (le_refl _)
      · exact fun k => by rw [degreeOf_C]; exact Nat.zero_le _
      · exact fun k => (degreeOf_C_mul_le _ k _).trans (degB_cubeP _ _ I.n (le_refl _) k)
      · exact fun k => (degreeOf_C_mul_le _ k _).trans (hdeg.2 k)
    · have c1 := csum_cubeP_le (I.n + 1) (slot P.W I.PpM) (2 ^ I.aH) hslot
      have c2 : csum (axP 0 (I.n + 1) (fun _ => 1)) ≤ (I.n + 1) * 1 := csum_axP_le 0 _ _ 1 (fun _ _ => le_refl 1)
      have c3 : csum (axP 1 (I.n + 1) (fun _ => 1)) ≤ (I.n + 1) * 1 := csum_axP_le 1 _ _ 1 (fun _ _ => le_refl 1)
      have c4 : csum (axP 2 (I.n + 1) (fun _ => 1)) ≤ (I.n + 1) * 1 := csum_axP_le 2 _ _ 1 (fun _ _ => le_refl 1)
      have hL := F.hL
      rw [hz] at hL
      unfold Lp
      simp only [map_add, map_mul, csum_C]
      calc I.cM * csum (cubeP (I.n + 1) (slot P.W I.PpM)) + I.cK * csum (termsP P I.terms).1
            + 2 ^ (I.aB - 1) * (csum (axP 0 (I.n + 1) (fun _ => 1)) + csum (axP 1 (I.n + 1) (fun _ => 1))
              + csum (axP 2 (I.n + 1) (fun _ => 1))) + I.cn
          ≤ I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1) * 2 ^ I.aH) + I.cK * csum (termsP P I.terms).1
            + 2 ^ I.aB * ((I.n + 1) * 1 + (I.n + 1) * 1 + (I.n + 1) * 1) + I.cn := by
            gcongr
        _ = I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1)) * 2 ^ I.aH + I.cK * csum (termsP P I.terms).1
            + 3 * (I.n + 1) * 2 ^ I.aB + I.cn := by ring
        _ < 2 ^ P.W := hL
    · have c1 := csum_cubeP_le (I.n + 1) (fun _ => 1) 1 (fun _ _ => le_refl 1)
      have c2 := csum_axP_le 0 (I.n + 1) (slot I.wB I.B0) (2 ^ I.wB) (fun d _ => (slot_lt I.wB I.B0 d).le)
      have c3 := csum_axP_le 1 (I.n + 1) (slot I.wB I.B1) (2 ^ I.wB) (fun d _ => (slot_lt I.wB I.B1 d).le)
      have c4 := csum_axP_le 2 (I.n + 1) (slot I.wB I.B2) (2 ^ I.wB) (fun d _ => (slot_lt I.wB I.B2 d).le)
      have hR := F.hR
      rw [hz] at hR
      unfold Rp
      simp only [map_add, map_mul, csum_C]
      calc csum (axP 0 (I.n + 1) (slot I.wB I.B0)) + csum (axP 1 (I.n + 1) (slot I.wB I.B1))
            + csum (axP 2 (I.n + 1) (slot I.wB I.B2)) + I.cp
            + I.cM * 2 ^ (I.aH - 1) * csum (cubeP (I.n + 1) (fun _ => 1)) + I.cK * csum (termsP P I.terms).2
          ≤ (I.n + 1) * 2 ^ I.wB + (I.n + 1) * 2 ^ I.wB + (I.n + 1) * 2 ^ I.wB + I.cp
            + I.cM * 2 ^ I.aH * ((I.n + 1) * (I.n + 1) * (I.n + 1) * 1) + I.cK * csum (termsP P I.terms).2 := by
            gcongr
        _ = 3 * (I.n + 1) * 2 ^ I.wB + I.cp + I.cM * ((I.n + 1) * (I.n + 1) * (I.n + 1)) * 2 ^ I.aH
            + I.cK * csum (termsP P I.terms).2 := by ring
        _ < 2 ^ P.W := hR
    · rw [← ev_runPt, ← ev_runPt, ev_Lp P I F, ev_Rp P I F]
      exact F.heq
  -- values at the real point
  have hv := congrArg (evN u v t) hLR
  unfold Lp Rp at hv
  simp only [map_add, map_mul, evN_C, evN_cubeP, evN_axP, evN_X0, evN_X1, evN_X2] at hv
  have ht := evN_sub u v t (termsP P I.terms)
  rw [evR_termsP P F.heb F.hcb u v t I.terms] at ht
  unfold mixR uniR
  simp only [sub_mul, sum_sub_distrib]
  simp only [← mul_sum] at hv ⊢
  push_cast at hv
  linear_combination hv - (I.cK : ℝ) * ht

end N14.Ident
