module

public import CAP.Schema.ThreePoint.Sound
public import N14.Ident.Sound3

/-!
# T7, the energy identity: soundness of the checker of the identity of a pair

**Theorem** (`id1_sound`). If `id1Ok P I = true`, then for all real `s`

  `∑ c, m_c * (3 * (- cM * Ĥ_c (s) + c1 * B_c (s)) + c1 * (cp_c - cn_c)) + 6 * c1 * cK * ∑ terms (s) = kp - kn`,

where the sum runs over the shares of `I` (`sharesR`), `Ĥ_c` is the polynomial of the table of the share (`hR`:
for the table of a run it is `CAP.UniPos.hEval`), `B_c` its polynomial of one variable (`uniR`), and a term is a
kernel at `(s, s, 1)`, `(s, 1, s)` or `(1, s, s)` (`dtermR`). Moreover `∑ c, m_c * Dn_c = fS` (`id1_dn`).

The proof is that of `id3_sound`, with polynomials of the variable `u` at the Kronecker point of
`CAP.ThreePoint` (`q = 2 * n + 1`): a kernel at `(s, s, 1)` is the substitution `sub1` of `CAP.ThreePoint`, and so
on, and the exponents are bounded through the total degree.
-/

@[expose] public section

namespace N14.Ident

open CAP CAP.ThreePoint MvPolynomial Finset

/-! ## The terms -/

/-- The substitution of a term: `(u, u, 1)`, `(u, 1, u)` or `(1, u, u)`. -/
noncomputable def dsub (T : DTerm) : Poly →ₐ[ℕ] Poly :=
  if T.pos = 0 then sub1 else if T.pos = 1 then sub2 else sub3

theorem ev_dpt (P : Params) (T : DTerm) (F : Poly) : ev P (dpt T) F = ev P (mainPt P) (dsub T F) := by
  obtain ⟨blocks, sel, pos⟩ := T
  rcases pos with _ | _ | pos
  · exact (ev_sub1 P F).symm
  · exact (ev_sub2 P F).symm
  · have e : dsub ⟨blocks, sel, pos + 1 + 1⟩ = sub3 := by simp [dsub]
    rw [e]
    exact (ev_sub3 P F).symm

theorem csum_dsub (T : DTerm) (F : Poly) : csum (dsub T F) = csum F := by
  unfold dsub
  split_ifs
  · exact csum_sub1 F
  · exact csum_sub2 F
  · exact csum_sub3 F

theorem deg_dsub (T : DTerm) (F : Poly) : (dsub T F).totalDegree ≤ F.totalDegree := by
  unfold dsub
  split_ifs
  · exact deg_sub1 F
  · exact deg_sub2 F
  · exact deg_sub3 F

/-- The pair of a term. -/
noncomputable def dtermP (P : Params) (T : DTerm) : Poly × Poly :=
  (dsub T (kernP P T.sel T.blocks).1, dsub T (kernP P T.sel T.blocks).2)

/-- The pair of the sum of the terms. -/
noncomputable def dtermsP (P : Params) : List DTerm → Poly × Poly
  | [] => (0, 0)
  | T :: l => dtermP P T + dtermsP P l

theorem dtermsGo_nil (P : Params) (f : DTerm → Pt) (Sp Sn : ℕ) : dtermsGo P f [] Sp Sn = (Sp, Sn) := rfl

theorem dtermsGo_cons (P : Params) (f : DTerm → Pt) (T : DTerm) (l : List DTerm) (Sp Sn : ℕ) :
    dtermsGo P f (T :: l) Sp Sn =
      dtermsGo P f l (Sp + (kern P (f T) T.sel T.blocks).1) (Sn + (kern P (f T) T.sel T.blocks).2) := rfl

theorem dtermsGo_eq (P : Params) : ∀ (l : List DTerm) (Sp Sn : ℕ),
    dtermsGo P dpt l Sp Sn = (Sp + ev P (mainPt P) (dtermsP P l).1, Sn + ev P (mainPt P) (dtermsP P l).2)
  | [], Sp, Sn => by simp [dtermsGo_nil, dtermsP]
  | T :: l, Sp, Sn => by
    rw [dtermsGo_cons, dtermsGo_eq P l, kern_eq]
    simp only [dtermsP, dtermP, evp, ev_dpt, Prod.fst_add, Prod.snd_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem dtermsGo_zero (P : Params) : ∀ (l : List DTerm) (Sp Sn : ℕ),
    dtermsGo P (fun _ => ⟨0, 0, 0⟩) l Sp Sn = (Sp + csum (dtermsP P l).1, Sn + csum (dtermsP P l).2)
  | [], Sp, Sn => by simp [dtermsGo_nil, dtermsP]
  | T :: l, Sp, Sn => by
    rw [dtermsGo_cons, dtermsGo_zero P l, kern_zero]
    simp only [dtermsP, dtermP, csum_dsub, Prod.fst_add, Prod.snd_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-- The value of a term: the kernel at `(s, s, 1)`, `(s, 1, s)` or `(1, s, s)`. -/
noncomputable def dtermR (P : Params) (T : DTerm) (s : ℝ) : ℝ :=
  if T.pos = 0 then evR s s 1 (kernZ P T.sel T.blocks)
  else if T.pos = 1 then evR s 1 s (kernZ P T.sel T.blocks)
  else evR 1 s s (kernZ P T.sel T.blocks)

/-- The sum of the values of the terms. -/
noncomputable def dtermsR (P : Params) : List DTerm → ℝ → ℝ
  | [], _ => 0
  | T :: l, s => dtermR P T s + dtermsR P l s

theorem evR_val_dtermP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (T : DTerm) (s v t : ℝ) :
    evR s v t (ThreePoint.val (dtermP P T)) = dtermR P T s := by
  have hk := val_kernP P heb hcb T.sel T.blocks
  unfold dtermR dtermP dsub ThreePoint.val
  split_ifs
  · rw [toZ_sub1, toZ_sub1, ← map_sub, evR_s1Z]
    exact congrArg _ hk
  · rw [toZ_sub2, toZ_sub2, ← map_sub, evR_s2Z]
    exact congrArg _ hk
  · rw [toZ_sub3, toZ_sub3, ← map_sub, evR_s3Z]
    exact congrArg _ hk

theorem evR_dtermsP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (s v t : ℝ) : ∀ l : List DTerm,
    evR s v t (ThreePoint.val (dtermsP P l)) = dtermsR P l s
  | [] => by simp [dtermsP, dtermsR, val_zero]
  | T :: l => by
    rw [dtermsP, val_add, map_add, evR_dtermsP P heb hcb s v t l, evR_val_dtermP P heb hcb]
    rfl

theorem dtermsOk_cons (m : ℕ) (T : DTerm) (l : List DTerm) :
    dtermsOk m (T :: l) = (blocksOk m T.blocks 0 && dtermsOk m l) := rfl

theorem degLe_dtermsP (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) (n : ℕ) : ∀ l : List DTerm,
    dtermsOk (n + 1) l = true → degLe (dtermsP P l) (2 * n)
  | [], _ => degLe_zero _
  | T :: l, h => by
    rw [dtermsOk_cons, Bool.and_eq_true] at h
    have hk := degLe_kernP P heb hcb T.sel n T.blocks h.1
    rw [dtermsP]
    exact degLe_add ⟨(deg_dsub T _).trans hk.1, (deg_dsub T _).trans hk.2⟩ (degLe_dtermsP P heb hcb n l h.2)

/-! ## The shares -/

/-- The polynomial `Ĥ` of the table of a share. -/
noncomputable def hR (S : Share) (s : ℝ) : ℝ :=
  ∑ d ∈ range (2 * S.Dt + 1), ((slot S.Wt S.K d : ℝ) - 2 ^ (S.aHt - 1)) * s ^ d

/-- The sum of the shares, without the Coulomb terms and with the factor `c1`. -/
noncomputable def sharesR (I : Id1) : List Share → ℝ → ℝ
  | [], _ => 0
  | S :: l, s => 3 * (S.mult : ℝ) * (-(I.cM : ℝ) * hR S s + (I.c1 : ℝ) * uniR I.wB I.aB I.n S.B s)
      + (S.mult : ℝ) * ((I.c1 : ℝ) * ((S.cp : ℝ) - S.cn)) + sharesR I l s

/-- The sum of the numerators of the Coulomb terms of the shares, with their multiplicities. -/
def sharesDn : List Share → ℕ
  | [] => 0
  | S :: l => S.mult * S.Dn + sharesDn l

/-- The positive part of the shares as a polynomial of `u`. -/
noncomputable def sharesLp (I : Id1) : List Share → Poly
  | [] => 0
  | S :: l => C (3 * S.mult) * (C (I.cM * 2 ^ (S.aHt - 1)) * uPoly (2 * S.Dt + 1) (fun _ => 1)
      + C I.c1 * uPoly (I.n + 1) (slot I.wB S.B)) + C (S.mult * (I.c1 * S.cp)) + sharesLp I l

/-- The negative part of the shares as a polynomial of `u`. -/
noncomputable def sharesRp (I : Id1) : List Share → Poly
  | [] => 0
  | S :: l => C (3 * S.mult) * (C I.cM * uPoly (2 * S.Dt + 1) (slot S.Wt S.K)
      + C (I.c1 * 2 ^ (I.aB - 1)) * uPoly (I.n + 1) (fun _ => 1)) + C (S.mult * (I.c1 * S.cn)) + sharesRp I l

theorem sharesGo_nil (P : Params) (I : Id1) (p q d : ℕ) : sharesGo P I [] p q d = (p, q, d) := rfl

theorem sharesGo_cons (P : Params) (I : Id1) (S : Share) (l : List Share) (p q d : ℕ) :
    sharesGo P I (S :: l) p q d =
      sharesGo P I l
        (p + 3 * S.mult * (I.cM * 1 <<< (S.aHt - 1) * ones P.W (2 * S.Dt + 1)
          + I.c1 * N14.Box.place I.wB P.W S.B (I.n + 1)) + S.mult * (I.c1 * S.cp))
        (q + 3 * S.mult * (I.cM * N14.Box.place S.Wt P.W S.K (2 * S.Dt + 1)
          + I.c1 * 1 <<< (I.aB - 1) * ones P.W (I.n + 1)) + S.mult * (I.c1 * S.cn))
        (d + S.mult * S.Dn) := rfl

theorem ev_uPoly_place (P : Params) (w q B : ℕ) :
    ev P (mainPt P) (uPoly q (slot w B)) = N14.Box.place w P.W B q := by
  rw [ev_uPoly, N14.Box.place_eq]
  rfl

theorem ev_uPoly_ones (P : Params) (hW : 0 < P.W) (q : ℕ) :
    ev P (mainPt P) (uPoly q (fun _ => 1)) = ones P.W q := by
  rw [ev_uPoly, ones_eq P.W q hW]

theorem sharesGo_eq (P : Params) (hW : 0 < P.W) (I : Id1) : ∀ (l : List Share) (p q d : ℕ),
    sharesGo P I l p q d
      = (p + ev P (mainPt P) (sharesLp I l), q + ev P (mainPt P) (sharesRp I l), d + sharesDn l)
  | [], p, q, d => by simp [sharesGo_nil, sharesLp, sharesRp, sharesDn]
  | S :: l, p, q, d => by
    rw [sharesGo_cons, sharesGo_eq P hW I l]
    simp only [sharesLp, sharesRp, sharesDn, map_add, map_mul, ev_C, ev_uPoly_place, ev_uPoly_ones P hW,
      Nat.one_shiftLeft]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem sharesBd_nil (I : Id1) (p q : ℕ) : sharesBd I [] p q = (p, q) := rfl

theorem sharesBd_cons (I : Id1) (S : Share) (l : List Share) (p q : ℕ) :
    sharesBd I (S :: l) p q =
      sharesBd I l
        (p + 3 * S.mult * (I.cM * (2 * S.Dt + 1) * 1 <<< S.aHt + I.c1 * (I.n + 1) * 1 <<< I.wB)
          + S.mult * (I.c1 * S.cp))
        (q + 3 * S.mult * (I.cM * (2 * S.Dt + 1) * 1 <<< S.Wt + I.c1 * (I.n + 1) * 1 <<< I.aB)
          + S.mult * (I.c1 * S.cn)) :=
  rfl

theorem csum_uPoly_le (q : ℕ) (c : ℕ → ℕ) (B : ℕ) (h : ∀ d, d < q → c d ≤ B) : csum (uPoly q c) ≤ q * B := by
  rw [csum_uPoly]
  have := Finset.sum_le_card_nsmul (range q) c B (fun p hp => h p (mem_range.mp hp))
  rwa [card_range, smul_eq_mul] at this

/-- The sums of the coefficients of the two parts of the shares are at most the bounds of the checker. -/
theorem sharesBd_le (I : Id1) : ∀ (l : List Share) (p q : ℕ),
    p + csum (sharesLp I l) ≤ (sharesBd I l p q).1 ∧ q + csum (sharesRp I l) ≤ (sharesBd I l p q).2
  | [], p, q => by simp [sharesBd_nil, sharesLp, sharesRp]
  | S :: l, p, q => by
    rw [sharesBd_cons]
    obtain ⟨h1, h2⟩ := sharesBd_le I l
      (p + 3 * S.mult * (I.cM * (2 * S.Dt + 1) * 1 <<< S.aHt + I.c1 * (I.n + 1) * 1 <<< I.wB)
        + S.mult * (I.c1 * S.cp))
      (q + 3 * S.mult * (I.cM * (2 * S.Dt + 1) * 1 <<< S.Wt + I.c1 * (I.n + 1) * 1 <<< I.aB)
        + S.mult * (I.c1 * S.cn))
    have a1 := csum_uPoly_le (2 * S.Dt + 1) (fun _ => 1) 1 (fun _ _ => le_refl 1)
    have a2 := csum_uPoly_le (I.n + 1) (slot I.wB S.B) (2 ^ I.wB) (fun d _ => (slot_lt I.wB S.B d).le)
    have a3 := csum_uPoly_le (2 * S.Dt + 1) (slot S.Wt S.K) (2 ^ S.Wt) (fun d _ => (slot_lt S.Wt S.K d).le)
    have a4 := csum_uPoly_le (I.n + 1) (fun _ => 1) 1 (fun _ _ => le_refl 1)
    have hpH : (2 : ℕ) ^ (S.aHt - 1) ≤ 2 ^ S.aHt := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have hpB : (2 : ℕ) ^ (I.aB - 1) ≤ 2 ^ I.aB := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    refine ⟨le_trans ?_ h1, le_trans ?_ h2⟩
    · simp only [sharesLp, map_add, map_mul, csum_C, Nat.one_shiftLeft]
      calc p + (3 * S.mult * (I.cM * 2 ^ (S.aHt - 1) * csum (uPoly (2 * S.Dt + 1) fun _ => 1)
              + I.c1 * csum (uPoly (I.n + 1) (slot I.wB S.B))) + S.mult * (I.c1 * S.cp) + csum (sharesLp I l))
          ≤ p + (3 * S.mult * (I.cM * 2 ^ S.aHt * ((2 * S.Dt + 1) * 1)
              + I.c1 * ((I.n + 1) * 2 ^ I.wB)) + S.mult * (I.c1 * S.cp) + csum (sharesLp I l)) := by gcongr
        _ = p + 3 * S.mult * (I.cM * (2 * S.Dt + 1) * 2 ^ S.aHt + I.c1 * (I.n + 1) * 2 ^ I.wB)
              + S.mult * (I.c1 * S.cp) + csum (sharesLp I l) := by ring
    · simp only [sharesRp, map_add, map_mul, csum_C, Nat.one_shiftLeft]
      calc q + (3 * S.mult * (I.cM * csum (uPoly (2 * S.Dt + 1) (slot S.Wt S.K))
              + I.c1 * 2 ^ (I.aB - 1) * csum (uPoly (I.n + 1) fun _ => 1)) + S.mult * (I.c1 * S.cn)
              + csum (sharesRp I l))
          ≤ q + (3 * S.mult * (I.cM * ((2 * S.Dt + 1) * 2 ^ S.Wt)
              + I.c1 * 2 ^ I.aB * ((I.n + 1) * 1)) + S.mult * (I.c1 * S.cn) + csum (sharesRp I l)) := by gcongr
        _ = q + 3 * S.mult * (I.cM * (2 * S.Dt + 1) * 2 ^ S.Wt + I.c1 * (I.n + 1) * 2 ^ I.aB)
              + S.mult * (I.c1 * S.cn) + csum (sharesRp I l) := by ring

theorem sharesOk_cons (P : Params) (I : Id1) (S : Share) (l : List Share) :
    sharesOk P I (S :: l) = (Nat.ble 1 S.aHt && Nat.ble S.aHt S.Wt && Nat.ble S.Wt P.W && Nat.ble S.Dt I.n
      && sharesOk P I l) := rfl

theorem totalDegree_C_mul_le' (c : ℕ) (F : Poly) : (C c * F).totalDegree ≤ F.totalDegree :=
  totalDegree_C_mul_le c F

/-- The two parts of the shares have total degree at most `2 * n`. -/
theorem deg_shares (P : Params) (I : Id1) : ∀ l : List Share, sharesOk P I l = true →
    (sharesLp I l).totalDegree ≤ 2 * I.n ∧ (sharesRp I l).totalDegree ≤ 2 * I.n
  | [], _ => by simp [sharesLp, sharesRp]
  | S :: l, h => by
    rw [sharesOk_cons] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, hD⟩, hl⟩ := h
    have hD' := Nat.le_of_ble_eq_true hD
    obtain ⟨h1, h2⟩ := deg_shares P I l hl
    have u1 : (uPoly (2 * S.Dt + 1) fun _ => 1).totalDegree ≤ 2 * I.n :=
      (totalDegree_uPoly _ _).trans (by omega)
    have u2 : (uPoly (I.n + 1) (slot I.wB S.B)).totalDegree ≤ 2 * I.n :=
      (totalDegree_uPoly _ _).trans (by omega)
    have u3 : (uPoly (2 * S.Dt + 1) (slot S.Wt S.K)).totalDegree ≤ 2 * I.n :=
      (totalDegree_uPoly _ _).trans (by omega)
    have u4 : (uPoly (I.n + 1) fun _ => 1).totalDegree ≤ 2 * I.n :=
      (totalDegree_uPoly _ _).trans (by omega)
    have hC : ∀ c : ℕ, (C c : Poly).totalDegree ≤ 2 * I.n := fun c => by
      rw [totalDegree_C]
      exact Nat.zero_le _
    refine ⟨?_, ?_⟩
    · rw [sharesLp]
      refine deg_add_le (deg_add_le ((totalDegree_C_mul_le _ _).trans ?_) (hC _)) h1
      exact deg_add_le ((totalDegree_C_mul_le _ _).trans u1) ((totalDegree_C_mul_le _ _).trans u2)
    · rw [sharesRp]
      refine deg_add_le (deg_add_le ((totalDegree_C_mul_le _ _).trans ?_) (hC _)) h2
      exact deg_add_le ((totalDegree_C_mul_le _ _).trans u3) ((totalDegree_C_mul_le _ _).trans u4)

theorem evN_uPoly (q : ℕ) (c : ℕ → ℕ) (u v t : ℝ) :
    evN u v t (uPoly q c) = ∑ d ∈ range q, (c d : ℝ) * u ^ d := by
  unfold uPoly
  simp only [map_sum, map_mul, map_pow, evN_C, evN_X0]

theorem evN_shares (I : Id1) (s v t : ℝ) : ∀ l : List Share,
    evN s v t (sharesLp I l) - evN s v t (sharesRp I l) = sharesR I l s
  | [] => by simp [sharesLp, sharesRp, sharesR]
  | S :: l => by
    have ih := evN_shares I s v t l
    simp only [sharesLp, sharesRp, sharesR, map_add, map_mul, evN_C, evN_uPoly]
    unfold hR uniR
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
    push_cast
    linear_combination ih

/-! ## The theorem -/

/-- The left side of the equation of the checker as a polynomial. -/
noncomputable def Lp1 (P : Params) (I : Id1) : Poly :=
  sharesLp I I.shares + C (6 * I.c1 * I.cK) * (dtermsP P I.terms).1 + C I.kn

/-- The right side of the equation of the checker as a polynomial. -/
noncomputable def Rp1 (P : Params) (I : Id1) : Poly :=
  sharesRp I I.shares + C (6 * I.c1 * I.cK) * (dtermsP P I.terms).2 + C I.kp

/-- What the checker of the identity of a pair tests. -/
structure Facts1 (P : Params) (I : Id1) : Prop where
  hW : 1 ≤ P.W
  heb : 2 ≤ P.eb
  hcb : 1 ≤ P.cb
  hD : P.D = I.n
  hterms : dtermsOk (I.n + 1) I.terms = true
  hshares : sharesOk P I I.shares = true
  hL : (sharesBd I I.shares 0 0).1 + 6 * I.c1 * I.cK * (dtermsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).1 + I.kn
      < 2 ^ P.W
  hR : (sharesBd I I.shares 0 0).2 + 6 * I.c1 * I.cK * (dtermsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).2 + I.kp
      < 2 ^ P.W
  heq : (sharesGo P I I.shares 0 0 0).1 + 6 * I.c1 * I.cK * (dtermsGo P dpt I.terms 0 0).1 + I.kn
      = (sharesGo P I I.shares 0 0 0).2.1 + 6 * I.c1 * I.cK * (dtermsGo P dpt I.terms 0 0).2 + I.kp
  hdn : (sharesGo P I I.shares 0 0 0).2.2 = I.fS

theorem facts1_of_ok {P : Params} {I : Id1} (h : id1Ok P I = true) : Facts1 P I := by
  have h' : (Nat.ble 1 P.W && Nat.ble 2 P.eb && Nat.ble 1 P.cb && Nat.beq P.D I.n &&
      Nat.ble 1 I.aB && Nat.ble I.aB I.wB && Nat.ble I.wB P.W &&
      dtermsOk (I.n + 1) I.terms && sharesOk P I I.shares &&
      Nat.blt ((sharesBd I I.shares 0 0).1
        + 6 * I.c1 * I.cK * (dtermsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).1 + I.kn) (1 <<< P.W) &&
      Nat.blt ((sharesBd I I.shares 0 0).2
        + 6 * I.c1 * I.cK * (dtermsGo P (fun _ => ⟨0, 0, 0⟩) I.terms 0 0).2 + I.kp) (1 <<< P.W) &&
      Nat.beq ((sharesGo P I I.shares 0 0 0).1 + 6 * I.c1 * I.cK * (dtermsGo P dpt I.terms 0 0).1 + I.kn)
        ((sharesGo P I I.shares 0 0 0).2.1 + 6 * I.c1 * I.cK * (dtermsGo P dpt I.terms 0 0).2 + I.kp) &&
      Nat.beq (sharesGo P I I.shares 0 0 0).2.2 I.fS) = true := h
  simp only [Bool.and_eq_true, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, _⟩, _⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩ := h'
  exact ⟨Nat.le_of_ble_eq_true a1, Nat.le_of_ble_eq_true a2, Nat.le_of_ble_eq_true a3,
    Nat.eq_of_beq_eq_true a4, a8, a9, lt_of_blt a10, lt_of_blt a11, Nat.eq_of_beq_eq_true a12,
    Nat.eq_of_beq_eq_true a13⟩

/-- The sum of the numerators of the Coulomb terms. -/
theorem id1_dn (P : Params) (I : Id1) (h : id1Ok P I = true) : sharesDn I.shares = I.fS := by
  have F := facts1_of_ok h
  have hd := F.hdn
  rw [sharesGo_eq P F.hW I] at hd
  simpa using hd

/-- **Soundness of the checker of the identity of a pair.** -/
theorem id1_sound (P : Params) (I : Id1) (h : id1Ok P I = true) (s : ℝ) :
    sharesR I I.shares s + 6 * (I.c1 : ℝ) * I.cK * dtermsR P I.terms s = (I.kp : ℝ) - I.kn := by
  have F := facts1_of_ok h
  have hW : 0 < P.W := F.hW
  have hq : qOf P = 2 * I.n + 1 := by
    unfold qOf
    rw [F.hD]
  have hz := dtermsGo_zero P I.terms 0 0
  simp only [zero_add] at hz
  have hdt := degLe_dtermsP P F.heb F.hcb I.n I.terms F.hterms
  have hds := deg_shares P I I.shares F.hshares
  have hbd := sharesBd_le I I.shares 0 0
  simp only [zero_add] at hbd
  have hC : ∀ c : ℕ, (C c : Poly).totalDegree ≤ 2 * I.n := fun c => by
    rw [totalDegree_C]
    exact Nat.zero_le _
  have hLR : Lp1 P I = Rp1 P I := by
    refine poly_eq_of_ev P.W (qOf P) _ _ ?_ ?_ ?_ ?_ ?_
    · intro m hm i
      have hdeg : (Lp1 P I).totalDegree ≤ 2 * I.n :=
        deg_add_le (deg_add_le hds.1 ((totalDegree_C_mul_le _ _).trans hdt.1)) (hC _)
      have := exponent_le (Lp1 P I) hdeg m hm i
      omega
    · intro m hm i
      have hdeg : (Rp1 P I).totalDegree ≤ 2 * I.n :=
        deg_add_le (deg_add_le hds.2 ((totalDegree_C_mul_le _ _).trans hdt.2)) (hC _)
      have := exponent_le (Rp1 P I) hdeg m hm i
      omega
    · have hL := F.hL
      rw [hz] at hL
      unfold Lp1
      simp only [map_add, map_mul, csum_C]
      exact lt_of_le_of_lt (by gcongr; exact hbd.1) hL
    · have hR := F.hR
      rw [hz] at hR
      unfold Rp1
      simp only [map_add, map_mul, csum_C]
      exact lt_of_le_of_lt (by gcongr; exact hbd.2) hR
    · rw [← ev_main, ← ev_main]
      have he := F.heq
      rw [sharesGo_eq P hW I, dtermsGo_eq] at he
      simp only [zero_add] at he
      unfold Lp1 Rp1
      simp only [map_add, map_mul, ev_C]
      exact he
  have hv := congrArg (evN s 0 0) hLR
  unfold Lp1 Rp1 at hv
  simp only [map_add, map_mul, evN_C] at hv
  have ht := evN_sub s 0 0 (dtermsP P I.terms)
  rw [evR_dtermsP P F.heb F.hcb s 0 0 I.terms] at ht
  have hs := evN_shares I s 0 0 I.shares
  push_cast at hv
  linear_combination hv - hs - 6 * (I.c1 : ℝ) * I.cK * ht

end N14.Ident
