module

public import CAP.Schema.ThreePoint.Digits

/-!
# Schema S2, soundness: from the checker to the sums over the permutations

The checker forms two numbers `kZp` and `kZn`. They are the values, at the Kronecker point, of
the polynomials `ZpP` and `ZnP` with natural coefficients (`ev_ZpP`, `ev_ZnP`); the polynomial
`Z` of the statement is their difference. If the checker accepts, then

* both polynomials have total degree at most `2 * D`, hence all exponents are below `q`;
* the sum of the coefficients of each of them is at most the bound of the checker, which is
  below `2 ^ (W - 1)`;
* hence the digits that the loops add are the coefficients, and for all `x`, `y`, `z` the sums of
  the coefficients of `ZpP` and of `ZnP` over the six permutations of `(x, y, z)` agree
  (`check_orbits`).
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-! ## The numbers of the checker -/

/-- `q = 2 * D + 1` -/
def qOf (P : Params) : ℕ := 2 * P.D + 1

/-- The Kronecker point. -/
def mainPt (P : Params) : Pt := ⟨1, qOf P, qOf P * qOf P⟩

theorem pval_main (P : Params) : pval P (mainPt P) = kpt P.W (qOf P) := by
  unfold pval mainPt kpt
  rw [mul_one]

theorem ev_main (P : Params) (F : Poly) : ev P (mainPt P) F = eval (kpt P.W (qOf P)) F := by
  unfold ev
  rw [pval_main]

/-- The result of `sosAll` in `check`. -/
noncomputable def kA (P : Params) (mrows : List ℕ) (sos : List Sos) : ℕ × ℕ × ℕ × Bool :=
  sosAll P (mainPt P) sos (9 * (P.N - 2) * (moment P (mainPt P) mrows).1)
    (9 * (P.N - 2) * (moment P (mainPt P) mrows).2.1)
    (9 * (P.N - 2) * ((moment P ⟨0, 0, 0⟩ mrows).1 + (moment P ⟨0, 0, 0⟩ mrows).2.1))
    (moment P (mainPt P) mrows).2.2

/-- The number `Zp` of `check`. -/
noncomputable def kZp (P : Params) (mrows : List ℕ) (sos : List Sos) (cp : ℕ) : ℕ :=
  (P.N - 1) * (kA P mrows sos).1
    + 9 * (P.N - 1) * ((moment P ⟨1, 1, 0⟩ mrows).1 + (moment P ⟨1, 0, 1⟩ mrows).1
      + (moment P ⟨0, 1, 1⟩ mrows).1)
    + 9 * (phiEval P ⟨0, 0, 0⟩ (P.D + 1) (hdNat mrows)).1
    + 9 * (P.N - 1) * (1 <<< (P.aH - 1)) * ones P.W (qOf P)
    + 9 * (P.N - 1) * cp

/-- The number `Zn` of `check`. -/
noncomputable def kZn (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp : ℕ) : ℕ :=
  (P.N - 1) * (kA P mrows sos).2.1
    + 9 * (P.N - 1) * ((moment P ⟨1, 1, 0⟩ mrows).2.1 + (moment P ⟨1, 0, 1⟩ mrows).2.1
      + (moment P ⟨0, 1, 1⟩ mrows).2.1)
    + 9 * (phiEval P ⟨0, 0, 0⟩ (P.D + 1) (hdNat mrows)).2.1
    + 9 * (P.N - 1) * Hp

/-- The number `bound` of `check`. -/
noncomputable def kBound (P : Params) (mrows : List ℕ) (sos : List Sos) : ℕ :=
  (P.N - 1) * (kA P mrows sos).2.2.1
    + 27 * (P.N - 1) * ((moment P ⟨0, 0, 0⟩ mrows).1 + (moment P ⟨0, 0, 0⟩ mrows).2.1)
    + 9 * ((phiEval P ⟨0, 0, 0⟩ (P.D + 1) (hdNat mrows)).1
      + (phiEval P ⟨0, 0, 0⟩ (P.D + 1) (hdNat mrows)).2.1)
    + 9 * (P.N - 1) * (qOf P + 1) * (1 <<< P.aH)

theorem check_eq (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ) :
    check P mrows sos Hp cp =
      (Nat.ble 3 P.N && Nat.blt (qOf P) (1 <<< P.eb) && Nat.ble P.a P.w && Nat.ble 1 P.a && Nat.ble 1 P.aH &&
        Nat.ble 2 P.eb && Nat.ble 1 P.cb &&
        Nat.beq (Hp >>> (P.W * qOf P)) 0 &&
        Nat.beq (Hp &&& ((1 <<< P.W) - (1 <<< P.aH)) * ones P.W (qOf P)) 0 &&
        Nat.beq (cp >>> P.aH) 0 &&
        (kA P mrows sos).2.2.2 && Nat.blt (kBound P mrows sos) (1 <<< (P.W - 1)) &&
        loop3 P.W (qOf P)
          (kZp P mrows sos cp + (1 <<< (P.W - 1)) * ones P.W (qOf P * (qOf P * qOf P)) - kZn P mrows sos Hp)
          (6 * (1 <<< (P.W - 1))) (2 * P.D) (qOf P)) := rfl

/-- The conditions that `check` tests. -/
structure Facts (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ) : Prop where
  hN : 3 ≤ P.N
  hq : qOf P < 2 ^ P.eb
  haw : P.a ≤ P.w
  ha : 1 ≤ P.a
  haH : 1 ≤ P.aH
  heb : 2 ≤ P.eb
  hcb : 1 ≤ P.cb
  hHp : Hp / 2 ^ (P.W * qOf P) = 0
  hHs : Hp &&& (2 ^ P.W - 2 ^ P.aH) * ones P.W (qOf P) = 0
  hcp : cp / 2 ^ P.aH = 0
  hA : (kA P mrows sos).2.2.2 = true
  hbound : kBound P mrows sos < 2 ^ (P.W - 1)
  hloop : loop3 P.W (qOf P)
    (kZp P mrows sos cp + 2 ^ (P.W - 1) * ones P.W (qOf P * (qOf P * qOf P)) - kZn P mrows sos Hp)
    (6 * 2 ^ (P.W - 1)) (2 * P.D) (qOf P) = true

theorem facts_of_check {P : Params} {mrows : List ℕ} {sos : List Sos} {Hp cp : ℕ}
    (h : check P mrows sos Hp cp = true) : Facts P mrows sos Hp cp := by
  rw [check_eq] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9,
    Nat.eq_of_beq_eq_true h10, h11, h12, h13⟩

/-! ## The polynomials -/

/-- The positive part of `Z`. -/
noncomputable def ZpP (P : Params) (mrows : List ℕ) (sos : List Sos) (cp : ℕ) : Poly :=
  C (P.N - 1) * (C (9 * (P.N - 2)) * (momentP P mrows).1 + (sosSum P sos).1)
    + C (9 * (P.N - 1)) * (sub1 (momentP P mrows).1 + sub2 (momentP P mrows).1 + sub3 (momentP P mrows).1)
    + C (9 * csum (phiP P (P.D + 1) (hdNat mrows)).1)
    + uPoly (qOf P) (fun _ => 9 * (P.N - 1) * 2 ^ (P.aH - 1))
    + C (9 * (P.N - 1) * cp)

/-- The negative part of `Z`. -/
noncomputable def ZnP (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp : ℕ) : Poly :=
  C (P.N - 1) * (C (9 * (P.N - 2)) * (momentP P mrows).2 + (sosSum P sos).2)
    + C (9 * (P.N - 1)) * (sub1 (momentP P mrows).2 + sub2 (momentP P mrows).2 + sub3 (momentP P mrows).2)
    + C (9 * csum (phiP P (P.D + 1) (hdNat mrows)).2)
    + C (9 * (P.N - 1)) * uPoly (qOf P) (slot P.W Hp)

/-! ## The substitutions at the Kronecker point -/

theorem ev_sub1 (P : Params) (F : Poly) : ev P (mainPt P) (sub1 F) = ev P ⟨1, 1, 0⟩ F := by
  have h : (fun i => eval (pval P (mainPt P)) ((![X 0, X 0, 1] : Fin 3 → Poly) i)) = pval P ⟨1, 1, 0⟩ := by
    funext i
    fin_cases i <;> simp [pval, mainPt]
  show eval (pval P (mainPt P)) (bind₁ ![X 0, X 0, 1] F) = eval (pval P ⟨1, 1, 0⟩) F
  rw [eval_bind₁', h]

theorem ev_sub2 (P : Params) (F : Poly) : ev P (mainPt P) (sub2 F) = ev P ⟨1, 0, 1⟩ F := by
  have h : (fun i => eval (pval P (mainPt P)) ((![X 0, 1, X 0] : Fin 3 → Poly) i)) = pval P ⟨1, 0, 1⟩ := by
    funext i
    fin_cases i <;> simp [pval, mainPt]
  show eval (pval P (mainPt P)) (bind₁ ![X 0, 1, X 0] F) = eval (pval P ⟨1, 0, 1⟩) F
  rw [eval_bind₁', h]

theorem ev_sub3 (P : Params) (F : Poly) : ev P (mainPt P) (sub3 F) = ev P ⟨0, 1, 1⟩ F := by
  have h : (fun i => eval (pval P (mainPt P)) ((![1, X 0, X 0] : Fin 3 → Poly) i)) = pval P ⟨0, 1, 1⟩ := by
    funext i
    fin_cases i <;> simp [pval, mainPt]
  show eval (pval P (mainPt P)) (bind₁ ![1, X 0, X 0] F) = eval (pval P ⟨0, 1, 1⟩) F
  rw [eval_bind₁', h]

theorem csum_sub (g : Fin 3 → Poly) (hg : ∀ i, csum (g i) = 1) (F : Poly) : csum (bind₁ g F) = csum F := by
  show eval (fun _ => 1) (bind₁ g F) = eval (fun _ => 1) F
  rw [eval_bind₁']
  have h : (fun i => eval (fun _ => (1 : ℕ)) (g i)) = fun _ => 1 := funext hg
  rw [h]

theorem csum_sub1 (F : Poly) : csum (sub1 F) = csum F :=
  csum_sub _ (fun i => by fin_cases i <;> simp [csum_X]) F

theorem csum_sub2 (F : Poly) : csum (sub2 F) = csum F :=
  csum_sub _ (fun i => by fin_cases i <;> simp [csum_X]) F

theorem csum_sub3 (F : Poly) : csum (sub3 F) = csum F :=
  csum_sub _ (fun i => by fin_cases i <;> simp [csum_X]) F

theorem deg_sub1 (F : Poly) : (sub1 F).totalDegree ≤ F.totalDegree :=
  totalDegree_bind₁_le _ (fun i => by fin_cases i <;> simp [totalDegree_X]) F

theorem deg_sub2 (F : Poly) : (sub2 F).totalDegree ≤ F.totalDegree :=
  totalDegree_bind₁_le _ (fun i => by fin_cases i <;> simp [totalDegree_X]) F

theorem deg_sub3 (F : Poly) : (sub3 F).totalDegree ≤ F.totalDegree :=
  totalDegree_bind₁_le _ (fun i => by fin_cases i <;> simp [totalDegree_X]) F

theorem ev_uPoly (P : Params) (q : ℕ) (c : ℕ → ℕ) : ev P (mainPt P) (uPoly q c) = packSum P.W q c := by
  unfold uPoly packSum
  rw [map_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [map_mul, ev_C, map_pow]
  show c d * (eval (pval P (mainPt P)) (X 0)) ^ d = _
  rw [eval_X]
  show c d * (2 ^ (P.W * 1)) ^ d = _
  rw [mul_one, ← pow_mul]

/-! ## The values of the functions of the checker -/

theorem moment_fst (P : Params) (pt : Pt) (mrows : List ℕ) :
    (moment P pt mrows).1 = ev P pt (momentP P mrows).1 := by
  obtain ⟨b, hb⟩ := moment_eq P pt mrows
  rw [hb]

theorem moment_snd (P : Params) (pt : Pt) (mrows : List ℕ) :
    (moment P pt mrows).2.1 = ev P pt (momentP P mrows).2 := by
  obtain ⟨b, hb⟩ := moment_eq P pt mrows
  rw [hb]

theorem phiEval_fst (P : Params) (pt : Pt) (n rows : ℕ) :
    (phiEval P pt n rows).1 = ev P pt (phiP P n rows).1 := by
  obtain ⟨b, hb⟩ := phiEval_eq P pt n rows
  rw [hb]

theorem phiEval_snd (P : Params) (pt : Pt) (n rows : ℕ) :
    (phiEval P pt n rows).2.1 = ev P pt (phiP P n rows).2 := by
  obtain ⟨b, hb⟩ := phiEval_eq P pt n rows
  rw [hb]

theorem kA_eq (P : Params) (mrows : List ℕ) (sos : List Sos) :
    kA P mrows sos =
      (9 * (P.N - 2) * ev P (mainPt P) (momentP P mrows).1 + ev P (mainPt P) (sosSum P sos).1,
       9 * (P.N - 2) * ev P (mainPt P) (momentP P mrows).2 + ev P (mainPt P) (sosSum P sos).2,
       9 * (P.N - 2) * (csum (momentP P mrows).1 + csum (momentP P mrows).2) + boundSum P sos,
       (moment P (mainPt P) mrows).2.2 && flagAll P sos) := by
  unfold kA
  rw [sosAll_eq, moment_fst, moment_snd, moment_fst, moment_snd, ev_zero, ev_zero]

/-- `Zp` is the value of `ZpP` at the Kronecker point. -/
theorem ev_ZpP (P : Params) (mrows : List ℕ) (sos : List Sos) (cp : ℕ) (hW : 0 < P.W) :
    ev P (mainPt P) (ZpP P mrows sos cp) = kZp P mrows sos cp := by
  unfold ZpP kZp
  rw [kA_eq, moment_fst, moment_fst, moment_fst, phiEval_fst, ev_zero, Nat.one_shiftLeft,
    ones_eq P.W _ hW, ← packSum_const]
  simp only [map_add, map_mul, ev_C, ev_sub1, ev_sub2, ev_sub3, ev_uPoly]

/-- `Zn` is the value of `ZnP` at the Kronecker point. -/
theorem ev_ZnP (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp : ℕ) (hHp : Hp < 2 ^ (P.W * qOf P)) :
    ev P (mainPt P) (ZnP P mrows sos Hp) = kZn P mrows sos Hp := by
  unfold ZnP kZn
  rw [kA_eq, moment_snd, moment_snd, moment_snd, phiEval_snd, ev_zero]
  simp only [map_add, map_mul, ev_C, ev_sub1, ev_sub2, ev_sub3, ev_uPoly, packSum_slot P.W _ _ hHp]

/-! ## Degrees -/

theorem deg_add_le {F G : Poly} {d : ℕ} (hF : F.totalDegree ≤ d) (hG : G.totalDegree ≤ d) :
    (F + G).totalDegree ≤ d :=
  (totalDegree_add F G).trans (max_le hF hG)

theorem deg_ZpP (P : Params) (mrows : List ℕ) (sos : List Sos) (cp : ℕ) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb)
    (hflag : flagAll P sos = true) : (ZpP P mrows sos cp).totalDegree ≤ 2 * P.D := by
  have hM : degLe (momentP P mrows) (2 * P.D) := degLe_momentFrom P heb hcb mrows 0
  have hS := degLe_sosSum P sos hflag
  unfold ZpP
  refine deg_add_le (deg_add_le (deg_add_le (deg_add_le ?_ ?_) ?_) ?_) ?_
  · exact (totalDegree_C_mul_le _ _).trans (deg_add_le ((totalDegree_C_mul_le _ _).trans hM.1) hS.1)
  · exact (totalDegree_C_mul_le _ _).trans (deg_add_le (deg_add_le ((deg_sub1 _).trans hM.1)
      ((deg_sub2 _).trans hM.1)) ((deg_sub3 _).trans hM.1))
  · rw [totalDegree_C]
    exact Nat.zero_le _
  · exact (totalDegree_uPoly _ _).trans (by unfold qOf; omega)
  · rw [totalDegree_C]
    exact Nat.zero_le _

theorem deg_ZnP (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp : ℕ) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb)
    (hflag : flagAll P sos = true) : (ZnP P mrows sos Hp).totalDegree ≤ 2 * P.D := by
  have hM : degLe (momentP P mrows) (2 * P.D) := degLe_momentFrom P heb hcb mrows 0
  have hS := degLe_sosSum P sos hflag
  unfold ZnP
  refine deg_add_le (deg_add_le (deg_add_le ?_ ?_) ?_) ?_
  · exact (totalDegree_C_mul_le _ _).trans (deg_add_le ((totalDegree_C_mul_le _ _).trans hM.2) hS.2)
  · exact (totalDegree_C_mul_le _ _).trans (deg_add_le (deg_add_le ((deg_sub1 _).trans hM.2)
      ((deg_sub2 _).trans hM.2)) ((deg_sub3 _).trans hM.2))
  · rw [totalDegree_C]
    exact Nat.zero_le _
  · exact (totalDegree_C_mul_le _ _).trans ((totalDegree_uPoly _ _).trans (by unfold qOf; omega))

/-! ## Sums of coefficients -/

theorem kBound_eq (P : Params) (mrows : List ℕ) (sos : List Sos) :
    kBound P mrows sos =
      (P.N - 1) * (9 * (P.N - 2) * (csum (momentP P mrows).1 + csum (momentP P mrows).2) + boundSum P sos)
        + 27 * (P.N - 1) * (csum (momentP P mrows).1 + csum (momentP P mrows).2)
        + 9 * (csum (phiP P (P.D + 1) (hdNat mrows)).1 + csum (phiP P (P.D + 1) (hdNat mrows)).2)
        + 9 * (P.N - 1) * (qOf P + 1) * 2 ^ P.aH := by
  unfold kBound
  rw [kA_eq, moment_fst, moment_snd, phiEval_fst, phiEval_snd, ev_zero, ev_zero, ev_zero, ev_zero,
    Nat.one_shiftLeft]

theorem csum_ZpP_le (P : Params) (mrows : List ℕ) (sos : List Sos) (cp : ℕ) (ha : 1 ≤ P.a) (haw : P.a ≤ P.w)
    (haH : 1 ≤ P.aH) (hflag : flagAll P sos = true) (hcp : cp < 2 ^ P.aH) :
    csum (ZpP P mrows sos cp) ≤ kBound P mrows sos := by
  have hS := nrm_sosSum_le P ha haw sos hflag
  unfold nrm at hS
  have e : 2 ^ P.aH = 2 * 2 ^ (P.aH - 1) := two_pow_pred haH
  rw [kBound_eq]
  unfold ZpP
  simp only [map_add, map_mul, csum_C, csum_sub1, csum_sub2, csum_sub3, csum_uPoly, sum_const, card_range,
    smul_eq_mul]
  rw [e]
  rw [e] at hcp
  generalize csum (momentP P mrows).1 = a1
  generalize csum (momentP P mrows).2 = a2
  generalize csum (sosSum P sos).1 = s1 at hS ⊢
  generalize csum (sosSum P sos).2 = s2 at hS
  generalize csum (phiP P (P.D + 1) (hdNat mrows)).1 = f1
  generalize csum (phiP P (P.D + 1) (hdNat mrows)).2 = f2
  generalize boundSum P sos = bS at hS ⊢
  generalize 2 ^ (P.aH - 1) = β at hcp ⊢
  generalize P.N - 1 = n1
  generalize 9 * (P.N - 2) = n9
  generalize qOf P = q
  have h1 : n1 * s1 ≤ n1 * bS := Nat.mul_le_mul_left _ (by omega)
  have h2 : n1 * cp ≤ n1 * (2 * β) := Nat.mul_le_mul_left _ hcp.le
  nlinarith [h1, h2, Nat.zero_le (n1 * n9 * a2), Nat.zero_le (n1 * a2), Nat.zero_le (q * n1 * β),
    Nat.zero_le f2]

theorem csum_ZnP_le (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp : ℕ) (ha : 1 ≤ P.a) (haw : P.a ≤ P.w)
    (hflag : flagAll P sos = true) (hH : ∀ d, d < qOf P → slot P.W Hp d < 2 ^ P.aH) :
    csum (ZnP P mrows sos Hp) ≤ kBound P mrows sos := by
  have hS := nrm_sosSum_le P ha haw sos hflag
  unfold nrm at hS
  have hsum : ∑ d ∈ range (qOf P), slot P.W Hp d ≤ qOf P * 2 ^ P.aH := by
    have h := Finset.sum_le_card_nsmul (range (qOf P)) (slot P.W Hp) (2 ^ P.aH)
      (fun d hd => (hH d (mem_range.mp hd)).le)
    simpa using h
  rw [kBound_eq]
  unfold ZnP
  simp only [map_add, map_mul, csum_C, csum_sub1, csum_sub2, csum_sub3, csum_uPoly]
  generalize csum (momentP P mrows).1 = a1
  generalize csum (momentP P mrows).2 = a2
  generalize csum (sosSum P sos).1 = s1 at hS
  generalize csum (sosSum P sos).2 = s2 at hS ⊢
  generalize csum (phiP P (P.D + 1) (hdNat mrows)).1 = f1
  generalize csum (phiP P (P.D + 1) (hdNat mrows)).2 = f2
  generalize boundSum P sos = bS at hS ⊢
  generalize ∑ d ∈ range (qOf P), slot P.W Hp d = σ at hsum ⊢
  generalize 2 ^ P.aH = β at hsum ⊢
  generalize P.N - 1 = n1
  generalize 9 * (P.N - 2) = n9
  generalize qOf P = q at hsum ⊢
  have h1 : n1 * s2 ≤ n1 * bS := Nat.mul_le_mul_left _ (by omega)
  have h2 : n1 * σ ≤ n1 * (q * β) := Nat.mul_le_mul_left _ hsum
  nlinarith [h1, h2, Nat.zero_le (n1 * n9 * a1), Nat.zero_le (n1 * a1), Nat.zero_le (n1 * β),
    Nat.zero_le f1]

/-! ## The sums over the permutations -/

/-- The coefficient of `u ^ x * v ^ y * t ^ z`. -/
noncomputable def cf (F : Poly) (x y z : ℕ) : ℕ := coeff (expo x y z) F

theorem orb_eq_zero (F : Poly) {d x y z : ℕ} (hF : F.totalDegree ≤ d) (h : d < x + y + z) :
    orb (cf F) x y z = 0 := by
  unfold orb cf
  rw [coeff_expo_eq_zero F hF (by omega : d < x + y + z), coeff_expo_eq_zero F hF (by omega : d < x + z + y),
    coeff_expo_eq_zero F hF (by omega : d < y + x + z), coeff_expo_eq_zero F hF (by omega : d < y + z + x),
    coeff_expo_eq_zero F hF (by omega : d < z + x + y), coeff_expo_eq_zero F hF (by omega : d < z + y + x)]

/-- **The checker and the sums over the permutations.** If the checker accepts, then for all
exponents `(x, y, z)` the coefficients of `ZpP` and of `ZnP` have the same sum over the six
permutations of `(x, y, z)`. -/
theorem check_orbits (P : Params) (mrows : List ℕ) (sos : List Sos) (Hp cp : ℕ)
    (h : check P mrows sos Hp cp = true) (x y z : ℕ) :
    orb (cf (ZpP P mrows sos cp)) x y z = orb (cf (ZnP P mrows sos Hp)) x y z := by
  have F := facts_of_check h
  -- the flags of the blocks
  have hflag : flagAll P sos = true := by
    have hA := F.hA
    rw [kA_eq] at hA
    exact (Bool.and_eq_true_iff.mp hA).2
  -- `aH + 1 < W`
  have hbnd := F.hbound
  have hN := F.hN
  have hW : P.aH < P.W - 1 := by
    have h1 : 2 ^ P.aH ≤ kBound P mrows sos := by
      rw [kBound_eq]
      have h2 : 1 ≤ 9 * (P.N - 1) * (qOf P + 1) := by
        have : 1 ≤ P.N - 1 := by omega
        nlinarith [Nat.zero_le (qOf P)]
      calc 2 ^ P.aH = 1 * 2 ^ P.aH := (one_mul _).symm
        _ ≤ 9 * (P.N - 1) * (qOf P + 1) * 2 ^ P.aH := Nat.mul_le_mul_right _ h2
        _ ≤ _ := Nat.le_add_left _ _
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 hbnd)
  have hW0 : 0 < P.W := by omega
  -- the data of `H`
  have hHp : Hp < 2 ^ (P.W * qOf P) := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp F.hHp
  have hcp : cp < 2 ^ P.aH := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp F.hcp
  have hH : ∀ d, d < qOf P → slot P.W Hp d < 2 ^ P.aH := by
    have h1 := F.hHs
    rw [← packSum_slot P.W (qOf P) Hp hHp, ones_eq P.W _ hW0] at h1
    exact slots_lt_of_and_hi P.W P.aH (qOf P) _ (by omega) (fun d _ => slot_lt P.W Hp d) h1
  -- degrees, exponents and coefficients
  have dp := deg_ZpP P mrows sos cp F.heb F.hcb hflag
  have dn := deg_ZnP P mrows sos Hp F.heb F.hcb hflag
  have ep : ∀ m ∈ (ZpP P mrows sos cp).support, ∀ i, m i < qOf P := fun m hm i =>
    lt_of_le_of_lt (exponent_le _ dp m hm i) (by unfold qOf; omega)
  have en : ∀ m ∈ (ZnP P mrows sos Hp).support, ∀ i, m i < qOf P := fun m hm i =>
    lt_of_le_of_lt (exponent_le _ dn m hm i) (by unfold qOf; omega)
  have cp' : ∀ m, coeff m (ZpP P mrows sos cp) < 2 ^ (P.W - 1) := fun m =>
    lt_of_le_of_lt ((coeff_le_csum _ m).trans (csum_ZpP_le P mrows sos cp F.ha F.haw F.haH hflag hcp)) hbnd
  have cn' : ∀ m, coeff m (ZnP P mrows sos Hp) < 2 ^ (P.W - 1) := fun m =>
    lt_of_le_of_lt ((coeff_le_csum _ m).trans (csum_ZnP_le P mrows sos Hp F.ha F.haw hflag hH)) hbnd
  by_cases hd : x + y + z ≤ 2 * P.D
  · refine orb_of_sorted _ _ (2 * P.D) (fun e1 e2 e3 h12 h23 hs => ?_) x y z hd
    have h3 : e3 < qOf P := by unfold qOf; omega
    have h2 : e2 < qOf P := lt_of_le_of_lt h23 h3
    have h1 : e1 < qOf P := lt_of_le_of_lt h12 h2
    have hsum := orbitOk_true (loop3_true _ _ _ _ _ (qOf P) F.hloop e3 h3 e2 h23 e1 h12 hs)
    simp only [slotAt_eq] at hsum
    rw [← ev_ZpP P mrows sos cp hW0, ← ev_ZnP P mrows sos Hp hHp, ev_main, ev_main] at hsum
    have s := fun (a b c : ℕ) (ha : a < qOf P) (hb : b < qOf P) (hc : c < qOf P) =>
      slot_Dd P.W (qOf P) hW0 (ZpP P mrows sos cp) (ZnP P mrows sos Hp) ep en cp' cn' ha hb hc
    rw [s e1 e2 e3 h1 h2 h3, s e1 e3 e2 h1 h3 h2, s e2 e1 e3 h2 h1 h3, s e2 e3 e1 h2 h3 h1,
      s e3 e1 e2 h3 h1 h2, s e3 e2 e1 h3 h2 h1] at hsum
    have b1 := cn' (expo e1 e2 e3)
    have b2 := cn' (expo e1 e3 e2)
    have b3 := cn' (expo e2 e1 e3)
    have b4 := cn' (expo e2 e3 e1)
    have b5 := cn' (expo e3 e1 e2)
    have b6 := cn' (expo e3 e2 e1)
    unfold orb cf
    omega
  · rw [orb_eq_zero _ dp (by omega), orb_eq_zero _ dn (by omega)]

end CAP.ThreePoint
