module

public import N14.Box.Tree
public import N14.Box.Cons

/-!
# T7, the slack on a domain: soundness of the checker of a cell

**Theorem** (`cell_sound`). Let the parameters of a run be accepted (`runOk`), and let the checker accept a cell
(`cellOk`). Then at every point of the box of the cell at which the Gram polynomial and the functions of all
cuts are nonnegative,

  `0 ≤ M(x) + T_i(x₁) + T_j(x₂) + T_k(x₃)`,

where `M` is the polynomial whose coefficients are the slots of `R.PpM` minus the bias (`pEval`), and `T_i`,
`T_j`, `T_k` are the polynomials of the table entries of the three intervals of the cell, whose coefficients are
the slots of their numbers (`uraw`).

The proof has three parts. `rootX_val`: the array of the root of `CAP.Bernstein` has, at the point of the box
with the local coordinates `t`, the value `A + ∏ q_a ^ n * p(x)`. `cell_poly`: the number of the coefficients of
the cell is the sum of the mixed part and of the three table entries on the three axes. `go_sound`
(`N14.Box.Tree`): the statement of the tree for the arrays of the root.
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein Finset Polynomial

/-! ## The array of the root -/

/-- The array of the root of `CAP.Bernstein`: it is at most `2 * A` times the binomial array, and at the point
with the local coordinates `t` its value is `A + ∏ q_a ^ n * p(x)`. -/
theorem rootX_val (P : Params) (Pp : ℕ) (h : rootOk P Pp = true) :
    ∃ f : ℕ → ℕ, Arr P P.A (rootX P Pp) f ∧
      ∀ x1 x2 x3 t1 t2 t3 : ℝ, (P.q1 : ℝ) * x1 = P.c1 + P.w1 * t1 - P.o1 →
        (P.q2 : ℝ) * x2 = P.c2 + P.w2 * t2 - P.o2 → (P.q3 : ℝ) * x3 = P.c3 + P.w3 * t3 - P.o3 →
        Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
            (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) f
          = (P.A : ℝ) + (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n * pEval P Pp x1 x2 x3 := by
  obtain ⟨⟨hV, hn, hfit⟩, hq1, hq2, hq3, hd, hb, hgP, hgN⟩ := rootOk_eq P Pp h
  obtain ⟨bP, bN, ⟨hXP, hbP⟩, ⟨hXN, hbN⟩, hPhi⟩ := root_rep P Pp hV hq1 hq2 hq3 hd hb
  have hF := fits_eq P hfit
  have hAJ : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) → P.A * cJ P.n e < 2 ^ (P.V - 1) := by
    intro e _
    calc P.A * cJ P.n e ≤ P.A * 2 ^ (3 * P.n) := Nat.mul_le_mul_left _ (cJ_le P.n e)
      _ ≤ (2 * P.A + P.th) * 2 ^ (3 * P.n) := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ (P.V - 1) := hF
  have hAJeq : P.A * binomJ P = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => P.A * cJ P.n e) := by
    rw [binomJ_eq, ← packSum_mul]
  rw [hAJeq, hXP] at hgP
  rw [hAJeq, hXN] at hgN
  have gP := UniPos.geTest_sound P.V _ (fun e => P.A * cJ P.n e) bP hV hAJ
    (fun e he => lt_of_le_of_lt (hbP e he) hb) hgP
  have gN := UniPos.geTest_sound P.V _ (fun e => P.A * cJ P.n e) bN hV hAJ
    (fun e he => lt_of_le_of_lt (hbN e he) hb) hgN
  have hX : rootP P Pp + (P.A * binomJ P - rootN P Pp)
      = packSum P.V ((P.n + 1) * (P.n + 1) * (P.n + 1)) (fun e => bP e + (P.A * cJ P.n e - bN e)) := by
    rw [hAJeq, hXP, hXN, packSum_sub P.V _ _ _ gN, ← packSum_add]
  have hbound : ∀ e, e < (P.n + 1) * (P.n + 1) * (P.n + 1) →
      bP e + (P.A * cJ P.n e - bN e) ≤ 2 * P.A * cJ P.n e := by
    intro e he
    have a1 := gP e he
    have a2 : P.A * cJ P.n e - bN e ≤ P.A * cJ P.n e := Nat.sub_le _ _
    have a3 : 2 * P.A * cJ P.n e = P.A * cJ P.n e + P.A * cJ P.n e := by ring
    omega
  refine ⟨fun e => bP e + (P.A * cJ P.n e - bN e), ⟨hX, hbound⟩, fun x1 x2 x3 t1 t2 t3 e1 e2 e3 => ?_⟩
  have hsum : Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
        (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) (fun e => bP e + (P.A * cJ P.n e - bN e))
      = (P.A : ℝ) + (Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
          (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) bP
        - Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
          (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) bN) := by
    rw [Phi_add, Phi_sub _ _ gN, Phi_smul, Phi_cJ]
    simp
    ring
  rw [hsum, hPhi, Phi_data]
  have hU0 : subU P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 0 = P.q1 := by simp [subU]
  have hU1 : subU P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 1 = P.q2 := by simp [subU]
  have hU2 : subU P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 2 = P.q3 := by simp [subU]
  have hV0 : subV P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 0 = P.q1 * x1 := by
    rw [e1]
    simp [subV]
  have hV1 : subV P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 1 = P.q2 * x2 := by
    rw [e2]
    simp [subV]
  have hV2 : subV P (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) 2 = P.q3 * x3 := by
    rw [e3]
    simp [subV]
  rw [hU0, hU1, hU2, hV0, hV1, hV2]
  have hfin : ∑ e3 ∈ range (P.n + 1), ∑ e2 ∈ range (P.n + 1), ∑ e1 ∈ range (P.n + 1),
        (coef P Pp (e1 + (P.n + 1) * (e2 + (P.n + 1) * e3)) : ℝ)
          * (hw P.n (P.q1 : ℝ) (P.q1 * x1) e1 * hw P.n (P.q2 : ℝ) (P.q2 * x2) e2 * hw P.n (P.q3 : ℝ) (P.q3 * x3) e3)
      = (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n * pEval P Pp x1 x2 x3 := by
    unfold pEval
    rw [mul_sum]
    refine sum_congr rfl fun e3 he3 => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e2 he2 => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e1 he1 => ?_
    rw [hw_scale P.n e1 (Nat.lt_succ_iff.mp (mem_range.mp he1)), hw_scale P.n e2 (Nat.lt_succ_iff.mp (mem_range.mp he2)),
      hw_scale P.n e3 (Nat.lt_succ_iff.mp (mem_range.mp he3))]
    ring
  rw [hfin]

/-! ## The polynomial of a cell -/

/-- The polynomial of a table entry: its coefficients are the slots of `T`. -/
noncomputable def uraw (W n T : ℕ) (x : ℝ) : ℝ := ∑ d ∈ range (n + 1), (slot W T d : ℝ) * x ^ d

theorem place_eq (W Vs T : ℕ) : ∀ cnt, place W Vs T cnt = ∑ d ∈ range cnt, slot W T d * 2 ^ (Vs * d)
  | 0 => rfl
  | cnt + 1 => by
    rw [sum_range_succ, ← place_eq W Vs T cnt]
    show place W Vs T cnt + (slot W T cnt) <<< (Vs * cnt) = _
    rw [Nat.shiftLeft_eq]

theorem packSum_sum (w N m : ℕ) (F : ℕ → ℕ → ℕ) :
    packSum w N (fun e => ∑ d ∈ range m, F d e) = ∑ d ∈ range m, packSum w N (F d) := by
  unfold packSum
  rw [sum_comm]
  exact sum_congr rfl fun e _ => by rw [sum_mul]

theorem Phi_sum (M : ℕ) (ω : ℕ → ℕ → ℝ) (m : ℕ) (F : ℕ → ℕ → ℕ) :
    Phi M ω (fun e => ∑ d ∈ range m, F d e) = ∑ d ∈ range m, Phi M ω (F d) := by
  unfold Phi
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [Nat.cast_sum, sum_mul]

theorem sum_unitF_le (m B e : ℕ) (g : ℕ → ℕ → ℕ) (hg : ∀ d, g d e ≤ B) :
    ∑ d ∈ range m, g d e ≤ m * B := by
  calc ∑ d ∈ range m, g d e ≤ ∑ _d ∈ range m, B := sum_le_sum fun d _ => hg d
    _ = m * B := by rw [sum_const, card_range, smul_eq_mul]

/-- The array with the coefficients `τ` on the first axis, and its number and value. -/
theorem place0 (R : Run) (T : ℕ) :
    place R.W R.V T (Nat.succ R.n) = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
      (fun e => ∑ d ∈ range (R.n + 1), unitF (R.n + 1) d 0 0 (slot R.W T d) e) := by
  show place R.W R.V T (R.n + 1) = _
  rw [place_eq, packSum_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [packSum_unitF R.V (R.n + 1) d 0 0 _ (mem_range.mp hd) (Nat.succ_pos _) (Nat.succ_pos _)]
  congr 2

theorem place1 (R : Run) (T : ℕ) :
    place R.W (Nat.mul R.V (Nat.succ R.n)) T (Nat.succ R.n) = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
      (fun e => ∑ d ∈ range (R.n + 1), unitF (R.n + 1) 0 d 0 (slot R.W T d) e) := by
  show place R.W (R.V * (R.n + 1)) T (R.n + 1) = _
  rw [place_eq, packSum_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [packSum_unitF R.V (R.n + 1) 0 d 0 _ (Nat.succ_pos _) (mem_range.mp hd) (Nat.succ_pos _)]
  congr 2
  ring

theorem place2 (R : Run) (T : ℕ) :
    place R.W (Nat.mul (Nat.mul R.V (Nat.succ R.n)) (Nat.succ R.n)) T (Nat.succ R.n)
      = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
        (fun e => ∑ d ∈ range (R.n + 1), unitF (R.n + 1) 0 0 d (slot R.W T d) e) := by
  show place R.W (R.V * (R.n + 1) * (R.n + 1)) T (R.n + 1) = _
  rw [place_eq, packSum_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [packSum_unitF R.V (R.n + 1) 0 0 d _ (Nat.succ_pos _) (Nat.succ_pos _) (mem_range.mp hd)]
  congr 2
  ring

theorem Phi_axis0 (n W T : ℕ) (x1 x2 x3 : ℝ) :
    Phi (n + 1) (pw x1 x2 x3) (fun e => ∑ d ∈ range (n + 1), unitF (n + 1) d 0 0 (slot W T d) e)
      = uraw W n T x1 := by
  rw [Phi_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [Phi_unitF _ _ d 0 0 _ (mem_range.mp hd) (Nat.succ_pos _) (Nat.succ_pos _)]
  simp [pw]

theorem Phi_axis1 (n W T : ℕ) (x1 x2 x3 : ℝ) :
    Phi (n + 1) (pw x1 x2 x3) (fun e => ∑ d ∈ range (n + 1), unitF (n + 1) 0 d 0 (slot W T d) e)
      = uraw W n T x2 := by
  rw [Phi_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [Phi_unitF _ _ 0 d 0 _ (Nat.succ_pos _) (mem_range.mp hd) (Nat.succ_pos _)]
  simp [pw]

theorem Phi_axis2 (n W T : ℕ) (x1 x2 x3 : ℝ) :
    Phi (n + 1) (pw x1 x2 x3) (fun e => ∑ d ∈ range (n + 1), unitF (n + 1) 0 0 d (slot W T d) e)
      = uraw W n T x3 := by
  rw [Phi_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [Phi_unitF _ _ 0 0 d _ (Nat.succ_pos _) (Nat.succ_pos _) (mem_range.mp hd)]
  simp [pw]

/-- The sizes: the sum of a coefficient of the mixed part and of three coefficients of table entries is a
slot. -/
theorem slot_room (V aH W n s f1 f2 f3 : ℕ) (hW : W + 4 ≤ aH) (hn : 2 ≤ n) (haV : aH + n ≤ V) (hs : s < 2 ^ aH)
    (h1 : f1 ≤ (n + 1) * 2 ^ W) (h2 : f2 ≤ (n + 1) * 2 ^ W) (h3 : f3 ≤ (n + 1) * 2 ^ W) :
    s + f1 + f2 + f3 < 2 ^ V := by
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hp : 16 * 2 ^ W ≤ 2 ^ aH := by
    calc 16 * 2 ^ W = 2 ^ (W + 4) := by rw [pow_add]; ring
      _ ≤ 2 ^ aH := Nat.pow_le_pow_right (by norm_num) hW
  have hV : 2 ^ aH * 2 ^ n ≤ 2 ^ V := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) haV
  have hf : (n + 1) * 2 ^ W ≤ 2 ^ n * 2 ^ W := Nat.mul_le_mul_right _ hn1
  have hA : 0 < 2 ^ aH := Nat.two_pow_pos _
  have hpW : 0 < 2 ^ W := Nat.two_pow_pos _
  nlinarith [Nat.mul_le_mul_left (2 ^ n) hp, Nat.mul_le_mul_left (2 ^ aH) hq]

/-- **The polynomial of a cell** is the sum of the mixed part and of the polynomials of its three table
entries. -/
theorem cell_poly (R : Run) (hM : R.PpM < 2 ^ (R.V * ((R.n + 1) * (R.n + 1) * (R.n + 1))))
    (hMs : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) → slot R.V R.PpM e < 2 ^ R.aH)
    (hW : R.W + 4 ≤ R.aH) (hn : 2 ≤ R.n) (haV : R.aH + R.n ≤ R.V) (A i j k : ℕ) (x1 x2 x3 : ℝ) :
    pEval (boxP R R.aH A i j k) (cellPp R i j k) x1 x2 x3
      = pEval (boxP R R.aH A i j k) R.PpM x1 x2 x3 + uraw R.W R.n (ent R.t1 i).T x1
        + uraw R.W R.n (ent R.t2 j).T x2 + uraw R.W R.n (ent R.t3 k).T x3 := by
  have e : cellPp R i j k = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
      (fun e => slot R.V R.PpM e
        + (∑ d ∈ range (R.n + 1), unitF (R.n + 1) d 0 0 (slot R.W (ent R.t1 i).T d) e)
        + (∑ d ∈ range (R.n + 1), unitF (R.n + 1) 0 d 0 (slot R.W (ent R.t2 j).T d) e)
        + (∑ d ∈ range (R.n + 1), unitF (R.n + 1) 0 0 d (slot R.W (ent R.t3 k).T d) e)) := by
    show R.PpM + place R.W R.V (ent R.t1 i).T (Nat.succ R.n)
        + place R.W (Nat.mul R.V (Nat.succ R.n)) (ent R.t2 j).T (Nat.succ R.n)
        + place R.W (Nat.mul (Nat.mul R.V (Nat.succ R.n)) (Nat.succ R.n)) (ent R.t3 k).T (Nat.succ R.n) = _
    rw [place0, place1, place2, packSum_add, packSum_add, packSum_add, packSum_slot R.V _ R.PpM hM]
  have hb : ∀ (T : ℕ) (a b c : ℕ → ℕ) (e : ℕ),
      (∑ d ∈ range (R.n + 1), unitF (R.n + 1) (a d) (b d) (c d) (slot R.W T d) e) ≤ (R.n + 1) * 2 ^ R.W :=
    fun T a b c e => sum_unitF_le (R.n + 1) (2 ^ R.W) e _
      (fun d => le_trans (unitF_le _ _ _ _ _ e) (slot_lt R.W T d).le)
  have hlt : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) →
      slot R.V R.PpM e
        + (∑ d ∈ range (R.n + 1), unitF (R.n + 1) d 0 0 (slot R.W (ent R.t1 i).T d) e)
        + (∑ d ∈ range (R.n + 1), unitF (R.n + 1) 0 d 0 (slot R.W (ent R.t2 j).T d) e)
        + (∑ d ∈ range (R.n + 1), unitF (R.n + 1) 0 0 d (slot R.W (ent R.t3 k).T d) e) < 2 ^ R.V :=
    fun e he => slot_room R.V R.aH R.W R.n _ _ _ _ hW hn haV (hMs e he)
      (hb _ (fun d => d) (fun _ => 0) (fun _ => 0) e) (hb _ (fun _ => 0) (fun d => d) (fun _ => 0) e)
      (hb _ (fun _ => 0) (fun _ => 0) (fun d => d) e)
  rw [e]
  have hP : pEval (boxP R R.aH A i j k) (packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) _) x1 x2 x3 = _ :=
    pEval_packSum (boxP R R.aH A i j k) _ hlt x1 x2 x3
  rw [hP, pEval_Phi]
  show Phi (R.n + 1) (pw x1 x2 x3) _ - Phi (R.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (R.aH - 1))
    = Phi (R.n + 1) (pw x1 x2 x3) (slot R.V R.PpM) - Phi (R.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (R.aH - 1))
      + uraw R.W R.n (ent R.t1 i).T x1 + uraw R.W R.n (ent R.t2 j).T x2 + uraw R.W R.n (ent R.t3 k).T x3
  rw [Phi_add, Phi_add, Phi_add, Phi_axis0, Phi_axis1, Phi_axis2]
  ring

/-! ## The parameters of a run -/

theorem len_eq {α : Type} (l : List α) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg Nat.succ ih

theorem cutsFit_mem (R : Run) : ∀ l : List Cut, cutsFit R l = true → ∀ c ∈ l, cutFits R c = true := by
  intro l
  induction l with
  | nil => exact fun _ c hc => absurd hc (List.not_mem_nil)
  | cons x l ih =>
    intro h c hc
    have h' : (cutFits R x && cutsFit R l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h'.1
    · exact ih h'.2 c hc'

/-- What the tests of the parameters of a run give. -/
structure RunFit (R : Run) : Prop where
  hV : 1 ≤ R.V
  hnV : R.n ≤ R.V
  hn : 2 ≤ R.n
  hA : 1 ≤ R.A
  hAG : 1 ≤ R.AG
  hsum : 2 * (R.A + (R.cuts.length + R.polys.length + 1) * 2 ^ R.mb * (R.AG + 1)) * 2 ^ (3 * R.n) < 2 ^ (R.V - 1)
  haV : R.aH + R.n ≤ R.V
  hW : R.W + 4 ≤ R.aH
  hM : R.PpM < 2 ^ (R.V * ((R.n + 1) * (R.n + 1) * (R.n + 1)))
  hMs : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) → slot R.V R.PpM e < 2 ^ R.aH
  con : ConFit R
  cuts : ∀ c ∈ R.cuts, cutFits R c = true

theorem runOk_fit (R : Run) (h : runOk R = true) : RunFit R := by
  have h' : (Nat.ble 1 R.V && Nat.ble R.n R.V && Nat.ble 2 R.n && Nat.ble 1 R.A && Nat.ble 1 R.AG
      && Nat.blt ((2 * (R.A + (len R.cuts + len R.polys + 1) * (1 <<< R.mb) * (R.AG + 1))) <<< (3 * R.n))
        (1 <<< (R.V - 1))
      && Nat.ble 2 R.aH && Nat.ble (R.aH + R.n) R.V && Nat.blt R.W (R.aH - 3)
      && Nat.blt R.PpM (1 <<< (R.V * ((R.n + 1) * (R.n + 1) * (R.n + 1))))
      && Nat.beq (R.PpM &&& ((1 <<< R.V - 1 <<< R.aH) * ones R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)))) 0
      && Nat.blt (R.sg + 2) (R.aG - 1) && Nat.ble R.aG R.V && cutsFit R R.cuts) = true := h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.shiftLeft_eq, one_mul, len_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hV, hnV⟩, hn⟩, hA⟩, hAG⟩, hsum⟩, haH⟩, haV⟩, hW⟩, hM⟩, hbits⟩, hsg⟩, haG⟩, hcuts⟩ := h'
  have hbits' := Nat.eq_of_beq_eq_true hbits
  have haHV : R.aH ≤ R.V := by omega
  have hs := packSum_slot R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) R.PpM hM
  rw [← hs, ones_eq R.V _ hV] at hbits'
  have hd := slots_lt_of_and_hi R.V R.aH _ (slot R.V R.PpM) haHV (fun j _ => slot_lt R.V R.PpM j) hbits'
  exact ⟨hV, hnV, hn, hA, hAG, hsum, haV, by omega, hM, hd, ⟨hV, hn, hsg, haG⟩, cutsFit_mem R R.cuts hcuts⟩

theorem RunFit.tree {R : Run} (h : RunFit R) (aH i j k : ℕ) :
    TreeFit (boxP R aH R.A i j k) R.AG (R.cuts.length + R.polys.length + 1) R.mb :=
  ⟨h.hV, h.hnV, h.hsum⟩

/-! ## The cell -/

/-- The point `t` lies in the interval of the entry. -/
def InIv (x : Ent) (t : ℝ) : Prop := (x.c : ℝ) / 2 ^ x.e - 1 ≤ t ∧ t ≤ ((x.c : ℝ) + 1) / 2 ^ x.e - 1

/-- A point of the interval of an entry is `(c + t) / 2 ^ e - 1` with `0 ≤ t ≤ 1`. -/
theorem InIv.local {x : Ent} {t : ℝ} (h : InIv x t) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (((1 <<< x.e : ℕ) : ℕ) : ℝ) * t = (x.c : ℝ) + ((1 : ℕ) : ℝ) * s - ((1 <<< x.e : ℕ) : ℝ) := by
  have hq : (1 : ℕ) ≤ 1 <<< x.e := by
    rw [Nat.one_shiftLeft]
    exact Nat.one_le_two_pow
  have hc : (((1 <<< x.e : ℕ) : ℕ) : ℝ) = 2 ^ x.e := by
    rw [Nat.one_shiftLeft]
    push_cast
    rfl
  have hp : (0 : ℝ) < 2 ^ x.e := by positivity
  obtain ⟨h1, h2⟩ := h
  refine exists_t x.c 1 (1 <<< x.e) (1 <<< x.e) hq t ?_ ?_
  · rw [hc, sub_div, div_self hp.ne']
    exact h1
  · rw [hc]
    have : ((x.c : ℝ) + ((1 : ℕ) : ℝ) - 2 ^ x.e) / 2 ^ x.e = ((x.c : ℝ) + 1) / 2 ^ x.e - 1 := by
      rw [sub_div, div_self hp.ne']
      push_cast
      rfl
    rw [this]
    exact h2

/-- The polynomial constraints that the bits of `use` select. -/
def selPolys : List ℕ → ℕ → List ℕ
  | [], _ => []
  | Pp :: l, use => if use &&& 1 = 0 then selPolys l (use >>> 1) else Pp :: selPolys l (use >>> 1)

theorem selPolys_mem : ∀ (l : List ℕ) (use Pp : ℕ), Pp ∈ selPolys l use → Pp ∈ l
  | [], _, _, h => h
  | Q :: l, use, Pp, h => by
    unfold selPolys at h
    split_ifs at h
    · exact List.mem_cons_of_mem _ (selPolys_mem l _ Pp h)
    · rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (selPolys_mem l _ Pp h')

theorem selPolys_length : ∀ (l : List ℕ) (use : ℕ), (selPolys l use).length ≤ l.length
  | [], _ => Nat.le_refl _
  | Q :: l, use => by
    unfold selPolys
    split_ifs
    · exact Nat.le_succ_of_le (selPolys_length l _)
    · exact Nat.succ_le_succ (selPolys_length l _)

theorem polyArrs_eq (R : Run) (i j k : ℕ) : ∀ (l : List ℕ) (use : ℕ),
    polyArrs R i j k l use = (selPolys l use).map (rootArr (boxP R R.aG R.AG i j k))
  | [], _ => rfl
  | Pp :: l, use => by
    have h : polyArrs R i j k (Pp :: l) use
        = Nat.rec (motive := fun _ => List ℕ) (polyArrs R i j k l (use >>> 1))
            (fun _ _ => rootArr (boxP R R.aG R.AG i j k) Pp :: polyArrs R i j k l (use >>> 1)) (use &&& 1) := rfl
    rw [h]
    unfold selPolys
    rcases hb : use &&& 1 with _ | b
    · rw [if_pos rfl]
      exact polyArrs_eq R i j k l _
    · rw [if_neg (Nat.succ_ne_zero b)]
      show rootArr (boxP R R.aG R.AG i j k) Pp :: polyArrs R i j k l (use >>> 1) = _
      rw [polyArrs_eq R i j k l]
      rfl

/-- The numbers of the coefficients of the constraints of a cell: the Gram inequality, the cuts, and the
selected polynomial constraints. -/
noncomputable def conPps (R : Run) (use : ℕ) : List ℕ :=
  gramPp R :: (R.cuts.map (cutPp R) ++ selPolys R.polys use)

theorem conArrs_eq (R : Run) (i j k use : ℕ) :
    conArrs R i j k use = (conPps R use).map (rootArr (boxP R R.aG R.AG i j k)) := by
  have h : ∀ (tail : List ℕ) (l : List Cut), cutArrs R i j k tail l
      = (l.map (cutPp R)).map (rootArr (boxP R R.aG R.AG i j k)) ++ tail := by
    intro tail l
    induction l with
    | nil => rfl
    | cons c l ih =>
      show List.cons (rootArr (boxP R R.aG R.AG i j k) (cutPp R c)) (cutArrs R i j k tail l) = _
      rw [ih]
      rfl
  show List.cons (rootArr (boxP R R.aG R.AG i j k) (gramPp R))
    (cutArrs R i j k (polyArrs R i j k R.polys use) R.cuts) = _
  rw [h, polyArrs_eq]
  unfold conPps
  rw [List.map_cons, List.map_append]

/-- The array of the root for a polynomial, or the array `0`: its value at the point with the local
coordinates `t` is `A + ∏ q_a ^ n * p(x)` or `0`. -/
theorem rootArr_val (P : Params) (Pp : ℕ) :
    ∃ f : ℕ → ℕ, Arr P P.A (rootArr P Pp) f ∧
      ∀ x1 x2 x3 t1 t2 t3 : ℝ, (P.q1 : ℝ) * x1 = P.c1 + P.w1 * t1 - P.o1 →
        (P.q2 : ℝ) * x2 = P.c2 + P.w2 * t2 - P.o2 → (P.q3 : ℝ) * x3 = P.c3 + P.w3 * t3 - P.o3 →
        (Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
            (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) f = 0 ∨
          Phi (P.n + 1) (hwω P.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
            (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) f
            = (P.A : ℝ) + (P.q1 : ℝ) ^ P.n * (P.q2 : ℝ) ^ P.n * (P.q3 : ℝ) ^ P.n * pEval P Pp x1 x2 x3) := by
  cases hr : rootOk P Pp with
  | true =>
    obtain ⟨f, hf, hval⟩ := rootX_val P Pp hr
    refine ⟨f, ?_, fun x1 x2 x3 t1 t2 t3 e1 e2 e3 => Or.inr (hval x1 x2 x3 t1 t2 t3 e1 e2 e3)⟩
    have : rootArr P Pp = rootX P Pp := by
      unfold rootArr
      rw [hr]
    rw [this]
    exact hf
  | false =>
    refine ⟨fun _ => 0, ⟨?_, fun e _ => Nat.zero_le _⟩, fun x1 x2 x3 t1 t2 t3 _ _ _ => Or.inl ?_⟩
    · have : rootArr P Pp = 0 := by
        unfold rootArr
        rw [hr]
      rw [this]
      unfold packSum
      simp
    · unfold Phi
      simp

/-- **Soundness of the checker of a cell.** -/
theorem cell_sound (R : Run) (hR : RunFit R) (c : Cell) (h : cellOk R c = true) (x1 x2 x3 : ℝ)
    (h1 : InIv (ent R.t1 c.i) x1) (h2 : InIv (ent R.t2 c.j) x2) (h3 : InIv (ent R.t3 c.k) x3)
    (hG : 0 ≤ gram x1 x2 x3) (hC : ∀ cut ∈ R.cuts, 0 ≤ cutVal cut x1 x2 x3)
    (hP : ∀ Pp ∈ R.polys, pEval (boxP R R.aG R.AG 0 0 0) Pp x1 x2 x3 ≤ 0) :
    0 ≤ pEval (boxP R R.aH R.A c.i c.j c.k) R.PpM x1 x2 x3 + uraw R.W R.n (ent R.t1 c.i).T x1
        + uraw R.W R.n (ent R.t2 c.j).T x2 + uraw R.W R.n (ent R.t3 c.k).T x3 := by
  have h' : (Nat.blt 0 (ent R.t1 c.i).T && Nat.blt 0 (ent R.t2 c.j).T && Nat.blt 0 (ent R.t3 c.k).T
      && go R (boxP R R.aH R.A c.i c.j c.k) (binomJ (boxP R R.aH R.A c.i c.j c.k)) R.fuel c.tree
        (rootArr (boxP R R.aH R.A c.i c.j c.k) (cellPp R c.i c.j c.k)) (conArrs R c.i c.j c.k c.use)
        (fun _ => true)) = true := h
  rw [Bool.and_eq_true] at h'
  have hlen : (conArrs R c.i c.j c.k c.use).length ≤ R.cuts.length + R.polys.length + 1 := by
    rw [conArrs_eq]
    have := selPolys_length R.polys c.use
    simp only [conPps, List.length_map, List.length_cons, List.length_append]
    omega
  obtain ⟨hgood, _⟩ := go_sound R (boxP R R.aH R.A c.i c.j c.k) (R.cuts.length + R.polys.length + 1)
    (hR.tree R.aH c.i c.j c.k) (Nat.succ_pos _) R.fuel c.tree _ _ _ hlen h'.2
  -- the local coordinates of the point
  obtain ⟨t1, t1a, t1b, e1⟩ := h1.local
  obtain ⟨t2, t2a, t2b, e2⟩ := h2.local
  obtain ⟨t3, t3a, t3b, e3⟩ := h3.local
  have hv : ∀ a : ℕ, 0 ≤ (if a = 0 then t1 else if a = 1 then t2 else t3) := by
    intro a
    split_ifs <;> assumption
  have hu : ∀ a : ℕ, 0 ≤ 1 - (if a = 0 then t1 else if a = 1 then t2 else t3) := by
    intro a
    split_ifs <;> linarith
  have hJv : Jv R.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) = 1 := by
    unfold Jv
    simp
  -- the product of the denominators
  have hQ : (0 : ℝ) < (((1 <<< (ent R.t1 c.i).e : ℕ) : ℕ) : ℝ) ^ R.n * (((1 <<< (ent R.t2 c.j).e : ℕ) : ℕ) : ℝ) ^ R.n
      * (((1 <<< (ent R.t3 c.k).e : ℕ) : ℕ) : ℝ) ^ R.n := by
    have a : ∀ e : ℕ, (0 : ℝ) < (((1 <<< e : ℕ) : ℕ) : ℝ) := by
      intro e
      rw [Nat.one_shiftLeft]
      positivity
    have := a (ent R.t1 c.i).e
    have := a (ent R.t2 c.j).e
    have := a (ent R.t3 c.k).e
    positivity
  -- the arrays of the constraints
  have hcons : ∀ l : List ℕ, (∀ Pp ∈ l, pEval (boxP R R.aG R.AG c.i c.j c.k) Pp x1 x2 x3 ≤ 0) →
      ∃ gs : List (ℕ → ℕ),
        List.Forall₂ (Arr (boxP R R.aH R.A c.i c.j c.k) R.AG) (l.map (rootArr (boxP R R.aG R.AG c.i c.j c.k))) gs ∧
        ∀ g ∈ gs, Phi (R.n + 1) (hwω R.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
          (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) g ≤ (R.AG : ℝ) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], List.Forall₂.nil, fun g hg => absurd hg (List.not_mem_nil)⟩
    | cons Pp l ih =>
      intro hl
      obtain ⟨gs, hgs, hval⟩ := ih (fun Pp' hPp' => hl Pp' (List.mem_cons_of_mem _ hPp'))
      obtain ⟨g, hg, hgv⟩ := rootArr_val (boxP R R.aG R.AG c.i c.j c.k) Pp
      refine ⟨g :: gs, List.Forall₂.cons hg hgs, fun g' hg' => ?_⟩
      rcases List.mem_cons.mp hg' with rfl | hg''
      · rcases hgv x1 x2 x3 t1 t2 t3 e1 e2 e3 with h0 | hv'
        · exact le_of_eq_of_le h0 (Nat.cast_nonneg _)
        · have hp := hl Pp List.mem_cons_self
          have : (R.AG : ℝ) + (((1 <<< (ent R.t1 c.i).e : ℕ) : ℕ) : ℝ) ^ R.n
              * (((1 <<< (ent R.t2 c.j).e : ℕ) : ℕ) : ℝ) ^ R.n * (((1 <<< (ent R.t3 c.k).e : ℕ) : ℕ) : ℝ) ^ R.n
              * pEval (boxP R R.aG R.AG c.i c.j c.k) Pp x1 x2 x3 ≤ R.AG := by nlinarith
          exact le_of_eq_of_le hv' this
      · exact hval g' hg''
  have hS : (0 : ℝ) < 2 ^ R.sg := by positivity
  obtain ⟨gs, hgs, hgval⟩ := hcons (conPps R c.use) (by
    intro Pp hPp
    rcases List.mem_cons.mp hPp with rfl | hPp'
    · rw [gram_poly R hR.con]
      nlinarith
    · rcases List.mem_append.mp hPp' with hcutm | hpolym
      · obtain ⟨cut, hcut, rfl⟩ := List.mem_map.mp hcutm
        rw [cut_poly R hR.con cut (hR.cuts cut hcut)]
        have := hC cut hcut
        nlinarith
      · exact hP Pp (selPolys_mem R.polys c.use Pp hpolym))
  rw [← conArrs_eq] at hgs
  -- the array of the polynomial
  obtain ⟨f, hf, hfv⟩ := rootArr_val (boxP R R.aH R.A c.i c.j c.k) (cellPp R c.i c.j c.k)
  have key := hgood f gs hf hgs _ _ hu hv (by
    intro g hg
    have := hgval g hg
    show Phi (R.n + 1) _ g ≤ (R.AG : ℝ) * Jv R.n _ _
    rw [hJv, mul_one]
    exact this)
  have key' : (R.A : ℝ) ≤ Phi (R.n + 1) (hwω R.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
      (fun a => if a = 0 then t1 else if a = 1 then t2 else t3)) f := by
    have : (R.A : ℝ) * Jv R.n (fun a => 1 - (if a = 0 then t1 else if a = 1 then t2 else t3))
        (fun a => if a = 0 then t1 else if a = 1 then t2 else t3) ≤ _ := key
    rw [hJv, mul_one] at this
    exact this
  rw [← cell_poly R hR.hM hR.hMs hR.hW hR.hn hR.haV R.A c.i c.j c.k x1 x2 x3]
  rcases hfv x1 x2 x3 t1 t2 t3 e1 e2 e3 with h0 | hv'
  · have key'' : (R.A : ℝ) ≤ 0 := le_of_le_of_eq key' h0
    have hA : (1 : ℝ) ≤ R.A := by exact_mod_cast hR.hA
    linarith
  · have key'' := le_of_le_of_eq key' hv'
    have h0 : (0 : ℝ) ≤ (((1 <<< (ent R.t1 c.i).e : ℕ) : ℕ) : ℝ) ^ R.n * (((1 <<< (ent R.t2 c.j).e : ℕ) : ℕ) : ℝ) ^ R.n
        * (((1 <<< (ent R.t3 c.k).e : ℕ) : ℕ) : ℝ) ^ R.n
        * pEval (boxP R R.aH R.A c.i c.j c.k) (cellPp R c.i c.j c.k) x1 x2 x3 := by
      have : (R.A : ℝ) ≤ (R.A : ℝ) + (((1 <<< (ent R.t1 c.i).e : ℕ) : ℕ) : ℝ) ^ R.n
          * (((1 <<< (ent R.t2 c.j).e : ℕ) : ℕ) : ℝ) ^ R.n * (((1 <<< (ent R.t3 c.k).e : ℕ) : ℕ) : ℝ) ^ R.n
          * pEval (boxP R R.aH R.A c.i c.j c.k) (cellPp R c.i c.j c.k) x1 x2 x3 := key''
      linarith
    exact (mul_nonneg_iff_of_pos_left hQ).mp h0

end N14.Box
