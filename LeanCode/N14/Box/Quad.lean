module

public import N14.Box.QuadKernel
public import N14.Box.Cover

/-!
# T7, a polynomial constraint that is given by its terms: soundness

`qEval l` is the polynomial `∑ (p - q) x₁^e₁ x₂^e₂ x₃^e₃` of a list of terms.

* `quad_poly`: if `quadOk R l Pp = true`, the number `Pp` is the polynomial `-qEval l` in the sense of
  `CAP.Bernstein.pEval`, with the bias of the constraints.
* **`polyVal_quad`**: then the function of the constraint `Pp` of the run (`polyVal`, the function whose
  nonnegativity is part of `Dom`) is `qEval l / 2 ^ sg`.

So the domain of a run with polynomial constraints is stated by explicit polynomials, and no sample is needed to
see which region the numbers of the run describe.
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein Finset

/-- The polynomial of a list of terms. -/
noncomputable def qEval : List QTerm → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | t :: l, x1, x2, x3 => ((t.p : ℝ) - t.q) * (x1 ^ t.e1 * x2 ^ t.e2 * x3 ^ t.e3) + qEval l x1 x2 x3

theorem qPos_cons (R : Run) (t : QTerm) (l : List QTerm) :
    qPos R (t :: l) = t.p * unit3 R t.e1 t.e2 t.e3 + qPos R l := rfl

theorem qNeg_cons (R : Run) (t : QTerm) (l : List QTerm) :
    qNeg R (t :: l) = t.q * unit3 R t.e1 t.e2 t.e3 + qNeg R l := rfl

theorem qNotIn_cons (n i : ℕ) (t : QTerm) (l : List QTerm) :
    qNotIn n i (t :: l) = (!(Nat.beq (qIdx n t) i) && qNotIn n i l) := rfl

theorem qDistinct_cons (n : ℕ) (t : QTerm) (l : List QTerm) :
    qDistinct n (t :: l) = (qNotIn n (qIdx n t) l && qDistinct n l) := rfl

theorem qBounds_cons (bias top : ℕ) (t : QTerm) (l : List QTerm) :
    qBounds bias top (t :: l) = (Nat.ble t.p bias && Nat.blt (bias + t.q) top && qBounds bias top l) := rfl

theorem unitF_idx (n : ℕ) (t : QTerm) (c e : ℕ) :
    unitF (n + 1) t.e1 t.e2 t.e3 c e = if e = qIdx n t then c else 0 := rfl

theorem qFits_cons (n : ℕ) (t : QTerm) (l : List QTerm) :
    qFits n (t :: l) = (Nat.ble t.e1 n && Nat.ble t.e2 n && Nat.ble t.e3 n && qFits n l) := rfl

theorem qFits_of_cons {n : ℕ} {t : QTerm} {l : List QTerm} (h : qFits n (t :: l) = true) :
    (t.e1 ≤ n ∧ t.e2 ≤ n ∧ t.e3 ≤ n) ∧ qFits n l = true := by
  rw [qFits_cons] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3⟩, h4⟩

/-- The array of the first parts of the coefficients, and that of the second parts. -/
def gP (m : ℕ) : List QTerm → ℕ → ℕ
  | [], _ => 0
  | t :: l, e => unitF m t.e1 t.e2 t.e3 t.p e + gP m l e

def gQ (m : ℕ) : List QTerm → ℕ → ℕ
  | [], _ => 0
  | t :: l, e => unitF m t.e1 t.e2 t.e3 t.q e + gQ m l e

theorem gP_zero (n : ℕ) : ∀ (l : List QTerm) (e : ℕ), qNotIn n e l = true → gP (n + 1) l e = 0
  | [], _, _ => rfl
  | t :: l, e, h => by
    rw [qNotIn_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hne : qIdx n t ≠ e := Nat.ne_of_beq_eq_false h.1
    show unitF (n + 1) t.e1 t.e2 t.e3 t.p e + gP (n + 1) l e = 0
    rw [unitF_idx, if_neg (fun h' => hne h'.symm), gP_zero n l e h.2]

theorem gQ_zero (n : ℕ) : ∀ (l : List QTerm) (e : ℕ), qNotIn n e l = true → gQ (n + 1) l e = 0
  | [], _, _ => rfl
  | t :: l, e, h => by
    rw [qNotIn_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hne : qIdx n t ≠ e := Nat.ne_of_beq_eq_false h.1
    show unitF (n + 1) t.e1 t.e2 t.e3 t.q e + gQ (n + 1) l e = 0
    rw [unitF_idx, if_neg (fun h' => hne h'.symm), gQ_zero n l e h.2]

/-- With distinct places, every entry of the array of the first parts is at most the bound of the terms. -/
theorem gP_bound (n bias top : ℕ) : ∀ l : List QTerm, qDistinct n l = true → qBounds bias top l = true →
    ∀ e, gP (n + 1) l e ≤ bias
  | [], _, _, _ => Nat.zero_le _
  | t :: l, hd, hb, e => by
    rw [qDistinct_cons, Bool.and_eq_true] at hd
    rw [qBounds_cons] at hb
    simp only [Bool.and_eq_true] at hb
    show unitF (n + 1) t.e1 t.e2 t.e3 t.p e + gP (n + 1) l e ≤ bias
    rw [unitF_idx]
    by_cases h : e = qIdx n t
    · rw [if_pos h, h, gP_zero n l (qIdx n t) hd.1, Nat.add_zero]
      exact Nat.le_of_ble_eq_true hb.1.1
    · rw [if_neg h, Nat.zero_add]
      exact gP_bound n bias top l hd.2 hb.2 e

theorem gQ_bound (n bias top : ℕ) (h0 : bias < top) : ∀ l : List QTerm, qDistinct n l = true →
    qBounds bias top l = true → ∀ e, bias + gQ (n + 1) l e < top
  | [], _, _, _ => h0
  | t :: l, hd, hb, e => by
    rw [qDistinct_cons, Bool.and_eq_true] at hd
    rw [qBounds_cons] at hb
    simp only [Bool.and_eq_true] at hb
    show bias + (unitF (n + 1) t.e1 t.e2 t.e3 t.q e + gQ (n + 1) l e) < top
    rw [unitF_idx]
    by_cases h : e = qIdx n t
    · rw [if_pos h, h, gQ_zero n l (qIdx n t) hd.1, Nat.add_zero]
      have h2 := hb.1.2
      rw [Nat.blt_eq] at h2
      exact h2
    · rw [if_neg h, Nat.zero_add]
      exact gQ_bound n bias top h0 l hd.2 hb.2 e

theorem qPos_packSum (R : Run) : ∀ l : List QTerm, qFits R.n l = true →
    qPos R l = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) (gP (R.n + 1) l)
  | [], _ => by
    show 0 = packSum _ _ (fun _ => 0)
    simp [packSum]
  | t :: l, h => by
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := qFits_of_cons h
    rw [qPos_cons, qPos_packSum R l h4, unit3_eq,
      ← packSum_unitF R.V (R.n + 1) t.e1 t.e2 t.e3 t.p (by omega) (by omega) (by omega), ← packSum_add]
    rfl

theorem qNeg_packSum (R : Run) : ∀ l : List QTerm, qFits R.n l = true →
    qNeg R l = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) (gQ (R.n + 1) l)
  | [], _ => by
    show 0 = packSum _ _ (fun _ => 0)
    simp [packSum]
  | t :: l, h => by
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := qFits_of_cons h
    rw [qNeg_cons, qNeg_packSum R l h4, unit3_eq,
      ← packSum_unitF R.V (R.n + 1) t.e1 t.e2 t.e3 t.q (by omega) (by omega) (by omega), ← packSum_add]
    rfl

/-- The values of the two parts. -/
noncomputable def wP (ω : ℕ → ℕ → ℝ) : List QTerm → ℝ
  | [] => 0
  | t :: l => (t.p : ℝ) * (ω 0 t.e1 * ω 1 t.e2 * ω 2 t.e3) + wP ω l

noncomputable def wQ (ω : ℕ → ℕ → ℝ) : List QTerm → ℝ
  | [] => 0
  | t :: l => (t.q : ℝ) * (ω 0 t.e1 * ω 1 t.e2 * ω 2 t.e3) + wQ ω l

theorem Phi_zero (m : ℕ) (ω : ℕ → ℕ → ℝ) : Phi m ω (fun _ => 0) = 0 := by
  unfold Phi
  simp

theorem Phi_gP (n : ℕ) (ω : ℕ → ℕ → ℝ) : ∀ l : List QTerm, qFits n l = true →
    Phi (n + 1) ω (gP (n + 1) l) = wP ω l
  | [], _ => Phi_zero (n + 1) ω
  | t :: l, h => by
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := qFits_of_cons h
    show Phi (n + 1) ω (fun e => unitF (n + 1) t.e1 t.e2 t.e3 t.p e + gP (n + 1) l e) = _
    rw [Phi_add, Phi_unitF _ _ _ _ _ _ (by omega) (by omega) (by omega), Phi_gP n ω l h4]
    rfl

theorem Phi_gQ (n : ℕ) (ω : ℕ → ℕ → ℝ) : ∀ l : List QTerm, qFits n l = true →
    Phi (n + 1) ω (gQ (n + 1) l) = wQ ω l
  | [], _ => Phi_zero (n + 1) ω
  | t :: l, h => by
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := qFits_of_cons h
    show Phi (n + 1) ω (fun e => unitF (n + 1) t.e1 t.e2 t.e3 t.q e + gQ (n + 1) l e) = _
    rw [Phi_add, Phi_unitF _ _ _ _ _ _ (by omega) (by omega) (by omega), Phi_gQ n ω l h4]
    rfl

theorem qEval_eq (x1 x2 x3 : ℝ) : ∀ l : List QTerm,
    qEval l x1 x2 x3 = wP (pw x1 x2 x3) l - wQ (pw x1 x2 x3) l
  | [] => by simp [qEval, wP, wQ]
  | t :: l => by
    have h := qEval_eq x1 x2 x3 l
    simp only [qEval, wP, wQ, pw] at h ⊢
    rw [h]
    norm_num
    ring

/-- **The number of a constraint is its polynomial.** -/
theorem quad_poly (R : Run) (l : List QTerm) (Pp : ℕ) (h : quadOk R l Pp = true) (A i j k : ℕ)
    (x1 x2 x3 : ℝ) : pEval (boxP R R.aG A i j k) Pp x1 x2 x3 = -qEval l x1 x2 x3 := by
  have h' : (Nat.ble 1 R.V && qFits R.n l && qDistinct R.n l &&
      Nat.blt (1 <<< (R.aG - 1)) (1 <<< R.V) && qBounds (1 <<< (R.aG - 1)) (1 <<< R.V) l
      && Nat.beq Pp (quadPp R l)) = true := h
  simp only [Bool.and_eq_true, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h'
  have hV : 1 ≤ R.V := Nat.le_of_ble_eq_true a1
  have h0 : 2 ^ (R.aG - 1) < 2 ^ R.V := by
    rw [Nat.blt_eq] at a4
    exact a4
  have hPp : Pp = quadPp R l := Nat.eq_of_beq_eq_true a6
  have hle : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) →
      gP (R.n + 1) l e ≤ 2 ^ (R.aG - 1) + gQ (R.n + 1) l e := fun e _ => by
    have := gP_bound R.n (2 ^ (R.aG - 1)) (2 ^ R.V) l a3 a5 e
    omega
  have hlt : ∀ e, e < (R.n + 1) * (R.n + 1) * (R.n + 1) →
      (2 ^ (R.aG - 1) + gQ (R.n + 1) l e) - gP (R.n + 1) l e < 2 ^ R.V := fun e _ => by
    have := gQ_bound R.n (2 ^ (R.aG - 1)) (2 ^ R.V) h0 l a3 a5 e
    have hpos : 0 < 2 ^ R.V := Nat.two_pow_pos _
    omega
  have e1 : quadPp R l = packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1))
      (fun e => (2 ^ (R.aG - 1) + gQ (R.n + 1) l e) - gP (R.n + 1) l e) := by
    show (biasG R + qNeg R l) - qPos R l = _
    rw [biasG_packSum R hV, qNeg_packSum R l a2, qPos_packSum R l a2, ← packSum_add, packSum_sub _ _ _ _ hle]
  rw [hPp, e1]
  have hP : pEval (boxP R R.aG A i j k) (packSum R.V ((R.n + 1) * (R.n + 1) * (R.n + 1)) _) x1 x2 x3 = _ :=
    pEval_packSum (boxP R R.aG A i j k) _ hlt x1 x2 x3
  rw [hP]
  show Phi (R.n + 1) (pw x1 x2 x3) _ - Phi (R.n + 1) (pw x1 x2 x3) (fun _ => 2 ^ (R.aG - 1)) = _
  rw [Phi_sub _ _ hle, Phi_add, Phi_gP R.n _ l a2, Phi_gQ R.n _ l a2, qEval_eq]
  ring

/-- **The function of a polynomial constraint of a run.** -/
theorem polyVal_quad (R : Run) (l : List QTerm) (Pp : ℕ) (h : quadOk R l Pp = true) (x1 x2 x3 : ℝ) :
    polyVal R Pp x1 x2 x3 = qEval l x1 x2 x3 / 2 ^ R.sg := by
  unfold polyVal
  rw [quad_poly R l Pp h, neg_neg]

end N14.Box
