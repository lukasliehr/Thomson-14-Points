module

public import Mathlib.Data.List.Basic
public import CAP.Core.PackedLemmas
public import CAP.Interval.Ball

/-!
# E6, interval arithmetic: soundness of the checker

**Theorem** (`CAP.Interval.check_sound`). Let `prog` be a program, and let `sem P prog env` be the
list of the real numbers that it defines from the inputs `env`: the inputs themselves, followed by
one number for each instruction (`den`). If `CAP.Interval.check P prog wit R0 nin claims = true` and
if every input lies in its ball, then for every claim `(i, lo, hi)`

  `(lo - B) / 2 ^ p ≤ x_i ≤ (hi - B) / 2 ^ p`,   `B = 2 ^ (W - 1)`,

where `x_i` is the number in register `i`.

The proof follows the checker. The invariant of the loop (`Inv`) states that the packed number `R`
consists of `k` registers and that register `i` is a ball that contains the `i`-th real number.
An instruction preserves it by the statements of `CAP/Interval/Ball.lean` (`step_sound`,
`push_inv`).
-/

@[expose] public section

namespace CAP.Interval

/-! ## The real numbers of a program -/

/-- The real number that an instruction defines from the registers `regs`. A register that does
not exist is read as `0`. -/
noncomputable def den (P : Params) (regs : List ℝ) : Instr → ℝ
  | .nat n => n
  | .cst b => ((b : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p
  | .add i j => regs.getD i 0 + regs.getD j 0
  | .sub i j => regs.getD i 0 - regs.getD j 0
  | .mul i j => regs.getD i 0 * regs.getD j 0
  | .inv i => (regs.getD i 0)⁻¹
  | .sqrt i => Real.sqrt (regs.getD i 0)

/-- The registers after a program that starts with the registers `regs`. -/
noncomputable def sem (P : Params) : List Instr → List ℝ → List ℝ
  | [], regs => regs
  | ins :: rest, regs => sem P rest (regs ++ [den P regs ins])

/-! ## The invariant -/

/-- The packed number `R` consists of `k` registers, and register `i` is a ball that contains the
`i`-th number of `regs`. -/
def Inv (P : Params) (B R k : ℕ) (regs : List ℝ) : Prop :=
  regs.length = k ∧ R < 2 ^ (P.W * (2 * k)) ∧
    ∀ i, i < k → Enc P.p B (slot P.W R (2 * i)) (slot P.W R (2 * i + 1)) (regs.getD i 0)

/-- An accepted instruction defines a ball that contains the real number of the instruction. -/
theorem step_sound (P : Params) (B R k : ℕ) (hB : B = 2 ^ (P.W - 1)) (wit : List ℕ) (regs : List ℝ)
    (hI : Inv P B R k regs) (ins : Instr) (hok : (step P B R k wit ins).1.2.2 = true) :
    Enc P.p B (step P B R k wit ins).1.1 (step P B R k wit ins).1.2.1 (den P regs ins) := by
  obtain ⟨_, _, hE⟩ := hI
  cases ins with
  | nat n =>
    show Enc P.p B (B + n <<< P.p) 0 (n : ℝ)
    rw [Nat.shiftLeft_eq]
    exact nat_sound P.p B n
  | cst b =>
    show Enc P.p B b 0 (((b : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p)
    have h := cst_sound P.p B b
    rw [hB] at h ⊢
    push_cast at h
    exact h
  | add i j =>
    obtain ⟨h1, h2⟩ := withFlag_ok hok
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h2
    exact addB_sound (hE i h2.1) (hE j h2.2) h1
  | sub i j =>
    obtain ⟨h1, h2⟩ := withFlag_ok hok
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h2
    exact subB_sound (hE i h2.1) (hE j h2.2) h1
  | mul i j =>
    obtain ⟨h1, h2⟩ := withFlag_ok hok
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h2
    exact mulB_sound (hE i h2.1) (hE j h2.2) h1
  | inv i =>
    obtain ⟨h1, h2⟩ := withFlag_ok hok
    rw [Nat.blt_eq] at h2
    exact invB_sound (hE i h2) h1
  | sqrt i =>
    cases wit with
    | nil => exact Bool.noConfusion (show false = true from hok)
    | cons t tl =>
      obtain ⟨h1, h2⟩ := withFlag_ok hok
      rw [Nat.blt_eq] at h2
      exact sqrtB_sound (hE i h2) h1

/-- Two numbers whose disjunction is below `2 ^ W` are below `2 ^ W`. -/
theorem lt_of_lor_shift {W b r : ℕ} (h : (b ||| r) >>> W = 0) : b < 2 ^ W ∧ r < 2 ^ W := by
  rw [Nat.shiftRight_eq_div_pow] at h
  have h1 : b ||| r < 2 ^ W := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos W)).mp h
  exact ⟨lt_of_le_of_lt Nat.left_le_or h1, lt_of_le_of_lt Nat.right_le_or h1⟩

theorem getD_append_lt {α : Type*} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_length {α : Type*} (l : List α) (d v : α) : (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

/-- Storing a ball as the next register preserves the invariant. -/
theorem push_inv (P : Params) (B R k b r : ℕ) (regs : List ℝ) (v : ℝ) (hI : Inv P B R k regs)
    (hv : Enc P.p B b r v) (hfit : (b ||| r) >>> P.W = 0) :
    Inv P B (R + (b + r <<< P.W) <<< (2 * P.W * k)) (k + 1) (regs ++ [v]) := by
  obtain ⟨hlen, hR, hE⟩ := hI
  obtain ⟨hb, hr⟩ := lt_of_lor_shift hfit
  have hK : 2 * P.W * k = P.W * (2 * k) := by ring
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, hK]
  have hpos : 0 < 2 ^ (P.W * (2 * k)) := Nat.two_pow_pos _
  -- the two parts of the new number
  have hmod : (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) % 2 ^ (P.W * (2 * k)) = R := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR]
  have hdiv : (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) / 2 ^ (P.W * (2 * k)) = b + r * 2 ^ P.W := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hR, Nat.zero_add]
  have hold : ∀ s, s < 2 * k →
      slot P.W (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) s = slot P.W R s := by
    intro s hs
    rw [← slot_mod P.W _ (2 * k) s hs, hmod]
  have hnew0 : slot P.W (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) (2 * k) = b := by
    have h := slot_div P.W (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) (2 * k) 0
    rw [Nat.add_zero, hdiv] at h
    rw [← h, slot_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hb]
  have hnew1 : slot P.W (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) (2 * k + 1) = r := by
    have h := slot_div P.W (R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))) (2 * k) 1
    rw [hdiv] at h
    rw [← h, slot_eq, Nat.mul_one, Nat.add_mul_div_right _ _ (Nat.two_pow_pos P.W), Nat.div_eq_of_lt hb,
      Nat.zero_add, Nat.mod_eq_of_lt hr]
  refine ⟨by simp [hlen], ?_, ?_⟩
  · -- the size
    have h1 : b + r * 2 ^ P.W + 1 ≤ 2 ^ P.W * 2 ^ P.W := by
      have : (r + 1) * 2 ^ P.W ≤ 2 ^ P.W * 2 ^ P.W := Nat.mul_le_mul_right _ hr
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have h2 : P.W * (2 * (k + 1)) = P.W + P.W + P.W * (2 * k) := by ring
    rw [h2, pow_add, pow_add]
    calc R + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k))
        < 2 ^ (P.W * (2 * k)) + (b + r * 2 ^ P.W) * 2 ^ (P.W * (2 * k)) := by omega
      _ = (b + r * 2 ^ P.W + 1) * 2 ^ (P.W * (2 * k)) := by ring
      _ ≤ 2 ^ P.W * 2 ^ P.W * 2 ^ (P.W * (2 * k)) := Nat.mul_le_mul_right _ h1
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · rw [hold (2 * i) (by omega), hold (2 * i + 1) (by omega),
        getD_append_lt _ _ _ _ (by rw [hlen]; exact hlt)]
      exact hE i hlt
    · subst heq
      rw [hnew0, hnew1, ← hlen, getD_append_length]
      exact hv

theorem bool_rec_and (c t : Bool) : Bool.rec (motive := fun _ => Bool) false t c = (c && t) := by
  cases c <;> rfl

/-- The loop preserves the invariant and ends with the final test. -/
theorem run_sound (P : Params) (B : ℕ) (hB : B = 2 ^ (P.W - 1)) (fin : ℕ → ℕ → Bool) :
    ∀ (prog : List Instr) (R k : ℕ) (wit : List ℕ) (regs : List ℝ), Inv P B R k regs →
      run P B fin prog R k wit = true →
      ∃ R' k', Inv P B R' k' (sem P prog regs) ∧ fin R' k' = true
  | [], R, k, _, regs, hI, h => ⟨R, k, hI, h⟩
  | ins :: rest, R, k, wit, regs, hI, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (run P B fin rest (R + ((step P B R k wit ins).1.1 + (step P B R k wit ins).1.2.1 <<< P.W)
            <<< (2 * P.W * k)) (k + 1) (step P B R k wit ins).2)
        ((step P B R k wit ins).1.2.2 &&
          Nat.beq (((step P B R k wit ins).1.1 ||| (step P B R k wit ins).1.2.1) >>> P.W) 0) = true := h
    rw [bool_rec_and, Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨⟨hok, hfit⟩, hrest⟩ := h'
    have hv := step_sound P B R k hB wit regs hI ins hok
    have hI' := push_inv P B R k _ _ regs _ hI hv (Nat.eq_of_beq_eq_true hfit)
    exact run_sound P B hB fin rest _ _ _ _ hI' hrest

/-! ## The claims -/

theorem claimsOk_sound (P : Params) (B R k : ℕ) (regs : List ℝ) (hI : Inv P B R k regs) :
    ∀ claims : List (ℕ × ℕ × ℕ), claimsOk P R k claims = true →
      ∀ c ∈ claims, ((c.2.1 : ℝ) - B) / 2 ^ P.p ≤ regs.getD c.1 0 ∧
        regs.getD c.1 0 ≤ ((c.2.2 : ℝ) - B) / 2 ^ P.p
  | [], _, c, hc => by simp at hc
  | d :: rest, h, c, hc => by
    have h' : (Nat.blt d.1 k && Nat.ble (d.2.1 + slot P.W R (2 * d.1 + 1)) (slot P.W R (2 * d.1))
        && Nat.ble (slot P.W R (2 * d.1) + slot P.W R (2 * d.1 + 1)) d.2.2
        && claimsOk P R k rest) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    rcases List.mem_cons.mp hc with rfl | hmem
    · have hE := hI.2.2 c.1 h1
      have h2' : (c.2.1 : ℝ) + slot P.W R (2 * c.1 + 1) ≤ slot P.W R (2 * c.1) := by
        exact_mod_cast Nat.le_of_ble_eq_true h2
      have h3' : (slot P.W R (2 * c.1) : ℝ) + slot P.W R (2 * c.1 + 1) ≤ c.2.2 := by
        exact_mod_cast Nat.le_of_ble_eq_true h3
      unfold Enc at hE
      rw [abs_le] at hE
      have hs := two_pow_pos' P.p
      constructor
      · rw [div_le_iff₀ hs]
        linarith [hE.1]
      · rw [le_div_iff₀ hs]
        linarith [hE.2]
    · exact claimsOk_sound P B R k regs hI rest h4 c hmem

/-! ## The theorem -/

/-- **Soundness of the checker of E6.** If the checker accepts and every input lies in its ball,
then the real number of every claimed register lies in the claimed interval. -/
theorem check_sound (P : Params) (prog : List Instr) (wit : List ℕ) (R0 nin : ℕ)
    (claims : List (ℕ × ℕ × ℕ)) (h : check P prog wit R0 nin claims = true) (env : List ℝ)
    (hlen : env.length = nin)
    (henv : ∀ i, i < nin →
      Enc P.p (2 ^ (P.W - 1)) (slot P.W R0 (2 * i)) (slot P.W R0 (2 * i + 1)) (env.getD i 0)) :
    ∀ c ∈ claims, ((c.2.1 : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p ≤ (sem P prog env).getD c.1 0 ∧
      (sem P prog env).getD c.1 0 ≤ ((c.2.2 : ℝ) - 2 ^ (P.W - 1)) / 2 ^ P.p := by
  have h' : (Nat.ble 1 P.W && Nat.beq (R0 >>> (2 * P.W * nin)) 0 &&
      run P (1 <<< (P.W - 1)) (fun R k => claimsOk P R k claims) prog R0 nin wit) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.one_shiftLeft] at h'
  obtain ⟨⟨_, hR0⟩, hrun⟩ := h'
  have hR : R0 < 2 ^ (P.W * (2 * nin)) := by
    have h0 := Nat.eq_of_beq_eq_true hR0
    rw [Nat.shiftRight_eq_div_pow, show 2 * P.W * nin = P.W * (2 * nin) by ring] at h0
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp h0
  have hI : Inv P (2 ^ (P.W - 1)) R0 nin env := ⟨hlen, hR, henv⟩
  obtain ⟨R', k', hI', hfin⟩ := run_sound P _ rfl _ prog R0 nin wit env hI hrun
  intro c hc
  have key := claimsOk_sound P _ R' k' _ hI' claims hfin c hc
  push_cast at key
  exact key

/-- The claims as balls: a claim `(i, b - r, b + r)` states that register `i` lies in the ball
`(b, r)`. -/
theorem check_sound_enc (P : Params) (prog : List Instr) (wit : List ℕ) (R0 nin : ℕ)
    (claims : List (ℕ × ℕ × ℕ)) (h : check P prog wit R0 nin claims = true) (env : List ℝ)
    (hlen : env.length = nin)
    (henv : ∀ i, i < nin →
      Enc P.p (2 ^ (P.W - 1)) (slot P.W R0 (2 * i)) (slot P.W R0 (2 * i + 1)) (env.getD i 0))
    (c : ℕ × ℕ × ℕ) (hc : c ∈ claims) (b r : ℕ) (hlo : c.2.1 + r = b) (hhi : c.2.2 = b + r) :
    Enc P.p (2 ^ (P.W - 1)) b r ((sem P prog env).getD c.1 0) := by
  obtain ⟨h1, h2⟩ := check_sound P prog wit R0 nin claims h env hlen henv c hc
  have hs := two_pow_pos' P.p
  rw [div_le_iff₀ hs] at h1
  rw [le_div_iff₀ hs] at h2
  have e1 : (c.2.1 : ℝ) + r = b := by exact_mod_cast hlo
  have e2 : (c.2.2 : ℝ) = b + r := by exact_mod_cast hhi
  unfold Enc
  rw [abs_le]
  push_cast
  constructor <;> linarith

theorem getD_mem_of_lt {α : Type*} (l : List α) (d : α) (k : ℕ) (hk : k < l.length) : l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

end CAP.Interval
