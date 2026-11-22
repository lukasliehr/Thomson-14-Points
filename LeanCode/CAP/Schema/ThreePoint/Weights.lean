module

public import CAP.Schema.ThreePoint.Semantics

/-!
# Schema S2, the bound: the weights of the blocks

The checker `weightsOk` compares the term fields of the weight of every block with those of the
three polynomials `1`, `1 - u ^ 2` and `1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2`.

**Theorem** (`weightsOk_sound`). If `weightsOk P sos = true`, then the weight of every block of
`sos`, as a polynomial with integer coefficients, is one of these three polynomials.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial

/-- The polynomial of a term field that is read as written. -/
theorem termZ_term (P : Params) {a b c coef neg : ℕ} (ha : a < 2 ^ P.eb) (hb : b < 2 ^ P.eb)
    (hc : c < 2 ^ P.eb) (hk : coef < 2 ^ P.cb) (hn : neg < 2) :
    termZ P (term P a b c coef neg)
      = (if Nat.beq neg 1 = true then -1 else 1) * (C (coef : ℤ) * (X 0 ^ a * X 1 ^ b * X 2 ^ c)) := by
  obtain ⟨-, h0, h1, h2, h3, h4⟩ := term_decode P ha hb hc hk hn
  unfold termZ
  rw [h0, h1, h2, h3, h4]

/-- The first of several term fields. -/
theorem polyZ_cons (P : Params) {f rest : ℕ} (hf : f < 2 ^ fw P) (T : ℕ) :
    polyZ P (T + 1) (f + 2 ^ fw P * rest) = termZ P f + polyZ P T rest := by
  rw [polyZ, (fld_head P hf).1, (fld_head P hf).2]

section weights
variable (P : Params) (heb : 2 ≤ P.eb) (hcb : 2 ≤ P.cb)
include heb hcb

theorem polyZ_wOne : polyZ P 1 (wOne P) = 1 := by
  have z : 0 < 2 ^ P.eb := small_lt_eb P heb (Nat.zero_le 2)
  have hk : 1 < 2 ^ P.cb := one_lt_cb P (by omega)
  have f0 := (term_decode P z z z hk (by norm_num : 0 < 2)).1
  have e : wOne P = term P 0 0 0 1 0 + 2 ^ fw P * 0 := by
    show term P 0 0 0 1 0 = _
    ring
  rw [e, polyZ_cons P f0 0, polyZ, termZ_term P z z z hk (by norm_num)]
  simp

theorem polyZ_wU : polyZ P 2 (wU P) = 1 - X 0 ^ 2 := by
  have z : 0 < 2 ^ P.eb := small_lt_eb P heb (Nat.zero_le 2)
  have t2 : 2 < 2 ^ P.eb := small_lt_eb P heb (le_refl 2)
  have hk : 1 < 2 ^ P.cb := one_lt_cb P (by omega)
  have f0 := (term_decode P z z z hk (by norm_num : 0 < 2)).1
  have f1 := (term_decode P t2 z z hk (by norm_num : 1 < 2)).1
  have e : wU P = term P 0 0 0 1 0 + 2 ^ fw P * (term P 2 0 0 1 1 + 2 ^ fw P * 0) := by
    show term P 0 0 0 1 0 + (term P 2 0 0 1 1) <<< (fw P) = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [e, polyZ_cons P f0 1, polyZ_cons P f1 0, polyZ, termZ_term P z z z hk (by norm_num),
    termZ_term P t2 z z hk (by norm_num)]
  simp
  ring

theorem polyZ_wDet :
    polyZ P 5 (wDet P) = 1 + 2 * X 0 * X 1 * X 2 - X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2 := by
  have z : 0 < 2 ^ P.eb := small_lt_eb P heb (Nat.zero_le 2)
  have o : 1 < 2 ^ P.eb := small_lt_eb P heb (by norm_num : 1 ≤ 2)
  have t2 : 2 < 2 ^ P.eb := small_lt_eb P heb (le_refl 2)
  have hk1 : 1 < 2 ^ P.cb := one_lt_cb P (by omega)
  have hk2 : 2 < 2 ^ P.cb := by
    have h : 2 ^ 2 ≤ 2 ^ P.cb := Nat.pow_le_pow_right (by norm_num) hcb
    omega
  have f0 := (term_decode P z z z hk1 (by norm_num : 0 < 2)).1
  have f1 := (term_decode P o o o hk2 (by norm_num : 0 < 2)).1
  have f2 := (term_decode P t2 z z hk1 (by norm_num : 1 < 2)).1
  have f3 := (term_decode P z t2 z hk1 (by norm_num : 1 < 2)).1
  have f4 := (term_decode P z z t2 hk1 (by norm_num : 1 < 2)).1
  have e : wDet P = term P 0 0 0 1 0 + 2 ^ fw P * (term P 1 1 1 2 0 + 2 ^ fw P * (term P 2 0 0 1 1
      + 2 ^ fw P * (term P 0 2 0 1 1 + 2 ^ fw P * (term P 0 0 2 1 1 + 2 ^ fw P * 0)))) := by
    show term P 0 0 0 1 0 + (term P 1 1 1 2 0 + (term P 2 0 0 1 1 + (term P 0 2 0 1 1
      + (term P 0 0 2 1 1) <<< (fw P)) <<< (fw P)) <<< (fw P)) <<< (fw P) = _
    simp only [Nat.shiftLeft_eq]
    ring
  rw [e, polyZ_cons P f0 4, polyZ_cons P f1 3, polyZ_cons P f2 2, polyZ_cons P f3 1, polyZ_cons P f4 0, polyZ,
    termZ_term P z z z hk1 (by norm_num), termZ_term P o o o hk2 (by norm_num),
    termZ_term P t2 z z hk1 (by norm_num), termZ_term P z t2 z hk1 (by norm_num),
    termZ_term P z z t2 hk1 (by norm_num)]
  simp
  ring

/-- The weight of an accepted block is one of the three weights. -/
theorem weightOk_sound (B : Sos) (h : weightOk P B = true) :
    polyZ P B.gT B.weight = 1 ∨ polyZ P B.gT B.weight = 1 - X 0 ^ 2
      ∨ polyZ P B.gT B.weight = 1 + 2 * X 0 * X 1 * X 2 - X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2 := by
  unfold weightOk at h
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · left
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
    exact polyZ_wOne P heb hcb
  · right
    left
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
    exact polyZ_wU P heb hcb
  · right
    right
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
    exact polyZ_wDet P heb hcb

end weights

theorem weightsAll_mem (P : Params) :
    ∀ l : List Sos, weightsAll P l = true → ∀ B ∈ l, weightOk P B = true
  | [], _, B, hB => by simp at hB
  | B0 :: l, h, B, hB => by
    have h' : (weightOk P B0 && weightsAll P l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hB with rfl | hB'
    · exact h'.1
    · exact weightsAll_mem P l h'.2 B hB'

/-- **Soundness of the checker of the weights.** -/
theorem weightsOk_sound (P : Params) (sos : List Sos) (h : weightsOk P sos = true) :
    ∀ B ∈ sos, polyZ P B.gT B.weight = 1 ∨ polyZ P B.gT B.weight = 1 - X 0 ^ 2
      ∨ polyZ P B.gT B.weight = 1 + 2 * X 0 * X 1 * X 2 - X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2 := by
  unfold weightsOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨heb, hcb⟩, hl⟩ := h
  exact fun B hB => weightOk_sound P (Nat.le_of_ble_eq_true heb) (Nat.le_of_ble_eq_true hcb) B
    (weightsAll_mem P sos hl B hB)

end CAP.ThreePoint
