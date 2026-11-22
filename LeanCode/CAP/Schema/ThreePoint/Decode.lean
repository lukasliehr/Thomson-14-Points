module

public import CAP.Schema.ThreePoint.Moment

/-!
# Schema S2, soundness: the fixed polynomials

The checker stores the two polynomials of the recurrence of the kernels as term fields:
`tuv P` for `t - u * v` and `wuv P` for `(1 - u ^ 2) * (1 - v ^ 2)`. If `2 ≤ eb` and `1 ≤ cb`, the
fields are read as written (`term_decode`), and the pairs of these polynomials are

  `tuvP P = (t, u * v)`,   `wuvP P = (1 + u ^ 2 * v ^ 2, u ^ 2 + v ^ 2)`.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial

theorem tExp_eq (P : Params) (f i : ℕ) : tExp P f i = f / 2 ^ (P.eb * i) % 2 ^ P.eb := by
  show (f >>> (P.eb * i)) &&& mask P.eb = _
  rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem tCoef_eq (P : Params) (f : ℕ) : tCoef P f = f / 2 ^ (3 * P.eb) % 2 ^ P.cb := by
  show (f >>> (3 * P.eb)) &&& mask P.cb = _
  rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem tNeg_eq (P : Params) (f : ℕ) : tNeg P f = Nat.beq (f / 2 ^ (3 * P.eb + P.cb)) 1 := by
  show Nat.beq (f >>> (3 * P.eb + P.cb)) 1 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem term_eq (P : Params) (a b c coef neg : ℕ) :
    term P a b c coef neg
      = a + 2 ^ P.eb * (b + 2 ^ P.eb * (c + 2 ^ P.eb * (coef + 2 ^ P.cb * neg))) := by
  show a + b <<< P.eb + c <<< (2 * P.eb) + coef <<< (3 * P.eb) + neg <<< (3 * P.eb + P.cb) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

/-- A term field whose entries fit into their bits is read as written. -/
theorem term_decode (P : Params) {a b c coef neg : ℕ} (ha : a < 2 ^ P.eb) (hb : b < 2 ^ P.eb)
    (hc : c < 2 ^ P.eb) (hk : coef < 2 ^ P.cb) (hn : neg < 2) :
    term P a b c coef neg < 2 ^ fw P ∧ tExp P (term P a b c coef neg) 0 = a ∧
      tExp P (term P a b c coef neg) 1 = b ∧ tExp P (term P a b c coef neg) 2 = c ∧
      tCoef P (term P a b c coef neg) = coef ∧ tNeg P (term P a b c coef neg) = Nat.beq neg 1 := by
  have he := Nat.two_pow_pos P.eb
  have hcb := Nat.two_pow_pos P.cb
  -- the tails of the field
  have d1 : term P a b c coef neg / 2 ^ P.eb = b + 2 ^ P.eb * (c + 2 ^ P.eb * (coef + 2 ^ P.cb * neg)) := by
    rw [term_eq, Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt ha, zero_add]
  have d2 : term P a b c coef neg / 2 ^ (P.eb * 2) = c + 2 ^ P.eb * (coef + 2 ^ P.cb * neg) := by
    rw [mul_two, pow_add, ← Nat.div_div_eq_div_mul, d1, Nat.add_mul_div_left _ _ he,
      Nat.div_eq_of_lt hb, zero_add]
  have d3 : term P a b c coef neg / 2 ^ (3 * P.eb) = coef + 2 ^ P.cb * neg := by
    have e : 3 * P.eb = P.eb * 2 + P.eb := by ring
    rw [e, pow_add, ← Nat.div_div_eq_div_mul, d2, Nat.add_mul_div_left _ _ he,
      Nat.div_eq_of_lt hc, zero_add]
  have d4 : term P a b c coef neg / 2 ^ (3 * P.eb + P.cb) = neg := by
    rw [pow_add, ← Nat.div_div_eq_div_mul, d3, Nat.add_mul_div_left _ _ hcb,
      Nat.div_eq_of_lt hk, zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the field is below `2 ^ fw`
    have h1 : coef + 2 ^ P.cb * neg < 2 ^ P.cb * 2 := digit_lt hk hn
    have h2 : c + 2 ^ P.eb * (coef + 2 ^ P.cb * neg) < 2 ^ P.eb * (2 ^ P.cb * 2) := digit_lt hc h1
    have h3 := digit_lt hb h2
    have h4 := digit_lt ha h3
    rw [term_eq, fw_eq]
    have e : 2 ^ (3 * P.eb + P.cb + 1) = 2 ^ P.eb * (2 ^ P.eb * (2 ^ P.eb * (2 ^ P.cb * 2))) := by
      ring
    rw [e]
    exact h4
  · rw [tExp_eq, mul_zero, pow_zero, Nat.div_one, term_eq, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha]
  · rw [tExp_eq, mul_one, d1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · rw [tExp_eq, d2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · rw [tCoef_eq, d3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  · rw [tNeg_eq, d4]

/-- The pair of a term field that is read as written. -/
theorem tPair_term (P : Params) {a b c coef neg : ℕ} (ha : a < 2 ^ P.eb) (hb : b < 2 ^ P.eb)
    (hc : c < 2 ^ P.eb) (hk : coef < 2 ^ P.cb) (hn : neg < 2) :
    tPair P (term P a b c coef neg) =
      if Nat.beq neg 1 = true then (0, C coef * (X 0 ^ a * X 1 ^ b * X 2 ^ c))
      else (C coef * (X 0 ^ a * X 1 ^ b * X 2 ^ c), 0) := by
  obtain ⟨-, h0, h1, h2, h3, h4⟩ := term_decode P ha hb hc hk hn
  unfold tPair tMono
  rw [h0, h1, h2, h3, h4]

/-- The first of several term fields: `fld` and the remaining fields. -/
theorem fld_head (P : Params) {f rest : ℕ} (hf : f < 2 ^ fw P) :
    fld P (f + 2 ^ fw P * rest) = f ∧ (f + 2 ^ fw P * rest) / 2 ^ fw P = rest := by
  constructor
  · rw [fld_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hf, zero_add]

theorem small_lt_eb (P : Params) (heb : 2 ≤ P.eb) {x : ℕ} (hx : x ≤ 2) : x < 2 ^ P.eb := by
  have h : 2 ^ 2 ≤ 2 ^ P.eb := Nat.pow_le_pow_right (by norm_num) heb
  omega

theorem one_lt_cb (P : Params) (hcb : 1 ≤ P.cb) : 1 < 2 ^ P.cb := Nat.one_lt_two_pow (by omega)

section fixed
variable (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb)
include heb hcb

/-- `t - u * v` as a pair. -/
theorem tuvP_eq : tuvP P = (X 2, X 0 * X 1) := by
  have hx := fun {x : ℕ} (h : x ≤ 2) => small_lt_eb P heb h
  have hk := one_lt_cb P hcb
  have f1 := (term_decode P (hx (Nat.zero_le 2)) (hx (Nat.zero_le 2)) (hx (by norm_num : 1 ≤ 2)) hk
    (by norm_num : 0 < 2)).1
  have f2 := (term_decode P (hx (by norm_num : 1 ≤ 2)) (hx (by norm_num : 1 ≤ 2)) (hx (Nat.zero_le 2)) hk
    (by norm_num : 1 < 2)).1
  have e : tuv P = term P 0 0 1 1 0 + 2 ^ fw P * (term P 1 1 0 1 1 + 2 ^ fw P * 0) := by
    show term P 0 0 1 1 0 + (term P 1 1 0 1 1) <<< (fw P) = _
    rw [Nat.shiftLeft_eq]
    ring
  unfold tuvP
  rw [e, polyOf, (fld_head P f1).1, (fld_head P f1).2, polyOf, (fld_head P f2).1, (fld_head P f2).2,
    polyOf,
    tPair_term P (hx (Nat.zero_le 2)) (hx (Nat.zero_le 2)) (hx (by norm_num : 1 ≤ 2)) hk (by norm_num : 0 < 2),
    tPair_term P (hx (by norm_num : 1 ≤ 2)) (hx (by norm_num : 1 ≤ 2)) (hx (Nat.zero_le 2)) hk
      (by norm_num : 1 < 2)]
  refine Prod.ext ?_ ?_ <;> simp

/-- `(1 - u ^ 2) * (1 - v ^ 2)` as a pair. -/
theorem wuvP_eq : wuvP P = (1 + X 0 ^ 2 * X 1 ^ 2, X 0 ^ 2 + X 1 ^ 2) := by
  have hx := fun {x : ℕ} (h : x ≤ 2) => small_lt_eb P heb h
  have hk := one_lt_cb P hcb
  have h0 : (0 : ℕ) ≤ 2 := Nat.zero_le 2
  have h2 : (2 : ℕ) ≤ 2 := le_refl 2
  have f1 := (term_decode P (hx h0) (hx h0) (hx h0) hk (by norm_num : 0 < 2)).1
  have f2 := (term_decode P (hx h2) (hx h0) (hx h0) hk (by norm_num : 1 < 2)).1
  have f3 := (term_decode P (hx h0) (hx h2) (hx h0) hk (by norm_num : 1 < 2)).1
  have f4 := (term_decode P (hx h2) (hx h2) (hx h0) hk (by norm_num : 0 < 2)).1
  have e : wuv P = term P 0 0 0 1 0 + 2 ^ fw P * (term P 2 0 0 1 1 + 2 ^ fw P * (term P 0 2 0 1 1
      + 2 ^ fw P * (term P 2 2 0 1 0 + 2 ^ fw P * 0))) := by
    show term P 0 0 0 1 0 + (term P 2 0 0 1 1) <<< (fw P) + (term P 0 2 0 1 1) <<< (2 * fw P)
      + (term P 2 2 0 1 0) <<< (3 * fw P) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    ring
  unfold wuvP
  rw [e, polyOf, (fld_head P f1).1, (fld_head P f1).2, polyOf, (fld_head P f2).1, (fld_head P f2).2,
    polyOf, (fld_head P f3).1, (fld_head P f3).2, polyOf, (fld_head P f4).1, (fld_head P f4).2, polyOf,
    tPair_term P (hx h0) (hx h0) (hx h0) hk (by norm_num : 0 < 2),
    tPair_term P (hx h2) (hx h0) (hx h0) hk (by norm_num : 1 < 2),
    tPair_term P (hx h0) (hx h2) (hx h0) hk (by norm_num : 1 < 2),
    tPair_term P (hx h2) (hx h2) (hx h0) hk (by norm_num : 0 < 2)]
  refine Prod.ext ?_ ?_ <;> simp

end fixed

end CAP.ThreePoint
