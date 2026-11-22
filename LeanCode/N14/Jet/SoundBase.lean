module

public import N14.Jet.Pass

/-!
# Jets: soundness of the checker, the simple operations

`Good par r J F`: if the flag of the jet `J` is set, then `J` is the result of a pass with triples `h`, and there
are a sequence `c` and a number `κ` with `Rep r F c κ` such that `κ` is at most `J.K` in units of `2^-s` and the
triple of every valid slot encloses the coefficient of `c` in units of `2^-s` (`Enc`).

This file proves `Good` for the operations without a product: constants, variables, the trigonometric functions
of a variable, sums, negatives and multiples by an enclosed constant. The rounding of the checker is in
`cdiv_ge`, `cdivn_ge`, `enc_sound` and `resc_sound`.
-/

@[expose] public section

namespace N14.Jet

open CAP Finset

/-- The radius of the box in the bounds of the checker: `33 / 4096`. -/
noncomputable def rb : ℝ := 33 / 4096

/-- The triples enclose the coefficients, in units of `2^-s`. -/
def Enc (s : ℕ) (h : ℕ → T3) (c : ℕ → ℝ) : Prop :=
  ∀ e, Valid e → |2 ^ s * c e - (((h e).p : ℝ) - (h e).n)| ≤ (h e).r

/-- The jet `J` encloses the function `F` on the box of radius `r`, if its flag is set. -/
def Good (par : Par) (r : ℝ) (J : Jet) (F : (Fin 4 → ℝ) → ℝ) : Prop :=
  J.ok = true → ∃ (h : ℕ → T3) (c : ℕ → ℝ) (κ : ℝ),
    IsPass par.w J h ∧ Rep r F c κ ∧ 0 ≤ κ ∧ κ * 2 ^ par.s ≤ J.K ∧ Enc par.s h c

/-! ## Rounding -/

theorem cond_beq {α : Type} (e k : ℕ) (x y : α) : cond (Nat.beq e k) x y = if e = k then x else y := by
  by_cases h : e = k
  · subst h
    rw [if_pos rfl, Nat.beq_refl]
    rfl
  · rw [if_neg h]
    have hb : Nat.beq e k = false := by
      cases hb : Nat.beq e k
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [hb]
    rfl

theorem le_div_mul (x d : ℕ) (hd : 0 < d) : x ≤ (x + (d - 1)) / d * d := by
  have h := Nat.lt_div_mul_add (a := x + (d - 1)) hd
  generalize (x + (d - 1)) / d * d = z at h ⊢
  omega

theorem cdiv_eq (x sh : ℕ) : cdiv x sh = (x + (2 ^ sh - 1)) / 2 ^ sh := by
  show (x + (1 <<< sh - 1)) >>> sh = _
  rw [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft]

theorem cdiv_ge (x sh : ℕ) : (x : ℝ) / 2 ^ sh ≤ (cdiv x sh : ℝ) := by
  rw [cdiv_eq, div_le_iff₀ (by positivity)]
  exact_mod_cast le_div_mul x (2 ^ sh) (Nat.two_pow_pos sh)

theorem cdivn_ge (x d : ℕ) (hd : 0 < d) : (x : ℝ) / d ≤ (cdivn x d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  exact_mod_cast le_div_mul x d hd

/-- The centre and the radius of an interval of natural numbers. -/
theorem enc_sound (l h : ℕ) (y : ℝ) (hl : (l : ℝ) ≤ y) (hh : y ≤ h) :
    |y - (encC l h : ℝ)| ≤ (encR l h : ℝ) := by
  have hlh : l ≤ h := by exact_mod_cast le_trans hl hh
  have hc : (l + h) / 2 ≤ h := by omega
  have e1 : encC l h = (l + h) / 2 := rfl
  have e2 : encR l h = h - (l + h) / 2 := rfl
  rw [e2, e1, Nat.cast_sub hc, abs_le]
  have h2 : (2 : ℝ) * (((l + h) / 2 : ℕ) : ℝ) ≤ (l : ℝ) + h := by
    exact_mod_cast Nat.mul_div_le (l + h) 2
  constructor <;> linarith

theorem norm3_sub (p n r : ℕ) :
    ((norm3 p n r).p : ℝ) - (norm3 p n r).n = (p : ℝ) - n ∧ (norm3 p n r).r = r := by
  refine ⟨?_, rfl⟩
  show ((p - n : ℕ) : ℝ) - ((n - p : ℕ) : ℝ) = (p : ℝ) - n
  rcases le_total n p with h | h
  · rw [Nat.cast_sub h, Nat.sub_eq_zero_of_le h]
    simp
  · rw [Nat.cast_sub h, Nat.sub_eq_zero_of_le h]
    simp

/-- **A coefficient after a product**: the triple of `resc` encloses `X / 2^s`, if `rc` bounds the distance
of `X` from `pc - nc`. -/
theorem resc_sound (s pc nc rc : ℕ) (X : ℝ) (hX : |X - ((pc : ℝ) - nc)| ≤ rc) :
    |X / 2 ^ s - (((resc s pc nc rc).p : ℝ) - (resc s pc nc rc).n)| ≤ (resc s pc nc rc).r := by
  have hd : (0 : ℝ) < 2 ^ s := by positivity
  have hdn : 0 < 2 ^ s := Nat.two_pow_pos s
  set c : ℕ := (pc - nc) + (nc - pc) with hc
  set q : ℕ := c / 2 ^ s with hq
  set m : ℕ := c % 2 ^ s with hm
  have hcq : c = q * 2 ^ s + m := by
    rw [hq, hm, mul_comm]
    exact (Nat.div_add_mod c (2 ^ s)).symm
  have hmlt : m < 2 ^ s := Nat.mod_lt c hdn
  -- the three numbers of `resc`
  have e_q : Nat.shiftRight (Nat.add (Nat.sub pc nc) (Nat.sub nc pc)) s = q := by
    show c >>> s = q
    rw [Nat.shiftRight_eq_div_pow]
  have e_m : Nat.sub (Nat.add (Nat.sub pc nc) (Nat.sub nc pc))
      (Nat.shiftLeft (Nat.shiftRight (Nat.add (Nat.sub pc nc) (Nat.sub nc pc)) s) s) = m := by
    rw [e_q]
    show c - q <<< s = m
    rw [Nat.shiftLeft_eq]
    generalize q * 2 ^ s = z at hcq
    omega
  have e_r : (resc s pc nc rc).r = cdiv rc s + (1 - (1 - m)) := by
    unfold resc
    simp only [e_m]
    by_cases hle : nc ≤ pc
    · rw [show Nat.ble nc pc = true from Nat.ble_eq.mpr hle]
      rfl
    · rw [show Nat.ble nc pc = false from by rw [← Bool.not_eq_true, Nat.ble_eq]; exact hle]
      rfl
  have hflag : (m : ℝ) / 2 ^ s ≤ ((1 - (1 - m) : ℕ) : ℝ) := by
    by_cases h0 : m = 0
    · rw [h0]
      simp
    · have h1 : 1 - (1 - m) = 1 := by omega
      rw [h1, Nat.cast_one, div_le_one hd]
      exact_mod_cast hmlt.le
  have hrc := cdiv_ge rc s
  have hXle := abs_le.mp hX
  have hcq' : (c : ℝ) = q * 2 ^ s + m := by exact_mod_cast hcq
  rw [e_r]
  push_cast
  by_cases hle : nc ≤ pc
  · have e_p : (resc s pc nc rc).p = q ∧ (resc s pc nc rc).n = 0 := by
      unfold resc
      simp only [e_q]
      rw [show Nat.ble nc pc = true from Nat.ble_eq.mpr hle]
      exact ⟨rfl, rfl⟩
    rw [e_p.1, e_p.2]
    have hcr : (c : ℝ) = (pc : ℝ) - nc := by
      rw [hc, Nat.sub_eq_zero_of_le hle, add_zero, Nat.cast_sub hle]
    have e : X / 2 ^ s - ((q : ℝ) - ((0 : ℕ) : ℝ)) = (X - ((pc : ℝ) - nc)) / 2 ^ s + (m : ℝ) / 2 ^ s := by
      rw [← hcr, hcq']
      field_simp
      push_cast
      ring
    rw [e, abs_le]
    have b1 : (X - ((pc : ℝ) - nc)) / 2 ^ s ≤ (rc : ℝ) / 2 ^ s := div_le_div_of_nonneg_right hXle.2 hd.le
    have b2 : -((rc : ℝ) / 2 ^ s) ≤ (X - ((pc : ℝ) - nc)) / 2 ^ s := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hXle.1 hd.le
    have b3 : (0 : ℝ) ≤ (m : ℝ) / 2 ^ s := by positivity
    have b4 : (0 : ℝ) ≤ (rc : ℝ) / 2 ^ s := by positivity
    constructor <;> linarith
  · have hlt : pc < nc := not_le.mp hle
    have e_p : (resc s pc nc rc).p = 0 ∧ (resc s pc nc rc).n = q := by
      unfold resc
      simp only [e_q]
      rw [show Nat.ble nc pc = false from by rw [← Bool.not_eq_true, Nat.ble_eq]; exact hle]
      exact ⟨rfl, rfl⟩
    rw [e_p.1, e_p.2]
    have hcr : (c : ℝ) = (nc : ℝ) - pc := by
      rw [hc, Nat.sub_eq_zero_of_le hlt.le, zero_add, Nat.cast_sub hlt.le]
    have e : X / 2 ^ s - (((0 : ℕ) : ℝ) - (q : ℝ)) = (X - ((pc : ℝ) - nc)) / 2 ^ s - (m : ℝ) / 2 ^ s := by
      have hcr2 : (pc : ℝ) - nc = -(c : ℝ) := by rw [hcr]; ring
      rw [hcr2, hcq']
      field_simp
      push_cast
      ring
    rw [e, abs_le]
    have b1 : (X - ((pc : ℝ) - nc)) / 2 ^ s ≤ (rc : ℝ) / 2 ^ s := div_le_div_of_nonneg_right hXle.2 hd.le
    have b2 : -((rc : ℝ) / 2 ^ s) ≤ (X - ((pc : ℝ) - nc)) / 2 ^ s := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hXle.1 hd.le
    have b3 : (0 : ℝ) ≤ (m : ℝ) / 2 ^ s := by positivity
    have b4 : (0 : ℝ) ≤ (rc : ℝ) / 2 ^ s := by positivity
    constructor <;> linarith

/-! ## The sums of the absolute values of the coefficients -/

/-- A coefficient is at most the sum of the three parts of its triple, in units of `2^-s`. -/
theorem coef_abs_le {s : ℕ} {h : ℕ → T3} {c : ℕ → ℝ} (he : Enc s h c) (e : ℕ) (hv : Valid e) :
    |c e| ≤ ((h e).t : ℝ) / 2 ^ s := by
  have hd : (0 : ℝ) < 2 ^ s := by positivity
  have h1 := abs_le.mp (he e hv)
  have hp : (0 : ℝ) ≤ (h e).p := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (h e).n := Nat.cast_nonneg _
  have ht : ((h e).t : ℝ) = (h e).p + (h e).n + (h e).r := by
    unfold T3.t
    push_cast
    ring
  rw [le_div_iff₀ hd, ht, ← abs_of_pos hd, ← abs_mul, mul_comm, abs_le]
  constructor <;> linarith [h1.1, h1.2]

theorem nrm_le_of_enc {s : ℕ} {h : ℕ → T3} {c : ℕ → ℝ} (hc : Supp c) (he : Enc s h c) (d : ℕ) :
    nrm c d ≤ (nsum h d : ℝ) / 2 ^ s := by
  unfold nrm nsum
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine sum_le_sum fun e _ => ?_
  by_cases hd : sdeg e = d
  · rw [if_pos hd, if_pos hd]
    by_cases hv : Valid e
    · rw [if_pos hv, ← div_eq_mul_inv]
      exact coef_abs_le he e hv
    · rw [if_neg hv, hc e hv]
      simp
  · rw [if_neg hd, if_neg hd]
    simp

/-! ## Constants, sums, negatives, multiples -/

theorem good_const (par : Par) (r : ℝ) (cp cn cr : ℕ) (a : ℝ)
    (ha : |2 ^ par.s * a - ((cp : ℝ) - cn)| ≤ cr) : Good par r (jconst par cp cn cr) (fun _ => a) := by
  intro hok
  obtain ⟨_, hp⟩ := fin_isPass par (fun e => cond (Nat.beq e 0) ⟨cp, cn, cr⟩ ⟨0, 0, 0⟩) 0 true hok
  refine ⟨_, fun e => if e = 0 then a else 0, 0, hp, Rep.const r a, le_refl 0, ?_, ?_⟩
  · show (0 : ℝ) * 2 ^ par.s ≤ ((0 : ℕ) : ℝ)
    simp
  · intro e _
    show |2 ^ par.s * (if e = 0 then a else 0)
      - (((cond (Nat.beq e 0) (⟨cp, cn, cr⟩ : T3) ⟨0, 0, 0⟩).p : ℝ)
        - (cond (Nat.beq e 0) (⟨cp, cn, cr⟩ : T3) ⟨0, 0, 0⟩).n)|
      ≤ (cond (Nat.beq e 0) (⟨cp, cn, cr⟩ : T3) ⟨0, 0, 0⟩).r
    rw [cond_beq]
    by_cases h0 : e = 0
    · rw [if_pos h0, if_pos h0]
      exact ha
    · rw [if_neg h0, if_neg h0]
      simp

theorem good_nat (par : Par) (r : ℝ) (n : ℕ) : Good par r (jnat par n) (fun _ => (n : ℝ)) := by
  refine good_const par r (Nat.shiftLeft n par.s) 0 0 (n : ℝ) ?_
  show |2 ^ par.s * (n : ℝ) - (((n <<< par.s : ℕ) : ℝ) - ((0 : ℕ) : ℝ))| ≤ ((0 : ℕ) : ℝ)
  rw [Nat.shiftLeft_eq]
  push_cast
  rw [show (2 : ℝ) ^ par.s * n - (n * 2 ^ par.s - 0) = 0 by ring]
  simp

theorem good_add (par : Par) (r : ℝ) (a b : Jet) (F1 F2 : (Fin 4 → ℝ) → ℝ) (h1 : Good par r a F1)
    (h2 : Good par r b F2) : Good par r (jadd par a b) (fun x => F1 x + F2 x) := by
  intro hok
  obtain ⟨hab, hp⟩ := fin_isPass par _ _ _ hok
  rw [Bool.and_eq_true] at hab
  obtain ⟨ha, c1, κ1, pa, ra, k1, K1, e1⟩ := h1 hab.1
  obtain ⟨hb, c2, κ2, pb, rb', k2, K2, e2⟩ := h2 hab.2
  refine ⟨_, fun e => c1 e + c2 e, κ1 + κ2, hp, Rep.add ra rb', add_nonneg k1 k2, ?_, ?_⟩
  · show (κ1 + κ2) * 2 ^ par.s ≤ ((a.K + b.K : ℕ) : ℝ)
    push_cast
    linarith
  · intro e hv
    have he := hv.1
    show |2 ^ par.s * (c1 e + c2 e)
      - (((norm3 (slot par.w a.P e + slot par.w b.P e) (slot par.w a.N e + slot par.w b.N e)
            (slot par.w a.R e + slot par.w b.R e)).p : ℝ)
        - (norm3 (slot par.w a.P e + slot par.w b.P e) (slot par.w a.N e + slot par.w b.N e)
            (slot par.w a.R e + slot par.w b.R e)).n)|
      ≤ (norm3 (slot par.w a.P e + slot par.w b.P e) (slot par.w a.N e + slot par.w b.N e)
            (slot par.w a.R e + slot par.w b.R e)).r
    rw [(norm3_sub _ _ _).1, (norm3_sub _ _ _).2, pa.slotP e he, pa.slotN e he, pa.slotR e he, pb.slotP e he,
      pb.slotN e he, pb.slotR e he, if_pos hv, if_pos hv, if_pos hv, if_pos hv, if_pos hv, if_pos hv]
    have g1 := abs_le.mp (e1 e hv)
    have g2 := abs_le.mp (e2 e hv)
    push_cast
    rw [abs_le]
    constructor <;> linarith [g1.1, g1.2, g2.1, g2.2]

theorem good_neg (par : Par) (r : ℝ) (a : Jet) (F : (Fin 4 → ℝ) → ℝ) (h1 : Good par r a F) :
    Good par r (jneg a) (fun x => -F x) := by
  intro hok
  obtain ⟨h, c, κ, pa, ra, k1, K1, e1⟩ := h1 hok
  refine ⟨fun e => ⟨(h e).n, (h e).p, (h e).r⟩, fun e => -c e, κ, ⟨pa.hN, pa.hP, pa.hR, ?_, ?_⟩, Rep.neg ra, k1,
    K1, ?_⟩
  · rw [show (jneg a).S = a.S from rfl, pa.hS]
    refine Finset.sum_congr rfl fun e _ => ?_
    have : (⟨(h e).n, (h e).p, (h e).r⟩ : T3).t = (h e).t := by
      show (h e).n + (h e).p + (h e).r = (h e).p + (h e).n + (h e).r
      omega
    rw [this]
  · have := pa.tot
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun e _ => ?_
    have : (⟨(h e).n, (h e).p, (h e).r⟩ : T3).t = (h e).t := by
      show (h e).n + (h e).p + (h e).r = (h e).p + (h e).n + (h e).r
      omega
    rw [this]
  · intro e hv
    have g1 := abs_le.mp (e1 e hv)
    show |2 ^ par.s * -c e - (((h e).n : ℝ) - (h e).p)| ≤ (h e).r
    rw [abs_le]
    constructor <;> linarith [g1.1, g1.2]

/-- The multiple by a real constant `γ` with the enclosure `(cp, cn, cr)`. -/
theorem good_scale (par : Par) (r : ℝ) (cp cn cr : ℕ) (γ : ℝ)
    (hγ : |2 ^ par.s * γ - ((cp : ℝ) - cn)| ≤ cr) (a : Jet) (F : (Fin 4 → ℝ) → ℝ) (h1 : Good par r a F) :
    Good par r (jscale par cp cn cr a) (fun x => γ * F x) := by
  intro hok
  obtain ⟨hoka, hp⟩ := fin_isPass par _ _ _ hok
  obtain ⟨h, c, κ, pa, ra, k1, K1, e1⟩ := h1 hoka
  have hd : (0 : ℝ) < 2 ^ par.s := by positivity
  have gγ := abs_le.mp hγ
  -- |γ| in units of 2^-s is at most cp + cn + cr
  have hγabs : |γ| * 2 ^ par.s ≤ (cp : ℝ) + cn + cr := by
    rw [← abs_of_pos hd, ← abs_mul, mul_comm, abs_le]
    have hp' : (0 : ℝ) ≤ cp := Nat.cast_nonneg _
    have hn' : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
    constructor <;> linarith [gγ.1, gγ.2]
  refine ⟨_, fun e => γ * c e, |γ| * κ, hp, Rep.smul γ ra, mul_nonneg (abs_nonneg γ) k1, ?_, ?_⟩
  · show |γ| * κ * 2 ^ par.s ≤ ((cdiv (a.K * (cp + cn + cr)) par.s : ℕ) : ℝ)
    refine le_trans ?_ (cdiv_ge _ _)
    rw [le_div_iff₀ hd]
    push_cast
    have hK0 : (0 : ℝ) ≤ a.K := Nat.cast_nonneg _
    calc |γ| * κ * 2 ^ par.s * 2 ^ par.s = (κ * 2 ^ par.s) * (|γ| * 2 ^ par.s) := by ring
      _ ≤ (a.K : ℝ) * ((cp : ℝ) + cn + cr) :=
          mul_le_mul K1 hγabs (mul_nonneg (abs_nonneg γ) hd.le) hK0
  · intro e hv
    have he := hv.1
    show |2 ^ par.s * (γ * c e)
      - (((resc par.s (slot par.w a.P e * cp + slot par.w a.N e * cn)
            (slot par.w a.P e * cn + slot par.w a.N e * cp)
            ((slot par.w a.P e + slot par.w a.N e) * cr + slot par.w a.R e * (cp + cn + cr))).p : ℝ)
        - (resc par.s (slot par.w a.P e * cp + slot par.w a.N e * cn)
            (slot par.w a.P e * cn + slot par.w a.N e * cp)
            ((slot par.w a.P e + slot par.w a.N e) * cr + slot par.w a.R e * (cp + cn + cr))).n)|
      ≤ (resc par.s (slot par.w a.P e * cp + slot par.w a.N e * cn)
            (slot par.w a.P e * cn + slot par.w a.N e * cp)
            ((slot par.w a.P e + slot par.w a.N e) * cr + slot par.w a.R e * (cp + cn + cr))).r
    rw [pa.slotP e he, pa.slotN e he, pa.slotR e he, if_pos hv, if_pos hv, if_pos hv]
    have e2 : 2 ^ par.s * (γ * c e) = (2 ^ par.s * c e) * (2 ^ par.s * γ) / 2 ^ par.s := by
      field_simp
    rw [e2]
    refine resc_sound par.s _ _ _ _ ?_
    have g1 := abs_le.mp (e1 e hv)
    set x := 2 ^ par.s * c e with hx
    set y := 2 ^ par.s * γ with hy
    push_cast
    have hpn : (0 : ℝ) ≤ (h e).p := Nat.cast_nonneg _
    have hnn : (0 : ℝ) ≤ (h e).n := Nat.cast_nonneg _
    have hrn : (0 : ℝ) ≤ (h e).r := Nat.cast_nonneg _
    have hcpn : (0 : ℝ) ≤ cp := Nat.cast_nonneg _
    have hcnn : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
    have hcrn : (0 : ℝ) ≤ cr := Nat.cast_nonneg _
    -- x y - m C = (x - m) y + m (y - C)
    have t1 : |(x - (((h e).p : ℝ) - (h e).n)) * y| ≤ (h e).r * ((cp : ℝ) + cn + cr) := by
      rw [abs_mul]
      refine mul_le_mul (e1 e hv) ?_ (abs_nonneg _) hrn
      rw [abs_le]
      constructor <;> linarith [gγ.1, gγ.2]
    have t2 : |(((h e).p : ℝ) - (h e).n) * (y - ((cp : ℝ) - cn))| ≤ (((h e).p : ℝ) + (h e).n) * cr := by
      rw [abs_mul]
      refine mul_le_mul ?_ hγ (abs_nonneg _) (by linarith)
      rw [abs_le]
      constructor <;> linarith
    have e3 : x * y - (((h e).p : ℝ) * cp + (h e).n * cn - ((h e).p * cn + (h e).n * cp))
        = (x - (((h e).p : ℝ) - (h e).n)) * y + (((h e).p : ℝ) - (h e).n) * (y - ((cp : ℝ) - cn)) := by ring
    rw [e3]
    calc |(x - (((h e).p : ℝ) - (h e).n)) * y + (((h e).p : ℝ) - (h e).n) * (y - ((cp : ℝ) - cn))|
        ≤ |(x - (((h e).p : ℝ) - (h e).n)) * y| + |(((h e).p : ℝ) - (h e).n) * (y - ((cp : ℝ) - cn))| :=
          abs_add_le _ _
      _ ≤ (h e).r * ((cp : ℝ) + cn + cr) + (((h e).p : ℝ) + (h e).n) * cr := add_le_add t1 t2
      _ = (((h e).p : ℝ) + (h e).n) * cr + (h e).r * ((cp : ℝ) + cn + cr) := by ring

end N14.Jet
