module

public import N14.Jet.SoundComp
public import N14.Jet.SoundLeaf

/-!
# Jets: soundness of the checker of a pair

`sem ρ e` is the real function of an expression `e`; the constant with the index `i` is `ρ i`, and the table
of the checker encloses these constants (`TabOk`).

* `jeval_good`: the jet of an expression encloses its function on the box.
* `pairOk_sound`: if `pairOk par tab e Pc Nc Rc n5c Kc = true`, then the function of `e` has a polynomial `c` of
  degree at most 5 and a bound `κ` of order six on the box (`Rep`) such that the coefficients of degree 2, 3, 4
  lie in the claimed enclosures, the sum of the absolute values of the coefficients of degree 5 is at most
  `n5c / 2^s`, and `κ ≤ Kc / 2^s` (`Claim`).
-/

@[expose] public section

namespace N14.Jet

open CAP Finset

attribute [local irreducible] nsum tsum

/-- The real function of an expression. The witnesses of the roots do not enter. -/
noncomputable def sem (ρ : ℕ → ℝ) : JExp → (Fin 4 → ℝ) → ℝ
  | .nat n => fun _ => (n : ℝ)
  | .cst i => fun _ => ρ i
  | .var k i => fun x => x (kf k) + ρ i
  | .trig k ic is => fun x => ρ ic * Real.cos (x (kf k)) - ρ is * Real.sin (x (kf k))
  | .add a b => fun x => sem ρ a x + sem ρ b x
  | .neg a => fun x => -sem ρ a x
  | .mul a b => fun x => sem ρ a x * sem ρ b x
  | .sqrt a _ _ => fun x => Real.sqrt (sem ρ a x)
  | .isqrt a _ _ => fun x => (Real.sqrt (sem ρ a x))⁻¹

/-- The table encloses the constants, in units of `2^-s`; outside the table the constants vanish. -/
def TabOk (s : ℕ) (tab : List T3) (ρ : ℕ → ℝ) : Prop :=
  ∀ i, |2 ^ s * ρ i - (((tget tab i).p : ℝ) - (tget tab i).n)| ≤ (tget tab i).r

/-- **The jet of an expression encloses its function.** -/
theorem jeval_good (par : Par) (r : ℝ) (hr : r ≤ rb) (tab : List T3) (ρ : ℕ → ℝ)
    (ht : TabOk par.s tab ρ) (e : JExp) : Good par r (jeval par tab e) (sem ρ e) := by
  induction e with
  | nat n => exact good_nat par r n
  | cst i => exact good_const par r _ _ _ (ρ i) (ht i)
  | var k i => exact good_var par r k _ _ _ (ρ i) (ht i)
  | trig k ic is => exact good_trig par r hr k _ _ _ _ _ _ (ρ ic) (ρ is) (ht ic) (ht is)
  | add a b iha ihb => exact good_add par r _ _ _ _ iha ihb
  | neg a iha => exact good_neg par r _ _ iha
  | mul a b iha ihb => exact good_mul par r hr _ _ _ _ iha ihb
  | sqrt a blo bhi iha => exact good_sqrt par r hr _ blo bhi _ iha
  | isqrt a blo bhi iha => exact good_isqrt par r hr _ blo bhi _ iha

/-! ## The final test -/

/-- The claims of a pair hold for the function `F`, with the polynomial `c` and the bound `κ`. -/
structure Claim (par : Par) (r : ℝ) (F : (Fin 4 → ℝ) → ℝ) (Pc Nc Rc n5c Kc : ℕ) (c : ℕ → ℝ) (κ : ℝ) :
    Prop where
  rep : Rep r F c κ
  kpos : 0 ≤ κ
  kle : κ * 2 ^ par.s ≤ Kc
  n5 : nrm c 5 * 2 ^ par.s ≤ n5c
  enc : ∀ e, Valid e → 2 ≤ sdeg e → sdeg e ≤ 4 →
    |2 ^ par.s * c e - ((slot par.w Pc e : ℝ) - (slot par.w Nc e : ℝ))| ≤ (slot par.w Rc e : ℝ)

theorem leSlots_sound (w : ℕ) (a : Jet) (Pc Nc Rc : ℕ) (l : List ℕ) (h : leSlots w a Pc Nc Rc l = true)
    (e : ℕ) (he : e ∈ l) (h2 : 2 ≤ e / 216) (h4 : e / 216 ≤ 4) :
    slot w Pc e + slot w a.N e + slot w a.R e ≤ slot w a.P e + slot w Nc e + slot w Rc e
      ∧ slot w a.P e + slot w Nc e + slot w a.R e ≤ slot w Pc e + slot w a.N e + slot w Rc e := by
  induction l with
  | nil => exact absurd he List.not_mem_nil
  | cons e0 l ih =>
    have hstep : leSlots w a Pc Nc Rc (e0 :: l)
        = cond (Nat.ble 2 (e0 / 216) && Nat.ble (e0 / 216) 4)
            (Nat.ble (slot w Pc e0 + slot w a.N e0 + slot w a.R e0) (slot w a.P e0 + slot w Nc e0 + slot w Rc e0)
              && Nat.ble (slot w a.P e0 + slot w Nc e0 + slot w a.R e0)
                (slot w Pc e0 + slot w a.N e0 + slot w Rc e0)
              && leSlots w a Pc Nc Rc l)
            (leSlots w a Pc Nc Rc l) := rfl
    rw [hstep] at h
    rcases List.mem_cons.mp he with rfl | hmem
    · have hc : (Nat.ble 2 (e / 216) && Nat.ble (e / 216) 4) = true := by
        rw [Bool.and_eq_true]
        exact ⟨Nat.ble_eq.mpr h2, Nat.ble_eq.mpr h4⟩
      rw [hc] at h
      have h' : (Nat.ble (slot w Pc e + slot w a.N e + slot w a.R e) (slot w a.P e + slot w Nc e + slot w Rc e)
          && Nat.ble (slot w a.P e + slot w Nc e + slot w a.R e) (slot w Pc e + slot w a.N e + slot w Rc e)
          && leSlots w a Pc Nc Rc l) = true := h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h'
      exact ⟨Nat.ble_eq.mp h'.1.1, Nat.ble_eq.mp h'.1.2⟩
    · refine ih ?_ hmem
      cases hc : (Nat.ble 2 (e0 / 216) && Nat.ble (e0 / 216) 4)
      · rw [hc] at h
        exact h
      · rw [hc] at h
        have h' : (Nat.ble (slot w Pc e0 + slot w a.N e0 + slot w a.R e0)
            (slot w a.P e0 + slot w Nc e0 + slot w Rc e0)
            && Nat.ble (slot w a.P e0 + slot w Nc e0 + slot w a.R e0)
              (slot w Pc e0 + slot w a.N e0 + slot w Rc e0)
            && leSlots w a Pc Nc Rc l) = true := h
        rw [Bool.and_eq_true] at h'
        exact h'.2

/-- **Soundness of the checker of a pair.** -/
theorem pairOk_sound (par : Par) (r : ℝ) (hr : r ≤ rb) (tab : List T3) (ρ : ℕ → ℝ)
    (ht : TabOk par.s tab ρ) (e : JExp) (Pc Nc Rc n5c Kc : ℕ)
    (h : pairOk par tab e Pc Nc Rc n5c Kc = true) :
    ∃ c κ, Claim par r (sem ρ e) Pc Nc Rc n5c Kc c κ := by
  have h' : ((jeval par tab e).ok && Nat.ble (jeval par tab e).K Kc
      && Nat.ble (nd par.w (jeval par tab e) 5) n5c
      && leSlots par.w (jeval par tab e) Pc Nc Rc idxs) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨hok, hK⟩, h5⟩, hle⟩ := h'
  obtain ⟨hh, c, κ, hp, hrep, hκ, hKK, henc⟩ := jeval_good par r hr tab ρ ht e hok
  have hd : (0 : ℝ) < 2 ^ par.s := by positivity
  refine ⟨c, κ, hrep, hκ, ?_, ?_, ?_⟩
  · exact le_trans hKK (by exact_mod_cast Nat.ble_eq.mp hK)
  · have h1 := nrm_le_of_enc hrep.supp henc 5
    rw [le_div_iff₀ hd] at h1
    refine le_trans h1 ?_
    rw [← hp.nd_eq 5 (by norm_num)]
    exact_mod_cast Nat.ble_eq.mp h5
  · intro s hv h2 h4
    have hm : s ∈ idxs := (valid_iff_mem s).mp hv
    obtain ⟨q1, q2⟩ := leSlots_sound par.w _ Pc Nc Rc idxs hle s hm h2 h4
    rw [hp.slotP s hv.1, hp.slotN s hv.1, hp.slotR s hv.1, if_pos hv, if_pos hv, if_pos hv] at q1 q2
    have g := abs_le.mp (henc s hv)
    have q1' : (slot par.w Pc s : ℝ) + (hh s).n + (hh s).r ≤ (hh s).p + slot par.w Nc s + slot par.w Rc s := by
      exact_mod_cast q1
    have q2' : ((hh s).p : ℝ) + slot par.w Nc s + (hh s).r ≤ slot par.w Pc s + (hh s).n + slot par.w Rc s := by
      exact_mod_cast q2
    rw [abs_le]
    constructor <;> linarith [g.1, g.2]

end N14.Jet
