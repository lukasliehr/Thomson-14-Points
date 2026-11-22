module

public import N14.Jet.SoundMul
public import N14.Jet.Root

/-!
# Jets: soundness of the checker, the roots

`jcomp par mode a blo bhi` is the jet of `F^(1/2)` (`mode = true`) or of `F^(-1/2)` (`mode = false`) for the
jet `a` of `F`. With the constant coefficient `u₀` of the polynomial of `a` and `b₀ = u₀^(-1/2)`:

* the tests give `u₀ > 0`, `blo ≤ 2^s b₀ ≤ bhi` and `ν r_b b₀² ≤ 1/8`, where `ν m` bounds `|F - u₀|` on the box
  (`comp_data`, `tail_bound`);
* the jet `tailJ` of `F - u₀` and its powers are jets by `good_mul`, the multiples by the enclosed
  coefficients of the Taylor polynomial by `good_term`;
* the rest of the Taylor polynomial is `isqrt_taylor`, `sqrt_taylor` of `N14/Jet/Root.lean`.
-/

@[expose] public section

namespace N14.Jet

open CAP Finset

attribute [local irreducible] nsum tsum

/-! ## The flags of the parts -/

theorem fin_ok {par : Par} {J : Jet} {K : ℕ} {ok : Bool} (h : (fin par J K ok).ok = true) : ok = true := by
  have h1 : (ok && Nat.blt (total par.w J) (Nat.shiftLeft 1 par.w)) = true := h
  rw [Bool.and_eq_true] at h1
  exact h1.1

theorem jadd_ok {par : Par} {a b : Jet} (h : (jadd par a b).ok = true) : a.ok = true ∧ b.ok = true := by
  have h1 : (a.ok && b.ok) = true := fin_ok h
  rwa [Bool.and_eq_true] at h1

theorem jscale_ok {par : Par} {cp cn cr : ℕ} {a : Jet} (h : (jscale par cp cn cr a).ok = true) :
    a.ok = true :=
  fin_ok h

theorem jmul_ok {par : Par} {a b : Jet} (h : (jmul par a b).ok = true) : a.ok = true ∧ b.ok = true := by
  have h1 : (a.ok && b.ok && Nat.blt (Nat.mul (total par.w a) (total par.w b)) (Nat.shiftLeft 1 par.w)) = true :=
    fin_ok h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  exact h1.1

theorem term_eq (par : Par) (lo hi nu sh : ℕ) (neg : Bool) (b : Jet) :
    term par lo hi nu sh neg b
      = cond neg
          (jscale par 0 (encC ((lo * nu) >>> sh) (cdiv (hi * nu) sh))
            (encR ((lo * nu) >>> sh) (cdiv (hi * nu) sh)) b)
          (jscale par (encC ((lo * nu) >>> sh) (cdiv (hi * nu) sh)) 0
            (encR ((lo * nu) >>> sh) (cdiv (hi * nu) sh)) b) := rfl

theorem term_ok {par : Par} {lo hi nu sh : ℕ} {neg : Bool} {b : Jet}
    (h : (term par lo hi nu sh neg b).ok = true) : b.ok = true := by
  rw [term_eq] at h
  cases neg
  · exact jscale_ok h
  · exact jscale_ok h

/-! ## Multiples by an enclosed coefficient -/

theorem cast_div_le' (x d : ℕ) : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := by
  by_cases hd : d = 0
  · subst hd
    simp
  · have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self x d

/-- The jet of `σ β ν / 2^sh · G`, where `lo ≤ 2^s β ≤ hi` and `σ` is the sign. -/
theorem good_term (par : Par) (r : ℝ) (lo hi nu sh : ℕ) (neg : Bool) (b : Jet) (G : (Fin 4 → ℝ) → ℝ)
    (β σ : ℝ) (hσ : σ = cond neg (-1) 1) (hlo : (lo : ℝ) ≤ 2 ^ par.s * β) (hhi : 2 ^ par.s * β ≤ hi)
    (hG : Good par r b G) :
    Good par r (term par lo hi nu sh neg b) (fun x => σ * (β * nu / 2 ^ sh) * G x) := by
  have hd : (0 : ℝ) < 2 ^ sh := by positivity
  have hl : ((((lo * nu) >>> sh : ℕ)) : ℝ) ≤ 2 ^ par.s * β * nu / 2 ^ sh := by
    rw [Nat.shiftRight_eq_div_pow]
    refine le_trans (cast_div_le' _ _) ?_
    push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg nu)) hd.le
  have hh : 2 ^ par.s * β * nu / 2 ^ sh ≤ (cdiv (hi * nu) sh : ℝ) := by
    refine le_trans ?_ (cdiv_ge _ _)
    push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg nu)) hd.le
  have henc := enc_sound _ _ _ hl hh
  rw [term_eq]
  cases neg
  · subst hσ
    refine good_scale par r _ 0 _ _ ?_ b G hG
    refine le_of_eq_of_le (congrArg abs ?_) henc
    show (2 : ℝ) ^ par.s * (1 * (β * nu / 2 ^ sh))
      - (((encC ((lo * nu) >>> sh) (cdiv (hi * nu) sh) : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) = _
    rw [Nat.cast_zero]
    ring
  · subst hσ
    refine good_scale par r 0 _ _ _ ?_ b G hG
    rw [← abs_neg]
    refine le_of_eq_of_le (congrArg abs ?_) henc
    show -((2 : ℝ) ^ par.s * (-1 * (β * nu / 2 ^ sh))
      - (((0 : ℕ) : ℝ) - ((encC ((lo * nu) >>> sh) (cdiv (hi * nu) sh) : ℕ) : ℝ))) = _
    rw [Nat.cast_zero]
    ring

/-- The powers of the witness. -/
theorem pw_bounds (s blo bhi j : ℕ) (b0 : ℝ) (hj : 1 ≤ j) (hlo : (blo : ℝ) ≤ 2 ^ s * b0)
    (hhi : 2 ^ s * b0 ≤ bhi) :
    (pwLo s blo j : ℝ) ≤ 2 ^ s * b0 ^ j ∧ 2 ^ s * b0 ^ j ≤ (pwHi s bhi j : ℝ) := by
  have hd : (0 : ℝ) < 2 ^ (s * (j - 1)) := by positivity
  have hb0 : (0 : ℝ) ≤ 2 ^ s * b0 := le_trans (Nat.cast_nonneg _) hlo
  have e : (2 : ℝ) ^ s * b0 ^ j = (2 ^ s * b0) ^ j / 2 ^ (s * (j - 1)) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hd' : (0 : ℝ) < 2 ^ (s * i) := by positivity
    rw [Nat.add_sub_cancel, eq_div_iff hd'.ne', mul_pow, pow_mul]
    ring
  rw [e]
  constructor
  · show ((((blo ^ j) >>> (s * (j - 1)) : ℕ)) : ℝ) ≤ _
    rw [Nat.shiftRight_eq_div_pow]
    refine le_trans (cast_div_le' _ _) ?_
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hlo j) hd.le
  · show _ ≤ ((cdiv (bhi ^ j) (s * (j - 1)) : ℕ) : ℝ)
    refine le_trans ?_ (cdiv_ge _ _)
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hb0 hhi j) hd.le

/-! ## The jet of `F - u₀` -/

/-- A valid slot of degree zero is the slot zero. -/
theorem valid_deg0 {e : ℕ} (hv : Valid e) (hd : sdeg e = 0) : e = 0 := by
  obtain ⟨h1, _, _, _⟩ := slot_decomp e
  have h2 := hv.2
  omega

theorem le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  rw [not_le] at hlt
  nlinarith

/-- The triples of the jet of `F - u₀`. -/
def tailH (w : ℕ) (a : Jet) (e : ℕ) : T3 :=
  cond (Nat.beq e 0) ⟨0, 0, 0⟩ ⟨slot w a.P e, slot w a.N e, slot w a.R e⟩

/-- The jet of `F - u₀`. -/
noncomputable def tailJ (par : Par) (a : Jet) : Jet := fin par (pass par.w (tailH par.w a) idxs) a.K a.ok

/-- The bound for `|F - u₀| / m`, in units of `2^-s`. -/
def nuOf (w : ℕ) (Nj : Jet) (K : ℕ) : ℕ :=
  nd w Nj 1 + cdiv (nd w Nj 2 * 33) 12 + cdiv (nd w Nj 3 * 1089) 24 + cdiv (nd w Nj 4 * 35937) 36
    + cdiv (nd w Nj 5 * 1185921) 48 + cdiv (K * 39135393) 60

theorem pow_step (m ρ : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ ρ) (n A : ℝ) (hn0 : 0 ≤ n) (hn : n ≤ A) (k d : ℕ)
    (hk : k = d + 1) : n * m ^ k ≤ A * ρ ^ d * m := by
  subst hk
  have h1 : m ^ d ≤ ρ ^ d := pow_le_pow_left₀ hm0 hm d
  have h2 : 0 ≤ m ^ d := pow_nonneg hm0 d
  calc n * m ^ (d + 1) = (n * m ^ d) * m := by ring
    _ ≤ (A * ρ ^ d) * m := mul_le_mul_of_nonneg_right (mul_le_mul hn h1 h2 (le_trans hn0 hn)) hm0

/-- **A function without a constant term on the box**: `|G| ≤ ν m`. -/
theorem tail_bound (par : Par) (r : ℝ) (hr : r ≤ rb) (Nj : Jet) (K : ℕ) (G : (Fin 4 → ℝ) → ℝ) (h : ℕ → T3)
    (c : ℕ → ℝ) (κ : ℝ) (hp : IsPass par.w Nj h) (hrep : Rep r G c κ) (hκ : 0 ≤ κ) (hK : κ * 2 ^ par.s ≤ K)
    (he : Enc par.s h c) (h0 : nrm c 0 = 0) (x : Fin 4 → ℝ) (m : ℝ) (hx : ∀ k, |x k| ≤ m) (hm : m ≤ r) :
    |G x| ≤ (nuOf par.w Nj K : ℝ) / 2 ^ par.s * m := by
  have hd : (0 : ℝ) < 2 ^ par.s := by positivity
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
  have hmb : m ≤ rb := le_trans hm hr
  have a1 := hrep.bound x m hx hm
  have a2 := pev_abs_le c hrep.supp x m hx
  rw [sum_range6, h0] at a2
  have s1 : nrm c 1 * m ^ 1 ≤ (nsum h 1 : ℝ) / 2 ^ par.s * m := by
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (nrm_le_of_enc hrep.supp he 1) hm0
  have s2 := pow_step m rb hm0 hmb _ _ (nrm_nonneg c 2) (nrm_le_of_enc hrep.supp he 2) 2 1 rfl
  have s3 := pow_step m rb hm0 hmb _ _ (nrm_nonneg c 3) (nrm_le_of_enc hrep.supp he 3) 3 2 rfl
  have s4 := pow_step m rb hm0 hmb _ _ (nrm_nonneg c 4) (nrm_le_of_enc hrep.supp he 4) 4 3 rfl
  have s5 := pow_step m rb hm0 hmb _ _ (nrm_nonneg c 5) (nrm_le_of_enc hrep.supp he 5) 5 4 rfl
  have s6 := pow_step m rb hm0 hmb κ ((K : ℝ) / 2 ^ par.s) hκ (by rw [le_div_iff₀ hd]; exact hK) 6 5 rfl
  have hnu : (nsum h 1 : ℝ) + (nsum h 2 : ℝ) * rb + (nsum h 3 : ℝ) * rb ^ 2 + (nsum h 4 : ℝ) * rb ^ 3
      + (nsum h 5 : ℝ) * rb ^ 4 + (K : ℝ) * rb ^ 5 ≤ (nuOf par.w Nj K : ℝ) := by
    unfold nuOf
    rw [hp.nd_eq 1 (by norm_num), hp.nd_eq 2 (by norm_num), hp.nd_eq 3 (by norm_num),
      hp.nd_eq 4 (by norm_num), hp.nd_eq 5 (by norm_num)]
    have c2 := cdiv_ge (nsum h 2 * 33) 12
    have c3 := cdiv_ge (nsum h 3 * 1089) 24
    have c4 := cdiv_ge (nsum h 4 * 35937) 36
    have c5 := cdiv_ge (nsum h 5 * 1185921) 48
    have c6 := cdiv_ge (K * 39135393) 60
    push_cast at c2 c3 c4 c5 c6 ⊢
    unfold rb
    norm_num at c2 c3 c4 c5 c6 ⊢
    linarith
  have hnu' : (nsum h 1 : ℝ) / 2 ^ par.s + (nsum h 2 : ℝ) / 2 ^ par.s * rb
      + (nsum h 3 : ℝ) / 2 ^ par.s * rb ^ 2 + (nsum h 4 : ℝ) / 2 ^ par.s * rb ^ 3
      + (nsum h 5 : ℝ) / 2 ^ par.s * rb ^ 4 + (K : ℝ) / 2 ^ par.s * rb ^ 5
      ≤ (nuOf par.w Nj K : ℝ) / 2 ^ par.s := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hnu hd.le)
    ring
  have hfin := mul_le_mul_of_nonneg_right hnu' hm0
  have t := abs_add_le (G x - pev c x) (pev c x)
  rw [sub_add_cancel] at t
  linarith

/-- The first and the last value of the constant coefficient, in units of `2^-s`. -/
def u0lo (w : ℕ) (a : Jet) : ℕ := slot w a.P 0 - slot w a.N 0 - slot w a.R 0

def u0hi (w : ℕ) (a : Jet) : ℕ := slot w a.P 0 - slot w a.N 0 + slot w a.R 0

/-- The tests of `jcomp`. -/
noncomputable def compOk (par : Par) (a : Jet) (blo bhi : ℕ) : Bool :=
  a.ok && Nat.blt (slot par.w a.N 0 + slot par.w a.R 0) (slot par.w a.P 0) && Nat.ble 1 blo && Nat.ble blo bhi
    && Nat.ble (blo * blo * u0hi par.w a) (1 <<< (3 * par.s))
    && Nat.ble (1 <<< (3 * par.s)) (bhi * bhi * u0lo par.w a)
    && Nat.ble (8 * nuOf par.w (tailJ par a) a.K * 33 * bhi * bhi) (1 <<< (12 + 3 * par.s))

/-- The constant coefficient `u₀` of a jet of `F`, the number `b₀ = u₀^(-1/2)`, and the jet of `F - u₀`. -/
structure CompData (par : Par) (r : ℝ) (a : Jet) (blo bhi : ℕ) (F : (Fin 4 → ℝ) → ℝ) (u0 b0 : ℝ) :
    Prop where
  hb0 : 0 < b0
  hbu : b0 ^ 2 * u0 = 1
  hblo : (blo : ℝ) ≤ 2 ^ par.s * b0
  hbhi : 2 ^ par.s * b0 ≤ bhi
  hulo : (u0lo par.w a : ℝ) ≤ 2 ^ par.s * u0
  huhi : 2 ^ par.s * u0 ≤ (u0hi par.w a : ℝ)
  good : Good par r (tailJ par a) (fun x => F x - u0)
  bound : ∀ x m, (∀ k, |x k| ≤ m) → m ≤ r →
    |F x - u0| ≤ (nuOf par.w (tailJ par a) a.K : ℝ) / 2 ^ par.s * m
  small : (nuOf par.w (tailJ par a) a.K : ℝ) / 2 ^ par.s * rb * b0 ^ 2 ≤ 1 / 8

theorem comp_data (par : Par) (r : ℝ) (hr : r ≤ rb) (a : Jet) (blo bhi : ℕ) (F : (Fin 4 → ℝ) → ℝ)
    (h1 : Good par r a F) (hck : compOk par a blo bhi = true) (hokN : (tailJ par a).ok = true) :
    ∃ u0 b0 : ℝ, CompData par r a blo bhi F u0 b0 := by
  unfold compOk at hck
  simp only [Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨⟨oka, t1⟩, _⟩, _⟩, t4⟩, t5⟩, t6⟩ := hck
  obtain ⟨ha, c, κ, pa, ra, hκ, hK, he⟩ := h1 oka
  have hD : (0 : ℝ) < 2 ^ par.s := by positivity
  -- the slot zero
  have sP : slot par.w a.P 0 = (ha 0).p := by rw [pa.slotP 0 (by norm_num), if_pos valid_zero]
  have sN : slot par.w a.N 0 = (ha 0).n := by rw [pa.slotN 0 (by norm_num), if_pos valid_zero]
  have sR : slot par.w a.R 0 = (ha 0).r := by rw [pa.slotR 0 (by norm_num), if_pos valid_zero]
  have e0 := abs_le.mp (he 0 valid_zero)
  have t1' : slot par.w a.N 0 + slot par.w a.R 0 < slot par.w a.P 0 := Nat.blt_eq.mp t1
  have hlo_nat : u0lo par.w a + slot par.w a.N 0 + slot par.w a.R 0 = slot par.w a.P 0 := by
    unfold u0lo
    omega
  have hhi_nat : u0hi par.w a + slot par.w a.N 0 = slot par.w a.P 0 + slot par.w a.R 0 := by
    unfold u0hi
    omega
  have hlo_pos : 1 ≤ u0lo par.w a := by
    unfold u0lo
    omega
  have hloR : (u0lo par.w a : ℝ) + (ha 0).n + (ha 0).r = (ha 0).p := by
    rw [← sP, ← sN, ← sR]
    exact_mod_cast hlo_nat
  have hhiR : (u0hi par.w a : ℝ) + (ha 0).n = (ha 0).p + (ha 0).r := by
    rw [← sP, ← sN, ← sR]
    exact_mod_cast hhi_nat
  have hulo : (u0lo par.w a : ℝ) ≤ 2 ^ par.s * c 0 := by linarith [e0.1]
  have huhi : 2 ^ par.s * c 0 ≤ (u0hi par.w a : ℝ) := by linarith [e0.2]
  have hlo1 : (1 : ℝ) ≤ (u0lo par.w a : ℝ) := by exact_mod_cast hlo_pos
  have hu0 : 0 < c 0 := (mul_pos_iff_of_pos_left hD).mp (by linarith)
  -- the inverse root
  obtain ⟨b0, hb0def⟩ : ∃ b0 : ℝ, b0 = (Real.sqrt (c 0))⁻¹ := ⟨_, rfl⟩
  have hsq : 0 < Real.sqrt (c 0) := Real.sqrt_pos.mpr hu0
  have hb0 : 0 < b0 := by
    rw [hb0def]
    exact inv_pos.mpr hsq
  have hbu : b0 ^ 2 * c 0 = 1 := by
    rw [hb0def, inv_pow, Real.sq_sqrt hu0.le]
    exact inv_mul_cancel₀ hu0.ne'
  have hDb0 : 0 ≤ 2 ^ par.s * b0 := (mul_pos hD hb0).le
  -- the witness from below
  have t4r : (blo : ℝ) ^ 2 * (u0hi par.w a : ℝ) ≤ (2 ^ par.s) ^ 3 := by
    have t4' : blo * blo * u0hi par.w a ≤ 2 ^ (3 * par.s) := by
      have := Nat.ble_eq.mp t4
      rwa [Nat.one_shiftLeft] at this
    have h : ((blo * blo * u0hi par.w a : ℕ) : ℝ) ≤ ((2 ^ (3 * par.s) : ℕ) : ℝ) := by exact_mod_cast t4'
    push_cast at h
    rw [pow_mul'] at h
    calc (blo : ℝ) ^ 2 * (u0hi par.w a : ℝ) = (blo : ℝ) * blo * u0hi par.w a := by ring
      _ ≤ (2 ^ par.s) ^ 3 := h
  have k2 : (blo : ℝ) ^ 2 * c 0 ≤ (2 ^ par.s) ^ 2 := by
    have k1 : (2 : ℝ) ^ par.s * ((blo : ℝ) ^ 2 * c 0) ≤ 2 ^ par.s * (2 ^ par.s) ^ 2 := by
      calc (2 : ℝ) ^ par.s * ((blo : ℝ) ^ 2 * c 0) = (blo : ℝ) ^ 2 * (2 ^ par.s * c 0) := by ring
        _ ≤ (blo : ℝ) ^ 2 * (u0hi par.w a : ℝ) := mul_le_mul_of_nonneg_left huhi (sq_nonneg _)
        _ ≤ (2 ^ par.s) ^ 3 := t4r
        _ = 2 ^ par.s * (2 ^ par.s) ^ 2 := by ring
    exact le_of_mul_le_mul_left k1 hD
  have hblo : (blo : ℝ) ≤ 2 ^ par.s * b0 := by
    refine le_of_sq_le hDb0 ?_
    calc (blo : ℝ) ^ 2 = ((blo : ℝ) ^ 2 * c 0) * b0 ^ 2 := by
          rw [mul_assoc, mul_comm (c 0), hbu, mul_one]
      _ ≤ (2 ^ par.s) ^ 2 * b0 ^ 2 := mul_le_mul_of_nonneg_right k2 (sq_nonneg b0)
      _ = (2 ^ par.s * b0) ^ 2 := by ring
  -- the witness from above
  have t5r : ((2 : ℝ) ^ par.s) ^ 3 ≤ (bhi : ℝ) ^ 2 * (u0lo par.w a : ℝ) := by
    have t5' : 2 ^ (3 * par.s) ≤ bhi * bhi * u0lo par.w a := by
      have := Nat.ble_eq.mp t5
      rwa [Nat.one_shiftLeft] at this
    have h : ((2 ^ (3 * par.s) : ℕ) : ℝ) ≤ ((bhi * bhi * u0lo par.w a : ℕ) : ℝ) := by exact_mod_cast t5'
    push_cast at h
    rw [pow_mul'] at h
    calc ((2 : ℝ) ^ par.s) ^ 3 ≤ (bhi : ℝ) * bhi * u0lo par.w a := h
      _ = (bhi : ℝ) ^ 2 * (u0lo par.w a : ℝ) := by ring
  have k4 : ((2 : ℝ) ^ par.s) ^ 2 ≤ (bhi : ℝ) ^ 2 * c 0 := by
    have k3 : (2 : ℝ) ^ par.s * (2 ^ par.s) ^ 2 ≤ 2 ^ par.s * ((bhi : ℝ) ^ 2 * c 0) := by
      calc (2 : ℝ) ^ par.s * (2 ^ par.s) ^ 2 = (2 ^ par.s) ^ 3 := by ring
        _ ≤ (bhi : ℝ) ^ 2 * (u0lo par.w a : ℝ) := t5r
        _ ≤ (bhi : ℝ) ^ 2 * (2 ^ par.s * c 0) := mul_le_mul_of_nonneg_left hulo (sq_nonneg _)
        _ = 2 ^ par.s * ((bhi : ℝ) ^ 2 * c 0) := by ring
    exact le_of_mul_le_mul_left k3 hD
  have hbhi : 2 ^ par.s * b0 ≤ (bhi : ℝ) := by
    refine le_of_sq_le (Nat.cast_nonneg bhi) ?_
    calc (2 ^ par.s * b0) ^ 2 = (2 ^ par.s) ^ 2 * b0 ^ 2 := by ring
      _ ≤ ((bhi : ℝ) ^ 2 * c 0) * b0 ^ 2 := mul_le_mul_of_nonneg_right k4 (sq_nonneg b0)
      _ = (bhi : ℝ) ^ 2 := by rw [mul_assoc, mul_comm (c 0), hbu, mul_one]
  -- the jet of `F - u₀`
  obtain ⟨_, hpN⟩ := fin_isPass par (tailH par.w a) a.K a.ok hokN
  have repN : Rep r (fun x => F x - c 0) (fun e => c e + if e = 0 then -c 0 else 0) κ :=
    ((Rep.add ra (Rep.const r (-c 0))).mono κ (add_zero κ).le).congr _ fun x => sub_eq_add_neg _ _
  have encN : Enc par.s (tailH par.w a) (fun e => c e + if e = 0 then -c 0 else 0) := by
    intro e hv
    by_cases h0 : e = 0
    · subst h0
      show |2 ^ par.s * (c 0 + if (0 : ℕ) = 0 then -c 0 else 0)
        - ((((⟨0, 0, 0⟩ : T3)).p : ℝ) - ((⟨0, 0, 0⟩ : T3)).n)| ≤ (((⟨0, 0, 0⟩ : T3)).r : ℝ)
      rw [if_pos rfl]
      simp
    · have hH : tailH par.w a e = ⟨slot par.w a.P e, slot par.w a.N e, slot par.w a.R e⟩ := by
        unfold tailH
        rw [cond_beq, if_neg h0]
      rw [hH]
      show |2 ^ par.s * (c e + if e = 0 then -c 0 else 0)
        - (((slot par.w a.P e : ℕ) : ℝ) - ((slot par.w a.N e : ℕ) : ℝ))| ≤ ((slot par.w a.R e : ℕ) : ℝ)
      rw [if_neg h0, add_zero, pa.slotP e hv.1, pa.slotN e hv.1, pa.slotR e hv.1, if_pos hv, if_pos hv,
        if_pos hv]
      exact he e hv
  have hn0 : nrm (fun e => c e + if e = 0 then -c 0 else 0) 0 = 0 := by
    unfold nrm
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases hd : sdeg e = 0
    · rw [if_pos hd]
      by_cases hv : Valid e
      · have h0 := valid_deg0 hv hd
        subst h0
        show |c 0 + if (0 : ℕ) = 0 then -c 0 else 0| = 0
        rw [if_pos rfl, add_neg_cancel, abs_zero]
      · have h0 : e ≠ 0 := fun h => hv (h ▸ valid_zero)
        show |c e + if e = 0 then -c 0 else 0| = 0
        rw [if_neg h0, add_zero, ra.supp e hv, abs_zero]
    · rw [if_neg hd]
  have hbound := tail_bound par r hr (tailJ par a) a.K (fun x => F x - c 0) (tailH par.w a) _ κ hpN repN hκ
    hK encN hn0
  -- the smallness of `F - u₀`
  have t6r : 8 * (nuOf par.w (tailJ par a) a.K : ℝ) * 33 * (bhi : ℝ) ^ 2 ≤ 4096 * (2 ^ par.s) ^ 3 := by
    have t6' : 8 * nuOf par.w (tailJ par a) a.K * 33 * bhi * bhi ≤ 2 ^ (12 + 3 * par.s) := by
      have := Nat.ble_eq.mp t6
      rwa [Nat.one_shiftLeft] at this
    have h : ((8 * nuOf par.w (tailJ par a) a.K * 33 * bhi * bhi : ℕ) : ℝ)
        ≤ ((2 ^ (12 + 3 * par.s) : ℕ) : ℝ) := by exact_mod_cast t6'
    push_cast at h
    rw [pow_add, pow_mul'] at h
    calc 8 * (nuOf par.w (tailJ par a) a.K : ℝ) * 33 * (bhi : ℝ) ^ 2
        = 8 * (nuOf par.w (tailJ par a) a.K : ℝ) * 33 * bhi * bhi := by ring
      _ ≤ 2 ^ 12 * (2 ^ par.s) ^ 3 := h
      _ = 4096 * (2 ^ par.s) ^ 3 := by norm_num
  have hsmall : (nuOf par.w (tailJ par a) a.K : ℝ) / 2 ^ par.s * rb * b0 ^ 2 ≤ 1 / 8 := by
    have hD3 : (0 : ℝ) < 4096 * (2 ^ par.s) ^ 3 := by positivity
    have hDinv : ((2 : ℝ) ^ par.s)⁻¹ * 2 ^ par.s = 1 := inv_mul_cancel₀ hD.ne'
    refine le_of_mul_le_mul_right ?_ hD3
    calc (nuOf par.w (tailJ par a) a.K : ℝ) / 2 ^ par.s * rb * b0 ^ 2 * (4096 * (2 ^ par.s) ^ 3)
        = (nuOf par.w (tailJ par a) a.K : ℝ) * 33 * (2 ^ par.s * b0) ^ 2
          * (((2 : ℝ) ^ par.s)⁻¹ * 2 ^ par.s) := by
          unfold rb
          ring
      _ = (nuOf par.w (tailJ par a) a.K : ℝ) * 33 * (2 ^ par.s * b0) ^ 2 := by rw [hDinv, mul_one]
      _ ≤ (nuOf par.w (tailJ par a) a.K : ℝ) * 33 * (bhi : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hDb0 hbhi 2)
            (mul_nonneg (Nat.cast_nonneg _) (by norm_num))
      _ ≤ 1 / 8 * (4096 * (2 ^ par.s) ^ 3) := by linarith
  exact ⟨c 0, b0, ⟨hb0, hbu, hblo, hbhi, hulo, huhi, fun _ => ⟨_, _, κ, hpN, repN, hκ, hK, encN⟩, hbound,
    hsmall⟩⟩

/-! ## The two roots -/

/-- The jets of the powers of `F - u₀`. -/
noncomputable def pw2 (par : Par) (a : Jet) : Jet := jmul par (tailJ par a) (tailJ par a)

noncomputable def pw3 (par : Par) (a : Jet) : Jet := jmul par (pw2 par a) (tailJ par a)

noncomputable def pw4 (par : Par) (a : Jet) : Jet := jmul par (pw2 par a) (pw2 par a)

noncomputable def pw5 (par : Par) (a : Jet) : Jet := jmul par (pw4 par a) (tailJ par a)

/-- The Taylor polynomial of the root, applied to the jet of `F - u₀`. -/
noncomputable def sqrtOut (par : Par) (a : Jet) (blo bhi : ℕ) : Jet :=
  jadd par (jadd par (jadd par (jadd par (jadd par
    (jconst par (encC ((u0lo par.w a * blo) >>> par.s) (cdiv (u0hi par.w a * bhi) par.s)) 0
      (encR ((u0lo par.w a * blo) >>> par.s) (cdiv (u0hi par.w a * bhi) par.s)))
    (term par (pwLo par.s blo 1) (pwHi par.s bhi 1) 1 1 false (tailJ par a)))
    (term par (pwLo par.s blo 3) (pwHi par.s bhi 3) 1 3 true (pw2 par a)))
    (term par (pwLo par.s blo 5) (pwHi par.s bhi 5) 1 4 false (pw3 par a)))
    (term par (pwLo par.s blo 7) (pwHi par.s bhi 7) 5 7 true (pw4 par a)))
    (term par (pwLo par.s blo 9) (pwHi par.s bhi 9) 7 8 false (pw5 par a))

/-- The Taylor polynomial of the inverse root, applied to the jet of `F - u₀`. -/
noncomputable def isqrtOut (par : Par) (a : Jet) (blo bhi : ℕ) : Jet :=
  jadd par (jadd par (jadd par (jadd par (jadd par
    (jconst par (encC (pwLo par.s blo 1) (pwHi par.s bhi 1)) 0 (encR (pwLo par.s blo 1) (pwHi par.s bhi 1)))
    (term par (pwLo par.s blo 3) (pwHi par.s bhi 3) 1 1 true (tailJ par a)))
    (term par (pwLo par.s blo 5) (pwHi par.s bhi 5) 3 3 false (pw2 par a)))
    (term par (pwLo par.s blo 7) (pwHi par.s bhi 7) 5 4 true (pw3 par a)))
    (term par (pwLo par.s blo 9) (pwHi par.s bhi 9) 35 7 false (pw4 par a)))
    (term par (pwLo par.s blo 11) (pwHi par.s bhi 11) 63 8 true (pw5 par a))

theorem jcomp_true (par : Par) (a : Jet) (blo bhi : ℕ) :
    jcomp par true a blo bhi
      = ⟨(sqrtOut par a blo bhi).P, (sqrtOut par a blo bhi).N, (sqrtOut par a blo bhi).R,
          (sqrtOut par a blo bhi).S,
          (sqrtOut par a blo bhi).K
            + cdivn (bhi ^ 11 * nuOf par.w (tailJ par a) a.K ^ 6) (16 <<< (par.s * 16)),
          (sqrtOut par a blo bhi).ok && compOk par a blo bhi⟩ := rfl

theorem jcomp_false (par : Par) (a : Jet) (blo bhi : ℕ) :
    jcomp par false a blo bhi
      = ⟨(isqrtOut par a blo bhi).P, (isqrtOut par a blo bhi).N, (isqrtOut par a blo bhi).R,
          (isqrtOut par a blo bhi).S,
          (isqrtOut par a blo bhi).K
            + cdivn (bhi ^ 13 * nuOf par.w (tailJ par a) a.K ^ 6) (2 <<< (par.s * 18)),
          (isqrtOut par a blo bhi).ok && compOk par a blo bhi⟩ := rfl

/-- **The root of a jet.** -/
theorem good_sqrt (par : Par) (r : ℝ) (hr : r ≤ rb) (a : Jet) (blo bhi : ℕ) (F : (Fin 4 → ℝ) → ℝ)
    (h1 : Good par r a F) : Good par r (jcomp par true a blo bhi) (fun x => Real.sqrt (F x)) := by
  intro hok
  rw [jcomp_true] at hok ⊢
  have hok2 : ((sqrtOut par a blo bhi).ok && compOk par a blo bhi) = true := hok
  rw [Bool.and_eq_true] at hok2
  obtain ⟨hout, hck⟩ := hok2
  have o5 : (pw5 par a).ok = true := term_ok (jadd_ok hout).2
  have oN : (tailJ par a).ok = true := (jmul_ok o5).2
  obtain ⟨u0, b0, D⟩ := comp_data par r hr a blo bhi F h1 hck oN
  have hD : (0 : ℝ) < 2 ^ par.s := by positivity
  have hb0 := D.hb0
  -- the powers of `F - u₀`
  have gN := D.good
  have g2 : Good par r (pw2 par a) (fun x => (F x - u0) * (F x - u0)) := good_mul par r hr _ _ _ _ gN gN
  have g3 : Good par r (pw3 par a) (fun x => (F x - u0) * (F x - u0) * (F x - u0)) :=
    good_mul par r hr _ _ _ _ g2 gN
  have g4 : Good par r (pw4 par a) (fun x => (F x - u0) * (F x - u0) * ((F x - u0) * (F x - u0))) :=
    good_mul par r hr _ _ _ _ g2 g2
  have g5 : Good par r (pw5 par a)
      (fun x => (F x - u0) * (F x - u0) * ((F x - u0) * (F x - u0)) * (F x - u0)) :=
    good_mul par r hr _ _ _ _ g4 gN
  -- the terms of the Taylor polynomial
  have pb1 := pw_bounds par.s blo bhi 1 b0 (by norm_num) D.hblo D.hbhi
  have pb3 := pw_bounds par.s blo bhi 3 b0 (by norm_num) D.hblo D.hbhi
  have pb5 := pw_bounds par.s blo bhi 5 b0 (by norm_num) D.hblo D.hbhi
  have pb7 := pw_bounds par.s blo bhi 7 b0 (by norm_num) D.hblo D.hbhi
  have pb9 := pw_bounds par.s blo bhi 9 b0 (by norm_num) D.hblo D.hbhi
  have c0 : Good par r
      (jconst par (encC ((u0lo par.w a * blo) >>> par.s) (cdiv (u0hi par.w a * bhi) par.s)) 0
        (encR ((u0lo par.w a * blo) >>> par.s) (cdiv (u0hi par.w a * bhi) par.s))) (fun _ => u0 * b0) := by
    refine good_const par r _ 0 _ (u0 * b0) ?_
    rw [Nat.cast_zero, sub_zero]
    refine enc_sound _ _ _ ?_ ?_
    · rw [Nat.shiftRight_eq_div_pow]
      refine le_trans (cast_div_le' _ _) ?_
      push_cast
      rw [div_le_iff₀ hD]
      calc (u0lo par.w a : ℝ) * blo ≤ (2 ^ par.s * u0) * (2 ^ par.s * b0) :=
            mul_le_mul D.hulo D.hblo (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) D.hulo)
        _ = 2 ^ par.s * (u0 * b0) * 2 ^ par.s := by ring
    · refine le_trans ?_ (cdiv_ge _ _)
      push_cast
      rw [le_div_iff₀ hD]
      calc 2 ^ par.s * (u0 * b0) * 2 ^ par.s = (2 ^ par.s * u0) * (2 ^ par.s * b0) := by ring
        _ ≤ (u0hi par.w a : ℝ) * bhi := mul_le_mul D.huhi D.hbhi (mul_pos hD hb0).le (Nat.cast_nonneg _)
  have t1 := good_term par r (pwLo par.s blo 1) (pwHi par.s bhi 1) 1 1 false (tailJ par a) _ (b0 ^ 1) 1 rfl
    pb1.1 pb1.2 gN
  have t2 := good_term par r (pwLo par.s blo 3) (pwHi par.s bhi 3) 1 3 true (pw2 par a) _ (b0 ^ 3) (-1) rfl
    pb3.1 pb3.2 g2
  have t3 := good_term par r (pwLo par.s blo 5) (pwHi par.s bhi 5) 1 4 false (pw3 par a) _ (b0 ^ 5) 1 rfl
    pb5.1 pb5.2 g3
  have t4 := good_term par r (pwLo par.s blo 7) (pwHi par.s bhi 7) 5 7 true (pw4 par a) _ (b0 ^ 7) (-1) rfl
    pb7.1 pb7.2 g4
  have t5 := good_term par r (pwLo par.s blo 9) (pwHi par.s bhi 9) 7 8 false (pw5 par a) _ (b0 ^ 9) 1 rfl
    pb9.1 pb9.2 g5
  have gs := good_add par r _ _ _ _ (good_add par r _ _ _ _ (good_add par r _ _ _ _
    (good_add par r _ _ _ _ (good_add par r _ _ _ _ c0 t1) t2) t3) t4) t5
  obtain ⟨h, c, κ, hp, hrep, hκ, hK, henc⟩ := gs hout
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = (nuOf par.w (tailJ par a) a.K : ℝ) / 2 ^ par.s := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := by
    rw [hν]
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  have hsmall := D.small
  rw [← hν] at hsmall
  refine ⟨h, c, κ + 1 / 16 * b0 ^ 11 * ν ^ 6, ⟨hp.hP, hp.hN, hp.hR, hp.hS, hp.tot⟩,
    hrep.perturb (fun x => Real.sqrt (F x)) _ ?_, ?_, ?_, henc⟩
  · -- the rest of the Taylor polynomial
    intro x m hx hm
    have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
    have hn := D.bound x m hx hm
    rw [← hν] at hn
    have hsm : |F x - u0| * b0 ^ 2 ≤ 1 / 8 := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg b0)) hsmall
      exact le_trans hn (mul_le_mul_of_nonneg_left (le_trans hm hr) hν0)
    have ht := sqrt_taylor u0 b0 (F x - u0) hb0 D.hbu hsm
    rw [add_sub_cancel] at ht
    have h6 : |F x - u0| ^ 6 ≤ (ν * m) ^ 6 := pow_le_pow_left₀ (abs_nonneg _) hn 6
    have hb11 : 0 ≤ 1 / 16 * b0 ^ 11 := by positivity
    refine le_trans (le_of_eq (congrArg abs ?_)) (le_trans ht ?_)
    · push_cast
      ring
    · calc 1 / 16 * b0 ^ 11 * |F x - u0| ^ 6 ≤ 1 / 16 * b0 ^ 11 * (ν * m) ^ 6 :=
            mul_le_mul_of_nonneg_left h6 hb11
        _ = 1 / 16 * b0 ^ 11 * ν ^ 6 * m ^ 6 := by ring
  · exact add_nonneg hκ (by positivity)
  · -- the bound of order six
    have hνD : ν * 2 ^ par.s = (nuOf par.w (tailJ par a) a.K : ℝ) := by
      rw [hν, div_mul_eq_mul_div, mul_div_assoc, div_self hD.ne', mul_one]
    have hpos : (0 : ℝ) < 16 * (2 ^ par.s) ^ 16 := by positivity
    have hrem := cdivn_ge (bhi ^ 11 * nuOf par.w (tailJ par a) a.K ^ 6) (16 <<< (par.s * 16))
      (by rw [Nat.shiftLeft_eq]; positivity)
    have e16 : ((16 <<< (par.s * 16) : ℕ) : ℝ) = 16 * (2 ^ par.s) ^ 16 := by
      rw [Nat.shiftLeft_eq]
      push_cast
      rw [pow_mul]
    rw [e16, div_le_iff₀ hpos] at hrem
    push_cast at hrem
    have hbD : (b0 * 2 ^ par.s) ^ 11 ≤ (bhi : ℝ) ^ 11 :=
      pow_le_pow_left₀ (mul_pos hb0 hD).le (by rw [mul_comm]; exact D.hbhi) 11
    have key : (1 / 16 * b0 ^ 11 * ν ^ 6 * 2 ^ par.s : ℝ)
        ≤ (cdivn (bhi ^ 11 * nuOf par.w (tailJ par a) a.K ^ 6) (16 <<< (par.s * 16)) : ℝ) := by
      refine le_of_mul_le_mul_right ?_ hpos
      calc 1 / 16 * b0 ^ 11 * ν ^ 6 * 2 ^ par.s * (16 * (2 ^ par.s) ^ 16)
          = (b0 * 2 ^ par.s) ^ 11 * (ν * 2 ^ par.s) ^ 6 := by ring
        _ ≤ (bhi : ℝ) ^ 11 * (ν * 2 ^ par.s) ^ 6 := mul_le_mul_of_nonneg_right hbD (by positivity)
        _ = (bhi : ℝ) ^ 11 * (nuOf par.w (tailJ par a) a.K : ℝ) ^ 6 := by rw [hνD]
        _ ≤ _ := hrem
    have hK' : κ * 2 ^ par.s ≤ ((sqrtOut par a blo bhi).K : ℝ) := hK
    show ((κ + 1 / 16 * b0 ^ 11 * ν ^ 6) * 2 ^ par.s : ℝ)
      ≤ (((sqrtOut par a blo bhi).K
        + cdivn (bhi ^ 11 * nuOf par.w (tailJ par a) a.K ^ 6) (16 <<< (par.s * 16)) : ℕ) : ℝ)
    push_cast
    linarith

/-- **The inverse root of a jet.** -/
theorem good_isqrt (par : Par) (r : ℝ) (hr : r ≤ rb) (a : Jet) (blo bhi : ℕ) (F : (Fin 4 → ℝ) → ℝ)
    (h1 : Good par r a F) : Good par r (jcomp par false a blo bhi) (fun x => (Real.sqrt (F x))⁻¹) := by
  intro hok
  rw [jcomp_false] at hok ⊢
  have hok2 : ((isqrtOut par a blo bhi).ok && compOk par a blo bhi) = true := hok
  rw [Bool.and_eq_true] at hok2
  obtain ⟨hout, hck⟩ := hok2
  have o5 : (pw5 par a).ok = true := term_ok (jadd_ok hout).2
  have oN : (tailJ par a).ok = true := (jmul_ok o5).2
  obtain ⟨u0, b0, D⟩ := comp_data par r hr a blo bhi F h1 hck oN
  have hD : (0 : ℝ) < 2 ^ par.s := by positivity
  have hb0 := D.hb0
  -- the powers of `F - u₀`
  have gN := D.good
  have g2 : Good par r (pw2 par a) (fun x => (F x - u0) * (F x - u0)) := good_mul par r hr _ _ _ _ gN gN
  have g3 : Good par r (pw3 par a) (fun x => (F x - u0) * (F x - u0) * (F x - u0)) :=
    good_mul par r hr _ _ _ _ g2 gN
  have g4 : Good par r (pw4 par a) (fun x => (F x - u0) * (F x - u0) * ((F x - u0) * (F x - u0))) :=
    good_mul par r hr _ _ _ _ g2 g2
  have g5 : Good par r (pw5 par a)
      (fun x => (F x - u0) * (F x - u0) * ((F x - u0) * (F x - u0)) * (F x - u0)) :=
    good_mul par r hr _ _ _ _ g4 gN
  -- the terms of the Taylor polynomial
  have pb1 := pw_bounds par.s blo bhi 1 b0 (by norm_num) D.hblo D.hbhi
  have pb3 := pw_bounds par.s blo bhi 3 b0 (by norm_num) D.hblo D.hbhi
  have pb5 := pw_bounds par.s blo bhi 5 b0 (by norm_num) D.hblo D.hbhi
  have pb7 := pw_bounds par.s blo bhi 7 b0 (by norm_num) D.hblo D.hbhi
  have pb9 := pw_bounds par.s blo bhi 9 b0 (by norm_num) D.hblo D.hbhi
  have pb11 := pw_bounds par.s blo bhi 11 b0 (by norm_num) D.hblo D.hbhi
  have c0 : Good par r
      (jconst par (encC (pwLo par.s blo 1) (pwHi par.s bhi 1)) 0
        (encR (pwLo par.s blo 1) (pwHi par.s bhi 1))) (fun _ => b0 ^ 1) := by
    refine good_const par r _ 0 _ (b0 ^ 1) ?_
    rw [Nat.cast_zero, sub_zero]
    exact enc_sound _ _ _ pb1.1 pb1.2
  have t1 := good_term par r (pwLo par.s blo 3) (pwHi par.s bhi 3) 1 1 true (tailJ par a) _ (b0 ^ 3) (-1) rfl
    pb3.1 pb3.2 gN
  have t2 := good_term par r (pwLo par.s blo 5) (pwHi par.s bhi 5) 3 3 false (pw2 par a) _ (b0 ^ 5) 1 rfl
    pb5.1 pb5.2 g2
  have t3 := good_term par r (pwLo par.s blo 7) (pwHi par.s bhi 7) 5 4 true (pw3 par a) _ (b0 ^ 7) (-1) rfl
    pb7.1 pb7.2 g3
  have t4 := good_term par r (pwLo par.s blo 9) (pwHi par.s bhi 9) 35 7 false (pw4 par a) _ (b0 ^ 9) 1 rfl
    pb9.1 pb9.2 g4
  have t5 := good_term par r (pwLo par.s blo 11) (pwHi par.s bhi 11) 63 8 true (pw5 par a) _ (b0 ^ 11) (-1)
    rfl pb11.1 pb11.2 g5
  have gs := good_add par r _ _ _ _ (good_add par r _ _ _ _ (good_add par r _ _ _ _
    (good_add par r _ _ _ _ (good_add par r _ _ _ _ c0 t1) t2) t3) t4) t5
  obtain ⟨h, c, κ, hp, hrep, hκ, hK, henc⟩ := gs hout
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = (nuOf par.w (tailJ par a) a.K : ℝ) / 2 ^ par.s := ⟨_, rfl⟩
  have hν0 : 0 ≤ ν := by
    rw [hν]
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  have hsmall := D.small
  rw [← hν] at hsmall
  refine ⟨h, c, κ + 1 / 2 * b0 ^ 13 * ν ^ 6, ⟨hp.hP, hp.hN, hp.hR, hp.hS, hp.tot⟩,
    hrep.perturb (fun x => (Real.sqrt (F x))⁻¹) _ ?_, ?_, ?_, henc⟩
  · -- the rest of the Taylor polynomial
    intro x m hx hm
    have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hx 0)
    have hn := D.bound x m hx hm
    rw [← hν] at hn
    have hsm : |F x - u0| * b0 ^ 2 ≤ 1 / 8 := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg b0)) hsmall
      exact le_trans hn (mul_le_mul_of_nonneg_left (le_trans hm hr) hν0)
    have ht := (isqrt_taylor u0 b0 (F x - u0) hb0 D.hbu hsm).2
    rw [add_sub_cancel] at ht
    have h6 : |F x - u0| ^ 6 ≤ (ν * m) ^ 6 := pow_le_pow_left₀ (abs_nonneg _) hn 6
    have hb13 : 0 ≤ 1 / 2 * b0 ^ 13 := by positivity
    refine le_trans (le_of_eq (congrArg abs ?_)) (le_trans ht ?_)
    · push_cast
      ring
    · calc 1 / 2 * b0 ^ 13 * |F x - u0| ^ 6 ≤ 1 / 2 * b0 ^ 13 * (ν * m) ^ 6 :=
            mul_le_mul_of_nonneg_left h6 hb13
        _ = 1 / 2 * b0 ^ 13 * ν ^ 6 * m ^ 6 := by ring
  · exact add_nonneg hκ (by positivity)
  · -- the bound of order six
    have hνD : ν * 2 ^ par.s = (nuOf par.w (tailJ par a) a.K : ℝ) := by
      rw [hν, div_mul_eq_mul_div, mul_div_assoc, div_self hD.ne', mul_one]
    have hpos : (0 : ℝ) < 2 * (2 ^ par.s) ^ 18 := by positivity
    have hrem := cdivn_ge (bhi ^ 13 * nuOf par.w (tailJ par a) a.K ^ 6) (2 <<< (par.s * 18))
      (by rw [Nat.shiftLeft_eq]; positivity)
    have e18 : ((2 <<< (par.s * 18) : ℕ) : ℝ) = 2 * (2 ^ par.s) ^ 18 := by
      rw [Nat.shiftLeft_eq]
      push_cast
      rw [pow_mul]
    rw [e18, div_le_iff₀ hpos] at hrem
    push_cast at hrem
    have hbD : (b0 * 2 ^ par.s) ^ 13 ≤ (bhi : ℝ) ^ 13 :=
      pow_le_pow_left₀ (mul_pos hb0 hD).le (by rw [mul_comm]; exact D.hbhi) 13
    have key : (1 / 2 * b0 ^ 13 * ν ^ 6 * 2 ^ par.s : ℝ)
        ≤ (cdivn (bhi ^ 13 * nuOf par.w (tailJ par a) a.K ^ 6) (2 <<< (par.s * 18)) : ℝ) := by
      refine le_of_mul_le_mul_right ?_ hpos
      calc 1 / 2 * b0 ^ 13 * ν ^ 6 * 2 ^ par.s * (2 * (2 ^ par.s) ^ 18)
          = (b0 * 2 ^ par.s) ^ 13 * (ν * 2 ^ par.s) ^ 6 := by ring
        _ ≤ (bhi : ℝ) ^ 13 * (ν * 2 ^ par.s) ^ 6 := mul_le_mul_of_nonneg_right hbD (by positivity)
        _ = (bhi : ℝ) ^ 13 * (nuOf par.w (tailJ par a) a.K : ℝ) ^ 6 := by rw [hνD]
        _ ≤ _ := hrem
    have hK' : κ * 2 ^ par.s ≤ ((isqrtOut par a blo bhi).K : ℝ) := hK
    show ((κ + 1 / 2 * b0 ^ 13 * ν ^ 6) * 2 ^ par.s : ℝ)
      ≤ (((isqrtOut par a blo bhi).K
        + cdivn (bhi ^ 13 * nuOf par.w (tailJ par a) a.K ^ 6) (2 <<< (par.s * 18)) : ℕ) : ℝ)
    push_cast
    linarith

end N14.Jet
