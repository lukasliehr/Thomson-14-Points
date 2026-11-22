module

public import CAP.UniPos.Sound
public import N14.Box.Cell

/-!
# T7, the slack on a domain: soundness of the table entries

**Theorem** (`table_sound`). If the checker accepts a table (`tableOk`), then for every interval of the table
with an entry `T`, and for every `t < 1` of the interval,

  `c1 * T(t) + K(t) ≤ Dn / √(2 - 2 t)`,

where `T(t) = ∑ d ≤ n, T_d t ^ d` with the slots `T_d` of the entry (`uraw`), and `K(t)` is the polynomial whose
coefficients are the slots of `K` minus the bias (`CAP.UniPos.hEval`). In other words, `T ≤ U` on the interval for
the function `U(t) = (Dn / √(2 - 2 t) - K(t)) / c1` of the table (`tabFn`).

The proof reduces the statement to the theorem `CAP.UniPos.interval_bound` of the library: the slots of
`c1 * T + K` are `c1 * T_d + K_d` (`slot_lin`), and the pieces of an entry cover its interval (`pieces_cover`).
For a function without a Coulomb term (`Dn = 0`) the test of a piece is `negOk`, and `neg_bound` shows `Ĥ ≤ 0`
on the piece with the lemmas of the library on Horner's rule (`hornerGo_top`, `hbP_rv`).
-/

@[expose] public section

namespace N14.Box

open CAP CAP.UniPos Finset

/-- The function of one variable of a table. -/
noncomputable def tabFn (U : Tab) (t : ℝ) : ℝ :=
  ((U.Dn : ℝ) / Real.sqrt (2 - 2 * t) - hEval U.P U.K t) / U.c1

/-- The statement of a table entry. -/
def EntryGood (U : Tab) (x : Ent) : Prop :=
  ∀ t : ℝ, InIv x t → t < 1 → uraw U.P.W U.n x.T t ≤ tabFn U t

/-- An accepted piece without a Coulomb term: the coefficients of the positive part of `Hb` are at most those
of the negative part. -/
theorem negOk_coeff (P : UniPos.Params) (Hp lk lk1 : ℕ) (hV : 1 ≤ P.V) (h : negOk P Hp lk lk1 = true) :
    ∀ i, (hbP P Hp lk lk1).1.coeff i ≤ (hbP P Hp lk lk1).2.coeff i := by
  have h0 : (Nat.blt (hornerGo P 0 Hp lk lk1 (2 * P.D + 1) 0 0 1).1 (1 <<< (P.V - 1))
      && Nat.blt (hornerGo P 0 Hp lk lk1 (2 * P.D + 1) 0 0 1).2 (1 <<< (P.V - 1))
      && geTest P.V (2 * P.D + 2) (hornerGo P P.V Hp lk lk1 (2 * P.D + 1) 0 0 1).2
        (hornerGo P P.V Hp lk lk1 (2 * P.D + 1) 0 0 1).1) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.one_shiftLeft, hornerGo_top, hornerGo_top,
    pow_zero] at h0
  obtain ⟨⟨hb1, hb2⟩, hg⟩ := h0
  obtain ⟨d1, d2⟩ := natDegree_hbP P Hp lk lk1
  have d1' : (hbP P Hp lk lk1).1.natDegree < 2 * P.D + 2 := by omega
  have d2' : (hbP P Hp lk lk1).2.natDegree < 2 * P.D + 2 := by omega
  have hg' : geTest P.V (2 * P.D + 2) (packSum P.V (2 * P.D + 2) (hbP P Hp lk lk1).2.coeff)
      (packSum P.V (2 * P.D + 2) (hbP P Hp lk lk1).1.coeff) = true := by
    rw [← eval_two_pow P.V _ _ d2', ← eval_two_pow P.V _ _ d1']
    exact hg
  have key := geTest_sound P.V (2 * P.D + 2) _ _ hV
    (fun i _ => lt_of_le_of_lt (coeff_le_eval_one _ i) hb2)
    (fun i _ => lt_of_le_of_lt (coeff_le_eval_one _ i) hb1) hg'
  intro i
  by_cases hi : i < 2 * P.D + 2
  · exact key i hi
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le d1' (not_lt.mp hi))]
    exact Nat.zero_le _

/-- An accepted piece without a Coulomb term: `Ĥ ≤ 0` on the piece. -/
theorem neg_bound (P : UniPos.Params) (Hp lk lk1 : ℕ) (hV : 1 ≤ P.V) (h : negOk P Hp lk lk1 = true)
    (t : ℝ) (h1 : (lk1 : ℝ) < 2 ^ P.s * (1 - t)) (h2 : 2 ^ P.s * (1 - t) ≤ lk) : hEval P Hp t ≤ 0 := by
  have hδ : 0 < 2 ^ P.s * (1 - t) - lk1 := sub_pos.mpr h1
  have hy : 0 ≤ ((lk : ℝ) - 2 ^ P.s * (1 - t)) / (2 ^ P.s * (1 - t) - lk1) :=
    div_nonneg (sub_nonneg.mpr h2) hδ.le
  generalize hyd : ((lk : ℝ) - 2 ^ P.s * (1 - t)) / (2 ^ P.s * (1 - t) - lk1) = y at hy
  have hmono := rv_mono y hy _ _ (negOk_coeff P Hp lk lk1 hV h)
  have hrv := hbP_rv P Hp lk lk1 y
  rw [rv_L2, rv_Mf] at hrv
  have hm : (lk : ℝ) + lk1 * y = 2 ^ P.s * (1 + y) * (1 - t) := by
    rw [← hyd]
    field_simp
    ring
  have hpos : (0 : ℝ) < 2 ^ P.s * (1 + y) := by positivity
  have hsub : (2 : ℝ) ^ P.s * (1 + y) - 2 ^ P.s * (1 + y) * (1 - t) = 2 ^ P.s * (1 + y) * t := by ring
  have hsum : ∑ d ∈ range (2 * P.D + 1), (coefZ P Hp d : ℝ) * (2 ^ P.s * (1 + y) * t) ^ d
        * (2 ^ P.s * (1 + y)) ^ (2 * P.D - d)
      = (2 ^ P.s * (1 + y)) ^ (2 * P.D) * hEval P Hp t := by
    unfold hEval
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hd' : d ≤ 2 * P.D := Nat.lt_succ_iff.mp (mem_range.mp hd)
    have e : (2 ^ P.s * (1 + y)) ^ (2 * P.D) = (2 ^ P.s * (1 + y)) ^ d * (2 ^ P.s * (1 + y)) ^ (2 * P.D - d) := by
      rw [← pow_add, Nat.add_sub_of_le hd']
    rw [e, mul_pow]
    ring
  rw [hm, hsub, hsum] at hrv
  have hle : (2 ^ P.s * (1 + y)) ^ (2 * P.D) * hEval P Hp t ≤ 0 := by linarith
  by_contra hc
  have := mul_pos (pow_pos hpos (2 * P.D)) (not_le.mp hc)
  linarith

/-- **An accepted piece.** `Ĥ(t) ≤ Dn / √(2 - 2 t)` at the points `t < 1` of the piece. -/
theorem piece_bound (P : UniPos.Params) (Hp Dn lk lk1 : ℕ) (hV : 1 ≤ P.V) (h : pieceOk P Hp Dn lk lk1 = true)
    (t : ℝ) (ht : t < 1) (h1 : (lk1 : ℝ) < 2 ^ P.s * (1 - t)) (h2 : 2 ^ P.s * (1 - t) ≤ lk) :
    hEval P Hp t ≤ (Dn : ℝ) / Real.sqrt (2 - 2 * t) := by
  cases Dn with
  | zero =>
    have h' : negOk P Hp lk lk1 = true := h
    rw [Nat.cast_zero, zero_div]
    exact neg_bound P Hp lk lk1 hV h' t h1 h2
  | succ k =>
    have h' : intervalOk P Hp (k + 1) lk lk1 = true := h
    exact le_div_sqrt (by linarith) (Nat.cast_nonneg _) (interval_bound P Hp (k + 1) lk lk1 hV h' t h1 h2)

/-- The pieces of an entry cover the numbers between the last cut and the first one. -/
theorem pieces_cover (P : UniPos.Params) (Hp Dn last : ℕ) : ∀ (l : List ℕ) (prev : ℕ),
    piecesGo P Hp Dn last l prev = true → ∀ μ : ℝ, (last : ℝ) < μ → μ ≤ prev →
      ∃ lk lk1 : ℕ, pieceOk P Hp Dn lk lk1 = true ∧ (lk1 : ℝ) < μ ∧ μ ≤ lk := by
  intro l
  induction l with
  | nil =>
    intro prev h μ h1 h2
    have h' : Nat.ble prev last = true := h
    rw [Nat.ble_eq] at h'
    have : (prev : ℝ) ≤ last := Nat.cast_le.mpr h'
    linarith
  | cons lam l ih =>
    intro prev h μ h1 h2
    have h' : (Nat.blt lam prev && pieceOk P Hp Dn prev lam && piecesGo P Hp Dn last l lam) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    by_cases hμ : (lam : ℝ) < μ
    · exact ⟨prev, lam, h'.1.2, hμ, h2⟩
    · exact ih lam h'.2 μ h1 (not_lt.mp hμ)

/-- The slots of a number below `2 ^ (w * m)` vanish from the slot `m` on. -/
theorem slot_zero (w x m d : ℕ) (hx : x < 2 ^ (w * m)) (hd : m ≤ d) : slot w x d = 0 := by
  rw [slot_eq]
  have : x / 2 ^ (w * d) = 0 := by
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hd))
  rw [this, Nat.zero_mod]

/-- The slots of `c * T + K`. -/
theorem slot_lin (w m c T K aT : ℕ) (hw : 1 ≤ w) (hT : T < 2 ^ (w * m)) (hK : K < 2 ^ (w * m))
    (hTs : ∀ d, d < m → slot w T d < 2 ^ aT) (hKs : ∀ d, d < m → slot w K d < 2 ^ (w - 1))
    (hc : c * 2 ^ aT ≤ 2 ^ (w - 1)) (d : ℕ) (hd : d < m) :
    slot w (c * T + K) d = c * slot w T d + slot w K d := by
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  have e : c * T + K = packSum w m (fun d => c * slot w T d + slot w K d) := by
    rw [packSum_add, packSum_mul, packSum_slot w m T hT, packSum_slot w m K hK]
  rw [e]
  refine slot_packSum w m _ (fun j hj => ?_) d hd
  have a1 := hTs j hj
  have a2 := hKs j hj
  have a3 : c * slot w T j ≤ c * 2 ^ aT := Nat.mul_le_mul_left _ a1.le
  omega

/-- What the tests of the parameters of a table give. -/
structure TabFit (U : Tab) : Prop where
  hV : 1 ≤ U.P.V
  hW : 1 ≤ U.P.W
  haT : U.aT ≤ U.P.W
  hc1 : 1 ≤ U.c1
  hn : U.n ≤ 2 * U.P.D
  hc : U.c1 * 2 ^ U.aT ≤ 2 ^ (U.P.W - 1)
  hK : U.K < 2 ^ (U.P.W * (2 * U.P.D + 1))
  hKs : ∀ d, d < 2 * U.P.D + 1 → slot U.P.W U.K d < 2 ^ (U.P.W - 1)

theorem tabOk_fit (U : Tab) (h : tabOk U = true) : TabFit U := by
  have h' : (Nat.ble 1 U.P.V && Nat.ble 1 U.P.W && Nat.ble U.aT U.P.W && Nat.ble 1 U.c1
      && Nat.ble U.n (2 * U.P.D) && Nat.ble (U.c1 * (1 <<< U.aT)) (1 <<< (U.P.W - 1))
      && Nat.blt U.K (1 <<< (U.P.W * (2 * U.P.D + 1)))
      && Nat.beq (U.K &&& ((1 <<< (U.P.W - 1)) * ones U.P.W (2 * U.P.D + 1))) 0) = true := h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨hV, hW⟩, haT⟩, hc1⟩, hn⟩, hc⟩, hK⟩, hbits⟩ := h'
  have hbits' := Nat.eq_of_beq_eq_true hbits
  have hs := packSum_slot U.P.W (2 * U.P.D + 1) U.K hK
  have h2 : 2 ^ (U.P.W - 1) = 2 ^ U.P.W - 2 ^ (U.P.W - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, U.P.W = k + 1 := ⟨U.P.W - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    omega
  rw [← hs, ones_eq U.P.W _ hW, h2] at hbits'
  have hd := slots_lt_of_and_hi U.P.W (U.P.W - 1) _ (slot U.P.W U.K) (Nat.sub_le _ _)
    (fun j _ => slot_lt U.P.W U.K j) hbits'
  exact ⟨hV, hW, haT, hc1, hn, hc, hK, hd⟩

/-- **Soundness of the checker of a table entry.** -/
theorem entry_sound (U : Tab) (hU : TabFit U) (x : Ent) (h : entryOk U x = true) : EntryGood U x := by
  have h' : (Nat.blt x.T (1 <<< (U.P.W * (U.n + 1)))
      && Nat.beq (x.T &&& ((1 <<< U.P.W - 1 <<< U.aT) * ones U.P.W (U.n + 1))) 0
      && Nat.ble x.e U.P.s && Nat.blt x.c (2 <<< x.e)
      && piecesGo U.P (U.c1 * x.T + U.K) U.Dn ((((2 <<< x.e) - x.c - 1) <<< (U.P.s - x.e)) - 1) x.cuts
        (((2 <<< x.e) - x.c) <<< (U.P.s - x.e))) = true := h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.one_shiftLeft] at h'
  obtain ⟨⟨⟨⟨hT, hbits⟩, he⟩, hc⟩, hp⟩ := h'
  have hbits' := Nat.eq_of_beq_eq_true hbits
  -- the slots of `T`
  have hsT := packSum_slot U.P.W (U.n + 1) x.T hT
  rw [← hsT, ones_eq U.P.W _ hU.hW] at hbits'
  have hTs := slots_lt_of_and_hi U.P.W U.aT _ (slot U.P.W x.T) hU.haT (fun j _ => slot_lt U.P.W x.T j) hbits'
  have hT' : x.T < 2 ^ (U.P.W * (2 * U.P.D + 1)) :=
    lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by have := hU.hn; omega)))
  have hTs' : ∀ d, d < 2 * U.P.D + 1 → slot U.P.W x.T d < 2 ^ U.aT := by
    intro d _
    by_cases hd : d < U.n + 1
    · exact hTs d hd
    · rw [slot_zero U.P.W x.T (U.n + 1) d hT (not_lt.mp hd)]
      exact Nat.two_pow_pos _
  intro t ht ht1
  -- the value of `Ĥ`
  have hval : hEval U.P (U.c1 * x.T + U.K) t = (U.c1 : ℝ) * uraw U.P.W U.n x.T t + hEval U.P U.K t := by
    unfold hEval uraw
    rw [mul_sum]
    have hsplit : ∑ d ∈ range (U.n + 1), (U.c1 : ℝ) * ((slot U.P.W x.T d : ℝ) * t ^ d)
        = ∑ d ∈ range (2 * U.P.D + 1), (U.c1 : ℝ) * ((slot U.P.W x.T d : ℝ) * t ^ d) := by
      refine sum_subset (fun d hd => mem_range.mpr (by have := mem_range.mp hd; have := hU.hn; omega))
        (fun d _ hd => ?_)
      rw [slot_zero U.P.W x.T (U.n + 1) d hT (by have := mt mem_range.mpr hd; omega)]
      simp
    rw [hsplit, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    unfold coefZ
    rw [slot_lin U.P.W (2 * U.P.D + 1) U.c1 x.T U.K U.aT hU.hW hT' hU.hK hTs' hU.hKs hU.hc d (mem_range.mp hd)]
    push_cast
    ring
  -- the point in the units of the pieces
  have hp2 : (0 : ℝ) < 2 ^ x.e := by positivity
  have hs2 : (2 : ℝ) ^ U.P.s = 2 ^ (U.P.s - x.e) * 2 ^ x.e := by
    rw [← pow_add, Nat.sub_add_cancel he]
  have hpd : (0 : ℝ) < 2 ^ (U.P.s - x.e) := by positivity
  have hc' : x.c < 2 * 2 ^ x.e := by
    rw [Nat.shiftLeft_eq] at hc
    exact hc
  obtain ⟨hta, htb⟩ := ht
  have hμ0 : (0 : ℝ) < (2 : ℝ) ^ U.P.s * ((1 : ℝ) - t) := by
    have : (0 : ℝ) < 1 - t := by linarith
    positivity
  -- the upper end
  have hhi : (2 : ℝ) ^ U.P.s * ((1 : ℝ) - t) ≤ ((((2 <<< x.e) - x.c) <<< (U.P.s - x.e) : ℕ) : ℝ) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_sub hc'.le]
    push_cast
    have h1 : 1 - t ≤ 2 - (x.c : ℝ) / 2 ^ x.e := by linarith
    have h2 : (2 : ℝ) ^ x.e * (1 - t) ≤ 2 * 2 ^ x.e - x.c := by
      have := mul_le_mul_of_nonneg_left h1 hp2.le
      have e : (2 : ℝ) ^ x.e * (2 - (x.c : ℝ) / 2 ^ x.e) = 2 * 2 ^ x.e - x.c := by
        field_simp
      linarith
    rw [hs2]
    nlinarith
  -- the lower end
  have hlo : ((((((2 <<< x.e) - x.c - 1) <<< (U.P.s - x.e)) - 1 : ℕ) : ℕ) : ℝ) < (2 : ℝ) ^ U.P.s * ((1 : ℝ) - t) := by
    by_cases hz : ((2 <<< x.e) - x.c - 1) <<< (U.P.s - x.e) = 0
    · rw [hz]
      simpa using hμ0
    · have hpos : 1 ≤ ((2 <<< x.e) - x.c - 1) <<< (U.P.s - x.e) := Nat.one_le_iff_ne_zero.mpr hz
      rw [Nat.cast_sub hpos, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      have hc1 : 1 ≤ 2 * 2 ^ x.e - x.c := by omega
      rw [Nat.cast_mul, Nat.cast_sub hc1, Nat.cast_sub hc'.le]
      push_cast
      have h1 : 2 - ((x.c : ℝ) + 1) / 2 ^ x.e ≤ 1 - t := by linarith
      have h2 : 2 * 2 ^ x.e - (x.c : ℝ) - 1 ≤ (2 : ℝ) ^ x.e * (1 - t) := by
        have := mul_le_mul_of_nonneg_left h1 hp2.le
        have e : (2 : ℝ) ^ x.e * (2 - ((x.c : ℝ) + 1) / 2 ^ x.e) = 2 * 2 ^ x.e - x.c - 1 := by
          field_simp
          ring
        linarith
      rw [hs2]
      nlinarith
  obtain ⟨lk, lk1, hok, hl, hu⟩ := pieces_cover U.P _ U.Dn _ x.cuts _ hp _ hlo hhi
  have key := piece_bound U.P _ U.Dn lk lk1 hU.hV hok t ht1 hl hu
  rw [hval] at key
  unfold tabFn
  have hc1 : (0 : ℝ) < U.c1 := by exact_mod_cast hU.hc1
  rw [le_div_iff₀ hc1]
  linarith

/-- The entries of a list of intervals. -/
theorem tableGo_sound (U : Tab) (hU : TabFit U) : ∀ l : List Ent, tableGo U l = true →
    ∀ x ∈ l, 0 < x.T → EntryGood U x := by
  intro l
  induction l with
  | nil => exact fun _ x hx => absurd hx (List.not_mem_nil)
  | cons y l ih =>
    intro h x hx hT
    have h' : (Nat.rec (motive := fun _ => Bool) true (fun _ _ => entryOk U y) y.T && tableGo U l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hx with rfl | hx'
    · have h1 := h'.1
      obtain ⟨k, hk⟩ : ∃ k, x.T = k + 1 := ⟨x.T - 1, by omega⟩
      rw [hk] at h1
      exact entry_sound U hU x h1
    · exact ih h'.2 x hx' hT

/-- **Soundness of the checker of a table.** -/
theorem table_sound (U : Tab) (entries : List Ent) (h : tableOk U entries = true) :
    ∀ x ∈ entries, 0 < x.T → EntryGood U x := by
  have h' : (tabOk U && tableGo U entries) = true := h
  rw [Bool.and_eq_true] at h'
  exact tableGo_sound U (tabOk_fit U h'.1) entries h'.2

end N14.Box
