module

public import CAP.Core.Triangular
public import CAP.Schema.ThreePoint.Terms

/-!
# Schema S2, soundness: the moment blocks

The functions `qNext`, `phiEval` and `moment` of the checker compute the values, at an arbitrary
point, of the following pairs of polynomials with natural coefficients:

* `qP P k`: the kernel `Qₖ`, defined by the recurrence of the checker;
* `phiP P n rows`: the polynomial `φ = ∑_{i ≤ j} X i j • u ^ i * v ^ j` of a block of order `n`,
  whose positive part has the slots of `rows` as coefficients and whose negative part has the
  bias `2 ^ (a - 1)`;
* `momentP P mrows`: the sum of the products `φₖ * Qₖ`.

The flags of the data that these functions return are not used here: the entries of the matrices
are defined as slot minus bias for arbitrary slots.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-! ## Pairs -/

/-- The product of two pairs (positive part, negative part). -/
noncomputable def pmul (a b : Poly × Poly) : Poly × Poly :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- The values of the two parts of a pair at a point. -/
noncomputable def evp (P : Params) (pt : Pt) (a : Poly × Poly) : ℕ × ℕ := (ev P pt a.1, ev P pt a.2)

theorem evp_add (P : Params) (pt : Pt) (a b : Poly × Poly) :
    evp P pt (a + b) = (ev P pt a.1 + ev P pt b.1, ev P pt a.2 + ev P pt b.2) := by
  simp [evp]

theorem evp_pmul (P : Params) (pt : Pt) (a b : Poly × Poly) :
    evp P pt (pmul a b) = (ev P pt a.1 * ev P pt b.1 + ev P pt a.2 * ev P pt b.2,
      ev P pt a.1 * ev P pt b.2 + ev P pt a.2 * ev P pt b.1) := by
  simp [evp, pmul]

/-- `mulTerms` on the values of pairs. -/
theorem mulTerms_evp (P : Params) (pt : Pt) (T tf : ℕ) (x y : Poly × Poly) :
    mulTerms P pt T tf (ev P pt x.1) (ev P pt x.2) (ev P pt y.1) (ev P pt y.2)
      = evp P pt (y + pmul (polyOf P T tf) x) := by
  rw [mulTerms_eq]
  simp only [evp, pmul, Prod.fst_add, Prod.snd_add, map_add, map_mul]

/-! ## The kernels `Qₖ` -/

/-- The pair of `t - u * v`, as the checker reads its term fields. -/
noncomputable def tuvP (P : Params) : Poly × Poly := polyOf P 2 (tuv P)

/-- The pair of `(1 - u ^ 2) * (1 - v ^ 2)`, as the checker reads its term fields. -/
noncomputable def wuvP (P : Params) : Poly × Poly := polyOf P 4 (wuv P)

/-- The pair of `2 * (t - u * v) * cur - (1 - u ^ 2) * (1 - v ^ 2) * prev`. -/
noncomputable def qNextP (P : Params) (cur prev : Poly × Poly) : Poly × Poly :=
  (2 * (pmul (tuvP P) cur).1 + (pmul (wuvP P) prev).2, 2 * (pmul (tuvP P) cur).2 + (pmul (wuvP P) prev).1)

/-- The pair of the kernel `Qₖ`. -/
noncomputable def qP (P : Params) : ℕ → Poly × Poly
  | 0 => (1, 0)
  | 1 => pmul (tuvP P) (1, 0)
  | k + 2 => qNextP P (qP P (k + 1)) (qP P k)

theorem qNext_evp (P : Params) (pt : Pt) (cur prev : Poly × Poly) :
    qNext P pt (evp P pt cur) (evp P pt prev) = evp P pt (qNextP P cur prev) := by
  have h1 := mulTerms_evp P pt 2 (tuv P) cur (0, 0)
  have h2 := mulTerms_evp P pt 4 (wuv P) prev (0, 0)
  simp only [map_zero] at h1 h2
  show (2 * (mulTerms P pt 2 (tuv P) (ev P pt cur.1) (ev P pt cur.2) 0 0).1
      + (mulTerms P pt 4 (wuv P) (ev P pt prev.1) (ev P pt prev.2) 0 0).2,
    2 * (mulTerms P pt 2 (tuv P) (ev P pt cur.1) (ev P pt cur.2) 0 0).2
      + (mulTerms P pt 4 (wuv P) (ev P pt prev.1) (ev P pt prev.2) 0 0).1) = _
  have h3 : ev P pt 2 = 2 := map_ofNat (ev P pt) 2
  rw [h1, h2]
  simp only [evp, qNextP, tuvP, wuvP, Prod.mk_zero_zero, zero_add, map_add, map_mul, h3]

theorem q_one_evp (P : Params) (pt : Pt) :
    mulTerms P pt 2 (tuv P) 1 0 0 0 = evp P pt (qP P 1) := by
  have h := mulTerms_evp P pt 2 (tuv P) (1, 0) (0, 0)
  simp only [map_zero, map_one] at h
  rw [h]
  show evp P pt ((0, 0) + pmul (polyOf P 2 (tuv P)) (1, 0)) = evp P pt (pmul (polyOf P 2 (tuv P)) (1, 0))
  rw [Prod.mk_zero_zero, zero_add]

/-! ## The polynomial `φ` of a moment block -/

theorem phiRow_zero (w mw beta dv rho s php phn : ℕ) :
    phiRow w mw beta dv 0 rho s php phn = (php, phn) := rfl

theorem phiRow_succ (w beta dv cnt rho s php phn : ℕ) :
    phiRow w (2 ^ w - 1) beta dv (cnt + 1) rho s php phn =
      phiRow w (2 ^ w - 1) beta dv cnt (rho / 2 ^ w) (s + dv) (php + rho % 2 ^ w * 2 ^ s)
        (phn + beta * 2 ^ s) := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_eq]
  rfl

/-- One row: the slots `f j` are added at the shifts `s + j * dv`. -/
theorem phiRow_eq (w beta dv : ℕ) : ∀ (cnt : ℕ) (f : ℕ → ℕ) (s php phn : ℕ),
    (∀ j, j < cnt → f j < 2 ^ w) →
    phiRow w (2 ^ w - 1) beta dv cnt (packSum w cnt f) s php phn =
      (php + ∑ j ∈ range cnt, f j * 2 ^ (s + j * dv), phn + ∑ j ∈ range cnt, beta * 2 ^ (s + j * dv))
  | 0, f, s, php, phn, _ => by simp [phiRow_zero]
  | cnt + 1, f, s, php, phn, hf => by
    have e : ∀ j, s + dv + j * dv = s + (j + 1) * dv := fun j => by ring
    rw [phiRow_succ, packSum_succ_mod w cnt f (hf 0 (Nat.succ_pos cnt)),
      packSum_succ_div w cnt f (hf 0 (Nat.succ_pos cnt)),
      phiRow_eq w beta dv cnt _ _ _ _ (fun j hj => hf (j + 1) (Nat.succ_lt_succ hj)),
      sum_range_succ', sum_range_succ']
    simp only [e, zero_mul, add_zero]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-- The pair of `φ` for a block of order `n` stored in `rows`. -/
noncomputable def phiP (P : Params) (n rows : ℕ) : Poly × Poly :=
  (∑ i ∈ range n, ∑ s ∈ range (n - i), C (triEnt P.w n rows i s) * (X 0 ^ i * X 1 ^ (i + s)),
   ∑ i ∈ range n, ∑ s ∈ range (n - i), C (2 ^ (P.a - 1)) * (X 0 ^ i * X 1 ^ (i + s)))

theorem ev_uv (P : Params) (pt : Pt) (i j : ℕ) :
    ev P pt (X 0 ^ i * X 1 ^ j) = 2 ^ (P.W * (i * pt.pu) + j * (P.W * pt.pv)) := by
  unfold ev
  simp only [map_mul, map_pow, eval_X]
  show (2 ^ (P.W * pt.pu)) ^ i * (2 ^ (P.W * pt.pv)) ^ j = _
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem ev_C_uv (P : Params) (pt : Pt) (c i j : ℕ) :
    ev P pt (C c * (X 0 ^ i * X 1 ^ j)) = c * 2 ^ (P.W * (i * pt.pu) + j * (P.W * pt.pv)) := by
  rw [map_mul, ev_C, ev_uv]

theorem phiGo_zero (P : Params) (pt : Pt) (n R i php phn : ℕ) (ok : Bool) :
    phiGo P pt n 0 R i php phn ok = (php, phn, ok && Nat.beq R 0) := rfl

theorem phiGo_succ (P : Params) (pt : Pt) (n cnt R i php phn : ℕ) (ok : Bool) :
    phiGo P pt n (cnt + 1) R i php phn ok =
      phiGo P pt n cnt (R / 2 ^ (P.w * (n - i))) (i + 1)
        (phiRow P.w (2 ^ P.w - 1) (2 ^ (P.a - 1)) (P.W * pt.pv) (n - i) (R % 2 ^ (P.w * (n - i)))
          (P.W * (i * (pt.pu + pt.pv))) php phn).1
        (phiRow P.w (2 ^ P.w - 1) (2 ^ (P.a - 1)) (P.W * pt.pv) (n - i) (R % 2 ^ (P.w * (n - i)))
          (P.W * (i * (pt.pu + pt.pv))) php phn).2
        (ok && Nat.beq (R % 2 ^ (P.w * (n - i)) &&& (2 ^ P.w - 2 ^ P.a) * ones P.w (n - i)) 0) := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow, ← mask_eq, ← mask_eq,
    ← Nat.one_shiftLeft, ← Nat.one_shiftLeft, ← Nat.one_shiftLeft]
  rfl

/-- The loop over the rows, started at row `i` with `cnt = n - i` rows left. The flag is not
described. -/
theorem phiGo_eq (P : Params) (pt : Pt) (n rows : ℕ) : ∀ (cnt i php phn : ℕ) (ok : Bool), i + cnt = n →
    ∃ b, phiGo P pt n cnt (rows / 2 ^ (P.w * triOff n i)) i php phn ok =
      (php + ∑ r ∈ range cnt, ∑ s ∈ range (n - (i + r)),
          triEnt P.w n rows (i + r) s * 2 ^ (P.W * ((i + r) * pt.pu) + (i + r + s) * (P.W * pt.pv)),
       phn + ∑ r ∈ range cnt, ∑ s ∈ range (n - (i + r)),
          2 ^ (P.a - 1) * 2 ^ (P.W * ((i + r) * pt.pu) + (i + r + s) * (P.W * pt.pv)),
       b)
  | 0, i, php, phn, ok, _ => ⟨ok && Nat.beq (rows / 2 ^ (P.w * triOff n i)) 0, by simp [phiGo_zero]⟩
  | cnt + 1, i, php, phn, ok, h => by
    have h0 := phiGo_succ P pt n cnt (rows / 2 ^ (P.w * triOff n i)) i php phn ok
    have hrow : rows / 2 ^ (P.w * triOff n i) % 2 ^ (P.w * (n - i)) = packSum P.w (n - i) (triEnt P.w n rows i) :=
      triRow_eq P.w n rows i
    rw [h0, triRow_rest, hrow, phiRow_eq P.w _ _ (n - i) _ _ _ _ (fun s _ => triEnt_lt P.w n rows i s)]
    obtain ⟨b, hb⟩ := phiGo_eq P pt n rows cnt (i + 1) _ _ _ (by omega)
    refine ⟨b, ?_⟩
    rw [hb, sum_range_succ', sum_range_succ']
    have e1 : ∀ r, i + 1 + r = i + (r + 1) := fun r => by ring
    have e2 : ∀ s, P.W * (i * (pt.pu + pt.pv)) + s * (P.W * pt.pv)
        = P.W * (i * pt.pu) + (i + s) * (P.W * pt.pv) := fun s => by ring
    simp only [e1, e2, add_zero]
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp only <;> ring

/-- `phiEval` computes the values of the two parts of `phiP`. The flag is not described. -/
theorem phiEval_eq (P : Params) (pt : Pt) (n rows : ℕ) :
    ∃ b, phiEval P pt n rows = (ev P pt (phiP P n rows).1, ev P pt (phiP P n rows).2, b) := by
  have h0 : rows / 2 ^ (P.w * triOff n 0) = rows := by
    rw [triOff_zero, mul_zero, pow_zero, Nat.div_one]
  obtain ⟨b, hb⟩ := phiGo_eq P pt n rows n 0 0 0 true (zero_add n)
  rw [h0] at hb
  simp only [zero_add] at hb
  refine ⟨b, ?_⟩
  show phiGo P pt n n rows 0 0 0 true = _
  rw [hb]
  simp only [phiP, map_sum, ev_C_uv]

/-! ## The sum over the moment blocks -/

/-- The pair of `∑ φₖ * Qₖ` over the blocks listed in `l`, where the first block has the index
`k` and the order `D + 1 - k`. -/
noncomputable def momentFrom (P : Params) : List ℕ → ℕ → Poly × Poly
  | [], _ => (0, 0)
  | rows :: l, k => pmul (phiP P (P.D + 1 - k) rows) (qP P k) + momentFrom P l (k + 1)

/-- The pair of `∑ₖ φₖ * Qₖ`. -/
noncomputable def momentP (P : Params) (mrows : List ℕ) : Poly × Poly := momentFrom P mrows 0

theorem momentGo_nil (P : Params) (pt : Pt) (k : ℕ) (cur prev : ℕ × ℕ) (Mp Mn : ℕ) (ok : Bool) :
    momentGo P pt [] k cur prev Mp Mn ok = (Mp, Mn, ok && Nat.beq k (Nat.succ P.D)) := rfl

theorem momentGo_cons (P : Params) (pt : Pt) (rows : ℕ) (l : List ℕ) (k : ℕ) (cur prev : ℕ × ℕ)
    (Mp Mn : ℕ) (ok : Bool) :
    momentGo P pt (rows :: l) k cur prev Mp Mn ok =
      momentGo P pt l (k + 1)
        (Bool.rec (motive := fun _ => ℕ × ℕ) (qNext P pt cur prev) (mulTerms P pt 2 (tuv P) 1 0 0 0)
          (Nat.beq k 0))
        cur
        (Mp + ((phiEval P pt (P.D + 1 - k) rows).1 * cur.1 + (phiEval P pt (P.D + 1 - k) rows).2.1 * cur.2))
        (Mn + ((phiEval P pt (P.D + 1 - k) rows).1 * cur.2 + (phiEval P pt (P.D + 1 - k) rows).2.1 * cur.1))
        (ok && (phiEval P pt (P.D + 1 - k) rows).2.2) := rfl

/-- The loop over the moment blocks. The flag is not described. -/
theorem momentGo_eq (P : Params) (pt : Pt) : ∀ (l : List ℕ) (k : ℕ) (cur prev : ℕ × ℕ) (Mp Mn : ℕ)
    (ok : Bool), cur = evp P pt (qP P k) → (∀ j, k = j + 1 → prev = evp P pt (qP P j)) →
    ∃ b, momentGo P pt l k cur prev Mp Mn ok =
      (Mp + ev P pt (momentFrom P l k).1, Mn + ev P pt (momentFrom P l k).2, b)
  | [], k, cur, prev, Mp, Mn, ok, _, _ =>
    ⟨ok && Nat.beq k (Nat.succ P.D), by simp [momentGo_nil, momentFrom]⟩
  | rows :: l, k, cur, prev, Mp, Mn, ok, hcur, hprev => by
    rw [momentGo_cons]
    obtain ⟨bφ, hφ⟩ := phiEval_eq P pt (P.D + 1 - k) rows
    have hnext : (Bool.rec (motive := fun _ => ℕ × ℕ) (qNext P pt cur prev)
        (mulTerms P pt 2 (tuv P) 1 0 0 0) (Nat.beq k 0)) = evp P pt (qP P (k + 1)) := by
      rcases k with _ | j
      · exact q_one_evp P pt
      · show qNext P pt cur prev = _
        rw [hcur, hprev j rfl, qNext_evp]
        rfl
    obtain ⟨b, hb⟩ := momentGo_eq P pt l (k + 1) _ cur _ _ (ok && (phiEval P pt (P.D + 1 - k) rows).2.2)
      hnext (fun j hj => by
        have : j = k := by omega
        rw [this, hcur])
    refine ⟨b, ?_⟩
    rw [hb, hφ, hcur]
    simp only [momentFrom, evp, pmul, Prod.fst_add, Prod.snd_add, map_add, map_mul]
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp only <;> ring

/-- `moment` computes the values of the two parts of `momentP`. The flag is not described. -/
theorem moment_eq (P : Params) (pt : Pt) (mrows : List ℕ) :
    ∃ b, moment P pt mrows = (ev P pt (momentP P mrows).1, ev P pt (momentP P mrows).2, b) := by
  obtain ⟨b, hb⟩ := momentGo_eq P pt mrows 0 (1, 0) (0, 0) 0 0 true
    (by simp [evp, qP]) (fun j hj => absurd hj (by omega))
  refine ⟨b, ?_⟩
  show momentGo P pt mrows 0 (1, 0) (0, 0) 0 0 true = _
  rw [hb]
  simp [momentP]

end CAP.ThreePoint
