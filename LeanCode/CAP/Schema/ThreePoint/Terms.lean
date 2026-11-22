module

public import CAP.Core.Kronecker
public import CAP.Schema.ThreePoint.Kernel

/-!
# Schema S2, soundness: terms and polynomials given by term fields

The checker represents a polynomial with integer coefficients by a pair of natural numbers, the
values of its positive and of its negative part at a point `(X ^ pu, X ^ pv, X ^ pt)`, `X = 2 ^ W`.
Here the same polynomials are pairs of polynomials with natural coefficients, and the functions
of the checker are their values:

* `polyEval` computes the values of `polyOf`, the sum of the coefficients and the degree flag
  (`polyEval_eq`);
* `mulTerms` adds the product with `polyOf` (`mulTerms_eq`).
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial

/-- Polynomials in `u`, `v`, `t` with natural coefficients. -/
abbrev Poly := MvPolynomial (Fin 3) ℕ

/-- The point `(X ^ pu, X ^ pv, X ^ pt)` with `X = 2 ^ W`. -/
def pval (P : Params) (pt : Pt) : Fin 3 → ℕ :=
  ![2 ^ (P.W * pt.pu), 2 ^ (P.W * pt.pv), 2 ^ (P.W * pt.pt)]

/-- Evaluation at a point. -/
noncomputable def ev (P : Params) (pt : Pt) : Poly →+* ℕ := eval (pval P pt)

theorem ev_C (P : Params) (pt : Pt) (k : ℕ) : ev P pt (C k) = k := eval_C k

/-! ## Term fields -/

theorem fw_eq (P : Params) : fw P = 3 * P.eb + P.cb + 1 := rfl

theorem fld_eq (P : Params) (tf : ℕ) : fld P tf = tf % 2 ^ fw P := by
  show tf &&& mask (fw P) = _
  rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem tPos_eq (P : Params) (pt : Pt) (f : ℕ) :
    tPos P pt f = P.W * (tExp P f 0 * pt.pu + tExp P f 1 * pt.pv + tExp P f 2 * pt.pt) := rfl

theorem tDeg_eq (P : Params) (f : ℕ) : tDeg P f = tExp P f 0 + tExp P f 1 + tExp P f 2 := rfl

/-- The monomial of a term field. -/
noncomputable def tMono (P : Params) (f : ℕ) : Poly :=
  X 0 ^ tExp P f 0 * X 1 ^ tExp P f 1 * X 2 ^ tExp P f 2

theorem ev_tMono (P : Params) (pt : Pt) (f : ℕ) : ev P pt (tMono P f) = 2 ^ tPos P pt f := by
  unfold ev tMono
  simp only [map_mul, map_pow, eval_X]
  show (2 ^ (P.W * pt.pu)) ^ tExp P f 0 * (2 ^ (P.W * pt.pv)) ^ tExp P f 1
      * (2 ^ (P.W * pt.pt)) ^ tExp P f 2 = _
  rw [tPos_eq, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

/-- The pair (positive part, negative part) of the term `± coef * monomial` of a term field. -/
noncomputable def tPair (P : Params) (f : ℕ) : Poly × Poly :=
  if tNeg P f = true then (0, C (tCoef P f) * tMono P f) else (C (tCoef P f) * tMono P f, 0)

/-- The pair of the polynomial with the `T` term fields `tf`. -/
noncomputable def polyOf (P : Params) : ℕ → ℕ → Poly × Poly
  | 0, _ => (0, 0)
  | T + 1, tf => tPair P (fld P tf) + polyOf P T (tf / 2 ^ fw P)

/-- The sum of the coefficients of the `T` term fields `tf`. -/
def coefSum (P : Params) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | T + 1, tf => tCoef P (fld P tf) + coefSum P T (tf / 2 ^ fw P)

/-- All of the `T` term fields `tf` have degree at most `dz`. -/
def degOk (P : Params) (dz : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | T + 1, tf => Nat.ble (tDeg P (fld P tf)) dz && degOk P dz T (tf / 2 ^ fw P)

theorem polyOf_succ_pos (P : Params) (T tf : ℕ) (h : tNeg P (fld P tf) = false) :
    polyOf P (T + 1) tf = (C (tCoef P (fld P tf)) * tMono P (fld P tf) + (polyOf P T (tf / 2 ^ fw P)).1,
      (polyOf P T (tf / 2 ^ fw P)).2) := by
  rw [polyOf, tPair, h]
  exact Prod.ext (by simp) (by simp)

theorem polyOf_succ_neg (P : Params) (T tf : ℕ) (h : tNeg P (fld P tf) = true) :
    polyOf P (T + 1) tf = ((polyOf P T (tf / 2 ^ fw P)).1,
      C (tCoef P (fld P tf)) * tMono P (fld P tf) + (polyOf P T (tf / 2 ^ fw P)).2) := by
  rw [polyOf, tPair, h]
  exact Prod.ext (by simp) (by simp)

/-! ## `polyEval` -/

theorem polyEval_zero (P : Params) (pt : Pt) (dz tf p n nm : ℕ) (ok : Bool) :
    polyEval P pt dz 0 tf p n nm ok = (p, n, nm, ok) := rfl

theorem polyEval_succ (P : Params) (pt : Pt) (dz T tf p n nm : ℕ) (ok : Bool) :
    polyEval P pt dz (T + 1) tf p n nm ok =
      Bool.rec (motive := fun _ => ℕ × ℕ × ℕ × Bool)
        (polyEval P pt dz T (tf / 2 ^ fw P) (p + tCoef P (fld P tf) * 2 ^ tPos P pt (fld P tf)) n
          (nm + tCoef P (fld P tf)) (ok && Nat.ble (tDeg P (fld P tf)) dz))
        (polyEval P pt dz T (tf / 2 ^ fw P) p (n + tCoef P (fld P tf) * 2 ^ tPos P pt (fld P tf))
          (nm + tCoef P (fld P tf)) (ok && Nat.ble (tDeg P (fld P tf)) dz))
        (tNeg P (fld P tf)) := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq]
  rfl

/-- `polyEval` computes the values of the two parts of `polyOf`, the sum of the coefficients and
the degree flag. -/
theorem polyEval_eq (P : Params) (pt : Pt) (dz : ℕ) : ∀ (T tf p n nm : ℕ) (ok : Bool),
    polyEval P pt dz T tf p n nm ok =
      (p + ev P pt (polyOf P T tf).1, n + ev P pt (polyOf P T tf).2, nm + coefSum P T tf,
        ok && degOk P dz T tf)
  | 0, tf, p, n, nm, ok => by
    simp [polyEval_zero, polyOf, coefSum, degOk]
  | T + 1, tf, p, n, nm, ok => by
    rw [polyEval_succ]
    cases h : tNeg P (fld P tf) with
    | false =>
      show polyEval P pt dz T (tf / 2 ^ fw P) (p + tCoef P (fld P tf) * 2 ^ tPos P pt (fld P tf)) n
        (nm + tCoef P (fld P tf)) (ok && Nat.ble (tDeg P (fld P tf)) dz) = _
      rw [polyEval_eq P pt dz T, polyOf_succ_pos P T tf h]
      simp only [map_add, map_mul, ev_C, ev_tMono, coefSum, degOk, add_assoc, Bool.and_assoc]
    | true =>
      show polyEval P pt dz T (tf / 2 ^ fw P) p (n + tCoef P (fld P tf) * 2 ^ tPos P pt (fld P tf))
        (nm + tCoef P (fld P tf)) (ok && Nat.ble (tDeg P (fld P tf)) dz) = _
      rw [polyEval_eq P pt dz T, polyOf_succ_neg P T tf h]
      simp only [map_add, map_mul, ev_C, ev_tMono, coefSum, degOk, add_assoc, Bool.and_assoc]

/-! ## `mulTerms` -/

theorem mulTerms_zero (P : Params) (pt : Pt) (tf xp xn yp yn : ℕ) :
    mulTerms P pt 0 tf xp xn yp yn = (yp, yn) := rfl

theorem mulTerms_succ (P : Params) (pt : Pt) (T tf xp xn yp yn : ℕ) :
    mulTerms P pt (T + 1) tf xp xn yp yn =
      Bool.rec (motive := fun _ => ℕ × ℕ)
        (Bool.rec (motive := fun _ => ℕ × ℕ)
          (mulTerms P pt T (tf / 2 ^ fw P) xp xn
            (yp + tCoef P (fld P tf) * (xp * 2 ^ tPos P pt (fld P tf)))
            (yn + tCoef P (fld P tf) * (xn * 2 ^ tPos P pt (fld P tf))))
          (mulTerms P pt T (tf / 2 ^ fw P) xp xn
            (yp + tCoef P (fld P tf) * (xn * 2 ^ tPos P pt (fld P tf)))
            (yn + tCoef P (fld P tf) * (xp * 2 ^ tPos P pt (fld P tf))))
          (tNeg P (fld P tf)))
        (mulTerms P pt T (tf / 2 ^ fw P) xp xn yp yn)
        (Nat.beq (tCoef P (fld P tf)) 0) := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]
  rfl

/-- `mulTerms` adds the product of the pair `(xp, xn)` with the pair of `polyOf`. -/
theorem mulTerms_eq (P : Params) (pt : Pt) : ∀ (T tf xp xn yp yn : ℕ),
    mulTerms P pt T tf xp xn yp yn =
      (yp + (ev P pt (polyOf P T tf).1 * xp + ev P pt (polyOf P T tf).2 * xn),
       yn + (ev P pt (polyOf P T tf).1 * xn + ev P pt (polyOf P T tf).2 * xp))
  | 0, tf, xp, xn, yp, yn => by
    simp [mulTerms_zero, polyOf]
  | T + 1, tf, xp, xn, yp, yn => by
    rw [mulTerms_succ]
    cases hz : Nat.beq (tCoef P (fld P tf)) 0 with
    | true =>
      have hk : tCoef P (fld P tf) = 0 := Nat.eq_of_beq_eq_true hz
      show mulTerms P pt T (tf / 2 ^ fw P) xp xn yp yn = _
      rw [mulTerms_eq P pt T]
      cases h : tNeg P (fld P tf) with
      | false =>
        rw [polyOf_succ_pos P T tf h, hk]
        simp
      | true =>
        rw [polyOf_succ_neg P T tf h, hk]
        simp
    | false =>
      cases h : tNeg P (fld P tf) with
      | false =>
        show mulTerms P pt T (tf / 2 ^ fw P) xp xn
          (yp + tCoef P (fld P tf) * (xp * 2 ^ tPos P pt (fld P tf)))
          (yn + tCoef P (fld P tf) * (xn * 2 ^ tPos P pt (fld P tf))) = _
        rw [mulTerms_eq P pt T, polyOf_succ_pos P T tf h]
        simp only [map_add, map_mul, ev_C, ev_tMono]
        refine Prod.ext ?_ ?_ <;> simp only <;> ring
      | true =>
        show mulTerms P pt T (tf / 2 ^ fw P) xp xn
          (yp + tCoef P (fld P tf) * (xn * 2 ^ tPos P pt (fld P tf)))
          (yn + tCoef P (fld P tf) * (xp * 2 ^ tPos P pt (fld P tf))) = _
        rw [mulTerms_eq P pt T, polyOf_succ_neg P T tf h]
        simp only [map_add, map_mul, ev_C, ev_tMono]
        refine Prod.ext ?_ ?_ <;> simp only <;> ring

end CAP.ThreePoint
