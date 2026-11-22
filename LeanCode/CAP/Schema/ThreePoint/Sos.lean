module

public import CAP.Schema.ThreePoint.Moment

/-!
# Schema S2, soundness: the blocks with a sum of squares

For a block `B` with the basis `z`, the weight `g` and the matrix data `X`, the function
`sosBlock` of the checker computes, at an arbitrary point, the values of the pair

  `sosP P B = g * ∑ᵢ zᵢ * rᵢ`,   `rᵢ = ∑_{j ≥ i} X i j • zⱼ`,

together with a flag and a bound, neither of which depends on the point (`sosBlock_eq`). The basis
elements are the polynomials `polyOf P B.T F`, where `F` runs through the term fields
`basisFields P B B.n B.basis`. The pair of `rᵢ` is `rowPair`: its positive part contains the slots
of row `i` as coefficients, and the bias `2 ^ (a - 1)` is moved to the other part by means of the
sums of the basis elements. `sosAll` adds the blocks with their factors (`sosAll_eq`).
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-! ## The basis -/

/-- The width of the term fields of one basis element. -/
def bw (P : Params) (B : Sos) : ℕ := fw P * B.T

/-- The term fields of the next `cnt` basis elements in `tf`. -/
def basisFields (P : Params) (B : Sos) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | cnt + 1, tf => tf % 2 ^ bw P B :: basisFields P B cnt (tf / 2 ^ bw P B)

theorem basisFields_length (P : Params) (B : Sos) : ∀ (cnt tf : ℕ), (basisFields P B cnt tf).length = cnt
  | 0, _ => rfl
  | cnt + 1, tf => by rw [basisFields, List.length_cons, basisFields_length P B cnt]

/-- The entry of the checker for the basis element with the term fields `F`. -/
noncomputable def eltOf (P : Params) (pt : Pt) (B : Sos) (F : ℕ) : Elt :=
  (ev P pt (polyOf P B.T F).1, ev P pt (polyOf P B.T F).2, F, coefSum P B.T F, degOk P B.dz B.T F)

theorem basisGo_eq (P : Params) (pt : Pt) (B : Sos) : ∀ (cnt tf : ℕ),
    basisGo P pt B cnt tf = (basisFields P B cnt tf).map (eltOf P pt B)
  | 0, _ => rfl
  | cnt + 1, tf => by
    have h : basisGo P pt B (cnt + 1) tf =
        ((polyEval P pt B.dz B.T (tf % 2 ^ bw P B) 0 0 0 true).1,
          (polyEval P pt B.dz B.T (tf % 2 ^ bw P B) 0 0 0 true).2.1, tf % 2 ^ bw P B,
          (polyEval P pt B.dz B.T (tf % 2 ^ bw P B) 0 0 0 true).2.2.1,
          (polyEval P pt B.dz B.T (tf % 2 ^ bw P B) 0 0 0 true).2.2.2)
          :: basisGo P pt B cnt (tf / 2 ^ bw P B) := by
      rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow, ← mask_eq]
      rfl
    rw [h, basisGo_eq P pt B cnt, polyEval_eq]
    simp [basisFields, eltOf]

/-- The sum of the pairs of the basis elements with the term fields in `l`. -/
noncomputable def sumP (P : Params) (B : Sos) : List ℕ → Poly × Poly
  | [] => (0, 0)
  | F :: l => polyOf P B.T F + sumP P B l

theorem hd_cons (x : ℕ × ℕ) (l : List (ℕ × ℕ)) : hd (x :: l) = x := rfl

theorem sufGo_cons (b : Elt) (l : List Elt) :
    sufGo (b :: l) = (b.1 + (hd (sufGo l)).1, b.2.1 + (hd (sufGo l)).2) :: sufGo l := rfl

theorem tl_sufGo_cons (b : Elt) (l : List Elt) : tl (sufGo (b :: l)) = sufGo l := rfl

/-- The first suffix sum is the sum of all listed basis elements. -/
theorem hd_sufGo (P : Params) (pt : Pt) (B : Sos) : ∀ l : List ℕ,
    hd (sufGo (l.map (eltOf P pt B))) = evp P pt (sumP P B l)
  | [] => by
    show ((0 : ℕ), (0 : ℕ)) = _
    simp [sumP, evp]
  | F :: l => by
    rw [List.map_cons, sufGo_cons, hd_cons, hd_sufGo P pt B l]
    simp [eltOf, evp, sumP]

/-! ## One row -/

theorem rowAcc_nil (w mw rho rp rn : ℕ) : rowAcc w mw [] rho rp rn = (rp, rn) := rfl

theorem rowAcc_cons (w : ℕ) (b : Elt) (l : List Elt) (rho rp rn : ℕ) :
    rowAcc w (2 ^ w - 1) (b :: l) rho rp rn =
      rowAcc w (2 ^ w - 1) l (rho / 2 ^ w) (rp + rho % 2 ^ w * b.1) (rn + rho % 2 ^ w * b.2.1) := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  rfl

/-- The pair of `∑ⱼ ξ j • zⱼ` for the basis elements with the term fields in `l`. -/
noncomputable def rowP (P : Params) (B : Sos) : List ℕ → (ℕ → ℕ) → Poly × Poly
  | [], _ => (0, 0)
  | F :: l, ξ => (C (ξ 0) * (polyOf P B.T F).1, C (ξ 0) * (polyOf P B.T F).2)
      + rowP P B l (fun j => ξ (j + 1))

theorem rowAcc_eq (P : Params) (pt : Pt) (B : Sos) : ∀ (l : List ℕ) (ξ : ℕ → ℕ) (rp rn : ℕ),
    (∀ j, j < l.length → ξ j < 2 ^ P.w) →
    rowAcc P.w (2 ^ P.w - 1) (l.map (eltOf P pt B)) (packSum P.w l.length ξ) rp rn =
      (rp + ev P pt (rowP P B l ξ).1, rn + ev P pt (rowP P B l ξ).2)
  | [], ξ, rp, rn, _ => by simp [rowAcc_nil, rowP]
  | F :: l, ξ, rp, rn, h => by
    have h0 : ξ 0 < 2 ^ P.w := h 0 (by simp)
    rw [List.map_cons, rowAcc_cons, List.length_cons, packSum_succ_mod _ _ _ h0,
      packSum_succ_div _ _ _ h0,
      rowAcc_eq P pt B l _ _ _ (fun j hj => h (j + 1) (by simpa using hj))]
    simp only [rowP, eltOf, Prod.fst_add, Prod.snd_add, map_add, map_mul, ev_C]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-! ## The loop over the rows -/

theorem sosGo_nil (P : Params) (pt : Pt) (B : Sos) (suf : List (ℕ × ℕ)) (R i Qp Qn : ℕ) (ok : Bool) :
    sosGo P pt B [] suf R i Qp Qn ok = (Qp, Qn, ok && Nat.beq R 0) := rfl

theorem sosGo_cons (P : Params) (pt : Pt) (B : Sos) (b : Elt) (rest : List Elt) (suf : List (ℕ × ℕ))
    (R i Qp Qn : ℕ) (ok : Bool) :
    sosGo P pt B (b :: rest) suf R i Qp Qn ok =
      sosGo P pt B rest (tl suf) (R / 2 ^ (P.w * (B.n - i))) (i + 1)
        (mulTerms P pt B.T b.2.2.1
          (rowAcc P.w (2 ^ P.w - 1) (b :: rest) (R % 2 ^ (P.w * (B.n - i)))
            (2 ^ (P.a - 1) * (hd suf).2) (2 ^ (P.a - 1) * (hd suf).1)).1
          (rowAcc P.w (2 ^ P.w - 1) (b :: rest) (R % 2 ^ (P.w * (B.n - i)))
            (2 ^ (P.a - 1) * (hd suf).2) (2 ^ (P.a - 1) * (hd suf).1)).2 Qp Qn).1
        (mulTerms P pt B.T b.2.2.1
          (rowAcc P.w (2 ^ P.w - 1) (b :: rest) (R % 2 ^ (P.w * (B.n - i)))
            (2 ^ (P.a - 1) * (hd suf).2) (2 ^ (P.a - 1) * (hd suf).1)).1
          (rowAcc P.w (2 ^ P.w - 1) (b :: rest) (R % 2 ^ (P.w * (B.n - i)))
            (2 ^ (P.a - 1) * (hd suf).2) (2 ^ (P.a - 1) * (hd suf).1)).2 Qp Qn).2
        (ok && Nat.beq (R % 2 ^ (P.w * (B.n - i)) &&& (2 ^ P.w - 2 ^ P.a) * ones P.w (B.n - i)) 0) := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow, ← mask_eq, ← mask_eq,
    ← Nat.one_shiftLeft, ← Nat.one_shiftLeft, ← Nat.one_shiftLeft]
  rfl

/-- The pair of `rᵢ = ∑_{j ≥ i} X i j • zⱼ`, where `l` lists the term fields of the basis elements
`zᵢ, zᵢ₊₁, …`. -/
noncomputable def rowPair (P : Params) (B : Sos) (l : List ℕ) (i : ℕ) : Poly × Poly :=
  (C (2 ^ (P.a - 1)) * (sumP P B l).2 + (rowP P B l (triEnt P.w B.n B.rows i)).1,
   C (2 ^ (P.a - 1)) * (sumP P B l).1 + (rowP P B l (triEnt P.w B.n B.rows i)).2)

/-- The pair of `∑_{i' ≥ i} zᵢ' * rᵢ'`, where `l` lists the term fields of `zᵢ, zᵢ₊₁, …`. -/
noncomputable def sosFrom (P : Params) (B : Sos) : List ℕ → ℕ → Poly × Poly
  | [], _ => (0, 0)
  | F :: l, i => pmul (polyOf P B.T F) (rowPair P B (F :: l) i) + sosFrom P B l (i + 1)

/-- The flag of the matrix data: the slots of the rows `i, …, i + cnt - 1` are below `2 ^ a`,
and no data follow. -/
def sosFlags (P : Params) (B : Sos) : ℕ → ℕ → Bool
  | 0, i => Nat.beq (B.rows / 2 ^ (P.w * triOff B.n i)) 0
  | cnt + 1, i =>
    Nat.beq (triRow P.w B.n B.rows i &&& (2 ^ P.w - 2 ^ P.a) * ones P.w (B.n - i)) 0
      && sosFlags P B cnt (i + 1)

theorem sosGo_eq (P : Params) (pt : Pt) (B : Sos) : ∀ (l : List ℕ) (i Qp Qn : ℕ) (ok : Bool),
    i + l.length = B.n →
    sosGo P pt B (l.map (eltOf P pt B)) (sufGo (l.map (eltOf P pt B)))
        (B.rows / 2 ^ (P.w * triOff B.n i)) i Qp Qn ok =
      (Qp + ev P pt (sosFrom P B l i).1, Qn + ev P pt (sosFrom P B l i).2,
        ok && sosFlags P B l.length i)
  | [], i, Qp, Qn, ok, _ => by simp [sosGo_nil, sosFrom, sosFlags]
  | F :: l, i, Qp, Qn, ok, h => by
    have hlen : B.n - i = l.length + 1 := by
      rw [List.length_cons] at h
      omega
    -- the first suffix sum, the row and its accumulation
    have hs : hd (sufGo (eltOf P pt B F :: l.map (eltOf P pt B))) = evp P pt (sumP P B (F :: l)) :=
      hd_sufGo P pt B (F :: l)
    have hrow : B.rows / 2 ^ (P.w * triOff B.n i) % 2 ^ (P.w * (B.n - i))
        = packSum P.w (F :: l).length (triEnt P.w B.n B.rows i) := by
      rw [List.length_cons, ← hlen]
      exact triRow_eq P.w B.n B.rows i
    have hacc := rowAcc_eq P pt B (F :: l) (triEnt P.w B.n B.rows i)
      (2 ^ (P.a - 1) * ev P pt (sumP P B (F :: l)).2) (2 ^ (P.a - 1) * ev P pt (sumP P B (F :: l)).1)
      (fun j _ => triEnt_lt P.w B.n B.rows i j)
    rw [List.map_cons] at hacc
    have hr : rowAcc P.w (2 ^ P.w - 1) (eltOf P pt B F :: l.map (eltOf P pt B))
        (B.rows / 2 ^ (P.w * triOff B.n i) % 2 ^ (P.w * (B.n - i)))
        (2 ^ (P.a - 1) * (hd (sufGo (eltOf P pt B F :: l.map (eltOf P pt B)))).2)
        (2 ^ (P.a - 1) * (hd (sufGo (eltOf P pt B F :: l.map (eltOf P pt B)))).1)
        = evp P pt (rowPair P B (F :: l) i) := by
      rw [hs, hrow]
      show rowAcc P.w (2 ^ P.w - 1) (eltOf P pt B F :: l.map (eltOf P pt B))
        (packSum P.w (F :: l).length (triEnt P.w B.n B.rows i))
        (2 ^ (P.a - 1) * ev P pt (sumP P B (F :: l)).2) (2 ^ (P.a - 1) * ev P pt (sumP P B (F :: l)).1) = _
      rw [hacc]
      simp only [evp, rowPair, map_add, map_mul, ev_C]
    have hflag : Nat.beq (B.rows / 2 ^ (P.w * triOff B.n i) % 2 ^ (P.w * (B.n - i))
        &&& (2 ^ P.w - 2 ^ P.a) * ones P.w (B.n - i)) 0
        = Nat.beq (triRow P.w B.n B.rows i &&& (2 ^ P.w - 2 ^ P.a) * ones P.w (B.n - i)) 0 := rfl
    rw [List.map_cons, sosGo_cons, tl_sufGo_cons, hr, triRow_rest, hflag]
    show sosGo P pt B (l.map (eltOf P pt B)) (sufGo (l.map (eltOf P pt B)))
      (B.rows / 2 ^ (P.w * triOff B.n (i + 1))) (i + 1)
      (mulTerms P pt B.T F (ev P pt (rowPair P B (F :: l) i).1) (ev P pt (rowPair P B (F :: l) i).2) Qp Qn).1
      (mulTerms P pt B.T F (ev P pt (rowPair P B (F :: l) i).1) (ev P pt (rowPair P B (F :: l) i).2) Qp Qn).2
      (ok && Nat.beq (triRow P.w B.n B.rows i &&& (2 ^ P.w - 2 ^ P.a) * ones P.w (B.n - i)) 0) = _
    rw [sosGo_eq P pt B l (i + 1) _ _ _ (by rw [List.length_cons] at h; omega), mulTerms_eq]
    simp only [sosFrom, sosFlags, pmul, List.length_cons, Prod.fst_add, Prod.snd_add, map_add, map_mul,
      Bool.and_assoc]
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp only <;> ring

/-! ## A block -/

/-- The pair of `g * ∑ᵢ zᵢ * rᵢ` for the block `B`. -/
noncomputable def sosP (P : Params) (B : Sos) : Poly × Poly :=
  pmul (polyOf P B.gT B.weight) (sosFrom P B (basisFields P B B.n B.basis) 0)

/-- Every basis element has degree at most `dz` and sum of coefficients at most `cmax`. -/
def basisFlag (P : Params) (B : Sos) : List ℕ → Bool
  | [] => true
  | F :: l => degOk P B.dz B.T F && Nat.ble (coefSum P B.T F) B.cmax && basisFlag P B l

theorem basisOk_eq (P : Params) (pt : Pt) (B : Sos) : ∀ l : List ℕ,
    basisOk B.cmax (l.map (eltOf P pt B)) = basisFlag P B l
  | [] => rfl
  | F :: l => by
    show (degOk P B.dz B.T F && Nat.ble (coefSum P B.T F) B.cmax
      && basisOk B.cmax (l.map (eltOf P pt B))) = _
    rw [basisOk_eq P pt B l]
    rfl

/-- The flag of a block. It does not depend on the point. -/
def blockFlag (P : Params) (B : Sos) : Bool :=
  sosFlags P B B.n 0 && basisFlag P B (basisFields P B B.n B.basis) && degOk P B.gdeg B.gT B.weight &&
    Nat.ble (2 * B.dz + B.gdeg) (2 * P.D) && Nat.beq (B.basis / 2 ^ (bw P B * B.n)) 0

/-- The bound of a block for the sum of the coefficients. It does not depend on the point. -/
def blockBound (P : Params) (B : Sos) : ℕ :=
  B.f * coefSum P B.gT B.weight * (B.cmax * B.cmax) * B.n * B.n * 2 ^ (P.a + 1)

theorem sosBlock_eq (P : Params) (pt : Pt) (B : Sos) :
    sosBlock P pt B = (ev P pt (sosP P B).1, ev P pt (sosP P B).2, blockFlag P B, blockBound P B) := by
  have hlen := basisFields_length P B B.n B.basis
  have hQ : sosGo P pt B (basisGo P pt B B.n B.basis) (sufGo (basisGo P pt B B.n B.basis)) B.rows 0 0 0 true
      = (ev P pt (sosFrom P B (basisFields P B B.n B.basis) 0).1,
        ev P pt (sosFrom P B (basisFields P B B.n B.basis) 0).2, sosFlags P B B.n 0) := by
    have h := sosGo_eq P pt B (basisFields P B B.n B.basis) 0 0 0 true (by rw [hlen, zero_add])
    rw [triOff_zero, mul_zero, pow_zero, Nat.div_one, hlen] at h
    rw [basisGo_eq, h]
    simp
  have hraw : sosBlock P pt B =
      ((mulTerms P pt B.gT B.weight
          (sosGo P pt B (basisGo P pt B B.n B.basis) (sufGo (basisGo P pt B B.n B.basis)) B.rows 0 0 0 true).1
          (sosGo P pt B (basisGo P pt B B.n B.basis) (sufGo (basisGo P pt B B.n B.basis)) B.rows 0 0 0 true).2.1
          0 0).1,
        (mulTerms P pt B.gT B.weight
          (sosGo P pt B (basisGo P pt B B.n B.basis) (sufGo (basisGo P pt B B.n B.basis)) B.rows 0 0 0 true).1
          (sosGo P pt B (basisGo P pt B B.n B.basis) (sufGo (basisGo P pt B B.n B.basis)) B.rows 0 0 0 true).2.1
          0 0).2,
        (sosGo P pt B (basisGo P pt B B.n B.basis) (sufGo (basisGo P pt B B.n B.basis)) B.rows 0 0 0 true).2.2
          && basisOk B.cmax (basisGo P pt B B.n B.basis)
          && (polyEval P pt B.gdeg B.gT B.weight 0 0 0 true).2.2.2
          && Nat.ble (2 * B.dz + B.gdeg) (2 * P.D)
          && Nat.beq (B.basis / 2 ^ (bw P B * B.n)) 0,
        B.f * (polyEval P pt B.gdeg B.gT B.weight 0 0 0 true).2.2.1 * (B.cmax * B.cmax) * B.n * B.n
          * 2 ^ (P.a + 1)) := by
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq]
    rfl
  rw [hraw, hQ, mulTerms_eq, polyEval_eq, basisGo_eq, basisOk_eq]
  simp only [sosP, pmul, blockFlag, blockBound, zero_add, Bool.true_and, map_add, map_mul]

/-! ## The sum over the blocks -/

/-- The pair of `∑_B f_B * G_B`. -/
noncomputable def sosSum (P : Params) : List Sos → Poly × Poly
  | [] => (0, 0)
  | B :: l => (C B.f * (sosP P B).1, C B.f * (sosP P B).2) + sosSum P l

/-- The sum of the bounds of the blocks. -/
def boundSum (P : Params) : List Sos → ℕ
  | [] => 0
  | B :: l => blockBound P B + boundSum P l

/-- The flags of all blocks. -/
def flagAll (P : Params) : List Sos → Bool
  | [] => true
  | B :: l => blockFlag P B && flagAll P l

theorem sosAll_nil (P : Params) (pt : Pt) (Qp Qn bd : ℕ) (ok : Bool) :
    sosAll P pt [] Qp Qn bd ok = (Qp, Qn, bd, ok) := rfl

theorem sosAll_cons (P : Params) (pt : Pt) (B : Sos) (l : List Sos) (Qp Qn bd : ℕ) (ok : Bool) :
    sosAll P pt (B :: l) Qp Qn bd ok =
      sosAll P pt l (Qp + B.f * (sosBlock P pt B).1) (Qn + B.f * (sosBlock P pt B).2.1)
        (bd + (sosBlock P pt B).2.2.2) (ok && (sosBlock P pt B).2.2.1) := rfl

theorem sosAll_eq (P : Params) (pt : Pt) : ∀ (l : List Sos) (Qp Qn bd : ℕ) (ok : Bool),
    sosAll P pt l Qp Qn bd ok =
      (Qp + ev P pt (sosSum P l).1, Qn + ev P pt (sosSum P l).2, bd + boundSum P l, ok && flagAll P l)
  | [], Qp, Qn, bd, ok => by simp [sosAll_nil, sosSum, boundSum, flagAll]
  | B :: l, Qp, Qn, bd, ok => by
    rw [sosAll_cons, sosBlock_eq, sosAll_eq P pt l]
    simp only [sosSum, boundSum, flagAll, Prod.fst_add, Prod.snd_add, map_add, map_mul, ev_C, add_assoc,
      Bool.and_assoc]

end CAP.ThreePoint
