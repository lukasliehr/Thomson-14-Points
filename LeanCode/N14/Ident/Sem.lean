module

public import CAP.Schema.ThreePoint.Semantics
public import N14.Ident.Kernel

/-!
# T7, the energy identity: the polynomials that the checker computes

The functions of `N14/Ident/Kernel.lean` compute values of polynomials in `u`, `v`, `t` with natural
coefficients at points `(X ^ a, X ^ b, X ^ c)`, as pairs (positive part, negative part). This file names these
polynomials, with the notions of `CAP.ThreePoint` (`Poly`, `ev`, `evp`, `pmul`):

* `phi00P`, `phi01P`: the parts of a block whose first basis function has the type `0` (`headGo_eq`, `head_eq`);
  the part with two basis functions of the type `1` is a block of `CAP.ThreePoint` (`phiP`) for the rest of the
  data;
* `partP`, `part_eq`: the part that `sel` selects;
* `kernP`, `kern_eq`: `∑ₖ φₖ * Qₖ`.

No bound on a coefficient is needed for these equations: evaluation at a point is a ring homomorphism.
-/

@[expose] public section

namespace N14.Ident

open CAP CAP.ThreePoint MvPolynomial Finset

/-- The low slots of a number as a packed sum. -/
theorem mod_packSum (w k x : ℕ) : x % 2 ^ (w * k) = packSum w k (slot w x) :=
  ((packSum_slot w k (x % 2 ^ (w * k)) (Nat.mod_lt _ (Nat.two_pow_pos _))).symm.trans
    (packSum_congr _ _ fun s hs => slot_mod w x k s hs))

theorem triOffK_eq (N : ℕ) : ∀ r, triOffK N r = triOff N r
  | 0 => by simp [triOffK, triOff_zero]
  | r + 1 => by
    rw [triOff_succ, ← triOffK_eq N r]
    rfl

/-! ## The head of a block -/

theorem headGo_zero (P : Params) (pt : Pt) (N n0 R i a b c d : ℕ) :
    headGo P pt N n0 0 R i a b c d = (a, b, c, d) := rfl

theorem headGo_succ' (P : Params) (pt : Pt) (N n0 cnt R i a b c d : ℕ) :
    headGo P pt N n0 (cnt + 1) R i a b c d =
      headGo P pt N n0 cnt (R >>> (P.w * (N - i))) (i + 1)
        (phiRow P.w (mask P.w) (1 <<< (P.a - 1)) (P.W * pt.pv) (n0 - i) (R &&& mask (P.w * (n0 - i)))
          (P.W * (i * (pt.pu + pt.pv))) a b).1
        (phiRow P.w (mask P.w) (1 <<< (P.a - 1)) (P.W * pt.pv) (n0 - i) (R &&& mask (P.w * (n0 - i)))
          (P.W * (i * (pt.pu + pt.pv))) a b).2
        (phiRow P.w (mask P.w) (1 <<< (P.a - 1)) (P.W * pt.pv) (N - n0)
          (R >>> (P.w * (n0 - i)) &&& mask (P.w * (N - n0))) (P.W * (i * pt.pu)) c d).1
        (phiRow P.w (mask P.w) (1 <<< (P.a - 1)) (P.W * pt.pv) (N - n0)
          (R >>> (P.w * (n0 - i)) &&& mask (P.w * (N - n0))) (P.W * (i * pt.pu)) c d).2 := rfl

theorem headGo_succ (P : Params) (pt : Pt) (N n0 cnt R i a b c d : ℕ) :
    headGo P pt N n0 (cnt + 1) R i a b c d =
      headGo P pt N n0 cnt (R / 2 ^ (P.w * (N - i))) (i + 1)
        (phiRow P.w (2 ^ P.w - 1) (2 ^ (P.a - 1)) (P.W * pt.pv) (n0 - i) (R % 2 ^ (P.w * (n0 - i)))
          (P.W * (i * (pt.pu + pt.pv))) a b).1
        (phiRow P.w (2 ^ P.w - 1) (2 ^ (P.a - 1)) (P.W * pt.pv) (n0 - i) (R % 2 ^ (P.w * (n0 - i)))
          (P.W * (i * (pt.pu + pt.pv))) a b).2
        (phiRow P.w (2 ^ P.w - 1) (2 ^ (P.a - 1)) (P.W * pt.pv) (N - n0)
          (R / 2 ^ (P.w * (n0 - i)) % 2 ^ (P.w * (N - n0))) (P.W * (i * pt.pu)) c d).1
        (phiRow P.w (2 ^ P.w - 1) (2 ^ (P.a - 1)) (P.W * pt.pv) (N - n0)
          (R / 2 ^ (P.w * (n0 - i)) % 2 ^ (P.w * (N - n0))) (P.W * (i * pt.pu)) c d).2 := by
  rw [headGo_succ']
  simp only [Nat.shiftRight_eq_div_pow, mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.one_shiftLeft]

/-- The loop over the rows of the head, started at row `i` with `cnt = n0 - i` rows left. -/
theorem headGo_eq (P : Params) (pt : Pt) (N n0 rows : ℕ) : ∀ (cnt i a b c d : ℕ), i + cnt = n0 →
    headGo P pt N n0 cnt (rows / 2 ^ (P.w * triOff N i)) i a b c d =
      (a + ∑ r ∈ range cnt, ∑ s ∈ range (n0 - (i + r)),
          triEnt P.w N rows (i + r) s * 2 ^ (P.W * ((i + r) * pt.pu) + (i + r + s) * (P.W * pt.pv)),
       b + ∑ r ∈ range cnt, ∑ s ∈ range (n0 - (i + r)),
          2 ^ (P.a - 1) * 2 ^ (P.W * ((i + r) * pt.pu) + (i + r + s) * (P.W * pt.pv)),
       c + ∑ r ∈ range cnt, ∑ j ∈ range (N - n0),
          triEnt P.w N rows (i + r) (n0 - (i + r) + j) * 2 ^ (P.W * ((i + r) * pt.pu) + j * (P.W * pt.pv)),
       d + ∑ r ∈ range cnt, ∑ j ∈ range (N - n0),
          2 ^ (P.a - 1) * 2 ^ (P.W * ((i + r) * pt.pu) + j * (P.W * pt.pv)))
  | 0, i, a, b, c, d, _ => by simp [headGo_zero]
  | cnt + 1, i, a, b, c, d, h => by
    have hrow1 : rows / 2 ^ (P.w * triOff N i) % 2 ^ (P.w * (n0 - i))
        = packSum P.w (n0 - i) (triEnt P.w N rows i) := by
      rw [mod_packSum]
      refine packSum_congr _ _ fun s _ => ?_
      unfold triEnt
      rw [slot_div]
    have hrow2 : rows / 2 ^ (P.w * triOff N i) / 2 ^ (P.w * (n0 - i)) % 2 ^ (P.w * (N - n0))
        = packSum P.w (N - n0) (fun j => triEnt P.w N rows i (n0 - i + j)) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, ← mul_add, mod_packSum]
      refine packSum_congr _ _ fun s _ => ?_
      unfold triEnt
      rw [slot_div, Nat.add_assoc]
    rw [headGo_succ, triRow_rest, hrow1, hrow2,
      phiRow_eq P.w _ _ (n0 - i) _ _ _ _ (fun s _ => triEnt_lt P.w N rows i s),
      phiRow_eq P.w _ _ (N - n0) _ _ _ _ (fun s _ => triEnt_lt P.w N rows i _),
      headGo_eq P pt N n0 rows cnt (i + 1) _ _ _ _ (by omega),
      sum_range_succ', sum_range_succ', sum_range_succ', sum_range_succ']
    have e1 : ∀ r, i + 1 + r = i + (r + 1) := fun r => by ring
    have e2 : ∀ s, P.W * (i * (pt.pu + pt.pv)) + s * (P.W * pt.pv)
        = P.W * (i * pt.pu) + (i + s) * (P.W * pt.pv) := fun s => by ring
    simp only [e1, e2, add_zero]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

/-- The pair of `∑_{i ≤ j < n0} X i j • u ^ i * v ^ j` for a block of order `N` stored in `rows`. -/
noncomputable def phi00P (P : Params) (N n0 rows : ℕ) : Poly × Poly :=
  (∑ i ∈ range n0, ∑ s ∈ range (n0 - i), C (triEnt P.w N rows i s) * (X 0 ^ i * X 1 ^ (i + s)),
   ∑ i ∈ range n0, ∑ s ∈ range (n0 - i), C (2 ^ (P.a - 1)) * (X 0 ^ i * X 1 ^ (i + s)))

/-- The pair of `∑_{i < n0, j < N - n0} X i (n0 + j) • u ^ i * v ^ j`. -/
noncomputable def phi01P (P : Params) (N n0 rows : ℕ) : Poly × Poly :=
  (∑ i ∈ range n0, ∑ j ∈ range (N - n0), C (triEnt P.w N rows i (n0 - i + j)) * (X 0 ^ i * X 1 ^ j),
   ∑ i ∈ range n0, ∑ j ∈ range (N - n0), C (2 ^ (P.a - 1)) * (X 0 ^ i * X 1 ^ j))

/-- `headGo` computes the values of the parts of `phi00P` and `phi01P`. -/
theorem head_eq (P : Params) (pt : Pt) (N n0 rows : ℕ) :
    headGo P pt N n0 n0 rows 0 0 0 0 0 =
      (ev P pt (phi00P P N n0 rows).1, ev P pt (phi00P P N n0 rows).2,
       ev P pt (phi01P P N n0 rows).1, ev P pt (phi01P P N n0 rows).2) := by
  have h0 : rows / 2 ^ (P.w * triOff N 0) = rows := by
    rw [triOff_zero, mul_zero, pow_zero, Nat.div_one]
  have hb := headGo_eq P pt N n0 rows n0 0 0 0 0 0 (zero_add n0)
  rw [h0] at hb
  simp only [zero_add] at hb
  rw [hb]
  simp only [phi00P, phi01P, map_sum, ev_C_uv]

/-! ## The parts of a block -/

/-- The pair of the polynomial `φ` of the part of a block that `sel` selects. -/
noncomputable def partP (P : Params) (B : Blk) (sel : ℕ) : Poly × Poly :=
  if sel = 0 then phi00P P B.N B.n0 B.rows
  else if sel = 1 then phi01P P B.N B.n0 B.rows
  else phiP P (B.N - B.n0) (B.rows / 2 ^ (P.w * triOff B.N B.n0))

theorem part_eq (P : Params) (pt : Pt) (B : Blk) (sel : ℕ) : part P pt B sel = evp P pt (partP P B sel) := by
  rcases sel with _ | _ | sel
  · show ((headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).1, (headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).2.1) = _
    rw [head_eq]
    rfl
  · show ((headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).2.2.1,
      (headGo P pt B.N B.n0 B.n0 B.rows 0 0 0 0 0).2.2.2) = _
    rw [head_eq]
    rfl
  · show ((phiEval P pt (B.N - B.n0) (B.rows >>> (P.w * triOffK B.N B.n0))).1,
      (phiEval P pt (B.N - B.n0) (B.rows >>> (P.w * triOffK B.N B.n0))).2.1) = _
    rw [Nat.shiftRight_eq_div_pow, triOffK_eq]
    obtain ⟨b, hb⟩ := phiEval_eq P pt (B.N - B.n0) (B.rows / 2 ^ (P.w * triOff B.N B.n0))
    rw [hb]
    simp [partP, evp]

/-! ## The kernel of a part -/

/-- The pair of `∑ φₖ * Qₖ` over the blocks of `l`, the first of which has the index `k`. -/
noncomputable def kernFrom (P : Params) (sel : ℕ) : List Blk → ℕ → Poly × Poly
  | [], _ => (0, 0)
  | B :: l, k => pmul (partP P B sel) (qP P k) + kernFrom P sel l (k + 1)

/-- The pair of the kernel `∑ₖ φₖ * Qₖ` of a part. -/
noncomputable def kernP (P : Params) (sel : ℕ) (blocks : List Blk) : Poly × Poly := kernFrom P sel blocks 0

theorem kernGo_nil (P : Params) (pt : Pt) (sel k : ℕ) (cur prev : ℕ × ℕ) (Mp Mn : ℕ) :
    kernGo P pt sel [] k cur prev Mp Mn = (Mp, Mn) := rfl

theorem kernGo_cons (P : Params) (pt : Pt) (sel : ℕ) (B : Blk) (l : List Blk) (k : ℕ) (cur prev : ℕ × ℕ)
    (Mp Mn : ℕ) :
    kernGo P pt sel (B :: l) k cur prev Mp Mn =
      kernGo P pt sel l (k + 1)
        (Bool.rec (motive := fun _ => ℕ × ℕ) (qNext P pt cur prev) (mulTerms P pt 2 (tuv P) 1 0 0 0)
          (Nat.beq k 0))
        cur
        (Mp + ((part P pt B sel).1 * cur.1 + (part P pt B sel).2 * cur.2))
        (Mn + ((part P pt B sel).1 * cur.2 + (part P pt B sel).2 * cur.1)) := rfl

/-- The loop over the blocks. -/
theorem kernGo_eq (P : Params) (pt : Pt) (sel : ℕ) : ∀ (l : List Blk) (k : ℕ) (cur prev : ℕ × ℕ) (Mp Mn : ℕ),
    cur = evp P pt (qP P k) → (∀ j, k = j + 1 → prev = evp P pt (qP P j)) →
    kernGo P pt sel l k cur prev Mp Mn =
      (Mp + ev P pt (kernFrom P sel l k).1, Mn + ev P pt (kernFrom P sel l k).2)
  | [], k, cur, prev, Mp, Mn, _, _ => by simp [kernGo_nil, kernFrom]
  | B :: l, k, cur, prev, Mp, Mn, hcur, hprev => by
    rw [kernGo_cons]
    have hnext : (Bool.rec (motive := fun _ => ℕ × ℕ) (qNext P pt cur prev)
        (mulTerms P pt 2 (tuv P) 1 0 0 0) (Nat.beq k 0)) = evp P pt (qP P (k + 1)) := by
      rcases k with _ | j
      · exact q_one_evp P pt
      · show qNext P pt cur prev = _
        rw [hcur, hprev j rfl, qNext_evp]
        rfl
    rw [kernGo_eq P pt sel l (k + 1) _ cur _ _ hnext (fun j hj => by
        have : j = k := by omega
        rw [this, hcur]), part_eq, hcur]
    simp only [kernFrom, evp, pmul, Prod.fst_add, Prod.snd_add, map_add, map_mul]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-- `kern` computes the values of the two parts of `kernP`. -/
theorem kern_eq (P : Params) (pt : Pt) (sel : ℕ) (blocks : List Blk) :
    kern P pt sel blocks = evp P pt (kernP P sel blocks) := by
  show kernGo P pt sel blocks 0 (1, 0) (0, 0) 0 0 = _
  rw [kernGo_eq P pt sel blocks 0 (1, 0) (0, 0) 0 0 (by simp [evp, qP]) (fun j hj => absurd hj (by omega))]
  simp [kernP, evp]

end N14.Ident
