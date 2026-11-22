module

public import CAP.Schema.ThreePoint.Main

/-!
# Schema S2, soundness: the polynomials with integer coefficients

The polynomials of the statement, as elements of `ℤ[u, v, t]`, and their relation to the pairs of
polynomials with natural coefficients of the previous files: for a pair `a`, the polynomial is
`val a = a.1 - a.2`.

* `QZ k`: the kernel `Qₖ`;
* `entZ P n rows i s`: the entry `(i, i + s)` of a block of order `n` stored in `rows`;
* `phiZ P n rows = ∑ᵢ ∑ₛ X i (i + s) • u ^ i * v ^ (i + s)`;
* `momentZ P mrows 0 = ∑ₖ φₖ * Qₖ`, where block `k` has the order `D + 1 - k`;
* `polyZ P T tf`: the polynomial with the `T` term fields `tf`; `zZ P B j`: the basis element `j`
  of the block `B`;
* `sosZ P B = g * ∑ᵣ zᵣ * ∑ₛ X r (r + s) • zᵣ₊ₛ`;
* `sosSumZ P sos = ∑_B f_B * G_B`.
-/

@[expose] public section

namespace CAP.ThreePoint

open MvPolynomial Finset

/-- Polynomials in `u`, `v`, `t` with integer coefficients. -/
abbrev PolyZ := MvPolynomial (Fin 3) ℤ

/-- A polynomial with natural coefficients as a polynomial with integer coefficients. -/
noncomputable def toZ : Poly →+* PolyZ := map (Nat.castRingHom ℤ)

theorem toZ_C (c : ℕ) : toZ (C c) = C (c : ℤ) := by simp [toZ]

theorem toZ_X (i : Fin 3) : toZ (X i) = X i := by simp [toZ]

/-- The polynomial of a pair (positive part, negative part). -/
noncomputable def val (a : Poly × Poly) : PolyZ := toZ a.1 - toZ a.2

theorem val_zero : val (0, 0) = 0 := by simp [val]

theorem val_add (a b : Poly × Poly) : val (a + b) = val a + val b := by
  simp only [val, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem val_pmul (a b : Poly × Poly) : val (pmul a b) = val a * val b := by
  simp only [val, pmul, map_add, map_mul]
  ring

theorem val_smul (c : ℕ) (a : Poly × Poly) : val (C c * a.1, C c * a.2) = C (c : ℤ) * val a := by
  simp only [val, map_mul, toZ_C]
  ring

/-! ## Polynomials given by term fields -/

/-- The term `± coef * u ^ a * v ^ b * t ^ c` of a term field. -/
noncomputable def termZ (P : Params) (f : ℕ) : PolyZ :=
  (if tNeg P f = true then -1 else 1)
    * (C (tCoef P f : ℤ) * (X 0 ^ tExp P f 0 * X 1 ^ tExp P f 1 * X 2 ^ tExp P f 2))

/-- The polynomial with the `T` term fields `tf`. -/
noncomputable def polyZ (P : Params) : ℕ → ℕ → PolyZ
  | 0, _ => 0
  | T + 1, tf => termZ P (fld P tf) + polyZ P T (tf / 2 ^ fw P)

theorem val_tPair (P : Params) (f : ℕ) : val (tPair P f) = termZ P f := by
  unfold tPair termZ tMono
  split <;> simp [val, toZ_X]

theorem val_polyOf (P : Params) : ∀ (T tf : ℕ), val (polyOf P T tf) = polyZ P T tf
  | 0, _ => val_zero
  | T + 1, tf => by rw [polyOf, val_add, val_tPair, val_polyOf P T, polyZ]

/-! ## The kernels -/

/-- The kernel `Qₖ`: `Q₀ = 1`, `Q₁ = t - u * v`,
`Qₖ₊₂ = 2 * (t - u * v) * Qₖ₊₁ - (1 - u ^ 2) * (1 - v ^ 2) * Qₖ`. -/
noncomputable def QZ : ℕ → PolyZ
  | 0 => 1
  | 1 => X 2 - X 0 * X 1
  | k + 2 => 2 * (X 2 - X 0 * X 1) * QZ (k + 1) - (1 - X 0 ^ 2) * (1 - X 1 ^ 2) * QZ k

section kernels
variable (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb)
include heb hcb

theorem val_tuvP : val (tuvP P) = X 2 - X 0 * X 1 := by
  rw [tuvP_eq P heb hcb]
  simp [val, toZ_X]

theorem val_wuvP : val (wuvP P) = (1 - X 0 ^ 2) * (1 - X 1 ^ 2) := by
  rw [wuvP_eq P heb hcb]
  simp only [val, map_add, map_mul, map_pow, map_one, toZ_X]
  ring

theorem val_qNextP (cur prev : Poly × Poly) :
    val (qNextP P cur prev)
      = 2 * (X 2 - X 0 * X 1) * val cur - (1 - X 0 ^ 2) * (1 - X 1 ^ 2) * val prev := by
  have h2 : toZ 2 = 2 := map_ofNat toZ 2
  have e : val (qNextP P cur prev) = 2 * val (pmul (tuvP P) cur) - val (pmul (wuvP P) prev) := by
    simp only [val, qNextP, map_add, map_mul, h2]
    ring
  rw [e, val_pmul, val_pmul, val_tuvP P heb hcb, val_wuvP P heb hcb]
  ring

theorem val_qP : ∀ k, val (qP P k) = QZ k ∧ val (qP P (k + 1)) = QZ (k + 1)
  | 0 => by
    refine ⟨by simp [qP, val, QZ], ?_⟩
    have e : qP P 1 = pmul (tuvP P) (1, 0) := rfl
    rw [e, val_pmul, val_tuvP P heb hcb]
    simp [val, QZ]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := val_qP k
    refine ⟨h2, ?_⟩
    have e : qP P (k + 1 + 1) = qNextP P (qP P (k + 1)) (qP P k) := rfl
    rw [e, val_qNextP P heb hcb, h1, h2]
    rfl

end kernels

/-! ## The moment blocks -/

/-- The entry `(i, i + s)` of a block of order `n` stored in `rows`: slot minus bias. -/
def entZ (P : Params) (n rows i s : ℕ) : ℤ := (triEnt P.w n rows i s : ℤ) - 2 ^ (P.a - 1)

/-- `φ = ∑_{i ≤ j} X i j • u ^ i * v ^ j` for a block of order `n` stored in `rows`. -/
noncomputable def phiZ (P : Params) (n rows : ℕ) : PolyZ :=
  ∑ i ∈ range n, ∑ s ∈ range (n - i), C (entZ P n rows i s) * (X 0 ^ i * X 1 ^ (i + s))

theorem val_phiP (P : Params) (n rows : ℕ) : val (phiP P n rows) = phiZ P n rows := by
  unfold val phiP phiZ
  simp only [map_sum, map_mul, map_pow, toZ_C, toZ_X]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  unfold entZ
  rw [map_sub, sub_mul]
  simp only [Nat.cast_ofNat, map_pow]

/-- `∑ₖ φₖ * Qₖ` over the blocks listed in `l`, where the first block has the index `k` and the
order `D + 1 - k`. -/
noncomputable def momentZ (P : Params) : List ℕ → ℕ → PolyZ
  | [], _ => 0
  | rows :: l, k => phiZ P (P.D + 1 - k) rows * QZ k + momentZ P l (k + 1)

theorem val_momentFrom (P : Params) (heb : 2 ≤ P.eb) (hcb : 1 ≤ P.cb) : ∀ (l : List ℕ) (k : ℕ),
    val (momentFrom P l k) = momentZ P l k
  | [], _ => val_zero
  | rows :: l, k => by
    rw [momentFrom, val_add, val_pmul, val_phiP, (val_qP P heb hcb k).1, val_momentFrom P heb hcb l,
      momentZ]

/-! ## The blocks with a sum of squares -/

/-- The term fields of the basis element `j` in `tf`. -/
def bField (P : Params) (B : Sos) (tf j : ℕ) : ℕ := tf / 2 ^ (bw P B * j) % 2 ^ bw P B

/-- The basis element `j` of the block `B`. -/
noncomputable def zZ (P : Params) (B : Sos) (j : ℕ) : PolyZ := polyZ P B.T (bField P B B.basis j)

theorem bField_zero (P : Params) (B : Sos) (tf : ℕ) : bField P B tf 0 = tf % 2 ^ bw P B := by
  simp [bField]

theorem bField_succ (P : Params) (B : Sos) (tf j : ℕ) :
    bField P B (tf / 2 ^ bw P B) j = bField P B tf (j + 1) := by
  unfold bField
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  have e : bw P B + bw P B * j = bw P B * (j + 1) := by ring
  rw [e]

theorem val_sumP (P : Params) (B : Sos) : ∀ (cnt tf : ℕ),
    val (sumP P B (basisFields P B cnt tf)) = ∑ j ∈ range cnt, polyZ P B.T (bField P B tf j)
  | 0, _ => by simp [basisFields, sumP, val_zero]
  | cnt + 1, tf => by
    rw [basisFields, sumP, val_add, val_polyOf, val_sumP P B cnt, sum_range_succ', bField_zero]
    simp only [bField_succ]
    ring

theorem val_rowP (P : Params) (B : Sos) : ∀ (cnt tf : ℕ) (ξ : ℕ → ℕ),
    val (rowP P B (basisFields P B cnt tf) ξ)
      = ∑ j ∈ range cnt, C (ξ j : ℤ) * polyZ P B.T (bField P B tf j)
  | 0, _, _ => by simp [basisFields, rowP, val_zero]
  | cnt + 1, tf, ξ => by
    rw [basisFields, rowP, val_add, val_smul, val_polyOf, val_rowP P B cnt, sum_range_succ', bField_zero]
    simp only [bField_succ]
    ring

/-- The polynomial of `rowPair`: `rᵢ = ∑ⱼ X i (i + j) • zⱼ` for the listed basis elements. -/
theorem val_rowPair (P : Params) (B : Sos) (cnt tf i : ℕ) :
    val (rowPair P B (basisFields P B cnt tf) i)
      = ∑ j ∈ range cnt, C (entZ P B.n B.rows i j) * polyZ P B.T (bField P B tf j) := by
  have h1 := val_sumP P B cnt tf
  have h2 := val_rowP P B cnt tf (triEnt P.w B.n B.rows i)
  have e : val (rowPair P B (basisFields P B cnt tf) i)
      = val (rowP P B (basisFields P B cnt tf) (triEnt P.w B.n B.rows i))
        - C (((2 ^ (P.a - 1) : ℕ) : ℤ)) * val (sumP P B (basisFields P B cnt tf)) := by
    simp only [val, rowPair, map_add, map_mul, toZ_C]
    ring
  rw [e, h1, h2, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  unfold entZ
  rw [map_sub, sub_mul]
  push_cast
  rfl

/-- The polynomial of `sosFrom`: `∑ᵣ zᵣ * ∑ₛ X (i + r) s • zᵣ₊ₛ` for the listed basis elements. -/
theorem val_sosFrom (P : Params) (B : Sos) : ∀ (cnt tf i : ℕ),
    val (sosFrom P B (basisFields P B cnt tf) i) =
      ∑ r ∈ range cnt, polyZ P B.T (bField P B tf r)
        * ∑ s ∈ range (cnt - r), C (entZ P B.n B.rows (i + r) s) * polyZ P B.T (bField P B tf (r + s))
  | 0, _, _ => by simp [basisFields, sosFrom, val_zero]
  | cnt + 1, tf, i => by
    have hrow := val_rowPair P B (cnt + 1) tf i
    rw [basisFields] at hrow
    have e1 : ∀ r, i + 1 + r = i + (r + 1) := fun r => by ring
    have e2 : ∀ r s, r + s + 1 = r + 1 + s := fun r s => by ring
    conv_rhs => rw [sum_range_succ']
    rw [basisFields, sosFrom, val_add, val_pmul, val_polyOf, hrow, val_sosFrom P B cnt, ← bField_zero]
    simp only [bField_succ, e1, e2, Nat.add_sub_add_right, Nat.sub_zero, add_zero, zero_add]
    ring

/-- `G_B = g * ∑ᵣ zᵣ * ∑ₛ X r (r + s) • zᵣ₊ₛ` for the block `B` with the weight `g`, the basis `z`
and the matrix entries `X`. -/
noncomputable def sosZ (P : Params) (B : Sos) : PolyZ :=
  polyZ P B.gT B.weight * ∑ r ∈ range B.n, zZ P B r
    * ∑ s ∈ range (B.n - r), C (entZ P B.n B.rows r s) * zZ P B (r + s)

theorem val_sosP (P : Params) (B : Sos) : val (sosP P B) = sosZ P B := by
  unfold sosP sosZ zZ
  rw [val_pmul, val_polyOf, val_sosFrom]
  simp only [zero_add]

/-- `∑_B f_B * G_B` over the listed blocks. -/
noncomputable def sosSumZ (P : Params) : List Sos → PolyZ
  | [] => 0
  | B :: l => C (B.f : ℤ) * sosZ P B + sosSumZ P l

theorem val_sosSum (P : Params) : ∀ l : List Sos, val (sosSum P l) = sosSumZ P l
  | [] => val_zero
  | B :: l => by rw [sosSum, val_add, val_smul, val_sosP, val_sosSum P l, sosSumZ]

end CAP.ThreePoint
