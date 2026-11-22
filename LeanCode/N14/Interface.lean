module

public import N14.Nodes
public import N14.Rigid
public import N14.Local.Theorem

/-!
# The theorem for 14 points: the statements of the computer-assisted part

`N14.T7.CAP` is the conjunction of the statements that the proof of the source takes from its computations
(the eight computational statements of `caps/n14.md`), for configurations of 14 points of `S²` in the form of
`N14/Statement.lean` (`x : Fin 14 → Fin 3 → ℝ`, `OnSphere x`, `energy x`, `dot x i j = ⟨x i, x j⟩`) and for the
candidate `Xstar`. The generated module `N14Cert.T7` proves it (`N14Cert.T7.cap`); the analytic part of the
proof of T7 (the case analysis, the rigidity lemma, criticality, the assembly) would prove
`CAP → N14.Thomson14` and is not part of this folder.

The fields, with the statements of the source (`N14/README.md` has the table with the differences):

* `height`, `hStar_enc`, `candidate`, `energy_enc`: Lemma 1.1.
* `sep`: Proposition 5.2 with its closure: two points with inner product at least `t0` give `E ≥ E* + 0.086`.
* `caseI`, `caseII`: Section 5 and Section 6 with their closure (Theorem 1.3): `E > E* + 3.6 · 10⁻⁴`.
* `cap_ge`, `cap_far`, `cap_loc`: Proposition 7.4 with the certificate of Section 7.4 and the counting of
  Lemma 7.1, for a configuration of the class of Case III (`Cap`): the energy is above `E* - 3.65 · 10⁻¹³`; a
  triple whose type has distance at least `1/100` from all nodes of its pattern, or a pair whose inner product
  has distance at least `1.95 · 10⁻⁴` from all class values of its pair class, gives `E > E*`. The nodes are
  the types of the triples of the candidate (`N14.FarAll`), the class values are the inner products of its
  pairs (`N14.PairFar`); no list of nodes occurs.
* `values`, `separation`, `rigid`: the nine inner products of the candidate, their separation, and the
  inequalities of the rigidity lemma (Lemma 8.1) at `τ = 10⁻³`.
* `local7`: the computational content of Proposition 9.1 (`N14.Local.Local7`).
* `tube`: `23 · 1.95 · 10⁻⁴ < 0.0075`.
-/

@[expose] public section

namespace N14.T7

open N14 CAP.ThreePoint N14.Energy

/-- The first cutoff of the source: the stored binary64 number `0.8`. -/
noncomputable def t0 : ℝ := 3602879701896397 / 4503599627370496

/-- The second cutoff of the source: the stored binary64 number `-0.98`. -/
noncomputable def b98 : ℝ := -(2206763817411543 / 2251799813685248)

/-- The third cutoff of the source: the stored binary64 number `-0.99`. -/
noncomputable def b99 : ℝ := -(4458563631096791 / 4503599627370496)

/-- **The class of Case III** (the cap): `p`, `q` is a pair with the smallest inner product, this inner product
is at most `b99`, and all inner products are at most `t0`. -/
def Cap (x : Fin 14 → Fin 3 → ℝ) (p q : Fin 14) : Prop :=
  p ≠ q ∧ (∀ i j, i ≠ j → dot x p q ≤ dot x i j) ∧ dot x p q ≤ b99 ∧ ∀ i j, i ≠ j → dot x i j ≤ t0

/-- **The computer-assisted part of the theorem for 14 points.** -/
structure CAP : Prop where
  /-- Lemma 1.1: the stationary height exists and is unique. -/
  height : ∃! h, StationaryHeight h
  /-- Lemma 1.1: the stationary height to 51 decimals. -/
  hStar_enc : |hStar - hDec| ≤ 2 / 10 ^ 51
  /-- The candidate consists of 14 distinct points of the sphere. -/
  candidate : OnSphere Xstar ∧ Function.Injective Xstar
  /-- Lemma 1.1: the energy of the candidate to 49 decimals. -/
  energy_enc : |energy Xstar - 69.306363296626421258489991276382007864282129573759| ≤ 1 / 10 ^ 49
  /-- Proposition 5.2 (separation). -/
  sep : ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x → ∀ i j : Fin 14, i ≠ j →
    t0 ≤ dot x i j → energy Xstar + 86 / 1000 < energy x
  /-- Case I: all inner products at least `-0.98`. -/
  caseI : ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x →
    (∀ i j : Fin 14, i ≠ j → b98 ≤ dot x i j) → energy Xstar + 36 / 100000 < energy x
  /-- Case II: the smallest inner product between `-0.99` and `-0.98`. -/
  caseII : ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x → ∀ p q : Fin 14, p ≠ q →
    (∀ i j, i ≠ j → dot x p q ≤ dot x i j) → b99 ≤ dot x p q → dot x p q ≤ b98 →
    energy Xstar + 36 / 100000 < energy x
  /-- Case III: the offset of the certificate is below the energy of the candidate by less than `3.65e-13`. -/
  cap_ge : ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x → ∀ p q : Fin 14, Cap x p q →
    energy Xstar - 365 / 10 ^ 15 < energy x
  /-- Case III: a triple far from the nodes of its pattern. -/
  cap_far : ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x → ∀ p q : Fin 14, Cap x p q →
    ∀ i j k : Fin 14, Distinct3 i j k →
      FarAll hStar (1 / 100) (tau p q i) (tau p q j) (tau p q k) (dot x i j) (dot x i k) (dot x j k) →
      energy Xstar < energy x
  /-- Case III: a pair whose inner product is displaced from the class values. -/
  cap_loc : ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x → ∀ p q : Fin 14, Cap x p q →
    ∀ i j : Fin 14, i ≠ j → PairFar hStar (39 / 200000) (tau p q i) (tau p q j) (dot x i j) →
      energy Xstar < energy x
  /-- The inner products of the candidate are the nine values. -/
  values : ∀ a b : Fin 14, a ≠ b → dot Xstar a b = ipc hStar a b
  /-- The nine values are separated. -/
  separation : ∀ c d : ℕ, c < 9 → d < 9 → c ≠ d → 18 / 1000 < |ipVal hStar c - ipVal hStar d|
  /-- The inequalities of the rigidity lemma. -/
  rigid : N14.Rigid.Consts hStar
  /-- The computational content of Proposition 9.1. -/
  local7 : N14.Local.Local7
  /-- The radius of the tubes times 23 is below the radius of Proposition 9.1. -/
  tube : (23 : ℝ) * (39 / 200000) < 75 / 10000

end N14.T7
