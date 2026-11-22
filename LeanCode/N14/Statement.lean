module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Thomson problem for 14 points: the statement

This file contains the statement of the theorem and nothing else. It uses the real numbers, finite
sums, the square root, the cosine, the derivative and the orthogonal group of Mathlib, and no file
of the library `CAP`.

**The family.** For a height `h` the configuration `X14 h` consists of

* the two poles `(0, 0, 1)` and `(0, 0, -1)` (the points `0` and `1`),
* the six points `(r cos (k π / 3), r sin (k π / 3), h)`, `k = 0, …, 5` (the points `2, …, 7`), and
* the six points `(r cos (k π / 3 + π / 6), r sin (k π / 3 + π / 6), -h)`, `k = 0, …, 5` (the points
  `8, …, 13`),

with `r = √(1 - h²)`: two parallel regular hexagons, rotated against each other by 30 degrees and
capped by the poles (a bicapped hexagonal antiprism). The numbering is that of the programs of the
source.

**The candidate.** The function `h ↦ energy (X14 h)` has exactly one stationary point `hStar` among
the heights within `10⁻⁴⁰` of the decimal number `hDec` (Lemma 1.1 of the source). The candidate is
`Xstar = X14 hStar`.

**The theorem** (`Thomson14`). The stationary height exists and is unique, the 14 points of `Xstar`
are distinct points of the unit sphere of `ℝ³`, every configuration `x` of 14 distinct points of the
unit sphere satisfies `energy Xstar ≤ energy x`, and if equality holds, then `x` arises from `Xstar`
by an orthogonal map and a relabelling of the points. Here `energy x = ∑_{i < j} 1 / |x i - x j|` is
the Coulomb energy.

The hypothesis that the points of `x` are distinct is needed in this form: for two equal points
Lean evaluates `1 / 0` to `0`, whereas the energy of such a configuration is infinite.

This is the theorem `T7` of the write-up. Its source is `n14` of `caps/sources.json` (`caps/n14.md`).
The file states the theorem as a proposition; see `N14/README.md` for what is proved. The theorem
is not proved in this folder: only its computational statements are.
-/

@[expose] public section

namespace N14

open Finset

/-- The Coulomb energy of `N` points of `ℝ³` that are given by their coordinates. -/
noncomputable def energy {N : ℕ} (x : Fin N → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j with i < j, 1 / Real.sqrt (∑ k, (x i k - x j k) ^ 2)

/-- All points lie on the unit sphere. -/
def OnSphere {N : ℕ} (x : Fin N → Fin 3 → ℝ) : Prop := ∀ i, ∑ k, x i k ^ 2 = 1

/-- The configuration `y` arises from `x` by an orthogonal map and a relabelling of the points. -/
def Congruent {N : ℕ} (x y : Fin N → Fin 3 → ℝ) : Prop :=
  ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∃ σ : Equiv.Perm (Fin N), ∀ i, y i = U.mulVec (x (σ i))

/-- A point of the family, for a natural index: the poles for `0` and `1`, the upper hexagon for
`2, …, 7` and the lower hexagon from `8` on. -/
noncomputable def X14N (h : ℝ) (n : ℕ) : Fin 3 → ℝ :=
  if n = 0 then ![0, 0, 1]
  else if n = 1 then ![0, 0, -1]
  else if n < 8 then
    ![Real.sqrt (1 - h ^ 2) * Real.cos (((n - 2 : ℕ) : ℝ) * (Real.pi / 3)),
      Real.sqrt (1 - h ^ 2) * Real.sin (((n - 2 : ℕ) : ℝ) * (Real.pi / 3)), h]
  else
    ![Real.sqrt (1 - h ^ 2) * Real.cos (((n - 8 : ℕ) : ℝ) * (Real.pi / 3) + Real.pi / 6),
      Real.sqrt (1 - h ^ 2) * Real.sin (((n - 8 : ℕ) : ℝ) * (Real.pi / 3) + Real.pi / 6), -h]

/-- **The bicapped hexagonal antiprism of height `h`.** -/
noncomputable def X14 (h : ℝ) (n : Fin 14) : Fin 3 → ℝ := X14N h n.val

/-- The decimal value of the stationary height, as stated by the source. -/
noncomputable def hDec : ℝ := 0.45536779516246300350924502372107445741075259468695

/-- A stationary height of the family near `hDec`. -/
def StationaryHeight (h : ℝ) : Prop :=
  |h - hDec| ≤ 1 / 10 ^ 40 ∧ HasDerivAt (fun t => energy (X14 t)) 0 h

open Classical in
/-- **The stationary height.** It is the stationary height near `hDec`; that this height exists and
is unique is a part of the theorem (and is Lemma 1.1 of the source). -/
noncomputable def hStar : ℝ := if H : ∃ h, StationaryHeight h then Classical.choose H else hDec

/-- **The candidate**: the bicapped hexagonal antiprism with the stationary height. -/
noncomputable def Xstar : Fin 14 → Fin 3 → ℝ := X14 hStar

/-- **The theorem for 14 points** (`T7`), as a proposition: the bicapped hexagonal antiprism with
the stationary height is the unique minimizer of the Coulomb energy of 14 points on the unit sphere,
up to orthogonal maps and relabelling. -/
def Thomson14 : Prop :=
  (∃! h, StationaryHeight h) ∧ OnSphere Xstar ∧ Function.Injective Xstar ∧
    ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x →
      energy Xstar ≤ energy x ∧ (energy x = energy Xstar → Congruent Xstar x)

/-- The first part of the theorem: the candidate is a minimizer. -/
def Minimizer14 : Prop :=
  (∃! h, StationaryHeight h) ∧ OnSphere Xstar ∧ Function.Injective Xstar ∧
    ∀ x : Fin 14 → Fin 3 → ℝ, OnSphere x → Function.Injective x → energy Xstar ≤ energy x

end N14
