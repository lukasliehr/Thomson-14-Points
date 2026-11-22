import Mathlib

/-!
# The Thomson problem for 14 points

The Thomson problem asks for the configurations of `N` points on the unit sphere of `ℝ³` that
minimize the Coulomb energy, the sum of the reciprocal distances over all pairs of points.
This file states its solution for `N = 14`: the minimizer is the bicapped hexagonal antiprism,
and it is unique up to orthogonal transformations and relabelling of the points.

All definitions needed to read the statement are included here, and Mathlib is the only import.
The same statement, with its proof, appears in `Showcase_WithProofs.lean`.
-/

noncomputable section
open Real

namespace Thomson14

/-! ## Configurations and Coulomb energy -/

/-- Three-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- Fourteen distinct points on the unit sphere. -/
def IsConfiguration (Y : Fin 14 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- The Coulomb energy, summed over the 91 unordered pairs of points.
(For two equal points Lean evaluates `1 / 0` to `0`; the theorem below concerns configurations
of distinct points only.) -/
def E (Y : Fin 14 → Point) : ℝ :=
  ∑ i : Fin 14, ∑ j : Fin 14 with i < j, 1 / ‖Y i - Y j‖

/-- `Y` arises from `Z` by an orthogonal transformation and a permutation of the labels.
Here `Point ≃ₗᵢ[ℝ] Point` is the type of the linear isometries of `ℝ³` onto itself, that is, of
the orthogonal transformations, and `Equiv.Perm (Fin 14)` is the type of the permutations of the
labels `0, …, 13`. -/
def Congruent (Y Z : Fin 14 → Point) : Prop :=
  ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 14)),
    ∀ i, Y i = U (Z (σ i))

/-- `Z` is a configuration that attains the global minimum of the energy, and equality occurs
exactly at its congruent copies. -/
def IsUniqueMinimizer (Z : Fin 14 → Point) : Prop :=
  IsConfiguration Z ∧ ∀ Y, IsConfiguration Y →
    E Z ≤ E Y ∧ (E Y = E Z ↔ Congruent Y Z)

/-! ## The bicapped hexagonal antiprism -/

/-- The point of the unit sphere at height `z` and longitude `θ`, for `-1 ≤ z ≤ 1`.
Here `!₂[x, y, z]` is the Euclidean vector with coordinates `(x, y, z)`. -/
def pointAt (z θ : ℝ) : Point :=
  !₂[√(1 - z ^ 2) * cos θ, √(1 - z ^ 2) * sin θ, z]

/-- `X(h)` consists of the two poles, a regular hexagon at height `h`, and a regular hexagon
at height `-h` that is rotated by `π/6` against the first: the six points at height `h` have the
longitudes `k π / 3`, and the six points at height `-h` the longitudes `(2 k + 1) π / 6`, for
`k = 0, …, 5`. Here `![x₀, …, x₁₃]` is the family with the entries `x₀, …, x₁₃`. -/
def X (h : ℝ) : Fin 14 → Point :=
  ![!₂[0, 0, 1], !₂[0, 0, -1],
    pointAt h 0, pointAt h (π / 3), pointAt h (2 * π / 3),
    pointAt h (3 * π / 3), pointAt h (4 * π / 3), pointAt h (5 * π / 3),
    pointAt (-h) (π / 6), pointAt (-h) (3 * π / 6), pointAt (-h) (5 * π / 6),
    pointAt (-h) (7 * π / 6), pointAt (-h) (9 * π / 6), pointAt (-h) (11 * π / 6)]

/-! ## The main theorem -/

/-- A decimal number with 50 decimal places, which approximates the optimal height. -/
def h₀ : ℝ := 0.45536779516246300350924502372107445741075259468695

/-- A decimal number with 48 decimal places, which approximates the minimal energy. -/
def E₀ : ℝ := 69.306363296626421258489991276382007864282129573759

/-- **The Thomson problem for 14 points.** There is a height `h` with the following properties.

* `h` agrees with the decimal number `h₀` up to `2 · 10⁻⁵¹`.
* Among all `t` within `10⁻⁴⁰` of `h₀`, the height `h` is the only stationary point of the
  energy `t ↦ E(X(t))` of the family of bicapped hexagonal antiprisms. Here
  `HasDerivAt f 0 t` states that `f` is differentiable at `t` with derivative `0`.
  This property and the previous one determine `h`.
* `X(h)` is a configuration of 14 distinct points on the unit sphere, every such configuration
  `Y` satisfies `E(X(h)) ≤ E(Y)`, and equality holds exactly when `Y` arises from `X(h)` by an
  orthogonal transformation and a relabelling of the points.
* The minimal energy `E(X(h))` agrees with the decimal number `E₀` up to `10⁻⁴⁹`. -/
theorem thomson_14_points :
    ∃ h : ℝ,
      |h - h₀| ≤ 2 / 10 ^ 51 ∧
      (∀ t : ℝ, |t - h₀| ≤ 1 / 10 ^ 40 → (HasDerivAt (fun s ↦ E (X s)) 0 t ↔ t = h)) ∧
      IsUniqueMinimizer (X h) ∧
      |E (X h) - E₀| ≤ 1 / 10 ^ 49 := by
  sorry

end Thomson14
