# The Thomson problem for 14 points

This repository contains a Lean 4 formalization of the solution of the Thomson problem for
$N=14$ points on the sphere $S^2$. The main theorem says that the bicapped hexagonal antiprism is the
unique minimizer of the Coulomb energy.

![The bicapped hexagonal antiprism on the unit sphere, rotating about its axis.](Visualization/bicapped-hexagonal-antiprism.svg)

## Preliminaries

For a configuration $Y=(y_1,\ldots,y_{14})$ of distinct points on $S^2$ let

```math
E(Y)=\sum_{1\le i\lt j\le 14}\frac{1}{\lVert y_i-y_j\rVert}.
```

For a height $h$ let $X(h)$ be the configuration that consists of the two poles $(0,0,\pm1)$, the
six points $(r\cos\frac{k\pi}{3},\,r\sin\frac{k\pi}{3},\,h)$ and the six points
$(r\cos(\frac{k\pi}{3}+\frac{\pi}{6}),\,r\sin(\frac{k\pi}{3}+\frac{\pi}{6}),\,-h)$,
$k=0,\ldots,5$, where $r=\sqrt{1-h^2}$: two regular hexagons at the heights $h$ and $-h$, the
second rotated by $\pi/6$ against the first, and the two poles. Let

```math
\begin{aligned}
h_0&=0.45536779516246300350924502372107445741075259468695,\\
E_0&=69.306363296626421258489991276382007864282129573759.
\end{aligned}
```

## Formalized theorem

**Theorem.** There exists a height $h^\ast$ with $|h^\ast-h_0|\le 2\cdot10^{-51}$ such that the
following holds:

1. Among all $t$ with $|t-h_0|\le10^{-40}$, the height $h^\ast$ is the only stationary point of
   the function $t\mapsto E(X(t))$.
2. Every configuration $Y$ of 14 distinct
   points on $S^2$ satisfies $E(Y)\ge E(X(h^\ast))$, with equality if and only if $Y$ arises from
   $X(h^\ast)$ by an orthogonal transformation and a relabelling of the points.
3. The minimal energy satisfies $|E(X(h^\ast))-E_0|\le10^{-49}$.

`thomson_14_points` is the Lean formulation of this theorem. The following declaration is from
[Showcase.lean](Showcase.lean), which contains all definitions that the statement uses and imports
only Mathlib.

```lean
theorem thomson_14_points :
    ∃ h : ℝ,
      |h - h₀| ≤ 2 / 10 ^ 51 ∧
      (∀ t : ℝ, |t - h₀| ≤ 1 / 10 ^ 40 → (HasDerivAt (fun s ↦ E (X s)) 0 t ↔ t = h)) ∧
      IsUniqueMinimizer (X h) ∧
      |E (X h) - E₀| ≤ 1 / 10 ^ 49
```

<table><tr><td>

**Dependencies:** The proof of `thomson_14_points` in
[Showcase_WithProofs.lean](Showcase_WithProofs.lean) compiles and depends only on `propext`,
`Classical.choice` and `Quot.sound`, Lean's three standard axioms. It uses neither
`native_decide` nor `sorry`.

</td></tr></table>

## The proof

The proof is computer-assisted. It follows the paper
[AnalyticArguments/thomson14.pdf](AnalyticArguments/thomson14.pdf) and has two parts in Lean.

* **The computer-assisted part.** Three-point bounds, given by four certificates with exact
  rational data, show that a configuration whose energy is at most that of the candidate
  $X(h^\ast)$ has all inner products within $1.95\cdot10^{-4}$ of those of the candidate. A
  further computation bounds the expansion of the energy at the candidate. Every computational
  statement is verified by a *checker*, a function with values in `Bool` whose soundness theorem
  is proved in Lean and which the Lean kernel evaluates on the data of the certificates
  (`decide +kernel`). The data are the 615 Lean modules of [Certificates](Certificates); the
  checkers and their soundness theorems are in [LeanCode](LeanCode). The result is the theorem
  `N14Cert.T7.cap : N14.T7.CAP`.
* **The analytic part.** A case analysis, a rigidity lemma and a second-order argument at the
  candidate derive the theorem from the computer-assisted part:
  `N14.thomson14_of : N14.T7.CAP → N14.Thomson14` in
  [LeanCode/N14/Analytic](LeanCode/N14/Analytic). The arguments are written up in
  [AnalyticArguments](AnalyticArguments).

## Lean entry points

- [Showcase.lean](Showcase.lean): the definitions and the statement of the theorem, with `sorry`
  in place of the proof. Mathlib is its only import.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the same definitions and the same
  statement with the complete proof, followed by a test of its axioms.
- [LeanCode/N14/Statement.lean](LeanCode/N14/Statement.lean): the theorem in the coordinates of
  the proof, `N14.Thomson14`.
- [LeanCode/N14/Interface.lean](LeanCode/N14/Interface.lean): the statements that the proof takes
  from its certificates, `N14.T7.CAP`.
- [Certificates/N14Cert/T7.lean](Certificates/N14Cert/T7.lean) and
  [Certificates/N14Cert/T7A.lean](Certificates/N14Cert/T7A.lean): the theorems `N14Cert.T7.cap`
  and `N14Cert.T7A.thomson14 : N14.Thomson14`.
- [LeanCode/N14/Analytic/Main.lean](LeanCode/N14/Analytic/Main.lean): the analytic part,
  `N14.thomson14_of`.
- [comparator.json](comparator.json): Comparator configuration for the theorem and its
  definitions in the two showcase files.

## Repository layout

| Path | Contents |
| --- | --- |
| [Showcase.lean](Showcase.lean) | The statement of the main theorem, self-contained on the basis of Mathlib. |
| [Showcase_WithProofs.lean](Showcase_WithProofs.lean) | The same statement with its proof. |
| [Certificates](Certificates) | The numerical certificates: 615 Lean modules with exact data and the kernel checks, and in [Certificates/Source](Certificates/Source) the certificates of the paper from which they were generated, with a verifier that does not use Lean. |
| [AnalyticArguments](AnalyticArguments) | The paper (TeX and PDF), and a note on the form in which Lean verifies its analytic arguments (TeX and PDF). |
| [LeanCode](LeanCode) | The Lean code of the verification: statement, checkers, soundness theorems, analytic part. |
| [Visualization](Visualization) | The animation above, an SVG file of 48 kB, and the program that writes it. |
| [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json), [lean-toolchain](lean-toolchain) | The Lake project. They pin Lean 4.33.0 and the revision of Mathlib. |

## Building

The project uses Lean 4.33.0. The dependencies are pinned in
[lake-manifest.json](lake-manifest.json). To compile the library, the certificates and both
showcase files, run

```sh
lake exe cache get
export GLIBC_TUNABLES=glibc.malloc.hugetlb=1:glibc.malloc.top_pad=67108864:glibc.malloc.mmap_threshold=33554432:glibc.malloc.arena_max=1
LEAN_NUM_THREADS=2 lake build
```

`Showcase.lean` produces one expected `sorry` warning. `GLIBC_TUNABLES` configures the memory
allocator: without it a single module takes more than 34 GB of memory in place of 20 GB.
`LEAN_NUM_THREADS` is the number of modules compiled at a time. With these settings, a complete
build on Linux compiles 725 modules of this repository on top of Mathlib in 15 minutes. It needs
up to 36 GB of memory, and the `.lake` directory needs about 8 GB of disk space.

## Verifying the certificates without Lean

The certificates of the paper can also be verified by the programs of the paper, which use exact
rational arithmetic and interval arithmetic and do not use Lean. See
[Certificates/Source/README.md](Certificates/Source/README.md).
