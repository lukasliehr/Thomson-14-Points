# LeanCode

The Lean code of the verification: the statement, the checkers with their soundness theorems, and
the analytic part of the proof. The certificates on which the checkers run are the Lean modules of
[Certificates](../Certificates).

| Path | Files | Lines | Contents |
| --- | ---: | ---: | --- |
| [N14](N14) | 65 | 19,707 | The proof for 14 points. |
| [CAP](CAP) | 40 | 10,146 | General checkers for the Lean kernel with their soundness theorems. |
| [N32](N32) | 1 | 132 | Lemmas on Gram matrices of three vectors of `ℝ³`. |
| [CAPNumeral](CAPNumeral) | 1 | 75 | The notation `hex% "…"` for large natural numbers. |

## How a computational statement is verified

A *checker* is a function with values in `Bool` that computes with natural numbers. Its
*soundness theorem* states what follows mathematically if the checker returns `true`. A module of
[Certificates](../Certificates) contains data and the theorem `checker data = true`, which the
Lean kernel proves by evaluating the checker (`decide +kernel`).

The checkers are the files `Kernel.lean`, `MasterKernel.lean`, `QuadKernel.lean`,
`KerVecKernel.lean` and `BernKernel.lean` of the folders below. They import no file of Mathlib, so
that a module with data loads in a fraction of a second. The file
[N14/Energy/Kernel.lean](N14/Energy/Kernel.lean) is not a checker: it concerns the kernels of the
three-point bound.

No file uses `native_decide` or `sorry`. The files [N14/Box/Audit.lean](N14/Box/Audit.lean) and
[N14/Box/AuditMaster.lean](N14/Box/AuditMaster.lean) test during the build that the soundness
theorems of the largest checker depend on the axioms `propext`, `Classical.choice` and
`Quot.sound` only.

## The folder N14

| Path | Contents |
| --- | --- |
| [Statement.lean](N14/Statement.lean) | The theorem as a proposition, `N14.Thomson14`, in coordinates `Fin 14 → Fin 3 → ℝ`. It imports Mathlib only. |
| [Interface.lean](N14/Interface.lean) | `N14.T7.CAP`: the statements that the proof takes from its certificates. |
| [Basic.lean](N14/Basic.lean), [Candidate.lean](N14/Candidate.lean), [Nodes.lean](N14/Nodes.lean), [Rigid.lean](N14/Rigid.lean) | Coordinates and Euclidean space; the inner products and the energy of the family `X(h)`; distances to the triple types of the candidate; constants of the rigidity lemma. |
| [Box](N14/Box) | The sign of a slack function on its domain: polynomial lower bounds in one variable, boxes with trees of bisections in the Bernstein form, a cover of the cube. Soundness: `N14.Box.run_sound_master`. |
| [Ident](N14/Ident) | The identity that expresses the energy by the slack functions of a certificate. Soundness: `id3_sound`, `id1_sound`. |
| [Energy](N14/Energy) | From positive semidefinite matrices, the identity and the sign of the slack functions to a lower bound for the energy of a configuration, for certificates with one and with two types of points. |
| [Jet](N14/Jet), [Local](N14/Local) | The expansion of the energy at the candidate in 25 coordinates, with bounds for its forms of degree two, three and four (`N14.Local.Local7`). |
| [Analytic](N14/Analytic) | The analytic part: `N14.thomson14_of : N14.T7.CAP → N14.Thomson14`. It is described in [AnalyticArguments/lean_proof.pdf](../AnalyticArguments/lean_proof.pdf). |

## The folder CAP

| Path | Contents |
| --- | --- |
| [Core](CAP/Core) | Vectors and polynomials as packed natural numbers; a lemma on sums over pairs. |
| [PSD](CAP/PSD) | Positive definiteness of a symmetric matrix with integer entries. |
| [UniPos](CAP/UniPos) | A polynomial lower bound for `(2 - 2x)^(-1/2)` on an interval. |
| [Subdivision](CAP/Subdivision) | The sign of a polynomial in three variables on a box, by the Bernstein form. |
| [Interval](CAP/Interval), [Root](CAP/Root) | Ball arithmetic for programs with square roots; a unique zero of a function of one variable. They verify the stationary height. |
| [Schema/ThreePoint](CAP/Schema/ThreePoint) | The three-point bound on the sphere: kernels and their positivity. |
| [Transport](CAP/Transport) | The name under which the certificate modules import `hex%`. |

`hex% "1f"` denotes the same natural number as `0x1f` and is read in time that is linear in its
length up to a logarithmic factor. The reader is an elaborator, which Lake compiles to native
code; it only produces a numeral, and the kernel checks every theorem about that numeral.

## Names in the comments

The files were developed in a repository that contains the verification of several theorems, and
their comments use its names.

| Name | Meaning |
| --- | --- |
| `T7` | The theorem for 14 points. |
| the source | The paper [AnalyticArguments/thomson14.pdf](../AnalyticArguments/thomson14.pdf) with its verification package [Certificates/Source](../Certificates/Source). Lemmas and propositions are cited with its numbers. |
| statements 1 to 8 | The eight computational statements of the paper: the stationary height; positive semidefinite matrices; the energy identity; the sign of the slack functions; the estimates near the triple types of the candidate; the geometry of the candidate; local minimality; closure. |
| `E2`, `E11`, … | Kinds of checkers of the library, for example `E2` for positive semidefiniteness. |
| `N14Cert`, generated modules | The modules of [Certificates](../Certificates). |
| `N14/README.md`, `N14/py/…`, `caps/…`, `certgen/…`, the write-up | Documents and programs of the development repository, which are not part of this repository. |

## Differences from the development repository

This folder contains the files of the development repository that the proof imports. Three of
them were changed, so that files of other proofs are not needed here.

* [N14/Candidate.lean](N14/Candidate.lean) imported a file of another proof for one lemma on sums
  over pairs. The lemma is now `CAP.sum_fin_pairs` in
  [CAP/Core/PairSum.lean](CAP/Core/PairSum.lean), and `Candidate.lean` imports that file and two
  files of Mathlib. [N14/Analytic/Critical.lean](N14/Analytic/Critical.lean) uses the lemma under
  its new name.
* [N32/Gram.lean](N32/Gram.lean) imported the statement of a theorem for 32 points, which it does
  not use. It now imports the two files of Mathlib that this statement imported.
