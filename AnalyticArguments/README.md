# AnalyticArguments

The analytic arguments of the proof.

| File | Contents |
| --- | --- |
| [thomson14.pdf](thomson14.pdf), [thomson14.tex](thomson14.tex) | The paper: *The Thomson problem for N = 14: the bicapped hexagonal antiprism is optimal*. It contains the proof with all analytic arguments and describes the certificates. |
| [lean_proof.pdf](lean_proof.pdf), [lean_proof.tex](lean_proof.tex) | The proof in the form that Lean verifies: the theorem, the statements that Lean takes from the certificates, the analytic statements with the names of their Lean theorems, and the three arguments that differ from those of the paper. |

The paper states that it makes no claim of formal verification. This repository adds that
verification.

The three arguments of the Lean proof that differ from the paper are the following.

* The rigidity lemma (Lemma 8.1) is proved for the one radius that the proof uses.
* The points of the two hexagons are matched with those of the candidate by assigning to each
  point one of eleven directions; the paper orders the points on a circle and sums the gaps.
* That the candidate is a critical point of the energy follows from the convexity of
  `t ↦ (2 - 2t)^(-1/2)` and a finite identity; the paper uses the symmetry group of the candidate.
