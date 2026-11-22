# Certificates

The numerical certificates of the proof, in two forms.

| Path | Contents |
| --- | --- |
| [N14Cert](N14Cert), [Height.lean](Height.lean), [HeightSound.lean](HeightSound.lean) | The certificates as 615 Lean modules: exact data, the evaluations of the checkers in the Lean kernel, and the theorems that follow. These modules are the library `N14Cert` of the [lakefile](../lakefile.toml), and `lake build` compiles them. |
| [Source](Source) | The certificates from which the Lean modules were generated: exact rational data in JSON, with the programs that verify them without Lean. `lake build` does not read this folder. |

## The Lean modules

Every computational statement of the proof is verified by a checker, a function with values in
`Bool` whose soundness theorem is proved in [LeanCode](../LeanCode). A module of this folder
contains data as numerals and theorems of the form `checker data = true`, which the Lean kernel
proves by evaluation (`by decide +kernel`, 2504 times in total). The statement modules apply the
soundness theorems to them. No module uses `native_decide` or `sorry`.

| Modules | Statement | Certificate in `Source/Certificates` |
| --- | --- | --- |
| `Height.lean`, `HeightSound.lean`, `N14Cert/Height/Star.lean` | The stationary height and the energy of the candidate (Lemma 1.1 of the paper) | none; the paper computes them in `common/enclose_h.py` |
| `N14Cert/Case0Pos`, `Case0Close`, `Case0Id` | Case 0: two points with inner product at least 0.8 | `Case0_separation_T0.8_D16` |
| `N14Cert/Case1`, `Case1Id` | Case I: all inner products at least −0.98 | `CaseI_a-0.98_D40` |
| `N14Cert/Case2Ppr`, `Case2Prr`, `Case2Rrr`, `Case2Id` | Case II: the smallest inner product in [−0.99, −0.98] | `Slab_m099_m098` |
| `N14Cert/CapPpr`, `CapPrr`, `CapRrr`, `CapId`, and `LocalN<NN>`, `AnnN<NN>`, `CoreN<NN>` for the 22 nodes `NN` | Case III: the smallest inner product at most −0.99, with the estimates near the 22 triple types of the candidate | `CaseIII_cap_D20` |
| `N14Cert/Geom.lean` | The nine inner products of the candidate, their separation, the list of the nodes | the list `nodes` of `CaseIII_cap_D20/certificate.json` |
| `N14Cert/Local` | The expansion of the energy at the candidate in 25 coordinates (Proposition 9.1 of the paper) | the numbers `q_ij` of `Local/local_norm_bounds.json` |
| `N14Cert/T7.lean` | All of the above as one theorem: `N14Cert.T7.cap : N14.T7.CAP` | |
| `N14Cert/T7A.lean` | The theorem for 14 points: `N14Cert.T7A.thomson14 : N14.Thomson14` | |

The first five rows of `N14Cert` consist of 74 *runs*. A run proves that a slack function of a
certificate is nonnegative on a domain of triples of inner products. Its folder contains

* `Run.lean`: the data of the run, among them the coefficients of the slack function;
* `Tables<t>.lean` and `Cells<g>.lean`: polynomial lower bounds in one variable, and boxes with
  trees of bisections, each with the theorem that the checker accepts it;
* `Slack.lean`: the theorem `slack_nonneg` of the run.

The folders `Case0Id`, `Case1Id`, `Case2Id` and `CapId` contain the positive semidefinite matrices
of the four certificates, the identity that expresses the energy by the slack functions, and the
resulting lower bound for the energy of a configuration (`energy_ge`).

The statement modules `Slack.lean`, `Energy.lean`, `T7.lean` and `T7A.lean` end with a test of the
axioms of their theorem (`#guard_msgs in #print axioms`), which fails the build if the theorem
depends on anything but `propext`, `Classical.choice` and `Quot.sound`.

### How the modules were generated

The certificates of the paper contain the slack functions and no trees: its verifier searches
while it verifies. Programs of the development repository of this project read the files of
[Source/Certificates](Source/Certificates), search the tables, the boxes and the trees in
floating-point arithmetic, and write the Lean modules. Nothing of this conversion is trusted: the
Lean kernel checks every module, and the identity between the numerals of a run and the slack
function of its certificate is one of the kernel checks. The programs are not part of this
repository.

The modules are as the programs wrote them, with one change: every definition of data is marked
`noncomputable`. Lean then generates no code for it. Without the mark, `lake build` writes the
numerals into C files in decimal notation, which takes about a minute for a module with a megabyte
of numerals. The mark does not change the definitions or the proofs.

## The certificates of the paper

[Source](Source) is a copy of the verification package of the paper
([AnalyticArguments/thomson14.pdf](../AnalyticArguments/thomson14.pdf)), without changes. Its
[README](Source/README.md) describes the files and the verification without Lean
(`bash verify.sh 4` in the folder `Source`, with Python 3.13, python-flint and g++). The paths in
that README are relative to `Source`. The package contains the paper a second time, because its
list of checksums covers it.
