# Thomson problem for 14 points

This repository contains an analytic and computer-assisted proof that the bicapped hexagonal antiprism with the certified stationary height is the unique minimizer, up to orthogonal transformations, of

$$
E(X)=\sum_{1\le i<j\le14}\frac{1}{|x_i-x_j|},\qquad x_i\in\mathbb S^2.
$$

The minimum energy is enclosed around `69.306363296626421258489991276382007864282129573759`, with radius `1e-49`. The proof combines exact rational three-point certificates, outward-rounded interval verification, geometric rigidity and a quantitative local minimum estimate.

- [Paper (PDF)](paper/thomson14.pdf)
- [Paper (TeX)](paper/thomson14.tex)
- [Exact certificate format and verifier inputs](Certificates/FORMAT.md)
- [Verification source](Certificates/common/)
- [Reference verification results](results/reference/)

## Reproduce the proof computations

The reference environment is **Linux x86_64, Python 3.13.5, python-flint 0.9.0, and g++ 14.2.0 with OpenMP**. Install Python with virtual-environment support and g++ with OpenMP using your operating system's package manager. Bash and standard command-line utilities, including `sha256sum`, are required. TeX is needed only to rebuild the PDF. The verification needs no numerical optimization or eigensolver package.

From this repository's root directory:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
PYTHON="$PWD/.venv/bin/python" bash verify.sh 4
```

Use Python 3.13.5 for the reference reproduction; check it with `python3 --version` before creating the environment. The argument `4` selects four OpenMP threads; integers from 1 through 8 are supported. BLAS is limited to one thread. Each verification process has a virtual-memory limit of 8,000,000 KiB. Allow several hundred MB of disk space for regenerated inputs. The run takes several minutes, depending on the machine.

The only successful final result is:

```text
Verified runs: 31 boxes: 2903200
AUDIT CLOSURE VERIFIED
FULL PROOF VERIFIED
```

The script checks the release hashes, verifies the analytic bounds and exact identities, regenerates every required numerical input from the JSON certificates, compiles both interval verifiers, reruns all 31 calculations, and checks their mathematical closure. It does not use the supplied reference logs to decide success.

New files go under `build/`: `work/regen/` contains regenerated inputs, `bin/` the compiled verifiers, and `logs/` the results. The full console transcript is `build/logs/full_verification.txt`. The marker `build/logs/FULL_PROOF_VERIFIED` is removed at startup and written only after every stage succeeds. An assertion failure, unresolved cell, input mismatch, arithmetic failure or resource limit is a failed reproduction. Python assertions must remain enabled; `verify.sh` enforces this.

The rational local coordinate changes and quartic norm-bound proposals are included in the JSON data. Their required properties are checked exactly or with outward interval bounds. Reproduction therefore does not depend on regenerating numerical eigenvectors. The regenerated root inputs must match the supplied reference files exactly. Do not ignore a mismatch or replace the reference files merely to obtain a successful result. The reference run uses a fresh virtual environment containing only the pinned `python-flint` dependency.

To check file integrity alone:

```bash
sha256sum -c SHA256SUMS
```

This checks file identity, not the mathematical proof. Run `verify.sh` for the latter. The manifest covers all supplied release files except itself; generated `build/` files are excluded.

## Proof-to-certificate map

All paths in the second column are relative to `Certificates/`. Each listed case directory contains an exact `certificate.json` and the problem/root files used by the verifiers.

| Paper statement | Data or checker | Role |
|---|---|---|
| Lemma 1.1 | `common/enclose_h.py` | Existence and enclosure of the stationary height and energy |
| Proposition 3.2 and the untyped identity in Section 5 | `common/audit_identity.py`, all four JSON certificates | Exact PSD checks, kernel identities, weights, multiplicities and symmetries |
| Proposition 5.2: Case 0 | `Case0_separation_T0.8_D16/` | Excludes any pair with inner product at least 0.8 |
| Proposition 5.1: Case I | `CaseI_a-0.98_D40/` | Excludes minimum inner product at least -0.98 |
| Section 6: Case II | `Slab_m099_m098/` | Excludes the slab from -0.99 to -0.98 |
| Theorem 1.5 and Section 7: Case III | `CaseIII_cap_D20/`, `common/prep_local3.py` | Cap positivity, inner-node estimates, local coverage and quantitative tubes |
| Lemmas 7.2, 7.3 and 8.1 | `common/audit_geometry.py` | Complete candidate node list, class separation and rigidity constants |
| Proposition 9.1 | `Local/local_norm_bounds.json`, `common/audit_local.py`, `common/localmin_jet.py` | Strict local minimality in the 25 gauge coordinates |
| Theorem 1.2: final implication | `common/audit_closure.py` and the analytic arguments in the paper | Joins every region and checks the final margins |

The case cutoffs and slack thresholds have the precise binary64 conventions stated in the paper. Every other terminating decimal used as an exact proof constant denotes a rational number.

## Verification results

The reference run verifies **31 branch-and-bound calculations and 2,903,200 cells**, with zero failed cells or reported counterexamples.

| Calculation | Runs | Cells |
|---|---:|---:|
| Case 0, nonnegative slack | 1 | 29,287 |
| Case 0, close-pair threshold | 1 | 10,041 |
| Case I | 1 | 376,059 |
| Case II, PPR | 1 | 53,303 |
| Case II, PRR | 1 | 219,381 |
| Case II, RRR | 1 | 76,285 |
| Cap, local nodes | 22 | 498,434 |
| Cap, global PPR | 1 | 533,876 |
| Cap, global PRR | 1 | 630,673 |
| Cap, global RRR | 1 | 475,861 |
| **Total** | **31** | **2,903,200** |

The exact and interval checks also establish:

- Every cap slack is nonnegative; the positive thresholds away from the candidate nodes force a tube radius below `1.95e-4`.
- The rigidity estimate gives coordinate distance at most `23 * 1.95e-4 = 0.004485`.
- Strict local minimality holds through Euclidean radius `0.0075`, since the Taylor bracket there is the positive rational `341/160000`.
- Thus every configuration with energy at most the candidate's energy is an orthogonal image of the candidate.

The rational cap certificate is not assumed to satisfy exact interpolation equations at its approximate nodes. Its actual constant and linear residuals are included in the verified estimates. Every ball omitted by a global run is covered by a checked local region. No unverified region is discarded.

## What must be trusted and reviewed

This is a conventional analytic and computer-assisted proof. The analytic argument is in the paper; its numerical premises are established by the supplied programs. The computational trust boundary consists of the reviewed verification algorithms, Python exact integer/rational arithmetic, FLINT/Arb, the compiler and its execution platform. The C++ verifiers require IEEE binary64 round-to-nearest arithmetic with correctly rounded basic operations and square root. They are compiled with `-ffp-contract=off -fno-fast-math`, and all interval operations enlarge their bounds outward.

The exact matrices, polynomials, local coordinate changes and norm proposals are supplied directly as rational JSON data. Every proposal is validated before use. Floating-point optimization, sample tests and the search that produced the certificates are not premises of the proof and are not required to reproduce it.

Reproduction verifies the stated computational claims; mathematical review must also assess the analytic implications and the implementations of the bounds and domain cuts. The repository does not claim formal proof-assistant verification or external peer-review acceptance.

## Rebuild the paper

With a TeX installation containing the packages listed in the preamble:

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error thomson14.tex
pdflatex -interaction=nonstopmode -halt-on-error thomson14.tex
```

Rebuilding a PDF may change its bytes and therefore its checksum, even without a mathematical change. Preserve a clean checkout when reproducing the recorded release hashes.

## Repository contents

Only the paper, exact proof data, compressed reference inputs, verification sources, reference results and reproduction metadata are included. Search experiments, superseded certificates, generated binaries, virtual environments and development notes are excluded. Everything needed by the verification is in this repository; it has no dependency on an external working directory or service.

No author name or license is assigned in this release.
