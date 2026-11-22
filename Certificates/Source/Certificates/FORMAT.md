# Exact certificate and verifier input formats

The coordinates of a triple are ordered as `u=<x0,x1>`, `v=<x0,x2>`, `t=<x1,x2>`. The Gram constraint is `G=1+2uvt-u^2-v^2-t^2 >= 0`. Type 0 denotes a pole in the P/R partition; type 1 denotes one of the other twelve points. The untyped certificates use type 0 for all fourteen points.

## Exact JSON data

Every case directory contains `certificate.json`, read by `common/certificate_io.py` using the Python standard JSON parser and `fractions.Fraction`. These files contain no executable object serialization and no floating-point polynomial or matrix coefficients.

| Field | Meaning |
|---|---|
| `format` | `thomson14-certificate-v1` |
| `case` | `case0`, `case1`, `case2`, or `cap` |
| `D` | Total polynomial degree: 16, 40, 20, or 20 |
| `e` | Exact energy offset as a rational string |
| `counts` | Type cardinalities: `[14]` or `[2,12]` |
| `factor` | Energy identity normalization: 4 for untyped cases, 1 for typed cases |
| `F` | Kernel matrix blocks, each with `root`, `k`, and `matrix` |
| `slacks` | One record per pattern, containing `pattern`, `polynomial`, and `weights` |
| `G`, `N` | Cap only: rational blocks satisfying `F = N G N^T`; each `G` is proved positive definite |
| `nodes` | Cap only: the complete ordered list of 69 node types, with `pattern` and three rational `coordinates` |
| `local_coordinates` | Cap only: 22 rational coordinate proposals, indexed by `node`, validated by `prep_local3.py` |

A rational is a canonical string such as `"7"`, `"-3/5"`, or `"0"`. A matrix is a row-major array of arrays of such strings. A polynomial row `[a,b,c,q]` represents `q*u^a*v^b*t^c`, with nonnegative integer exponents. A weight row `[i,w]` represents `w*(2-2*x_i)^(-1/2)`, where `x_0=u`, `x_1=v`, and `x_2=t`. Thus the slack is the stored polynomial plus these Coulomb terms.

Block `k` is the angular degree in the recurrence for `Q_k` in Section 3. In the untyped cases its basis is `T_0,...,T_(D/2-k)`. In the slab both type blocks use `T_0,...,T_(10-k)`. In the cap, a type-0 root has type-block sizes `min(11-k,2)` and `11-k`; a type-1 root has sizes `11-k` and `11-k`. The full matrix groups the basis first by type and then by Chebyshev degree.

`common/audit_identity.py` checks the energy identity directly from these matrices and polynomials, including the factor, constant offset and every relabelling symmetry. The positive-definiteness tests use exact rational arithmetic. The schema reader also checks the required case parameters, pattern list, unique indices and positive Coulomb weights.

The rational node centres approximate the true candidate types. Their order is retained so that `nXX` denotes entry `XX` of the 69-element list, numbered from zero. The 22 fundamental-domain entries used by the local calculations are:

```text
00 02 03 04 05 06 07 11 12 13 14 15 16 17 19 25 26 34 36 44 48 56
```

Each local-coordinate proposal contains a `matrix` M, three `semiaxes`, a proposed operator `norm_bound`, and nonnegative `gram_multiplier` and `edge_multiplier` for the inner-node estimate. The `kind` (`int`, `bnd`, or `edge`) selects which terms are used. These fields are proposals only: exact matrix tests prove the norm and containment properties, and the full rational/interval node estimate must pass. The edge multiplier is used only for the PPR pattern, where `u+1 >= 0` is a valid domain inequality.

`Local/local_norm_bounds.json` has format tag `thomson14-local-norm-bounds-v1` and a `pairs` list. Each entry contains a pair `[i,j]`, with `0 <= i < j < 14`, and a positive rational `bound`. All 91 pairs must occur exactly once. In `audit_local.py`, the proposed bound q is accepted only after exact positive-definiteness tests on `q I + M` and `q I - M`, where M is the rational midpoint of the flattened fourth-order coefficient tensor. The Arb radius is then added to obtain a rigorous pair bound. The row-sum estimate in Proposition 9.1 proves the final quartic constant. No eigensolver is called during reproduction.

## Global verifier problems

The global problem file has suffix `_ts.txt`. Fields are whitespace separated:

```text
D
number_of_Coulomb_terms
variable_index weight_lower weight_upper       # repeated for each term
number_of_cuts
kind i j value                                # repeated for each cut
minimum_half_width
[threshold]
[number_of_excluded_balls
 cx cy cz radius                              # repeated for each ball
 number_of_include_balls
 cx cy cz radius]                             # repeated for each ball
```

Cut kinds are 0: `x_i >= value`; 1: `x_i <= value`; 2: `x_i >= x_j`. An omitted threshold is zero. A cell is omitted as inside an excluded ball only after its entire enclosing box is proved contained in that ball. The closure checker verifies that all excluded balls are covered by the local node calculations.

The supplied cap problem files retain include balls of infinite radius from the reference input format. Their union is the whole space. Regeneration writes zero include balls, which has exactly the same meaning; `audit_closure.py` checks this equivalence and all other fields. No bounded include region is used in this proof.

## Local verifier problems

The local problem file also has suffix `_ts.txt`, with format:

```text
D
epsilon threshold y_theta y_in has_Gram
s0 s1 s2
number_of_cuts
a0 a1 a2 b                                    # repeated for each cut
minimum_half_width
```

The local region is the ellipsoid `sum(y_i^2/s_i^2) <= 1`, with `x = node + M*y`. `epsilon` is an outward bound on the Taylor approximation error. The inner ball of radius `y_in` is justified by the exact/interval node estimate in `prep_local3.py`. `y_theta` controls whether a cell is tested at the positive threshold or at zero; the verifier records an outward norm bound `y_tube` for cells accepted only at zero. Affine cuts mean `a.y+b >= 0`; their coefficients and constants are rounded conservatively.

The matrix `M`, exact node bounds and containment tests are regenerated and checked in `prep_local3.py`. The intermediate summary under `build/work/regen/local/` is generated locally, then consumed by `audit_closure.py`; it is not a supplied proof input.

## Root Taylor data

Every `_roots.txt.xz` file is an XZ-compressed text file. After decompression:

```text
number_of_roots
c0 c1 c2 r0 r1 r2
coefficient_lower coefficient_upper            # one per monomial
...
```

The block repeats for each root. There are `binomial(D+3,3)` monomials, ordered by the loops `a=0..D`, `b=0..D-a`, `c=0..D-a-b`. Coefficients are Taylor coefficients at the stored centre, so the monomial variables are displacements from that centre. A local root has a second complete coefficient block for the Gram polynomial when `has_Gram=1`.

In the global files the polynomial is the slack's polynomial part; the verifier handles the Coulomb terms separately. In local files it is the rational Taylor approximation to the whole slack, and the stated approximation error is subtracted when forming a lower bound.

Each decimal in a verifier file is parsed as a binary64 number. Interval endpoints are constructed by directed rational-to-binary64 conversion; root radii enclose the original exact cells. Children track centre-rounding errors explicitly. The full reproduction regenerates all root files from the exact JSON data and requires byte-for-byte agreement with these decompressed reference files.

## Results

`RESULT VERIFIED` in one branch-and-bound log certifies only that calculation. The complete proof also requires the exact identities, inner-node estimates, local/global coverage, rigidity, local minimality and final rational comparisons. `verify.sh` runs all of them and writes `FULL PROOF VERIFIED` only when the complete chain succeeds.

The reference logs in `results/reference/` are evidence of a completed run, not inputs used to establish positivity. SHA256 hashes identify the files; they do not replace the arithmetic verification or mathematical review.
