"""Certify local minimality with exact rational matrix tests and Arb error bounds.

The Jet algebra in localmin_jet supplies interval Taylor coefficients.
The supplied rational quartic norm proposals are each proved over Q.
No ordinary floating-point result is accepted as a proof bound.
"""
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

from flint import arb, ctx
from exactpoly import ldl_psd
from localmin_jet import pair_jets, HS
from enclose_h import certify_candidate

ctx.prec = 200


def A(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


def rational_mid(x):
    m, e = x.mid().man_exp()
    return Q(int(m)) * Q(2) ** int(e)


def frobenius(entries):
    squares = Q(0)
    for x in entries:
        m, e = abs(x).upper().man_exp()
        bound = Q(int(m)) * Q(2) ** int(e)
        squares += bound * bound
    return A(squares).sqrt()


def pd(matrix):
    assert all(matrix[i][j] == matrix[j][i]
               for i in range(len(matrix)) for j in range(len(matrix)))
    assert ldl_psd(matrix), 'exact positive-definiteness check failed'


def certify():
    assert HS.contains(certify_candidate()), 'Taylor centre does not enclose the certified height'
    n = 25
    H = [[arb(0) for _ in range(n)] for _ in range(n)]
    cubic = {}
    for _, _, indices, jet in pair_jets(0):
        for powers, value in jet.c.items():
            degree = sum(powers)
            if degree not in (2, 3):
                continue
            ids = tuple(sorted(i for i, p in zip(indices, powers) for _ in range(p)))
            if degree == 2:
                a, b = ids
                if a == b:
                    H[a][a] += 2 * value
                else:
                    H[a][b] += value
                    H[b][a] += value
            else:
                cubic[ids] = cubic.get(ids, arb(0)) + value
    Hq = [[rational_mid(x) for x in row] for row in H]
    midpoint_lower = Q('0.0965')
    pd([[Hq[i][j] - (midpoint_lower if i == j else 0)
         for j in range(n)] for i in range(n)])
    h_error = frobenius([abs(H[i][j] - A(Hq[i][j]))
                         for i in range(n) for j in range(n)])
    mu = Q('0.0964')
    assert A(midpoint_lower - mu) > h_error
    print('Hessian: exact LDL and Arb radius prove lambda_min >= 0.0964', flush=True)

    F = [[Q(0) for _ in range(n * n)] for _ in range(n)]
    errors = []
    for ids, value in cubic.items():
        permutations = set(itertools.permutations(ids))
        mid = rational_mid(value) / len(permutations)
        error = abs(value / len(permutations) - A(mid))
        for i, j, k in permutations:
            F[i][j * n + k] = mid
            errors.append(error)
    c_mid = Q('5.039')
    FFt = [[sum((F[i][k] * F[j][k] for k in range(n * n)), Q(0))
            for j in range(n)] for i in range(n)]
    pd([[(c_mid ** 2 if i == j else 0) - FFt[i][j]
         for j in range(n)] for i in range(n)])
    b3 = Q('5.04')
    assert A(b3 - c_mid) > frobenius(errors)
    print('Cubic: exact LDL and Arb radius prove |C| <= 5.04 ||Delta||^3', flush=True)

    # The float 0.008 is slightly larger than the exact decimal; Arb's radius
    # encloses it, hence the entire box |Delta|_infinity <= 0.008 is covered.
    assert Q(float('0.008')) >= Q('0.008')
    rows = [arb(0) for _ in range(14)]
    bounds = []
    path = Path(__file__).resolve().parents[1]/'Local/local_norm_bounds.json'
    data = json.loads(path.read_text())
    assert data['format'] == 'thomson14-local-norm-bounds-v1'
    proposals = {tuple(item['pair']):Q(item['bound']) for item in data['pairs']}
    assert len(data['pairs']) == 91
    assert set(proposals) == set(itertools.combinations(range(14),2))
    assert all(q > 0 for q in proposals.values())
    for i, j, indices, jet in pair_jets(float('0.008')):
        d = max(1, len(indices))
        nn = d * d
        M = [[Q(0) for _ in range(nn)] for _ in range(nn)]
        errors = []
        for powers, value in jet.c.items():
            if sum(powers) != 4:
                continue
            ids = tuple(k for k, p in enumerate(powers) for _ in range(p))
            permutations = set(itertools.permutations(ids))
            mid = rational_mid(value) / len(permutations)
            error = abs(value / len(permutations) - A(mid))
            for a, b, c, e in permutations:
                M[a * d + b][c * d + e] = mid
                errors.append(error)
        bound = proposals[i,j]
        for sign in (-1, 1):
            pd([[(bound if a == b else 0) + sign * M[a][b]
                 for b in range(nn)] for a in range(nn)])
        total = A(bound) + frobenius(errors)
        bounds.append(total)
        rows[i] += total
        rows[j] += total
    C4 = Q(147)
    # Either inequality suffices; use the row-sum inequality, with all sums
    # still in ball arithmetic (no conversion to a machine float).
    assert all(A(C4) > 2 * row for row in rows)
    print('Quartic: 91 exact matrix tests and Arb radii prove |R4| <= 147 ||Delta||^4', flush=True)
    radius = Q('0.0075')
    margin = mu / 2 - b3 * radius - C4 * radius ** 2
    assert margin > 0 and radius < Q('0.008')
    print('Exact Taylor margin at radius 0.0075:', margin, flush=True)
    print('AUDIT LOCAL MINIMALITY VERIFIED', flush=True)


if __name__ == '__main__':
    certify()
