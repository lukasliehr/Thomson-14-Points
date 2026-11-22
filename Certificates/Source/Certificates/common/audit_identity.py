"""Independent coefficientwise energy-identity checks over Q.

Build kernels directly from their matrices. Add the distinct-triple kernels
to the archived slack polynomials; all mixed monomials must cancel. Then
count the remaining one-edge terms and all constants. No sampled identity
or optimiser model is used to establish these identities.
"""
import itertools
import math
from fractions import Fraction as Q
from pathlib import Path

from certificate_io import load_certificate
from flint import fmpq, fmpq_mat
from exactpoly import padd, pscale, pmul, var, ONE, cheb_poly, permute, ldl_psd

ROOT = Path(__file__).resolve().parents[2]
CERT = ROOT / 'Certificates'
ZERO = (0, 0, 0)


def pd(M):
    assert all(M[i][j] == M[j][i] for i in range(len(M)) for j in range(len(M)))
    assert ldl_psd(M), 'non-positive kernel block'


def fm(M):
    return fmpq_mat([[fmpq(x.numerator, x.denominator) for x in row] for row in M])


class Kernels:
    def __init__(self, blocks, sizes):
        self.blocks = blocks
        self.sizes = sizes
        self.K = max(k for _, k in blocks)
        self.T = [cheb_poly(self.K, a) for a in range(3)]
        u, v, t = [var(a) for a in range(3)]
        self.q = [ONE, padd(t, pscale(pmul(u, v), -1))]
        s2 = pmul(padd(ONE, pscale(pmul(u, u), -1)),
                   padd(ONE, pscale(pmul(v, v), -1)))
        for k in range(2, self.K + 1):
            self.q.append(padd(pscale(pmul(self.q[1], self.q[-1]), 2),
                               pscale(pmul(s2, self.q[-2]), -1)))
        self.cache = {}

    def block(self, root, k, a, b):
        sizes = self.sizes(root, k)
        oa, ob = sum(sizes[:a]), sum(sizes[:b])
        F = self.blocks[root, k]
        assert len(F) == sum(sizes)
        return [[F[oa+i][ob+j] for j in range(sizes[b])] for i in range(sizes[a])]

    def kernel(self, root, a, b):
        key = root, a, b
        if key not in self.cache:
            ans = {}
            for k in range(self.K + 1):
                F = self.block(root, k, a, b)
                base = {}
                for i, row in enumerate(F):
                    for j, value in enumerate(row):
                        if value:
                            base = padd(base, pscale(pmul(self.T[0][i], self.T[1][j]), value))
                ans = padd(ans, pmul(base, self.q[k]))
            self.cache[key] = ans
        return self.cache[key]

    def gm(self, root, other):
        # K_x(y,y) + 2 K_x(x,y), written as a polynomial in <x,y>.
        result = {}
        omt = padd(ONE, pscale(pmul(var(0), var(0)), -1))
        power = ONE
        for k in range(self.K + 1):
            F = self.block(root, k, other, other)
            B = {}
            for i, row in enumerate(F):
                for j, value in enumerate(row):
                    if value:
                        B = padd(B, pscale(pmul(self.T[0][i], self.T[0][j]), value))
            result = padd(result, pmul(B, power))
            power = pmul(power, omt)
        F = self.block(root, 0, root, other)
        for j in range(len(F[0])):
            result = padd(result, pscale(self.T[0][j], 2 * sum(row[j] for row in F)))
        return result

    def sing(self, root):
        return sum(sum(row) for row in self.block(root, 0, root, root))


def identity(name, blocks, sizes, counts, slacks, e, factor):
    kernels = Kernels(blocks, sizes)
    residual = {}
    pattern_counts = {}
    for pat, (P, weights) in slacks.items():
        # Exact pattern symmetry of both polynomial and singular parts.
        for pm in itertools.permutations(range(3)):
            if any(pat[pm[i]] != pat[i] for i in range(3)):
                continue
            edges = {(0, 1): 0, (0, 2): 1, (1, 2): 2}
            edge_map = tuple(edges[tuple(sorted((pm[i], pm[j])))] for i, j in edges)
            assert permute(P, edge_map) == P, (name, pat, 'symmetry')
            assert sorted((edge_map[i], w) for i, w in weights) == sorted(weights)
        S = P
        for root, a, b, permutation in [(0, 1, 2, (0, 1, 2)),
                                       (1, 0, 2, (0, 2, 1)),
                                       (2, 0, 1, (1, 2, 0))]:
            K = kernels.kernel(pat[root], pat[a], pat[b])
            S = padd(S, pscale(permute(K, permutation), 2))
        assert all(sum(x > 0 for x in exponent) <= 1 for exponent in S), (name, pat, 'mixed terms')
        residual[pat] = S, dict(weights)
        mult = 1
        for a, count in enumerate(counts):
            mult *= math.comb(count, pat.count(a))
        pattern_counts[pat] = mult
    constants = sum(pattern_counts[p] * S.get(ZERO, Q(0)) for p, (S, _) in residual.items())
    for a in range(len(counts)):
        for b in range(a, len(counts)):
            number = math.comb(counts[a], 2) if a == b else counts[a] * counts[b]
            if not number:
                continue
            pairpoly = padd(kernels.gm(a, b), kernels.gm(b, a))
            constants += number * pairpoly.pop(ZERO, Q(0))
            phi = Q(0)
            for c, count in enumerate(counts):
                multiplicity = count - (c == a) - (c == b)
                if not multiplicity:
                    continue
                pat = tuple(sorted((a, b, c)))
                labels = list(pat)
                i = labels.index(a)
                j = next(j for j in range(3) if j != i and labels[j] == b)
                slot = {(0, 1): 0, (0, 2): 1, (1, 2): 2}[tuple(sorted((i, j)))]
                S, weights = residual[pat]
                for exponent, value in S.items():
                    if exponent[slot] and sum(exponent) == exponent[slot]:
                        degree = exponent[slot]
                        key = (degree, 0, 0)
                        pairpoly[key] = pairpoly.get(key, Q(0)) + multiplicity * value
                phi += multiplicity * weights.get(slot, Q(0))
            assert not any(pairpoly.values()), (name, (a, b), 'pair identity')
            assert phi == factor, (name, (a, b), phi)
    constants += sum(count * kernels.sing(a) for a, count in enumerate(counts))
    assert constants == -factor * e, (name, 'constant identity')
    print(name, ': EXACT coefficientwise energy identity and all symmetries VERIFIED', flush=True)


def main():
    directories = [('case0','Case0_separation_T0.8_D16'),
                   ('case1','CaseI_a-0.98_D40'), ('case2','Slab_m099_m098'),
                   ('cap','CaseIII_cap_D20')]
    for name,directory in directories:
        data = load_certificate(CERT/directory/'certificate.json')
        assert data['case'] == name
        K = data['D']//2
        if name == 'cap':
            assert set(data['F']) == {(r,k) for r in range(2) for k in range(11)}
            for key,G in data['G'].items():
                pd(G)
                N = fm(data['N'][key])
                assert N*fm(G)*N.transpose() == fm(data['F'][key]), (key,'factorisation')
            sizes = lambda root,k: [min(11-k,2),11-k] if root == 0 else [11-k,11-k]
        else:
            roots = 1 if name in ('case0','case1') else 2
            assert set(data['F']) == {(r,k) for r in range(roots) for k in range(K+1)}
            for F in data['F'].values():
                pd(F)
            sizes = (lambda root,k: [K-k+1]) if roots == 1 else (lambda root,k: [11-k,11-k])
        identity(name,data['F'],sizes,data['counts'],data['slacks'],data['e'],data['factor'])
    print('Cap: all 22 rational G blocks PD and F = N G N^T exactly',flush=True)
    print('AUDIT ALL IDENTITIES VERIFIED',flush=True)


if __name__ == '__main__':
    main()
