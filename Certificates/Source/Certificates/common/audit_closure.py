"""Join the certificate checks and B&B results with exact rational margins.

Checks the complete expected run list, byte-for-byte root regeneration,
problem parameters, local/global coverage, and the final tube inequality.
"""
from certificate_io import load_certificate
import hashlib
import lzma
import pickle
import re
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'Certificates'
A = ROOT / 'build'
R = A / 'work/regen'


def digest(path, compressed=False):
    h = hashlib.sha256()
    opener = lzma.open if compressed else open
    with opener(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.digest()


def roots_match(new, old):
    assert digest(new) == digest(old, True), (new, 'root data mismatch')


def tokens(path):
    return Path(path).read_text().split()


def global_problem(path):
    t = iter(tokens(path))
    D = int(next(t))
    nphi = int(next(t))
    phi = [(int(next(t)), Q(float(next(t))), Q(float(next(t)))) for _ in range(nphi)]
    nc = int(next(t))
    cuts = [(int(next(t)), int(next(t)), int(next(t)), Q(float(next(t)))) for _ in range(nc)]
    width = Q(float(next(t)))
    rest = list(t)
    if not rest:
        return D, phi, cuts, width, Q(0), [], []
    t = iter(rest)
    threshold = Q(float(next(t)))
    rest = list(t)
    if not rest:
        return D, phi, cuts, width, threshold, [], []
    t = iter(rest)
    excluded = [tuple(Q(float(next(t))) for _ in range(4)) for _ in range(int(next(t)))]
    rest = list(t)
    if not rest:
        return D, phi, cuts, width, threshold, excluded, []
    t = iter(rest)
    included = [tuple(float(next(t)) for _ in range(4)) for _ in range(int(next(t)))]
    assert not list(t)
    return D, phi, cuts, width, threshold, excluded, included


def result(label, local=False):
    lines = (A / f'logs/verified_{label}.txt').read_text().splitlines()
    lines = [s for s in lines if s.startswith('RESULT ')]
    assert len(lines) == 1 and lines[0].startswith('RESULT VERIFIED '), label
    fields = dict(re.findall(r'(\w+)=([^ ]+)', lines[0]))
    assert int(fields['failed']) == 0
    if not local:
        assert int(fields['counterexamples']) == 0
    return fields


def check():
    run_count = 0
    box_count = 0
    for name in ('pos', 'close'):
        d = result('case0_' + name)
        run_count += 1
        box_count += int(d['boxes'])
        assert tokens(R/f'case0_{name}_ts.txt') == tokens(C/f'Case0_separation_T0.8_D16/case0_{name}_ts.txt')
    roots_match(R/'case0_roots.txt', C/'Case0_separation_T0.8_D16/case0_roots.txt.xz')
    d = result('case1')
    run_count += 1
    box_count += int(d['boxes'])
    roots_match(R/'case1_roots.txt', C/'CaseI_a-0.98_D40/v3t98_roots.txt.xz')
    assert tokens(R/'case1_ts.txt') == tokens(C/'CaseI_a-0.98_D40/v3t98_ts.txt')
    for p in ('PPR', 'PRR', 'RRR'):
        d = result('case2_' + p)
        run_count += 1
        box_count += int(d['boxes'])
        roots_match(R/f'case2_{p}_roots.txt', C/f'Slab_m099_m098/s1_D20_{p}_roots.txt.xz')
        assert tokens(R/f'case2_{p}_ts.txt') == tokens(C/f'Slab_m099_m098/s1_D20_{p}_ts.txt')
    summary = pickle.load(open(R/'local/summary_all.pkl', 'rb'))
    expected = {int(p.name[1:3]) for p in (C/'CaseIII_cap_D20/local').glob('n*_ts.txt')}
    assert set(summary) == expected and len(expected) == 22
    tube = Q(0)
    for ni, s in sorted(summary.items()):
        label = f'n{ni:02d}'
        assert s['ok'] and s['node_lemma'] and all(s['chk'])
        roots_match(R/f'local/{label}_roots.txt', C/f'CaseIII_cap_D20/local/{label}_roots.txt.xz')
        assert tokens(R/f'local/{label}_ts.txt') == tokens(C/f'CaseIII_cap_D20/local/{label}_ts.txt')
        d = result('cap_' + label, True)
        run_count += 1
        box_count += int(d['boxes'])
        # %.17g roundtrips the actual outward binary64 value, unlike the old
        # four-digit display. Convert through float, then exactly to Q.
        y = Q(float(d['ytube']))
        bound = s['cM_q'] * max(y, s['ytin_q']) + Q('1e-50')
        tube = max(tube, bound)
        assert s['cM_q'] <= Q('237.3')
        assert s['ytin_q'] <= Q('4.22e-7') < s['yin_q']
        assert y < Q('8.211e-7')
        assert s['eps_q'] < Q('1e-34')
        assert bound < Q('1.95e-4')
        print(label, 'node lemma, regenerated roots and tube VERIFIED', flush=True)
    for pat, name in [((0,0,1), 'PPR'), ((0,1,1), 'PRR'), ((1,1,1), 'RRR')]:
        d = result('cap_global_' + name)
        run_count += 1
        box_count += int(d['boxes'])
        roots_match(R/f'cap_{name}_roots.txt', C/f'CaseIII_cap_D20/global/g_{name}_roots.txt.xz')
        new = global_problem(R/f'cap_{name}_ts.txt')
        old = global_problem(C/f'CaseIII_cap_D20/global/g_{name}_ts.txt')
        assert new[:6] == old[:6] and not new[6]
        assert all(ball[3] == float('inf') for ball in old[6])
        nodes = [s for s in summary.values() if tuple(s['p']) == pat]
        assert len(nodes) == len(old[5])
        for ball in old[5]:
            matching = [s for s in nodes if sum((ball[i]-s['s_q'][i])**2 for i in range(3)) < Q('1e-28')]
            assert len(matching) == 1
            assert ball[3] <= Q('0.0095') + Q('1e-16')
            # Local containment was proved for 0.0095+1e-14; the centre
            # error is in fact < 1e-16, leaving a strict overlap.
            assert sum((ball[i]-matching[0]['s_q'][i])**2 for i in range(3)) < Q('1e-32')
            assert ball[3] + Q('1e-16') < Q('0.0095') + Q('1e-14')
            assert ball[3] + Q('1e-16') + Q('1e-50') < Q('0.01')
    assert run_count == 31
    # The exclusion certificates' energy gaps are rational comparisons.
    K = {name:load_certificate(C/directory/'certificate.json') for name,directory in
         [('case0','Case0_separation_T0.8_D16'),('case1','CaseI_a-0.98_D40'),('case2','Slab_m099_m098')]}
    Estar_hi = Q('69.306363296626421258489991276382007864282129573759') + Q('1e-49')
    assert K['case0']['e'] + 3*Q(float('0.0459')) > Estar_hi + Q('0.086')
    assert K['case1']['e'] > Estar_hi + Q('3.6e-4')
    assert K['case2']['e'] > Estar_hi + Q('3.6e-4')
    assert 23*Q('1.95e-4') < Q('0.0075')
    print('Tube upper bound < 1.95e-4; 23 tau <= 0.004485 < 0.0075', flush=True)
    print('Verified runs:', run_count, 'boxes:', box_count, flush=True)
    print('AUDIT CLOSURE VERIFIED', flush=True)


if __name__ == '__main__':
    check()
