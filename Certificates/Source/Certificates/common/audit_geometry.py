"""Interval checks for candidate nodes, rigidity, and the final margins."""
import itertools
from certificate_io import load_certificate
from fractions import Fraction as Q
from pathlib import Path
from flint import arb, ctx
from enclose_h import certify_candidate, E

ctx.prec = 256
ROOT = Path(__file__).resolve().parents[2]


def A(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


def check():
    h = certify_candidate()
    r = (1-h*h).sqrt()
    pi = arb.pi()
    s3 = arb(3).sqrt()/2
    values = [arb(-1), h, -h, (1+h*h)/2, (3*h*h-1)/2, 2*h*h-1,
              -h*h+s3*(1-h*h), -h*h, -h*h-s3*(1-h*h)]
    for a, b in itertools.combinations(values, 2):
        assert abs(a-b) > A('0.018')
    def pair(i, j):
        if i > j:
            i, j = j, i
        if i == 0 and j == 1:
            return 0
        if i < 2:
            return 1 if ((i == 0) == (j < 8)) else 2
        if (i < 8) == (j < 8):
            k = min((j-i) % 6, (i-j) % 6)
            return {1: 3, 2: 4, 3: 5}[k]
        # upper i has angle (i-2)*pi/3; lower j has angle (j-8)*pi/3+pi/6.
        k = (2*(j-8)-2*(i-2)+1) % 12
        return {1: 6, 3: 7, 5: 8, 7: 8, 9: 7, 11: 6}[k]
    expected = {p: set() for p in [(0,0,1), (0,1,1), (1,1,1)]}
    for triple in itertools.combinations(range(14), 3):
        for perm in itertools.permutations(triple):
            pattern = tuple(int(i >= 2) for i in perm)
            if pattern in expected:
                a, b, c = perm
                expected[pattern].add((pair(a,b), pair(a,c), pair(b,c)))
    assert [len(expected[p]) for p in expected] == [2, 12, 55]
    cap = load_certificate(ROOT/'Certificates/CaseIII_cap_D20/certificate.json')
    matched = {p: set() for p in expected}
    for p, _, centre in cap['nodes']:
        p = tuple(p)
        matches = []
        for symbolic in expected[p]:
            # Coordinatewise bound 5e-51 implies Euclidean error < 1e-50.
            if all(abs(A(centre[i])-values[symbolic[i]]) < A('5e-51') for i in range(3)):
                matches.append(symbolic)
        assert len(matches) == 1
        assert matches[0] not in matched[p]
        matched[p].add(matches[0])
    assert matched == expected
    print('All 69 archived nodes match the complete symbolic node list within Euclidean error 1e-50', flush=True)

    # Rigidity, uniformly for 0 < tau <= 1e-3. The following upper bounds are
    # increasing functions of tau; their denominators are positive.
    tau = A('0.001')
    beta = (h+tau)/(1-(h+tau)**2).sqrt()
    den = (r-beta*tau)**2
    eta = (1+2*h+tau+2*r*beta+beta**2*tau)/den
    etap = (1+2*h+tau+s3*(2*r*beta+beta**2*tau))/den
    assert beta < A('0.513') and eta < A('3.569') and etap < A('3.414')
    # Use fixed rational constants in the written proof.
    a = A('1.16')*A('3.569')
    b = A('1.001')*A('3.414')
    c = A('2.32')*A('3.414')
    assert A('1.16')*(pi/3-a*tau).sin() > 1
    assert A('1.001')*(b*tau).cos() > 1
    assert A('2.32')*(pi/6-c*tau).sin() > 1
    assert 7*(pi/3-a*tau) > 2*pi
    assert pi/3+5*a*tau < 2*pi/3-a*tau
    # A near-antipodal gap cannot be confused with either smaller option.
    # cos(pi/3 + 5 a tau) > -1 + eta*tau excludes that option directly.
    assert (pi/3+5*a*tau).cos() > -1+A('3.569')*tau
    # Cumulative upper-ring errors cannot change the 60/120-degree option.
    assert 6*a*tau < pi/3
    assert (2*pi/3+2*a*tau).cos() > -1+A('3.569')*tau
    # Lower-ring preliminary odd slots, then a non-opposite upper reference
    # at 90 degrees. Other inner-product options are separated by pi/3.
    assert (2*c+2*a)*tau < pi/3
    lower = a+b
    assert 2*lower*tau < pi/3-a*tau
    rmin = r-beta*tau
    pole_a = (2+h)/rmin
    pole_b = ((2+h)/rmin+pole_a*(lower*tau).sin())/(lower*tau).cos()
    assert pole_a < A('2.79') and pole_b < A('2.79')
    # Twelve height coordinates, four upper angles, one opposite upper angle,
    # six lower angles, and the two coordinates of the second pole.
    norm2 = 12 + 4*a*a + (2*a)**2 + 6*lower**2 + 2*A('2.79')**2
    assert norm2 < A(23)**2
    assert 2*a < 9 and lower < 9
    print('Rigidity: all angular and counting inequalities verified; ||p-p*||_2 < 23 tau, ||p-p*||_infty < 9 tau', flush=True)
    # Class coupling uses all cross-class differences, not a guessed minimum.
    assert all(abs(values[i]-values[j]) > A('0.018') for i in (3,4,5) for j in (6,7,8))
    assert 2*h-2*tau > A('0.9') and (2*tau).sqrt() < A('0.05')
    e = A(cap['e'])
    assert E(h)-e > 0 and E(h)-e < A('3.65e-13')
    assert 12*A(Q(float('4e-14'))) > A('3.65e-13')
    assert A(Q(float('1e-12'))) > A('3.65e-13')
    assert Q(23)*Q('1.95e-4') < Q('0.0075')
    print('Counting, class coupling and local-radius margins VERIFIED', flush=True)
    print('AUDIT GEOMETRY VERIFIED', flush=True)


if __name__ == '__main__':
    check()
