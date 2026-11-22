# rigorous enclosure of the stationary height h* of the D6d family and of E* = E(X(h*)) using arb ball arithmetic
from flint import arb, ctx
ctx.prec = 256
S3 = arb(3).sqrt()
C = [S3/2, arb(0), -S3/2]           # cos 30, cos 90, cos 150
def E(h):
    r2 = 1-h*h
    s = arb(1)/2 + 12/(2-2*h).sqrt() + 12/(2+2*h).sqrt() + (15 + 12/S3)/r2.sqrt()
    for c in C: s += 12/(2*r2*(1-c)+4*h*h).sqrt()
    return s
def dE(h):
    r2 = 1-h*h
    s = 12*(2-2*h)**(arb(-3)/2) - 12*(2+2*h)**(arb(-3)/2) + (15+12/S3)*h*r2**(arb(-3)/2)
    for c in C: s += -12*2*h*(1+c)*(2*r2*(1-c)+4*h*h)**(arb(-3)/2)
    return s
def d2E(h):
    r2 = 1-h*h
    s = 12*3*(2-2*h)**(arb(-5)/2) + 12*3*(2+2*h)**(arb(-5)/2)
    s += (15+12/S3)*(r2**(arb(-3)/2) + 3*h*h*r2**(arb(-5)/2))
    for c in C:
        A = 2*r2*(1-c)+4*h*h; Ap = 4*h*(1+c)
        s += -24*(1+c)*(A**(arb(-3)/2) - arb(3)/2*h*Ap*A**(arb(-5)/2))
    return s
def certify_candidate():
    """Existence by endpoint signs; uniqueness and enclosure by interval Newton."""
    m = arb('0.45536779516246300350924502372107445741075259468695')
    I = m + arb(0, arb('1e-40'))
    assert dE(I.lower()) < 0 and dE(I.upper()) > 0
    assert d2E(I) > 0
    Nw = m - dE(m)/d2E(I)
    assert I.contains(Nw)
    I = Nw
    claimed_h = m + arb(0, arb('2e-51'))
    claimed_E = arb('69.306363296626421258489991276382007864282129573759') + arb(0, arb('1e-49'))
    assert claimed_h.contains(I) and claimed_E.contains(E(I))
    return I

if __name__=='__main__':
    I = certify_candidate()
    print('Endpoint signs, positive second derivative, and interval Newton inclusion: VERIFIED')
    print('h* in', I.str(50, radius=True))
    print('E* in', E(I).str(50, radius=True))
    print("E''(h*) =", d2E(I).str(20))
