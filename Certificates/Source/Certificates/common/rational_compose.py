"""Exact polynomial substitution through FLINT's rational polynomial ring."""
from fractions import Fraction
from flint import fmpq, fmpq_mpoly_ctx

CONTEXT = fmpq_mpoly_ctx.get(('u', 'v', 't'), 'lex')
GENERATORS = CONTEXT.gens()


def rational(q):
    q = Fraction(q)
    return fmpq(q.numerator, q.denominator)


def as_poly(P):
    return CONTEXT.from_dict({e: rational(q) for e, q in P.items()})


def as_dict(P):
    return {tuple(int(k) for k in e): Fraction(int(q.numerator), int(q.denominator))
            for e, q in P.to_dict().items()}


def translate(P, axis, offset):
    args = list(GENERATORS)
    args[axis] += rational(offset)
    return as_dict(as_poly(P).compose(*args))


def linear_compose(P, M):
    args = [sum((rational(M[i][j])*GENERATORS[j] for j in range(3)), CONTEXT.constant(0))
            for i in range(3)]
    return as_dict(as_poly(P).compose(*args))
