"""Exact Taylor shifts used by the audited root generators.

Root coverage is constructed in run_typed_ts.write_roots from rational cell
endpoints; coefficients are translated to the actual stored binary centres.
The obsolete generator that did not track centre conversion was removed.
"""
def shift1(P, ax, d):
    """Exact Taylor shift P(x + d e_ax), using FLINT rational polynomials."""
    from rational_compose import translate
    return translate(P, ax, d)
