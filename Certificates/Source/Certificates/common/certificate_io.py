"""Read the public exact-rational certificate format (no executable data).

Rational numbers are canonical strings such as "7", "-3/5", or "0".
Monomial rows [a,b,c,q] mean q*u**a*v**b*t**c. Matrix blocks are indexed
by (root type, angular degree). See Certificates/FORMAT.md for the schema.
"""
import json
from fractions import Fraction
from pathlib import Path


def rational(value):
    assert isinstance(value, str)
    q = Fraction(value)
    assert str(q) == value, 'noncanonical rational'
    return q


def matrix_blocks(items):
    result = {}
    for item in items:
        key = item['root'], item['k']
        assert all(type(i) is int and i >= 0 for i in key)
        assert key not in result
        M = [[rational(v) for v in row] for row in item['matrix']]
        assert M and M[0] and all(len(row) == len(M[0]) for row in M)
        result[key] = M
    return result


def load_certificate(path):
    data = json.loads(Path(path).read_text())
    assert data['format'] == 'thomson14-certificate-v1'
    case = data['case']
    expected = {'case0':(16,[14],4), 'case1':(40,[14],4),
                'case2':(20,[2,12],1), 'cap':(20,[2,12],1)}
    assert (data['D'], data['counts'], data['factor']) == expected[case]
    result = {'case':case, 'D':data['D'], 'counts':data['counts'],
              'factor':data['factor'], 'e':rational(data['e']),
              'F':matrix_blocks(data['F']), 'slacks':{}}
    patterns = {(0,0,0)} if case in ('case0','case1') else {(0,0,1),(0,1,1),(1,1,1)}
    for item in data['slacks']:
        pattern = tuple(item['pattern'])
        assert pattern in patterns and pattern not in result['slacks']
        polynomial = {}
        for a,b,c,value in item['polynomial']:
            exponent = (a,b,c)
            assert all(type(i) is int and i >= 0 for i in exponent)
            assert sum(exponent) <= data['D'] and exponent not in polynomial
            polynomial[exponent] = rational(value)
        weights = [(i,rational(w)) for i,w in item['weights']]
        assert len({i for i,w in weights}) == len(weights)
        assert all(type(i) is int and 0 <= i <= 2 and w > 0 for i,w in weights)
        result['slacks'][pattern] = polynomial, weights
    assert set(result['slacks']) == patterns
    if case == 'cap':
        result['G'], result['N'] = matrix_blocks(data['G']), matrix_blocks(data['N'])
        assert set(result['F']) == set(result['G']) == set(result['N'])
        result['nodes'] = []
        for item in data['nodes']:
            pattern = tuple(item['pattern'])
            coordinates = [rational(v) for v in item['coordinates']]
            assert pattern in patterns and len(coordinates) == 3
            result['nodes'].append((pattern, [float(v) for v in coordinates], coordinates))
        result['local_coordinates'] = {}
        for item in data['local_coordinates']:
            node = item['node']
            assert type(node) is int and 0 <= node < len(result['nodes'])
            assert node not in result['local_coordinates']
            M = [[rational(v) for v in row] for row in item['matrix']]
            semiaxes = [rational(v) for v in item['semiaxes']]
            assert len(M) == 3 and all(len(row) == 3 for row in M)
            assert len(semiaxes) == 3 and all(v > 0 for v in semiaxes)
            assert item['kind'] in ('edge','bnd','int')
            result['local_coordinates'][node] = {
                'M':M, 'sc':semiaxes, 'cM':rational(item['norm_bound']),
                'mG':rational(item['gram_multiplier']),
                'nu':rational(item['edge_multiplier']), 'kind':item['kind']}
        assert set(result['local_coordinates']) == {0,2,3,4,5,6,7,11,12,13,14,15,16,17,19,25,26,34,36,44,48,56}
    return result
