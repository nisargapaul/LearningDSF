"""Polarized angular polynomials and complete thermal DSF moments.

Pauli operators, unit interaction coefficients, and applied field -B n·sigma.
Thermal moments include every eigenstate; only coherent elastic means are removed.
"""
from collections import Counter, defaultdict
import time
import numpy as np
import scipy.sparse as sp
from scipy.linalg import eigh
from scipy.special import sph_harm_y

FIELD = 32.
RATIOS = np.unique(np.r_[0., np.geomspace(.05, .65, 21), .1, .2, .4, .6])
GRIDS = dict(coarse=(12, 24), fine=(16, 32))
RING = {'XXXX': 1, 'XXZZ': 1, 'XZXZ': -1, 'XZZX': 1,
        'ZXXZ': 1, 'ZXZX': -1, 'ZZXX': 1, 'ZZZZ': 1}


def lattice(family, lx=None, ly=None, shear=None):  # Periodic sites, bonds, translations.
    if family not in ('square', 'honeycomb'):
        raise ValueError('Choose square or honeycomb.')
    honeycomb = family == 'honeycomb'
    lx = (2 if honeycomb else 4) if lx is None else lx
    ly = 3 if ly is None else ly
    shear = (-1 if honeycomb and (lx, ly) == (2, 3) else 0) if shear is None else shear
    if not honeycomb and (min(lx, ly) < 3 or shear):
        raise ValueError('Square lattices need lx,ly >= 3 and zero shear.')
    def index(x, y, sub=0):
        turns, y = divmod(y, ly)
        x = (x-turns*shear) % lx
        return 2*(y*lx+x)+sub if honeycomb else x*ly+y
    cells = ([(x, y, sub) for y in range(ly) for x in range(lx) for sub in (0, 1)]
             if honeycomb else [(x, y, 0) for x in range(lx) for y in range(ly)])
    graph = {i: {} for i in range(len(cells))}
    for i, (x, y, sub) in enumerate(cells):
        if honeycomb:
            if sub:
                continue
            for axis, dx, dy in [('X', -1, 0), ('Y', 0, -1), ('Z', 0, 0)]:
                j = index(x+dx, y+dy, 1)
                graph[i][axis], graph[j][axis] = j, i
        else:
            graph[i] = {axis: index(x+dx, y+dy) for axis, dx, dy in
                        [('R', 1, 0), ('L', -1, 0), ('U', 0, 1), ('D', 0, -1)]}
    bonds = ([(i, graph[i]['Z']) for i in range(0, len(cells), 2)] if honeycomb
             else [(i, graph[i]['R']) for i in graph])  # Bonds used to measure C(n).
    translations = ([(x, y) for y in range(ly) for x in range(lx)] if honeycomb
                    else [(x, y) for x in range(lx) for y in range(ly)])
    permutations = [[index(x+tx, y+ty, sub) for x, y, sub in cells]
                    for tx, ty in translations]
    characters = [np.exp(-2j*np.pi*np.array([
        kx*x/lx+(ky-shear*kx/lx)*y/ly for x, y in translations]))
        for kx in range(lx) for ky in range(ly)]
    return dict(family=family, lx=lx, ly=ly, shear=shear, cells=cells, graph=graph,
                bonds=bonds, permutations=permutations, characters=characters)


def terms(family, graph, j=1., kappa=1., lam=1.):  # Fixed two-, three-, four-spin terms.
    result = []
    def add(sites, axes, coupling):
        result.append(dict(k=len(sites), sites=sites, axes=axes, coupling=coupling))
    for start in sorted(graph):
        if family == 'square':
            right, up = graph[start]['R'], graph[start]['U']
            add([start, right], 'XX', -j)
            add([start, up], 'ZZ', -j)
            for x in ('L', 'R'):
                for y in ('D', 'U'):
                    add([graph[start][x], start, graph[start][y]], 'XYZ', -kappa)
            for word, sign in RING.items():
                add([start, right, graph[right]['U'], up], word, -lam*sign)
        elif family == 'honeycomb':
            for a, second in sorted(graph[start].items()):
                if start < second:
                    add([start, second], a+a, -j)
                for b, third in sorted(graph[second].items()):
                    if third == start:
                        continue
                    c = next(axis for axis in 'XYZ' if axis not in (a, b))
                    path = [start, second, third]
                    if path < path[::-1]:
                        add(path, a+c+b, -kappa)
                    path = path+[graph[third][c]]
                    assert len(set(path)) == 4
                    if path < path[::-1]:
                        add(path, a+c+a+c, lam)
        else:
            raise ValueError('Choose square or honeycomb.')
    n = len(graph)
    assert Counter(t['k'] for t in result) == ({2: 2*n, 3: 4*n, 4: 8*n}
        if family == 'square' else {2: 3*n//2, 3: 3*n, 4: 3*n})
    keys = [tuple(sorted(zip(t['sites'], t['axes']))) for t in result]
    assert len(keys) == len(set(keys))
    return result


def bond_polynomial(interactions, bond, order):  # Exact one-spin-flip matrix element.
    polynomial = defaultdict(complex)
    for term in interactions:
        if term['k'] > order or not set(bond) <= set(term['sites']):
            continue
        axes = dict(zip(term['sites'], map('XYZ'.index, term['axes'])))
        a, b = axes[bond[0]], axes[bond[1]]
        powers = [sum(axis == c for site, axis in axes.items() if site not in bond)
                  for c in range(3)]  # One factor of n per spectator spin.
        g = term['coupling']
        if a == b:  # Real flip factor: δ_ab − n_a n_b.
            polynomial[tuple(powers)] += g
        quadratic = powers.copy(); quadratic[a] += 1; quadratic[b] += 1
        polynomial[tuple(quadratic)] -= g
        for c in range(3):
            epsilon = (a-b)*(b-c)*(c-a)//2
            if epsilon:
                linear = powers.copy(); linear[c] += 1
                polynomial[tuple(linear)] -= 1j*g*epsilon
    return dict(polynomial)


def evaluate(polynomial, directions):  # Evaluate a Cartesian sphere polynomial.
    directions = np.atleast_2d(directions)
    return sum((value*np.prod(directions**powers, axis=1) for powers, value in polynomial.items()),
               np.zeros(len(directions), complex))


def centered_polynomial(polynomial):  # Remove the exact spherical mean.
    def double_factorial(n):
        return int(np.prod(np.arange(n, 0, -2), dtype=np.int64))
    real = {powers: float(value.real) for powers, value in polynomial.items() if value.real}
    mean = sum(value*np.prod([double_factorial(p-1) for p in powers])/
               double_factorial(sum(powers)+1) for powers, value in real.items()
               if all(p % 2 == 0 for p in powers))
    real[(0, 0, 0)] = real.get((0, 0, 0), 0.)-mean
    return real, float(mean)


def angular_grid(ntheta=16, nphi=32):  # Gauss–Legendre × uniform azimuth quadrature.
    z, w = np.polynomial.legendre.leggauss(ntheta)
    zz, pp = np.meshgrid(z, 2*np.pi*np.arange(nphi)/nphi, indexing='ij')
    theta, phi = np.arccos(zz.ravel()), pp.ravel()
    directions = np.column_stack([np.sin(theta)*np.cos(phi), np.sin(theta)*np.sin(phi), np.cos(theta)])
    return directions, theta, phi, np.repeat(w, nphi)*2*np.pi/nphi


def decompose(signal, theta, phi, weights, lmax=8):  # Orthonormal spherical harmonics.
    lm = np.array([(ell, m) for ell in range(lmax+1) for m in range(-ell, ell+1)])
    harmonics = np.column_stack([sph_harm_y(int(ell), int(m), theta, phi) for ell, m in lm])
    coefficients = (np.asarray(signal)*weights) @ harmonics.conj()  # Integrate C against Y_lm*.
    amplitudes = np.stack([np.linalg.norm(coefficients[..., lm[:, 0] == ell], axis=-1)/np.sqrt(4*np.pi)
                           for ell in range(lmax+1)], axis=-1)
    return coefficients, amplitudes, lm


def ideal(family='honeycomb'):  # Unscaled B=∞, T=0 sphere maps and amplitudes.
    geometry = lattice(family, 6, 6, 0)
    interactions = terms(family, geometry['graph'])
    directions, theta, phi, weights = angular_grid()
    maps = [evaluate(centered_polynomial(bond_polynomial(
        interactions, geometry['bonds'][0], order))[0], directions).real for order in (2, 3, 4)]
    coefficients, amplitudes, lm = decompose(maps, theta, phi, weights)
    return dict(directions=directions, weights=weights, theta=theta, phi=phi,
                maps=np.array(maps), coefficients=coefficients, amplitudes=amplitudes, lm=lm)


def local_operators(n):  # Sparse Pauli matrices, site zero as least-significant bit.
    states = np.arange(2**n)
    return [[sp.csr_matrix((np.ones(len(states)), (states ^ (1 << i), states)), shape=(2**n,)*2),
             sp.csr_matrix((1j*(1-2*((states >> i) & 1)), (states ^ (1 << i), states)), shape=(2**n,)*2),
             sp.diags(1.-2*((states >> i) & 1), format='csr')]
            for i in range(n)]


def translation_blocks(geometry):  # All momentum sectors, retaining all 2**N states.
    n = len(geometry['cells'])
    states = np.arange(2**n, dtype=np.int64)
    moved = np.array([sum(((states >> source) & 1) << destination
                         for source, destination in enumerate(permutation))
                      for permutation in geometry['permutations']])
    representatives = np.flatnonzero(np.min(moved, axis=0) == states)
    projectors = []
    for characters in geometry['characters']:
        rows, columns, values, column = [], [], [], 0
        for representative in representatives:
            orbit, inverse = np.unique(moved[:, representative], return_inverse=True)
            weight = np.zeros(len(orbit), complex)
            np.add.at(weight, inverse, characters)
            norm = np.linalg.norm(weight)
            if norm < 1e-10:
                continue
            rows.extend(orbit); columns.extend([column]*len(orbit)); values.extend(weight/norm)
            column += 1
        projector = sp.csr_matrix((values, (rows, columns)), shape=(2**n, column))
        error = projector.conj().T @ projector-sp.eye(column)
        assert np.max(abs(error.data), initial=0) < 1e-12
        projectors.append(projector)
    assert sum(p.shape[1] for p in projectors) == 2**n
    return projectors


class ThermalSystem:
    def __init__(self, family='honeycomb', lx=None, ly=None, shear=None):  # Compile moment operators once.
        geometry = lattice(family, lx, ly, shear)
        self.n = len(geometry['cells'])
        local = local_operators(self.n)
        zero = sp.csr_matrix((2**self.n,)*2, dtype=complex)
        interactions = [zero.copy() for _ in range(3)]
        for term in terms(family, geometry['graph']):
            operator = sp.eye(2**self.n, dtype=complex, format='csr')
            for site, axis in zip(term['sites'], term['axes']):
                operator = operator @ local[site]['XYZ'.index(axis)]
            interactions[term['k']-2] += term['coupling']*operator
        magnets = [sum((site[a] for site in local), zero.copy()) for a in range(3)]
        components, bonds = interactions+magnets, geometry['bonds']
        response = []
        for h in components:  # Build the first moment for each piece of H.
            first = sum((local[i][a] @ (h @ local[j][a]-local[j][a] @ h)
                         for i, j in bonds for a in range(3)), zero.copy())
            response.append(((first+first.conj().T)/(4*len(bonds))).tocsr())  # Real, bond-averaged moment.
        static = sum((local[i][a] @ local[j][a] for i, j in bonds for a in range(3)),
                     zero.copy())/(2*len(bonds))
        means = ([sum((local[i][a] for i in range(sub, self.n, 2)), zero.copy())/(self.n/2)
                  for sub in (0, 1) for a in range(3)] if family == 'honeycomb'
                 else [magnet/self.n for magnet in magnets]*2)
        self.full = components+response+[static]+means  # 6 Hamiltonian parts, 6 moments, static, 6 means.
        self.blocks = []
        for projector in translation_blocks(geometry):
            block = [(projector.conj().T @ operator @ projector).tocsr() for operator in self.full]
            for operator in block:
                anti = operator-operator.conj().T
                assert np.max(abs(anti.data), initial=0) < 1e-10
            for operator, projected in zip(components, block[:6]):
                residual = operator @ projector-projector @ projected
                assert np.max(abs(residual.data), initial=0) < 1e-10
            self.blocks.append(block)

    def evaluate(self, order, direction, field=FIELD, ratios=RATIOS, full=False):  # Complete Gibbs traces.
        start = time.perf_counter()
        direction, ratios = np.asarray(direction, float), np.asarray(ratios, float)
        np.testing.assert_allclose(np.linalg.norm(direction), 1, atol=1e-12, rtol=0)
        if field <= 0 or np.any(ratios < 0):
            raise ValueError('Use positive field and nonnegative T/B.')
        coefficients = np.r_[np.arange(2, 5) <= order, -field*direction]  # Keep orders ≤ k and add the field.
        energies, diagonals, residuals = [], [], []
        for operators in [self.full] if full else self.blocks:
            h = sum(c*operator for c, operator in zip(coefficients, operators[:6]))
            first = sum(c*operator for c, operator in zip(coefficients, operators[6:12]))
            eigenvalues, vectors = eigh(h.toarray(), driver='evd', check_finite=False)
            diagonal = np.column_stack([np.sum(vectors.conj()*(operator @ vectors), axis=0)
                                        for operator in [first]+operators[12:]])
            assert np.max(abs(diagonal.imag)) < 1e-9
            energies.append(eigenvalues); diagonals.append(diagonal.real)
            residuals.append(float(np.linalg.norm(h @ vectors[:, 0]-eigenvalues[0]*vectors[:, 0])))
        energies, diagonals = np.concatenate(energies), np.vstack(diagonals)
        assert len(energies) == 2**self.n
        np.testing.assert_allclose(np.mean(diagonals, axis=0), 0., atol=1e-10)
        delta = energies-energies.min()
        ground = delta < 1e-9
        weights = np.array([ground.astype(float) if ratio == 0 else np.exp(-delta/(ratio*field))
                            for ratio in ratios])
        weights /= weights.sum(axis=1, keepdims=True)  # Normalize across all sectors at each T.
        expectations = weights @ diagonals
        first, static, magnet = expectations[:, 0], expectations[:, 1], expectations[:, 2:]
        connected_static = static-.5*np.sum(magnet[:, :3]*magnet[:, 3:], axis=1)  # Remove the product of means.
        assert max(residuals) < 1e-9
        return dict(signal=first-2*field*connected_static, first=first, static=static,  # Center at 2B.
                    connected_static=connected_static, magnetization=magnet,
                    polarization=.5*(magnet[:, :3]+magnet[:, 3:]) @ direction,
                    gap=float(np.min(delta[~ground])), ground_rank=int(ground.sum()),
                    residual=max(residuals), seconds=time.perf_counter()-start)
