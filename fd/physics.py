"""Recover Pauli Hamiltonians from normalized zeroth and symmetrized first moments."""
import numpy as np
from scipy import sparse
from scipy.linalg import eigh

CLASSES = ('su2', 'u1', 'z2', 'generic')
ONSITE = np.triu_indices(3)
EPS = np.zeros((3, 3, 3))
for a, b, c in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
    EPS[a, b, c], EPS[b, a, c] = 1, -1
ONSITE_COMM = -4 * np.einsum('uac,bce->abue', EPS, EPS)
ONSITE_COMM = ((ONSITE_COMM + ONSITE_COMM.swapaxes(0, 1)) / 2)[ONSITE]


def embedding(family):  # Map independent parameters to the 21 physical couplings.
    if family == 'generic':
        return np.eye(21)
    fields = [] if family == 'su2' else [np.eye(21)[2]]
    axes = np.eye(9)
    exchange = {
        'su2': [axes[0] + axes[4] + axes[8]],
        'u1': [axes[0] + axes[4], axes[8], axes[1] - axes[3]],
        'z2': axes[[0, 4, 1, 3, 8]],
    }[family]
    return np.stack(fields + [np.pad(column, (3 + 9*r, 9*(1-r)))
                              for r in range(2) for column in exchange], axis=1)


def design(c):  # Double commutators expressed in the 21 measured static moments.
    # Rows are 18 ordered bond channels, then six symmetric onsite channels.
    shape = c.shape[:-1]
    matrix = np.zeros((*shape, 24, 21))
    matrix[..., 18:, :3] = np.einsum('kue,...e->...ku', ONSITE_COMM, c[..., :3])
    for r in range(2):
        cols = slice(3 + 9*r, 12 + 9*r)
        corr = c[..., cols].reshape(*shape, 3, 3)
        bond = 4 * np.einsum('uac,vbe,...ce->...abuv', EPS, EPS, corr, optimize=True)
        matrix[..., 9*r:9*(r+1), cols] = bond.reshape(*shape, 9, 9)
        # The onsite commutator acts on both the incoming and outgoing bonds.
        onsite = (np.einsum('kue,...ev->...kuv', ONSITE_COMM, corr)
                  + np.einsum('kve,...ue->...kuv', ONSITE_COMM, corr))
        matrix[..., 18:, cols] = onsite.reshape(*shape, 6, 9)
    return matrix


def chain_design(c):  # Six equations for the three diagonal nearest-neighbor exchanges.
    x, y, z = np.moveaxis(4*c, -1, 0)
    zero = np.zeros_like(x)
    rows = ((zero, z, y), (z, zero, x), (y, x, zero),
            (zero, -2*y, -2*z), (-2*x, zero, -2*z), (-2*x, -2*y, zero))
    return np.moveaxis(np.array(rows), (0, 1), (-2, -1))


def recover(matrix, first, allowed):  # Solve in the symmetry subspace, then return physical couplings.
    inverse = np.linalg.pinv(matrix @ allowed, rcond=1e-12)
    return np.einsum('...ij,...j->...i', inverse, first) @ allowed.T


def relative_error(estimate, truth):  # Use the full physical coupling norm.
    return np.linalg.norm(estimate - truth, axis=-1) / np.linalg.norm(truth)


def noisy_errors(c, first, truth, allowed, sigmas, trials, seed, matrix=design):  # Fit noisy batch means.
    # Preserve the archived draw order. The same draws are shared across noise strengths.
    rng = np.random.default_rng(seed)
    if matrix is chain_design:
        noise = rng.standard_normal((len(c), trials, 9))
        dc, df = noise[..., :3], noise[..., 3:]
    else:
        dc = rng.standard_normal((len(c), trials, 21))
        df = rng.standard_normal((len(c), trials, 24))
    return np.array([relative_error(recover(matrix(c[:, None] + sigma/10*dc),
                                            first[:, None] + sigma/10*df, allowed), truth)
                     for sigma in sigmas])


def pauli_word(n, *operators):  # Build a sparse Pauli product in the bit basis.
    states = np.arange(2**n)
    target, phase = states.copy(), np.ones(2**n, complex)
    for site, axis in operators:
        sign = 1 - 2*((states >> site) & 1)
        if axis < 2:
            target ^= 1 << site
        if axis == 1:
            phase *= 1j*sign
        if axis == 2:
            phase *= sign
    return sparse.csr_matrix((phase, (target, states)), shape=(2**n, 2**n))


def thermal_moments(truth, betas, shape=(6,)):  # Direct ED moment calculation for small periodic systems.
    n = int(np.prod(shape))
    if len(shape) not in (1, 2) or (len(shape) == 1 and n < 5) or (len(shape) == 2 and min(shape) < 3):
        raise ValueError('Choose a chain of length ≥5 or a square grid with both lengths ≥3.')
    sites = np.arange(n).reshape(shape)
    neighbors = ([np.roll(sites, -d) for d in (1, 2)] if len(shape) == 1
                 else [np.roll(sites, -1, axis=a).ravel() for a in (0, 1)])
    h = sparse.csr_matrix((2**n, 2**n), dtype=complex)
    for a in np.flatnonzero(truth[:3]):
        h += truth[a]*sum(pauli_word(n, (i, a)) for i in range(n))
    for r, bonds in enumerate(neighbors):
        for a, b in np.ndindex(3, 3):
            coupling = truth[3 + 9*r + 3*a + b]
            if coupling:
                h += coupling*sum(pauli_word(n, (i, a), (j, b)) for i, j in enumerate(bonds))
    energy, vectors = eigh(h.toarray())
    weights = np.exp(-np.asarray(betas)[:, None]*(energy - energy[0]))
    weights /= weights.sum(axis=1, keepdims=True)
    origin = [pauli_word(n, (0, a)) @ vectors for a in range(3)]
    static = [weights @ np.sum(vectors.conj()*v, axis=0).real for v in origin]
    first = []
    for j in [*(int(b[0]) for b in neighbors), 0]:
        for a, b in (zip(*ONSITE) if j == 0 else np.ndindex(3, 3)):
            right = pauli_word(n, (j, b)) @ vectors
            left = origin[a].conj()
            if j:
                static.append(weights @ np.sum(left*right, axis=0).real)
            # In eigenstate s, the signed first moment inserts H − E_s.
            first.append(2 * (weights @ np.sum(left*(h @ right - right*energy), axis=0).real))
    return np.column_stack(static), np.column_stack(first)
