"""Pauli honeycomb models and polarized-state SF measurement maps."""
from functools import cache  # Reuse fixed geometry and matrices across calculations.
from itertools import combinations
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from scipy.linalg import eigh_tridiagonal
from scipy.ndimage import gaussian_filter1d

PAULI = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]])
DIRECTIONS = np.array([[1.,0,0],[0,1.,0],[0,0,1.],[1.,1.,0],[1.,0,1.],[0,1.,1.]])
DIRECTIONS /= np.linalg.norm(DIRECTIONS, axis=1)[:,None]
TWO_FIELDS = np.array([[0.,0.,1.], [2**-.5,-2**-.5,0.]])

@cache
def geometry(n):  # Build the periodic honeycomb cluster.
    # y-wrap subtracts (-1,3) on the tilted twelve-site torus.
    lx, ly, shear = {8: (2, 2, 0), 12: (2, 3, -1), 16: (4, 2, 0)}[n]
    def index(x, y, sub):  # Wrap cells onto the torus.
        turns, y = divmod(y, ly)
        return 2 * (y * lx + (x - turns * shear) % lx) + sub
    cells = [(x, y, sub) for y in range(ly) for x in range(lx) for sub in range(2)]
    bonds = {g: [] for g in "xyz"}
    for x, y, sub in cells:
        if sub:
            continue
        a = index(x, y, 0)
        for g, dx, dy in [("x", -1, 0), ("y", 0, -1), ("z", 0, 0)]:
            bonds[g].append((a, index(x + dx, y + dy, 1)))
    a1, a2 = np.array([np.sqrt(3)/2, 1.5]), np.array([-np.sqrt(3)/2, 1.5])
    reciprocal = 2*np.pi*np.linalg.inv(np.column_stack([a1, a2])).T
    positions = np.array([x*a1+y*a2+sub*np.array([0.,1.]) for x,y,sub in cells])  # Include the two-site basis.
    momenta = np.array([reciprocal @ np.array([kx/lx+gx, (ky-shear*kx/lx)/ly+gy])
                        for gx,gy in [(0,0),(1,0),(0,1)]
                        for kx in range(lx) for ky in range(ly)])
    signs = np.array([(-1.)**(x+y) for x,y,_ in cells])
    return dict(n=n, cells=cells, bonds=bonds, positions=positions, momenta=momenta,
                signs=signs, wrapping=[[lx, 0], [shear, ly]])

@cache
def spins(n):  # Sparse Pauli operators on every site.
    states = np.arange(2**n)
    return [[sp.csr_matrix((np.ones(len(states)), (states^(1<<i), states)), shape=(2**n,)*2),
             sp.csr_matrix((1j*(1-2*((states>>i)&1)), (states^(1<<i), states)), shape=(2**n,)*2),
             sp.diags(1-2*((states>>i)&1), format='csr')] for i in range(n)]

@cache
def basis(n=12):  # All 27 oriented honeycomb exchanges.
    local = spins(n)
    return [sum((local[i][a]@local[j][b] for i,j in pairs), sp.csr_matrix((2**n,)*2, dtype=complex))
            for pairs in geometry(n)['bonds'].values() for a in range(3) for b in range(3)]

def jkg_design():  # Embed J, K, Gamma in 27 exchanges.
    return np.array([(a==b, a==b==g, a!=b and a!=g and b!=g)
                     for g in range(3) for a in range(3) for b in range(3)], float)

def ground_space(h, seed=0):  # Resolve the degenerate ground subspace.
    rng = np.random.default_rng(seed)
    v = rng.normal(size=h.shape[0]) + 1j*rng.normal(size=h.shape[0])
    k = 4
    while True:
        e, u = eigsh(h, k=k, which="SA", tol=1e-12, ncv=max(32, 2*k+1),
                     maxiter=2000, v0=v)
        order = np.argsort(e)
        e, u = e[order], u[:,order]
        rank = int(np.sum(e-e[0] <= 1e-10))  # Retain the full ground-state degeneracy.
        if rank < k:
            break
        k *= 2
        if k > 64:
            raise ValueError("Ground degeneracy exceeds the verified search capacity")
    ground, _ = np.linalg.qr(u[:,:rank])
    levels,rotation = np.linalg.eigh(ground.conj().T@(h@ground))
    ground = ground@rotation
    e0 = float(levels[0])
    residual = max(np.linalg.norm(h@ground[:,j]-levels[j]*ground[:,j]) for j in range(rank))
    if residual > 1e-10*max(1., abs(e0)):
        raise ValueError(f"Ground residual {residual:g} exceeds tolerance")
    return e0, ground, dict(rank=rank, residual=float(residual), gap=float(e[rank]-e0),energies=levels.tolist())

def polarizations():  # Coordinate, linear, and circular spin channels.
    eye = np.eye(3, dtype=complex)
    vectors = list(eye)
    for a, b in combinations(range(3), 2):
        for phase in (1., 1j):
            vectors.append((eye[a]+phase*eye[b])/np.sqrt(2))
    return np.asarray(vectors)

def spinors(direction):  # Polarized spinor and one-flip matrix elements.
    _, vectors = np.linalg.eigh(np.einsum('a,aij->ij', direction, PAULI))
    down, up = vectors[:, 0], vectors[:, 1]
    transition = np.einsum('i,aij,j->a', down.conj(), PAULI, up)
    return up, transition

def probes(n=12):  # Eighteen momenta and nine spin polarizations.
    g = geometry(n); reduced = g['momenta'][:n//2]
    reciprocal = g['momenta'][n//2]-reduced[0]
    momenta = np.concatenate([reduced+k*reciprocal for k in range(3)])
    coefficients, settings, seen = [], [], set()
    def add(setting, c):  # Preserve the original probe order and phase convention.
        flat = c.ravel(); canonical = flat*np.exp(-1j*np.angle(flat[np.argmax(abs(flat))]))
        key = (setting, *np.round(canonical.real,11), *np.round(canonical.imag,11))
        if key not in seen:
            seen.add(key); coefficients.append(flat); settings.append(setting)
    for s in range(3):
        add(s, g['signs'][:,None]*np.eye(3)[s]/np.sqrt(n))
    for s in range(3):
        for q in momenta:
            for p in polarizations(): add(s,np.exp(-1j*g['positions']@q)[:,None]*p/np.sqrt(n))
    return np.array(coefficients), np.array(settings)

@cache
def layout(kind='general', n=12):  # Match the saved measurement ordering.
    coefficients, settings = probes(n)
    if kind == 'general':
        directions = DIRECTIONS
        base = coefficients[settings==0]
        coefficients = np.tile(base, (6,1))
        settings = np.repeat(np.arange(6), len(base))
        design = leading_design(coefficients, settings, directions, n)
    else:
        directions = TWO_FIELDS
        coefficients, settings = coefficients[settings!=1], settings[settings!=1]//2
        design = leading_design(coefficients, settings, directions, n)@jkg_design()
    active = np.linalg.norm(design, axis=1)>1e-10
    return coefficients[active], settings[active], directions, design[active]

def leading_design(coefficients, settings, directions, n=12):  # Polarized one-spin-flip matrix elements.
    """Exact polarized-state first-order map, using only the one-flip sector."""
    design = np.zeros((len(coefficients), 27))
    for setting, direction in enumerate(directions):
        _, transition = spinors(direction)
        ids = np.flatnonzero(settings == setting)
        flips = coefficients[ids].reshape(-1, n, 3) @ transition
        column = 0
        for pairs in geometry(n)['bonds'].values():
            for a in range(3):
                for b in range(3):
                    for i, j in pairs:
                        design[ids, column] += (
                            -2*direction[a]*direction[b]*(abs(flips[:, i])**2 + abs(flips[:, j])**2)
                            + 2*np.real(flips[:, i].conj()*flips[:, j]*transition[a]*transition[b].conj()))
                    column += 1
    return design

def chain_design(n=12):  # Leading SF map for twelve chain couplings.
    """Polarized one-flip matrix for three fields and nine oriented exchanges.

    Parameter order: bx,by,bz,Lxx,Lxy,...,Lzz. The normalized probe is
    O=N^(-1/2) sum_j exp(-iqj) p.sigma_j. Its one-flip amplitudes are f_j.
    Each column is <v|V_j|v>-<Omega|V_j|Omega>*<v|v>.
    """
    q = 2*np.pi*np.arange(n)/n
    p = polarizations()  # x,y,z and six linear/circular combinations.
    base = (np.exp(-1j*q[:, None, None, None]*np.arange(n)[None, None, :, None])
            *p[None, :, None, :]/np.sqrt(n)).reshape(n*len(p), 3*n)
    coefficients = np.tile(base, (len(DIRECTIONS), 1))
    settings = np.repeat(np.arange(len(DIRECTIONS)), len(base))
    diagonal = np.tile(np.arange(len(p)) < 3, len(DIRECTIONS)*n)
    design = np.zeros((len(coefficients), 12))
    for setting, direction in enumerate(DIRECTIONS):
        _, transition = spinors(direction)
        ids = np.flatnonzero(settings == setting)
        flips = coefficients[ids].reshape(-1, n, 3) @ transition
        weight = np.sum(abs(flips)**2, axis=1)
        neighbor = np.sum(flips.conj()*np.roll(flips, -1, axis=1), axis=1)
        design[ids, :3] = -2*weight[:, None]*direction
        for a in range(3):
            for b in range(3):
                design[ids, 3+3*a+b] = (-4*direction[a]*direction[b]*weight
                    +2*np.real(neighbor*transition[a]*transition[b].conj()))
    return design, coefficients, settings, diagonal

def centered_moments(theta, field, kind='general', n=12, seed=20260915):  # Exact finite-field inelastic first moments.
    local = spins(n); coefficients, settings, directions, _ = layout(kind,n)
    exchange = jkg_design()@theta if len(theta)==3 else theta
    interaction = sum(t*h for t,h in zip(exchange,basis(n)))
    values, diagnostics = np.zeros(len(coefficients)), []
    for s,direction in enumerate(directions):
        h = interaction-field*sum(direction[a]*local[i][a] for i in range(n) for a in range(3))
        energy, ground, info = ground_space(h, seed+s)
        gram = np.zeros((3*n,3*n), complex)
        for state in ground.T:
            acted = np.column_stack([op@state for site in local for op in site])
            acted -= ground@(ground.conj().T@acted)  # Remove the full elastic ground-manifold response.
            gram += acted.conj().T@(h@acted-(energy+2*field)*acted)/ground.shape[1]
        ids = np.flatnonzero(settings==s)
        moments = np.einsum('mi,ij,mj->m',coefficients[ids].conj(),gram,coefficients[ids],optimize=True)
        np.testing.assert_allclose(moments.imag,0,atol=1e-9)
        values[ids] = moments.real
        diagnostics.append(info['residual']/max(1.,abs(energy)))
    assert max(diagnostics)<1e-10
    return values, np.array(diagnostics)

def broaden_poles(poles, weights, omega):  # Bin poles and apply resolution.
    coord = (poles-omega[0])/.05
    left = np.floor(coord).astype(int)
    frac = coord-left
    if left.min(initial=0) < 0 or left.max(initial=0)+1 >= len(omega):
        raise ValueError("Spectral pole outside padded frequency window")
    mass = np.bincount(left, weights=weights*(1-frac), minlength=len(omega))  # Linear binning preserves m0 and m1.
    mass += np.bincount(left+1, weights=weights*frac, minlength=len(omega))
    return gaussian_filter1d(mass, 3., mode="constant", truncate=5.5)  # Resolution sigma = 3 * 0.05 = 0.15.

def difference(a, b, counts=100000.):  # Compare spectra by L1 and GKL.
    l1 = np.abs(a-b).sum()/max(b.sum(), 1e-30)
    gain = counts/max(b.sum(),1e-30)
    x,y = gain*a, gain*b
    positive = y > 0
    dev = np.sum(x-y) + np.sum(y[positive]*(np.log(y[positive])-np.log(np.maximum(x[positive],1e-300))))
    return float(l1), float(2*max(dev,0))

def response(h, e0, vector, omega, depths=(128,256,512,1024)):  # Converge a Lanczos spectral response.
    """Lanczos quadrature; two-pass full reorthogonalization, converged after broadening."""
    mass = float(np.vdot(vector,vector).real)
    first = float(np.vdot(vector, h@vector-e0*vector).real)
    if mass < 1e-24:
        return np.zeros(len(omega)), dict(depth=0, l1=0., deviance=0., mass=mass, first=first)
    cap = min(max(depths), h.shape[0])
    basis = np.empty((cap, len(vector)), dtype=complex)
    conjugate = np.empty_like(basis)
    alpha, beta = [], []
    v = vector/np.sqrt(mass)
    previous = None
    lapack_fallbacks = 0
    for j in range(cap):
        basis[j], conjugate[j] = v, v.conj()
        w = h@v-e0*v
        if j:
            w -= beta[-1]*basis[j-1]
        a = np.vdot(v,w).real
        alpha.append(a)
        w -= a*v
        for _ in range(2):
            w -= (conjugate[:j+1]@w)@basis[:j+1]
        b = float(np.linalg.norm(w))
        exhausted = b < 1e-11 or j+1 == h.shape[0]
        if j+1 in depths or exhausted or j+1 == cap:
            try:
                poles, u = eigh_tridiagonal(np.array(alpha), np.array(beta), check_finite=False)
            except np.linalg.LinAlgError:
                # MRRR can fail for nearly repeated Ritz values; QR is independent.
                poles, u = eigh_tridiagonal(np.array(alpha), np.array(beta),
                                            check_finite=False,lapack_driver="stev")
                lapack_fallbacks += 1
            weights = mass*u[0]**2
            if not np.isfinite(poles).all() or not np.isfinite(weights).all():
                raise ValueError("Nonfinite quadrature eigensystem")
            spectrum = broaden_poles(poles, weights, omega)
            m0, m1 = spectrum.sum(), spectrum@omega
            if abs(m0-mass) > 1e-8*max(mass,1e-14) or abs(m1-first) > 1e-8*max(abs(first),mass,1e-14):
                raise ValueError("Broadened quadrature fails exact moment check")
            l1,dev = difference(spectrum,previous) if previous is not None else (float("inf"),float("inf"))
            if exhausted or (previous is not None and l1 < 1e-3 and dev < 1.):
                return spectrum, dict(depth=j+1, l1=0. if exhausted else l1,
                                      deviance=0. if exhausted else dev, mass=mass, first=first,
                                      lapack_fallbacks=lapack_fallbacks)
            previous = spectrum
        beta.append(b)
        v = w/b
    raise ValueError(f"Spectral Lanczos failed at depth {cap}: L1={l1:g}, deviance={dev:g}")

def spectrum_field(theta, field, index=0, n=12):  # Momentum-averaged transverse DSF, with resolution.
    local = spins(n); h = sum(t*op for t,op in zip(jkg_design()@theta,basis(n)))-field*sum(site[2] for site in local)
    energy, ground, info = ground_space(h, 2400+index//2+(100 if index%2 else 0))
    omega = np.arange(-80.,900.+.025,.05); spectrum = np.zeros(len(omega)); exact = np.zeros(2)
    assert omega[0]+2*field < -1 and omega[-1]+2*field > np.max(np.asarray(abs(h).sum(axis=1)))-energy+1
    for state in ground.T:
        moments = np.zeros((n,2,2))
        for site in range(n):
            for axis in range(2):
                v = local[site][axis]@state; v -= ground@(ground.conj().T@v)
                moments[site,axis] = [np.vdot(v,v).real,np.vdot(v,h@v-(energy+2*field)*v).real]
                if site<2:
                    line, _ = response(h,energy,v,omega+2*field)
                    spectrum += line/(4*ground.shape[1])  # Mean over sublattices, x/y, and ground states.
        np.testing.assert_allclose(moments[:2].mean(axis=(0,1)),moments.mean(axis=(0,1)),atol=1e-9,rtol=1e-9)
        exact += moments.mean(axis=(0,1))/ground.shape[1]
    np.testing.assert_allclose([spectrum.sum(),spectrum@omega],exact,atol=1e-8,rtol=1e-8)
    return dict(omega=omega,mass=spectrum,exact_moments=exact,residual=info['residual'])
