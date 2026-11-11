"""Honeycomb operators, converged spectra and exact HT/SF/FD reference moments."""

from functools import lru_cache
import time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from scipy.linalg import eigh, eigh_tridiagonal
from scipy.ndimage import gaussian_filter1d

DIRECTIONS = np.array([[0., 0., 1.], [1., 0., 0.], [1., -1., 0.]])
DIRECTIONS[2] /= np.sqrt(2.)

@lru_cache(None)
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

def exchange_terms(n):  # Enumerate J, K, Gamma interactions.
    """Parameter index, sites and spin axes for every J/K/Gamma Pauli term."""
    for gamma, pairs in enumerate(geometry(n)['bonds'].values()):
        a, b = [axis for axis in range(3) if axis != gamma]
        axes = [(0,k,k) for k in range(3)]+[(1,gamma,gamma),(2,a,b),(2,b,a)]
        for i, j in pairs:
            for parameter, u, v in axes:
                yield parameter, i, j, u, v

@lru_cache(None)
def operators(n):  # Construct sparse Pauli operators.
    states = np.arange(2**n)
    local = []
    for i in range(n):
        bit = (states >> i) & 1
        flipped = states ^ (1 << i)
        local.append([
            sp.csr_matrix((np.ones(len(states), complex), (flipped, states)), shape=(2**n,)*2),
            sp.csr_matrix((np.where(bit == 0, 1j, -1j), (flipped, states)), shape=(2**n,)*2),
            sp.diags(np.where(bit == 0, 1., -1.), format="csr", dtype=complex)])
    basis = [sp.csr_matrix((2**n,)*2, dtype=complex) for _ in range(3)]
    for parameter, i, j, a, b in exchange_terms(n):
        basis[parameter] += local[i][a]@local[j][b]
    magnets = [sum(d[k]*local[i][k] for i in range(n) for k in range(3)).tocsr()
               for d in DIRECTIONS]
    return local, basis, magnets

def hamiltonian(theta, n, field=0., setting=0):  # Combine exchange and applied field.
    _, basis, magnets = operators(n)
    return (sum(t*v for t,v in zip(theta, basis)) - field*magnets[setting]).tocsr()

@lru_cache(None)
def translation_blocks(n):  # Separate lattice-momentum sectors.
    """Exact orbit bases for every character of the finite translation group."""
    g = geometry(n)
    lx,ly,shear = {8:(2,2,0),12:(2,3,-1),16:(4,2,0)}[n]
    translations = [(x,y) for y in range(ly) for x in range(lx)]
    cells = g["cells"]
    states = np.arange(2**n,dtype=np.int64)
    translated = []
    for tx,ty in translations:
        moved = np.zeros_like(states)
        for site,(x,y,sub) in enumerate(cells):
            turns,yy = divmod(y+ty,ly)
            xx = (x+tx-turns*shear)%lx
            destination = 2*(yy*lx+xx)+sub
            moved |= ((states>>site)&1)<<destination
        translated.append(moved)
    translated = np.array(translated)
    representatives = np.min(translated,axis=0)
    reps = np.flatnonzero(representatives==states)
    momenta = g["momenta"][:len(translations)]
    real_translations = g["positions"][::2]
    projectors,bases = [],[]
    _,full_basis,_ = operators(n)
    for momentum in momenta:
        characters = np.exp(-1j*real_translations@momentum)
        rows,columns,values = [],[],[]
        column = 0
        for representative in reps:
            orbit,inverse = np.unique(translated[:,representative],return_inverse=True)
            weights = np.zeros(len(orbit),complex)
            np.add.at(weights,inverse,characters)
            norm = np.linalg.norm(weights)
            if norm < 1e-10:
                continue
            rows.extend(orbit.tolist())
            columns.extend([column]*len(orbit))
            values.extend((weights/norm).tolist())
            column += 1
        u = sp.csr_matrix((values,(rows,columns)),shape=(2**n,column))
        reduced = [(u.conj().T@h@u).tocsr() for h in full_basis]
        for h in reduced:
            anti = h-h.conj().T
            if anti.nnz and abs(anti.data).max()>1e-11:
                raise ValueError("Non-Hermitian symmetry block")
        projectors.append(u)
        bases.append(reduced)
    if sum(u.shape[1] for u in projectors)!=2**n:
        raise ValueError("Incomplete momentum-sector decomposition")
    return momenta,real_translations,projectors,bases

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

def channels(n=12):  # List momentum and spin settings.
    axes = np.eye(3)
    pairs = [(axes[a], axes[(a+1)%3]) for a in range(3)]
    pairs += [((axes[a]-axes[b])/np.sqrt(2), (axes[a]+axes[b])/np.sqrt(2))
              for a,b in [(0,1),(0,2),(1,2)]]
    return np.array([np.r_[q,np.zeros(3),pol] for direction,b in pairs
                     for pol in (b,np.cross(direction,b)) for q in geometry(n)["momenta"]])

def unique_probes(n):  # Remove global-phase duplicates.
    rows = channels(n)
    phases = np.exp(-1j*rows[:,:2]@geometry(n)["positions"].T)/np.sqrt(n)
    coefficients = phases[:,:,None]*rows[:,None,5:]
    unique, mapping, keys = [], [], {}
    for c in coefficients:
        flat = c.ravel()
        pivot = flat[np.argmax(abs(flat))]
        canonical = flat*np.exp(-1j*np.angle(pivot))
        key = tuple(np.round(canonical.real,11)) + tuple(np.round(canonical.imag,11))
        if key not in keys:
            keys[key] = len(unique)
            unique.append(c)
        mapping.append(keys[key])
    return np.array(unique), np.array(mapping)

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

def response(h, e0, vector, omega, depths=(128,256,512,1024), force_depth=None):  # Converge a Lanczos spectral response.
    """Lanczos quadrature; two-pass full reorthogonalization, converged after broadening."""
    mass = float(np.vdot(vector,vector).real)
    first = float(np.vdot(vector, h@vector-e0*vector).real)
    if mass < 1e-24:
        return np.zeros(len(omega)), dict(depth=0, l1=0., deviance=0., mass=mass, first=first)
    cap = min(max(depths) if force_depth is None else force_depth, h.shape[0])
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
            if exhausted or (force_depth is None and previous is not None and l1 < 1e-3 and dev < 1.):
                return spectrum, dict(depth=j+1, l1=0. if exhausted else l1,
                                      deviance=0. if exhausted else dev, mass=mass, first=first,
                                      lapack_fallbacks=lapack_fallbacks)
            previous = spectrum
        if exhausted:
            break
        beta.append(b)
        v = w/b
    if force_depth is not None:
        return spectrum, dict(depth=cap,l1=l1,deviance=dev,mass=mass,first=first)
    raise ValueError(f"Spectral Lanczos failed at depth {cap}: L1={l1:g}, deviance={dev:g}")

def spectrum(theta,n,omega):  # Compute the zero-temperature inelastic DSF.
    """The same spectral Lanczos calculation, in exact translation sectors."""
    started = time.perf_counter()
    momenta,translations,projectors,bases = translation_blocks(n)
    hamiltonians = [sum(t*b for t,b in zip(theta,basis)).tocsr() for basis in bases]
    sector_ground = [ground_space(h,seed=19+i) for i,h in enumerate(hamiltonians)]
    e0 = min(item[0] for item in sector_ground)
    ground_states,labels = [],[]
    for sector,(energy,ground,info) in enumerate(sector_ground):
        if energy-e0<=1e-10:
            for level,vector in zip(info["energies"],ground.T):
                if level-e0<=1e-10:
                    ground_states.append(projectors[sector]@vector)
                    labels.append(sector)
    ground = np.column_stack(ground_states)
    np.testing.assert_allclose(ground.conj().T@ground,np.eye(len(labels)),atol=1e-10,rtol=0)
    local,_,_ = operators(n)
    full_h = hamiltonian(theta,n)
    residual = max(np.linalg.norm(full_h@v-e0*v) for v in ground.T)
    if residual>1e-10*max(1.,abs(e0)):
        raise ValueError("Full-space ground residual failed after symmetry reduction")
    coefficients,mapping = unique_probes(n)
    source_lines = [np.flatnonzero(mapping==i)[0] for i in range(len(coefficients))]
    probe_q = channels(n)[source_lines,:2]
    result = np.zeros((len(coefficients),len(omega)))
    diagnostics = []
    for initial,initial_sector in zip(ground.T,labels):
        acted = np.array([[op@initial for op in site] for site in local])
        for i,(c,q) in enumerate(zip(coefficients,probe_q)):
            target = np.exp(1j*translations@(momenta[initial_sector]+q))
            distances = [np.max(abs(np.exp(1j*translations@k)-target)) for k in momenta]
            sector = int(np.argmin(distances))
            if distances[sector]>1e-10:
                raise ValueError("Probe momentum does not belong to the torus")
            v = np.einsum("ia,iad->d",c,acted,optimize=True)
            v -= ground@(ground.conj().T@v)  # Exclude elastic transitions within the ground subspace.
            projected = projectors[sector].conj().T@v
            mass = np.vdot(v,v).real
            if abs(np.vdot(projected,projected).real-mass)>1e-10*max(1.,mass):
                raise ValueError("Probe has weight outside the predicted momentum sector")
            values,report = response(hamiltonians[sector],e0,projected,omega)
            first = np.vdot(v,full_h@v-e0*v).real
            if abs(report["first"]-first)>1e-8*max(1.,abs(first)):
                raise ValueError("Reduced and full-space first moments disagree")
            report["sector"] = sector
            result[i] += values/len(labels)  # Equal mixture of degenerate ground states.
            diagnostics.append(report)
    info = dict(rank=len(labels),residual=float(residual),ground_sectors=labels,
                deviance_convention="2*Poisson log-likelihood ratio",
                block_dimensions=[u.shape[1] for u in projectors],backend="translation-resolved Lanczos")
    return result,mapping,dict(**info,channels=len(mapping),unique_channels=len(result),
            seconds=time.perf_counter()-started,responses=diagnostics)

def acted_spins(state, ground, n):  # Project spin excitations above ground.
    local, _, _ = operators(n)
    acted = np.column_stack([op@state for site in local for op in site])
    return acted-ground@(ground.conj().T@acted)

def quadratic(coefficients, matrix):  # Evaluate moments in each channel.
    values = np.einsum('mi,ij,mj->m', coefficients.conj(), matrix, coefficients, optimize=True)
    np.testing.assert_allclose(values.imag, 0., atol=1e-9)
    return values.real

@lru_cache(None)
def layouts(n=12):  # Build HT and SF linear maps.
    """Compile all channel definitions and leading maps, without fitted couplings."""
    g = geometry(n); cells = n//2
    reduced = g['momenta'][:cells]
    reciprocal = g['momenta'][cells]-reduced[0]
    momenta = np.concatenate([reduced+k*reciprocal for k in range(3)])
    polarizations = list(np.eye(3, dtype=complex))
    for a, b in [(0, 1), (0, 2), (1, 2)]:
        polarizations += [(np.eye(3)[a]+np.eye(3)[b])/np.sqrt(2),
                          (np.eye(3)[a]+1j*np.eye(3)[b])/np.sqrt(2)]
    coefficients, settings, seen = [], [], set()

    def add(setting, c):  # Keep each distinct measurement once.
        flat = c.ravel()
        canonical = flat*np.exp(-1j*np.angle(flat[np.argmax(abs(flat))]))
        key = (setting, *np.round(canonical.real, 11), *np.round(canonical.imag, 11))
        if key not in seen:
            seen.add(key); coefficients.append(flat); settings.append(setting)

    for s in range(3):
        add(s, g['signs'][:, None]*np.eye(3)[s]/np.sqrt(n))
    for s in range(3):
        for q in momenta:
            phase = np.exp(-1j*g['positions']@q)/np.sqrt(n)
            for p in polarizations:
                add(s, phase[:, None]*p)
    coefficients, settings = np.array(coefficients), np.array(settings)
    _, basis, _ = operators(n)
    pauli = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]])
    design = np.zeros((len(coefficients), 3))
    for s, direction in enumerate(DIRECTIONS):
        _, u = np.linalg.eigh(np.einsum('a,aij->ij', direction, pauli))
        vacuum = u[:, -1]
        for _ in range(n-1):
            vacuum = np.kron(u[:, -1], vacuum)
        acted = acted_spins(vacuum, vacuum[:, None], n)
        ids = np.flatnonzero(settings == s)
        for parameter, op in enumerate(basis):
            energy = np.vdot(vacuum, op@vacuum).real
            design[ids, parameter] = quadratic(coefficients[ids], acted.conj().T@(op@acted-energy*acted))
    keep = (np.linalg.norm(design, axis=1) > 1e-10) & (settings != 1)
    ht_rows, ht_design = [], []
    for gamma, pairs in enumerate(g['bonds'].values()):
        i, j = pairs[0]
        for a in range(3):
            for b in range(3):
                row = (float(a == b), float(a == b == gamma),
                       float(a != b and a != gamma and b != gamma))
                if any(row):
                    ht_rows.append((gamma, i, j, a, b)); ht_design.append(row)
    return dict(sf_coefficients=coefficients[keep], sf_settings=settings[keep], sf_design=design[keep],
                ht_rows=np.array(ht_rows), ht_design=np.array(ht_design), field=32., beta=.05)

_PRODUCT = {
    (0,0):(1.,0), (0,1):(1.,1), (0,2):(1.,2), (0,3):(1.,3),
    (1,0):(1.,1), (2,0):(1.,2), (3,0):(1.,3),
    (1,1):(1.,0), (2,2):(1.,0), (3,3):(1.,0),
    (1,2):(1j,3), (2,1):(-1j,3), (2,3):(1j,1),
    (3,2):(-1j,1), (3,1):(1j,2), (1,3):(-1j,2)}

def multiply(left, right):  # Multiply two Pauli strings.
    phase, output = 1., []
    for a, b in zip(left, right, strict=True):
        factor, axis = _PRODUCT[a,b]; phase *= factor; output.append(axis)
    return phase, tuple(output)

def commutator(terms, right):  # Commute a sum with one string.
    output = {}
    for left, coefficient in terms.items():
        lr, product = multiply(left, right); rl, _ = multiply(right, left)
        value = coefficient*(lr-rl)
        if abs(value) > 1e-14:
            output[product] = output.get(product, 0.)+value
    return {key: value for key, value in output.items() if abs(value) > 1e-13}

@lru_cache(None)
def fd_compiler(n):  # Expand FD double commutators.
    terms = [{} for _ in range(3)]
    for parameter, i, j, a, b in exchange_terms(n):
        string = [0]*n
        string[i], string[j] = a+1, b+1
        key = tuple(string)
        terms[parameter][key] = terms[parameter].get(key, 0.)+1.
    compiled, labels = [], []
    for mu in range(6):
        for nu in range(3*n):
            left, right = [0]*n, [0]*n
            left[mu//3], right[nu//3] = mu%3+1, nu%3+1
            columns = []
            for dictionary in terms:
                outer = commutator(commutator(dictionary, tuple(left)), tuple(right))
                columns.append([(-coefficient, tuple(3*i+axis-1 for i, axis in enumerate(string) if axis))
                                for string, coefficient in outer.items()])
            compiled.append(columns); labels.append((mu,nu))
    return compiled, np.array(labels)

def one_target(theta, n=12):  # Calculate HT, SF, FD references.
    layout = layouts(n)
    local, _, _ = operators(n)
    moments = np.zeros(len(layout['sf_design']))
    for setting in (0, 2):
        h = hamiltonian(theta, n, 32., setting)
        energy, ground, _ = ground_space(h, seed=17+setting)
        ids = np.flatnonzero(layout['sf_settings'] == setting)
        matrix = np.zeros((3*n, 3*n), complex)
        for state in ground.T:
            acted = acted_spins(state, ground, n)
            matrix += acted.conj().T@(h@acted-(energy+64)*acted)/ground.shape[1]  # Center SF moments at 2B=64.
        moments[ids] = quadratic(layout['sf_coefficients'][ids], matrix)

    probes = [local[i][a]@local[j][b] for _, i, j, a, b in layout['ht_rows']]
    energies, diagonal = [], []
    _, _, projectors, blocks = translation_blocks(n)
    for projector, block in zip(projectors, blocks):
        e, v = eigh(sum(t*op for t, op in zip(theta, block)).toarray(), driver='evd', check_finite=False)
        values = []
        for probe in probes:
            value = np.einsum('ij,ij->j', v.conj(), (projector.conj().T@probe@projector)@v)
            np.testing.assert_allclose(value.imag, 0., atol=2e-12); values.append(value.real)
        energies.append(e); diagonal.append(np.array(values).T)
    e, d = np.concatenate(energies), np.concatenate(diagonal)
    assert len(e) == 2**n
    weight = np.exp(-.05*(e-e.min())); weight /= weight.sum()  # Complete Gibbs trace at beta=0.05.
    ht = weight@d

    h = hamiltonian(theta, n)
    _, ground, _ = ground_space(h, seed=19)
    statics = np.zeros((3*n,3*n), complex); first = np.zeros_like(statics)
    for state in ground.T:
        acted = np.column_stack([op@state for site in local for op in site])
        energy = np.vdot(state, h@state).real
        statics += acted.conj().T@acted/ground.shape[1]
        first += acted.conj().T@(h@acted-energy*acted)/ground.shape[1]
    compiled, labels = fd_compiler(n)
    design = np.array([[sum(coefficient*statics[active] for coefficient, active in column)
                        for column in columns] for columns in compiled], complex)
    mu, nu = labels.T
    symmetric = first[mu,nu]+first[nu,mu]  # FD right-hand side from symmetrized first moments.
    matrix = np.vstack([design.real, design.imag]); rhs = np.r_[symmetric.real, symmetric.imag]
    estimate, _, rank, _ = np.linalg.lstsq(matrix, rhs, rcond=1e-12)
    assert rank == 3 and np.linalg.norm(matrix@theta-rhs)/np.linalg.norm(rhs) < 1e-9
    return dict(sf_moments=moments, sf_estimate=np.linalg.pinv(layout['sf_design'])@moments,
                ht_correlations=ht, ht_estimate=-np.linalg.pinv(layout['ht_design'])@ht/.05,
                fd_statics=statics, fd_first_moments=first, fd_designs=matrix, fd_rhs=rhs,
                fd_estimates=estimate, fd_row_labels=labels)
