"""High-temperature tomography: exact moments, inversion, and saved-data figures.
Paulis have eigenvalues +/-1; moments are divided by 2*pi; J_star=1.
"""
import os
for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'
import argparse
import hashlib
import json
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import numpy as np
from scipy import sparse
from scipy.linalg import eigh
from scipy.optimize import least_squares
HERE = Path(__file__).resolve().parent
DATA = HERE/'data'
QUANTILES = [.375, .5, .625]  # Central 25% band: lower edge, median, upper edge.
SIGMAS = np.array([.005, .01, .02])
TRIALS, SEED = 5000, 20261015  # Parameter-sweep noise trials and seed.

def load(group):  # Load saved study data.
    with np.load(DATA/'results.npz', allow_pickle=False) as data:
        return {k[len(group)+1:]: data[k] for k in data.files if k.startswith(group+'_')}

def digest(path):  # Compute a file checksum.
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

@lru_cache(None)
def spins(n):  # Build site Pauli matrices.
    states = np.arange(2**n)
    return [[sparse.csr_matrix((values, (states ^ ((axis < 2) << i), states)), shape=(2**n,)*2)
             for axis, values in enumerate((np.ones(2**n), 1j*(-1.)**((states >> i) & 1),
                                             (-1.)**((states >> i) & 1)))] for i in range(n)]

@lru_cache(None)
def geometry(n=12):  # Construct the periodic honeycomb lattice.
    """Honeycomb torus: wraps (2,0),(-1,3) at N=12; (2,0),(0,2) at N=8."""
    lx, ly, shear = {8: (2, 2, 0), 12: (2, 3, -1)}[n]
    def index(x, y, sub):  # Map a cell to its site index.
        turns, y = divmod(y, ly)
        return 2*(y*lx+(x-turns*shear) % lx)+sub
    cells = [(x, y, s) for y in range(ly) for x in range(lx) for s in (0, 1)]
    lattice = np.array([[np.sqrt(3)/2, -np.sqrt(3)/2], [1.5, 1.5]])
    positions = np.array([lattice @ [x, y]+[0, s] for x, y, s in cells])
    momenta = np.array([2*np.pi*np.linalg.inv(lattice).T @ [kx/lx+gx, (ky-shear*kx/lx)/ly+gy]
        for gx, gy in ((0, 0), (1, 0), (0, 1)) for kx in range(lx) for ky in range(ly)])
    bonds = [[(index(x, y, 0), index(x+dx, y+dy, 1)) for x, y, s in cells if s == 0]
             for dx, dy in ((-1, 0), (0, -1), (0, 0))]
    moves = [[index(x+tx, y+ty, s) for x, y, s in cells] for ty in range(ly) for tx in range(lx)]
    return dict(bonds=bonds, positions=positions, momenta=momenta, moves=moves)

def jkg_design():  # Map J, K, Gamma to exchanges.
    return np.array([(a == b, a == b == g, a != b and a != g and b != g)
                     for g, a, b in product(range(3), repeat=3)], dtype=float)

def bond_layout(n=12):  # Select measured bond components.
    rows = np.array([(g, *bonds[0], a, b) for g, bonds in enumerate(geometry(n)['bonds'])
                     for a, b in product(range(3), repeat=2)])
    return rows, jkg_design(), {3: np.array([18, 26, 19]), 15: np.flatnonzero(jkg_design().any(axis=1))}

@lru_cache(None)
def honeycomb_basis(n=12):  # Build the exchange operators.
    local = spins(n)
    return [sum(local[i][a] @ local[j][b] for i, j in bonds)
            for bonds in geometry(n)['bonds'] for a, b in product(range(3), repeat=2)]

@lru_cache(None)
def momentum_blocks(n=12):  # Split operators into momentum sectors.
    """All translation sectors, retaining the complete 2**n-dimensional space."""
    g, states = geometry(n), np.arange(2**n, dtype=np.int64)
    translated = np.array([sum(((states >> i) & 1) << dest for i, dest in enumerate(move))
                           for move in g['moves']])
    blocks = []
    for q in g['momenta'][:n//2]:
        characters = np.exp(-1j*g['positions'][::2] @ q)
        rows, columns, values, column = [], [], [], 0
        for state in np.flatnonzero(np.min(translated, axis=0) == states):
            orbit, inverse = np.unique(translated[:, state], return_inverse=True)
            weights = np.zeros(len(orbit), complex)
            np.add.at(weights, inverse, characters)
            norm = np.linalg.norm(weights)
            if norm < 1e-10:
                continue
            rows.extend(orbit); columns.extend([column]*len(orbit)); values.extend(weights/norm)
            column += 1
        u = sparse.csr_matrix((values, (rows, columns)), shape=(2**n, column))
        blocks.append((u, [(u.conj().T @ h @ u).tocsr() for h in honeycomb_basis(n)]))
    assert sum(u.shape[1] for u, _ in blocks) == 2**n  # Keep all states; no energy truncation.
    return blocks

def thermal_pairs(theta, betas, pairs=None, n=12):  # Compute thermal spin correlations.
    """Complete Gibbs traces of Pauli pairs; theta is ordered (bond,spin,spin)."""
    pairs = bond_layout(n)[0][:, [1, 3, 2, 4]] if pairs is None else pairs
    local, energies, diagonal = spins(n), [], []
    for u, basis in momentum_blocks(n):
        e, v = eigh(sum(t*h for t, h in zip(theta, basis)).toarray(), driver='evd', check_finite=False)
        values = np.array([np.einsum('ij,ij->j', v.conj(), (u.conj().T @ local[i][a] @ local[j][b] @ u) @ v)
                           for i, a, j, b in pairs])
        np.testing.assert_allclose(values.imag, 0, atol=1e-11)
        energies.append(e); diagonal.append(values.real.T)
    e = np.concatenate(energies)
    weights = np.exp(-np.atleast_1d(betas)[:, None]*(e-e.min()))  # Shift energies to keep exponentials bounded.
    return (weights/weights.sum(axis=1, keepdims=True)) @ np.concatenate(diagonal), e  # Gibbs-weighted correlations.

def dsf_layout(n=12):  # Map spin correlations to DSF integrals.
    """Normalized total-spin DSF integrals, with the beta=0 value 1 subtracted."""
    g = geometry(n)
    def ordered(i, a, j, b):  # Order sites in each pair.
        return (i, a, j, b) if i < j else (j, b, i, a)
    mapping = {(i, a, j, b): min(ordered(p[i], a, p[j], b) for p in g['moves'])
               for i, j in combinations(range(n), 2) for a, b in product(range(3), repeat=2)}
    pairs = sorted(set(mapping.values()))
    indices, literal = {row: k for k, row in enumerate(pairs)}, {}
    for gamma, bonds in enumerate(g['bonds']):
        for i, j in bonds:
            for a, b in product(range(3), repeat=2):
                key = ordered(i, a, j, b)
                literal[key] = literal.get(key, np.zeros(3))+jkg_design()[9*gamma+3*a+b]
    eye = np.eye(3, dtype=complex)
    polarizations = list(eye)+[(eye[a]+phase*eye[b])/np.sqrt(2)
        for a, b in combinations(range(3), 2) for phase in (1., -1., 1j, -1j)]
    momenta = np.concatenate([g['momenta'][:n//2]+k*(g['momenta'][n//2]-g['momenta'][0]) for k in range(3)])
    weights = np.zeros((len(momenta)*len(polarizations), len(pairs)))
    for row, (q, p) in enumerate(product(momenta, polarizations)):
        c = np.exp(-1j*g['positions'] @ q)[:, None]*p/np.sqrt(n)
        for (i, a, j, b), representative in mapping.items():
            weights[row, indices[representative]] += 2*np.real(c[i, a].conj()*c[j, b])
    return np.array(pairs), weights, weights @ np.array([literal.get(row, np.zeros(3)) for row in pairs])

@lru_cache(None)
def chain_map():  # Build moment polynomials and Jacobian.
    """Twelve chain features and analytic Jacobian; b then row-major exchange L."""
    import sympy as sp
    x = sp.symbols('v0:12', real=True)
    b, L = x[:3], sp.Matrix(3, 3, x[3:])
    static, second, slope, onsite = [], [], [], []
    for a in range(3):
        u, v = (a+1) % 3, (a+2) % 3
        static.append(-L[a, a])
        second.append(-8*(L[u, u]*L[v, v]-L[u, v]*L[v, u]))
        slope.append(-4*(L[a, a]*sum(L[r, s]**2 for r, s in product((u, v), repeat=2))
            -sum(L[a, r]*L[s, a]*L[s, r] for r, s in product((u, v), repeat=2)))
            +4*(L[u, u]*b[v]**2+L[v, v]*b[u]**2-(L[u, v]+L[v, u])*b[u]*b[v]))
        onsite.append(4*(b[u]**2+b[v]**2+sum(L[r, s]**2+L[s, r]**2 for r in (u, v) for s in range(3))))
    f = sp.Matrix([sp.expand(value) for value in static+second+slope+onsite])  # Collect the twelve measured coefficients.
    funcs = [sp.lambdify([x], obj, 'numpy', cse=True) for obj in (f, f.jacobian(x))]  # Evaluate polynomials and exact derivatives numerically.
    return lambda t: np.asarray(funcs[0](t), float).ravel(), lambda t: np.asarray(funcs[1](t), float)

def quantiles(errors, axis=-1):  # Compute medians and percentile bands.
    return np.moveaxis(np.quantile(errors, QUANTILES, axis=axis), 0, -1)

def moment_sweep(moments, design, betas, theta, sigmas, draws):  # Reconstruct couplings across temperatures.
    """Gaussian moment noise followed by -M^+ c/beta; central-25% ribbons."""
    inverse = np.linalg.pinv(design)  # Least-squares inverse of the leading HT map.
    estimates, noise = -(moments @ inverse.T)/betas[:, None], -draws @ inverse.T  # Clean estimates and projected unit noise.
    clean = np.linalg.norm(estimates-theta, axis=1)/np.linalg.norm(theta)  # Relative Euclidean coupling error.
    bands = np.array([quantiles(np.linalg.norm(estimates[:, None]-theta+
        s*noise[None]/betas[:, None, None], axis=-1)/np.linalg.norm(theta)) for s in sigmas])  # Noise is amplified by 1/beta.
    return dict(estimates=estimates, clean=clean, bands=bands)

def feature_comparison(data):  # Compare three versus fifteen measurements.
    draws = np.random.default_rng(20261008).normal(size=(TRIALS, 15))  # Share measurement noise between feature sets.
    small = [int(np.flatnonzero(np.all(data['rows_15'] == row, axis=1))[0]) for row in data['rows_3']]  # Locate the three shared measurements.
    fixed, result = np.flatnonzero(data['betas'] == .05)[0], {}
    for size, columns in ((3, small), (15, np.arange(15))):
        args = (data[f'design_{size}'], data['betas'], data['theta'], [.05], draws[:, columns])
        sweep = moment_sweep(data[f'correlations_{size}'], *args)
        noise = moment_sweep(data[f'correlations_{size}'][[fixed]], args[0], np.array([.05]),
                             data['theta'], data['sigmas'], draws[:, columns])
        result.update({f'clean_{size}': sweep['clean'], f'noise_stats_{size}': sweep['bands'][0],
                       f'sigma_stats_{size}': noise['bands'][:, 0]})
    return result

def chain_trial(index, theta, sigmas, replicates=5, n=12):  # Fit one chain with noisy coefficients.
    """Exact coefficients + noise; truth-initialized local LM fits, all retained."""
    polynomial, jacobian = chain_map()
    full, diagonal = -theta, polynomial(theta)
    draws = np.random.default_rng(np.random.SeedSequence([20261008, index])).normal(size=(replicates, 21))
    zdiag = np.column_stack([draws[:, [3, 7, 11]], draws[:, 12:]])  # Share static diagonal noise with full access.
    errors, records = np.empty((len(sigmas), 2, replicates)), []
    for level, sigma in enumerate(sigmas):
        errors[level, 0] = np.linalg.norm(-(full+sigma*draws[:, :12])-theta, axis=1)/np.linalg.norm(theta)
        for trial, noise in enumerate(zdiag):
            target = diagonal+sigma*noise
            fit = least_squares(lambda x: polynomial(x)-target, theta.copy(), jac=jacobian,  # Start at truth to test local stability.
                method='lm', ftol=1e-12, xtol=1e-12, gtol=1e-12, max_nfev=5000)
            records.append((fit.x, np.linalg.norm(fit.fun), fit.status))  # Retain every fit, including failed convergence.
            errors[level, 1, trial] = np.linalg.norm(fit.x-theta)/np.linalg.norm(theta)
    return dict(errors=errors, estimates=np.array([r[0] for r in records]), residuals=np.array([r[1] for r in records]),
                statuses=np.array([r[2] for r in records]), full_coefficients=full, diagonal_coefficients=diagonal)

def chain_summary(errors, bootstraps=5000):  # Estimate mean error and its sampling uncertainty.
    per_model, rng = errors.mean(axis=-1), np.random.default_rng(20261010)  # Average noise trials within each Hamiltonian.
    samples = np.concatenate([per_model[rng.integers(len(errors), size=(min(64, bootstraps-i), len(errors)))].mean(axis=1)  # Resample Hamiltonians with replacement.
                              for i in range(0, bootstraps, 64)])
    low, high = np.quantile(samples, [.375, .625], axis=0)  # Central 25% of resampled means, not individual errors.
    return dict(per_hamiltonian_mean=per_model, ensemble_mean=per_model.mean(axis=0), ribbon_low=low, ribbon_high=high)

def parameter_summary(theta, moments, order, betas, sigmas=SIGMAS):  # Summarize error versus parameter count.
    """Compare parameter counts using known supports and temperatures chosen on validation data."""
    medians = np.empty((len(sigmas), len(betas), len(order)))
    for member in range(len(order)):
        draws = np.random.default_rng(np.random.SeedSequence([SEED, member])).normal(size=(TRIALS, 27))  # Reuse noise across parameter counts and strengths.
        for ip, p in enumerate(np.r_[1, np.arange(3, 28, 3)]):
            ids = order[member, :p]  # The known set of nonzero, unknown couplings.
            bias = -moments[ip, member, ids]/betas[ip]-theta[ip, member, ids]  # Finite-temperature error before noise.
            noise = -np.sqrt(27/828)*draws[:, ids]/betas[ip]  # 27 HT vs 828 SF moments; equal total measurement effort.
            medians[:, ip, member] = [np.median(np.linalg.norm(bias+s*noise, axis=1)) for s in sigmas]  # Median over noise for each Hamiltonian.
    return dict(member_medians=medians, bands=quantiles(medians, axis=2))  # Then summarize variation across Hamiltonians.

def calculate_cell(task):  # Calculate or reload one Hamiltonian.
    study, index, folder = task
    data = load('chain' if study == 'coefficients' else 'parameters')
    path = folder/f'{study}_{index:04d}.npz'
    signature = digest(__file__)+digest(DATA/'results.npz')  # Reject checkpoints from different code or data.
    if path.exists():
        with np.load(path) as saved:
            if str(saved['signature']) != signature:
                raise ValueError(f'Stale checkpoint: {path}')
            return saved['errors' if study == 'coefficients' else 'moments']
    if study == 'coefficients':
        result = chain_trial(index, data['theta'][index], data['sigmas'])
    else:
        ip, member = divmod(index, data['theta'].shape[1])
        result = dict(moments=thermal_pairs(data['theta'][ip, member], [data['betas'][ip]])[0][0])
    temporary = path.with_suffix('.tmp.npz')
    np.savez_compressed(temporary, signature=signature, **result)
    temporary.replace(path)  # Publish only a fully written checkpoint.
    return result['errors' if study == 'coefficients' else 'moments']

def calculate(study, workers):  # Run the selected numerical study.
    folder = HERE.parent/'runs'/'ht'/'work'
    folder.mkdir(parents=True, exist_ok=True)
    data = load('chain' if study == 'coefficients' else study)
    if study in ('temperature', 'supplement'):
        pairs, weights, design = dsf_layout() if study == 'temperature' else (None, None, None)
        moments, _ = thermal_pairs(jkg_design() @ data['theta'], data['betas'], pairs)
        if study == 'temperature':
            moments = moments @ weights.T
            draws = np.random.default_rng(20261056).normal(size=(TRIALS, len(design)))
            result = dict(moments=moments, design=design, **moment_sweep(moments, design,
                          data['betas'], data['theta'], data['sigmas'], draws))
        else:
            data.update({f'correlations_{size}': moments[:, ids] for size, ids in bond_layout()[2].items()})
            result = feature_comparison(data)
    else:
        count = len(data['theta']) if study == 'coefficients' else np.prod(data['theta'].shape[:2])
        with ProcessPoolExecutor(max_workers=workers) as pool:
            cells = list(pool.map(calculate_cell, [(study, i, folder) for i in range(count)]))
        if study == 'coefficients':
            result = dict(errors=np.array(cells), **chain_summary(np.array(cells)))
        else:
            moments = np.array(cells).reshape(data['theta'].shape)
            result = dict(moments=moments, **parameter_summary(data['theta'], moments, data['order'], data['betas'], data['sigmas']))
    np.savez_compressed(folder/f'{study}_results.npz', **result)
    print(folder/f'{study}_results.npz')

def plot(data, output=HERE.parent/'runs'/'ht'/'figures'):  # Draw the saved benchmark figure.
    """Six-panel HT/SF comparison; SF curves are saved references."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import NullLocator, NullFormatter
    style = json.loads((DATA/'settings.json').read_text())['figure']
    plt.rcParams.update(style['rc'])
    fig = plt.figure(figsize=(180/25.4, 76/25.4))
    def curve(ax, x, y, color, label, ls='-', marker='', lw=1.25, alpha=.88):  # Draw a curve and uncertainty band.
        assert len(np.unique(x)) >= 6
        if y.ndim == 2:
            ax.fill_between(x, y[:, 0], y[:, 2], color=color, alpha=.13, linewidth=0)
            y = y[:, 1]
        ax.plot(x, y, color=color, label=label, ls=ls, lw=lw, alpha=alpha)
        if marker:
            ax.plot(x, y, ls='none', marker=marker, ms=2.1, color=color, alpha=alpha)
    for i, panel in enumerate(style['panels']):
        method, col = ('ht', 'sf')[i//3], i % 3
        ax = fig.add_axes(panel['position'])
        ax.set(**panel['axes'])
        ax.xaxis.set_minor_locator(NullLocator())
        ax.yaxis.set_minor_formatter(NullFormatter())
        ax.set_title(panel['title'], fontfamily='sans-serif', fontsize=9, pad=8)
        ax.text(-.037/panel['position'][2], 1., f'({"abcdef"[i]})', fontfamily='sans-serif', fontsize=9,
                transform=ax.title.get_transform(), ha='left', va=ax.title.get_va())
        x = data[panel['x']]
        if col == 1:
            for access, color in enumerate(style['access_colors'][method]):
                ax.plot(x, data[method+'_member_means'][:12, :, access].T, color=color, alpha=.16, lw=.45, zorder=1)
                q = np.column_stack([data[method+'_'+k][:, access] for k in ('low', 'mean', 'high')])
                curve(ax, x, q, color, ('full DSF access', 'diagonal DSF access')[access], marker='o', lw=1.3)
        else:
            for level, color in enumerate(style['colors'][method]):
                q = data[method+'_quantiles' if col == 0 else f'dimension_{method}_quantiles'][level]
                curve(ax, x, q, color, rf'$\sigma={data["sigmas"][level]:g}$', '--',
                      '' if col == 0 else ('o' if method == 'ht' else 's'), lw=1.25 if col == 0 else 1.15)
            if col == 0:
                curve(ax, x, data[method+'_clean'], style['colors'][method][1], 'noiseless', lw=1.1, alpha=.85)
                lx, ly = np.log(ax.get_xlim()), np.log(ax.get_ylim())
                cx, cy = np.exp([lx[0]+.35*np.diff(lx)[0], ly[0]+.34*np.diff(ly)[0]])
                guide = np.exp(np.linspace(np.log(cx)-.13*np.diff(lx)[0], np.log(cx)+.13*np.diff(lx)[0], 40))
                ax.plot(guide, cy*cx/guide, color='#B98200', lw=1.1)
                ax.annotate(panel['guide'], (cx, cy), xytext=(0, -6), textcoords='offset points',
                            ha='center', va='top', color='#B98200', fontsize=8)
        handles, labels = ax.get_legend_handles_labels()
        order = [-1, 0, 1, 2] if col == 0 else list(range(len(handles)))
        ax.legend([handles[j] for j in order], [labels[j] for j in order], **panel['legend'])
        ax.grid(which='major', color='#E2E5E9', linewidth=.45)
        if col != 1:
            ax.grid(which='minor', axis='y', color='#F0F1F3', linewidth=.3)
    output.mkdir(parents=True, exist_ok=True)
    for ext in ('pdf', 'png'):
        fig.savefig(output/f'fig2_ht_sf_six_panel.{ext}', dpi=300, facecolor='white')
    plt.close(fig)
    print(output/'fig2_ht_sf_six_panel.pdf')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('check', 'plot', 'calculate'))
    parser.add_argument('--study', choices=('temperature', 'supplement', 'coefficients', 'parameters'), default='temperature')
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    args = parser.parse_args()
    if args.command == 'check':
        subprocess.run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', str(HERE), '-p', 'test.py'], check=True, cwd=HERE.parent)
    elif args.command == 'plot':
        plot(load('figure'))
    else:
        calculate(args.study, args.workers)

