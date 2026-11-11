"""Try a small FD reconstruction or reproduce the supplement figures."""
import argparse
import csv
import os
from pathlib import Path

for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'
os.environ.setdefault('MPLBACKEND', 'Agg')

import numpy as np

if __package__:
    from .physics import CLASSES, chain_design, design, embedding, noisy_errors, recover, relative_error, thermal_moments
else:
    from physics import CLASSES, chain_design, design, embedding, noisy_errors, recover, relative_error, thermal_moments

HERE = Path(__file__).resolve().parent
DATA = HERE/'data'
COLORS = ('#69A9D4', '#3279B5', '#153F73')
INK = '#23252F'
QUANTILES = (.375, .5, .625)
MODELS = ('XYZ', 'XXZ', 'Heisenberg')
COUPLINGS = ([.4, .2, -1.], [1., 1., 1.5], [1., 1., 1.])
ALLOWED = (np.eye(3), np.array([[1., 0.], [1., 0.], [0., 1.]]), np.ones((3, 1)))
HAMILTONIANS = (
    (r'$H=\sum_i(J_xX_iX_{i+1}$', r'$\quad+J_yY_iY_{i+1}$', r'$\quad+J_zZ_iZ_{i+1})$'),
    (r'$H=\sum_i[J_\perp(X_iX_{i+1}$', r'$\qquad+Y_iY_{i+1})$', r'$\quad+J_zZ_iZ_{i+1}]$'),
    (r'$H=J\sum_i\boldsymbol{\sigma}_i\!\cdot\!\boldsymbol{\sigma}_{i+1}$',),
)


def xyz_mps_errors(c, first, truth, sigmas):  # Replay the original explicit 100-observation averages.
    rng = np.random.default_rng([0, 5611])
    errors = np.empty((len(sigmas), len(c), 5000))
    for i, clean in enumerate(np.c_[c, first]):
        raw = rng.standard_normal((5000, 100, 9))
        for j, sigma in enumerate(sigmas):
            measured = (clean + sigma*raw).mean(axis=1)
            estimate = recover(chain_design(measured[:, :3]), measured[:, 3:], ALLOWED[0])
            errors[j, i] = relative_error(estimate, truth)
    return errors


def worked_curves(data):  # Refit all worked-chain noise trials from the saved moments.
    beta, sigmas = data['chain_beta'], data['sigmas']
    for i, (truth, allowed) in enumerate(zip(COUPLINGS, ALLOWED)):
        for j, backend in enumerate(('ED', 'MPS')):
            c = data['chain_c'][i, j]
            first = chain_design(c) @ truth  # Generate clean first moments with the sum rule.
            if (i, j) == (0, 1):
                errors = xyz_mps_errors(c, first, truth, sigmas)
            else:
                errors = noisy_errors(c, first, truth, allowed, sigmas, 5000, [0, 5711, i, j], chain_design)
            # The ED endpoint is finite temperature. The MPS endpoint is its ground state.
            x = 1/beta if j == 0 else np.r_[1/beta[:-1], 0.]
            for sigma, values in zip(sigmas, np.quantile(errors, QUANTILES, axis=-1).transpose(1, 0, 2)):
                yield i+1, backend, sigma, x, values


def ensemble_curves(data, members):  # Summarize the 1,000 Hamiltonian-wise medians in each panel.
    assert members.shape == (2, 4, 1000, 3, 47)
    low, high = np.quantile(members, [QUANTILES[0], QUANTILES[2]], axis=2)
    median = np.median(members, axis=2)  # Preserve the archived float32 median convention.
    for g, family, s in np.ndindex(2, 4, 3):
        index = g, family, s
        yield 4*g+family, CLASSES[family], data['sigmas'][s], 1/data['ensemble_beta'], (
            low[index], median[index], high[index])


def demo():
    """Infer the three nearest-neighbor couplings of a six-spin XYZ chain."""
    indices = [3, 7, 11]  # xx, yy, zz entries of the first exchange matrix.
    truth = np.zeros(21)
    truth[indices] = COUPLINGS[0]
    static, first = thermal_moments(truth, [1.])
    estimate = recover(design(static), first, np.eye(21)[:, indices])[0]

    print('Six-spin XYZ chain at T = 1 (no measurement noise)')
    print(f'{"Coupling":<10}{"Original":>12}{"Recovered":>12}')
    for axis, i in zip('xyz', indices):
        print(f'{"J_" + axis:<10}{truth[i]:>12.6f}{estimate[i]:>12.6f}')
    print(f'Relative coupling error: {relative_error(estimate, truth):.2e}')


def check(data, members):  # Replay one archived member per panel and verify the moment identity.
    for g, c in np.ndindex(2, 4):
        static, first, truth = (data[key][g, c] for key in ('static', 'first', 'truth'))
        np.testing.assert_allclose(design(static) @ truth, first, atol=2e-10, rtol=0)
        seed = [0, 1907, g+1, c, 0]  # The archived geometry IDs are 1 and 2.
        errors = noisy_errors(static, first, truth, embedding(CLASSES[c]), data['sigmas'], 100, seed)
        np.testing.assert_allclose(np.median(errors.astype(np.float32), axis=-1), members[g, c, 0], rtol=2e-6)
    truth = data['truth'][0, -1]
    static, first = thermal_moments(truth, [.1, 1.])
    np.testing.assert_allclose(recover(design(static), first, np.eye(21)),
                               np.broadcast_to(truth, (2, 21)), atol=2e-10, rtol=0)
    print('Passed eight archived fits and independent six-spin ED recovery.')
    for geometry, static in zip(('chain', 'square'), data['u1_ground']):
        mz = abs(static[:, 2])
        expected = np.where(mz < 1e-10, 6, np.where(mz > 1-1e-10, 5, 7))
        s = np.linalg.svd(design(static) @ embedding('u1'), compute_uv=False)
        np.testing.assert_array_equal((s > 1e-8*s[:, :1]).sum(axis=1), expected)
        print(f'U(1) {geometry}: {(expected == 6).sum()} unmagnetized, '
              f'{(expected == 5).sum()} saturated, {(expected == 7).sum()} full rank.')


def schematic(ax):  # Draw the FDT relation and its schematic linear system.
    from matplotlib.patches import Rectangle

    ax.set(xlim=(0, 4.2), ylim=(0, 3.8), aspect='equal')
    ax.axis('off')
    ax.text(2.10, 3.42, r"$\chi^{\prime\prime}=\frac{1}{2}(1-e^{-\beta\omega})S$", ha='center', fontsize=14)
    ax.annotate('', (2.1, 2.50), (2.1, 3.16), arrowprops=dict(arrowstyle='->', color='#8198AA'))
    for x, label, color, values in [
        (1.14, r'$\mathsf{A}$', COLORS[1], [[.2,.7,.5],[.8,.3,.5],[.4,.6,.2],[.6,.2,.8],[.5,.8,.3],[.3,.5,.7]]),
        (2.04, r'$\boldsymbol{\lambda}$', INK, [[.35],[.7],[.5]]),
        (3.20, r'$\mathsf{b}$', '#B98200', [[.8],[.3],[.6],[.5],[.7],[.4]]),
    ]:
        n, m = np.shape(values)
        width = .30 if m == 3 else .15
        ax.text(x, 2.26 if n == 6 else 2.02, label, color=color, ha='center', fontsize=16, math_fontfamily='cm')
        for (i, j), value in np.ndenumerate(values):
            ax.add_patch(Rectangle((x+(j-m/2)*width, 1.90-.18*i-.09*(6-n)), width-.03, .15,
                                   facecolor=color, edgecolor='none', alpha=.16+.58*value))
    ax.text(2.60, 1.64, '$=$', fontsize=18, ha='center')
    ax.annotate('', (2.1, .64), (2.1, .92), arrowprops=dict(arrowstyle='->', color='#8198AA'))
    ax.text(2.10, .28, r'$H(\boldsymbol{\lambda})$', ha='center', fontsize=18)


def style():  # Match the supplement with fonts available on a clean checkout.
    import matplotlib.pyplot as plt
    from matplotlib.font_manager import fontManager

    available = {f.name for f in fontManager.ttflist}
    plt.rcParams.update({'font.family': 'serif', 'font.serif': ['Times New Roman', 'STIXGeneral'],
                         'mathtext.fontset': 'stix', 'font.size': 13, 'pdf.fonttype': 42,
                         'text.color': INK, 'axes.edgecolor': INK})
    return 'Avenir' if 'Avenir' in available else 'DejaVu Sans'


def render(curves, output, worked):  # Share plotting and export code across both supplement figures.
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch
    from matplotlib.ticker import LogLocator, NullFormatter, SymmetricalLogLocator

    sans = style()
    if worked:
        fig = plt.figure(figsize=(12.3, 4.8))
        axes = [fig.add_axes([x/12.3, .90/4.8, w/12.3, 3./4.8])
                for x, w in ((.18, 2.80), (3.65, 2.15), (6.65, 2.15), (9.65, 2.15))]
        schematic(axes[0])
        titles = ('Fluctuation-dissipation\ntomography', *MODELS)
    else:
        fig, panels = plt.subplots(2, 4, figsize=(14, 7.2), sharex=True, sharey=True)
        fig.subplots_adjust(left=.075, right=.985, bottom=.14, top=.86, wspace=.26, hspace=.30)
        axes = panels.ravel()
        titles = ('SU(2)-symmetric', 'U(1)-symmetric', r'$\mathbb{Z}_2$-symmetric', 'Generic')*2
    rows = []
    lower = .7 * min(np.min(values[0]) for _, _, _, _, values in curves)
    sigmas = sorted({sigma for _, _, sigma, _, _ in curves})
    for panel, backend, sigma, temperature, values in curves:
        order = np.argsort(temperature)
        x, (low, median, high) = temperature[order], np.asarray(values)[:, order]
        assert len(x) == 47 and np.all(np.diff(x) > 0)
        assert np.isfinite([low, median, high]).all() and np.all((low > 0) & (low <= median) & (median <= high))
        color = COLORS[sigmas.index(sigma)]
        ax = axes[panel]
        ax.fill_between(x, low, high, color=color, alpha=.10 if worked else .12, linewidth=0, zorder=1)
        ed = backend == 'ED'
        ax.plot(x, median, color=INK if ed else color, lw=1.6, alpha=.8,
                ls=(0, (5, 3)) if ed else '-', zorder=4 if ed else 3)
        if backend == 'MPS':
            ax.scatter(x[x == 0], median[x == 0], color=color, s=16, zorder=5, clip_on=False)
        rows.extend((chr(97+panel), backend, sigma, t, l, m, h) for t,l,m,h in zip(x, low, median, high))
    for i, (ax, title) in enumerate(zip(axes, titles)):
        ax.set_title(title, fontfamily=sans, fontsize=15, pad=14)
        if worked and i == 0:
            continue
        ax.set(xlim=(0 if worked else .001, 1000), yscale='log', ylim=(lower, .2), axisbelow=True)
        if worked:
            ax.set_xscale('symlog', linthresh=.001, linscale=.6)
            ax.set_xticks([0, .01, 1, 1000], ['0', r'$10^{-2}$', '1', r'$10^3$'])
            ax.xaxis.set_minor_locator(SymmetricalLogLocator(base=10, linthresh=.001, subs=range(2, 10)))
            for j, equation in enumerate(HAMILTONIANS[i-1]):
                ax.text(.06, .91-.09*j, equation, transform=ax.transAxes, va='top', fontsize=11.5,
                        bbox=dict(facecolor='white', edgecolor='none', alpha=.9, pad=.8))
        else:
            ax.set_xscale('log')
            ax.set_xticks([.001, .1, 10, 1000])
            ax.xaxis.set_minor_locator(LogLocator(subs=range(2, 10), numticks=100))
            ax.text(.95, .07, '1D' if i < 4 else '2D', transform=ax.transAxes,
                    ha='right', va='bottom', fontfamily=sans)
        ax.set_yticks([.001, .01, .1], ['0.001', '0.01', '0.1'])
        ax.yaxis.set_minor_locator(LogLocator(subs=range(2, 10), numticks=100))
        for axis in (ax.xaxis, ax.yaxis):
            axis.set_minor_formatter(NullFormatter())
        ax.spines[['top', 'right']].set_visible(False)
        ax.tick_params(which='minor', length=2, width=.5)
        ax.grid(which='major', color='#E6E8EC', linewidth=.65)
        ax.grid(which='minor', color='#F1F2F4', linewidth=.45)
        if worked or i >= 4:
            ax.set_xlabel(r'$T/J_\star$')
        if worked or i % 4 == 0:
            ax.set_ylabel('Relative coupling error')
    handles = [Patch(facecolor=color, alpha=.8, label=rf'$\sigma={sigma:g}$')
               for sigma, color in zip(sigmas, COLORS)]
    if worked:
        handles = [Line2D([], [], color=INK, ls=ls, label=label)
                   for ls, label in [((0, (5, 3)), 'ED'), ('-', 'MPS')]] + handles
        fig.legend(handles=handles, ncol=5, frameon=False, loc='center', bbox_to_anchor=(.628, .035))
    else:
        axes[0].legend(handles=handles, frameon=False, loc='upper left', fontsize=12)
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    for i, ax in enumerate(axes):
        box = (axes[1].title if worked and i == 0 else ax.title).get_window_extent(renderer)
        y = fig.transFigure.inverted().transform((0, (box.y0+box.y1)/2))[1]
        fig.text(max(.008, ax.get_position().x0-.034), y, f'({chr(97+i)})',
                 va='center', fontfamily=sans, fontsize=15)
    for ext in ('.pdf', '.png'):
        fig.savefig(output.with_suffix(ext), dpi=220, bbox_inches='tight')
    plt.close(fig)
    with output.with_suffix('.csv').open('w', newline='') as handle:
        writer = csv.writer(handle)
        writer.writerow(('panel', 'curve', 'sigma', 'temperature', 'low', 'median', 'high'))
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('demo', 'plot', 'check'), default='plot', nargs='?')
    parser.add_argument('--output', type=Path, default=HERE.parent/'runs/fd/figures')
    args = parser.parse_args()
    if args.command == 'demo':
        demo()
        return
    with np.load(DATA/'moments.npz') as saved, np.load(DATA/'ensemble.npz') as ensemble:
        data, members = dict(saved), ensemble['member_medians']
    if args.command == 'check':
        check(data, members)
    else:
        args.output.mkdir(parents=True, exist_ok=True)
        render(list(worked_curves(data)), args.output/'fig1_matrix_fdt', worked=True)
        render(list(ensemble_curves(data, members)), args.output/'fig2_symmetry_ensembles', worked=False)


if __name__ == '__main__':
    main()
