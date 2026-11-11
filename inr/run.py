"""INR benchmark: saved results, plotting, and resumable calculations."""

import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import hashlib
import json
import os
from pathlib import Path
import sys
import time

for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'
os.environ.setdefault('MPLBACKEND','Agg')
if not __package__:  # Support both python run.py and package imports.
    sys.path[0] = str(Path(__file__).resolve().parent.parent)
    __package__ = Path(__file__).resolve().parent.name
import numpy as np

HERE = Path(__file__).resolve().parent
DATA = HERE/'data'
RUNS = HERE.parent/'runs'/'inr'
QUANTILES = [.375, .5, .625]


def seed_for(*keys):  # Stable seeds for each stage.
    return int(np.random.SeedSequence([20260909, *map(int, keys)]).generate_state(1)[0])


def digest(path):  # SHA256 of saved bytes.
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):  # Read settings or results.
    return json.loads(Path(path).read_text())


def write_json(path, value):  # Save without partial writes.
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    temporary.replace(path)


def initialize(root):  # Copy frozen settings and populations.
    root = Path(root).resolve()
    if root == HERE or root == DATA or DATA in root.parents:
        raise ValueError('Choose a separate work directory, not the frozen source/data directory.')
    config = read_json(DATA/'settings.json')
    if (root/'config.json').exists() and read_json(root/'config.json') != config:
        raise ValueError('Existing run has a different configuration.')
    write_json(root/'config.json',config)
    with np.load(DATA/'populations.npz') as data:
        for split in ('train','validation','test'):
            directory = root/'data'/split
            directory.mkdir(parents=True,exist_ok=True)
            for name, value in [('theta',data[split]),('omega',data['omega'])]:
                path = directory/(name+'.npy')
                if path.exists():
                    np.testing.assert_array_equal(np.load(path),value)
                else:
                    np.save(path,value)


def calculate(task):  # Save one spectrum or reference.
    from .physics import spectrum, one_target
    root, split, index = task
    root = Path(root)
    reference = split == 'reference'
    directory = root/'data'/('test' if reference else split)
    theta, omega = np.load(directory/'theta.npy')[index], np.load(directory/'omega.npy')
    path = root/f'reference_shards/{index:03d}.npz' if reference else directory/f'shards/{index:05d}.npz'
    if path.exists():
        with np.load(path) as saved:
            np.testing.assert_array_equal(saved['theta'],theta)
        report_path = path.with_suffix('.json')
        if reference:
            return
        if report_path.exists():
            if read_json(report_path)['sha256'] != digest(path):
                raise ValueError(f'Spectrum checksum mismatch: {path}')
            return
        # A stopped write can leave the spectrum without its report; regenerate it.
    started = time.perf_counter()
    if reference:
        values, report = dict(theta=theta,**one_target(theta)), None
    else:
        n = read_json(root/'config.json')['n_sites']
        spectra, mapping, report = spectrum(theta,n,omega)
        values = dict(spectra=spectra.astype(np.float32),mapping=mapping,theta=theta,omega=omega,n_sites=n)
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary = path.with_suffix('.tmp.npz')
    np.savez_compressed(temporary,**values)
    temporary.replace(path)
    if report is not None:
        write_json(path.with_suffix('.json'),dict(report,sha256=digest(path)))
    print(f'{split}/{index}: {time.perf_counter()-started:.1f}s',flush=True)


def compute(args):  # Distribute independent forward calculations.
    config = read_json(args.work_dir/'config.json')
    splits = ['reference'] if args.command == 'references' else [args.split] if args.split else ['validation','test','train']
    tasks = [(str(args.work_dir),split,i) for split in splits
             for i in range(config['n_test' if split == 'reference' else 'n_'+split])]
    if args.command == 'generate':
        tasks = tasks[args.shard::args.shards][:args.limit]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(calculate,tasks))


def learn(args):  # Train networks or fit couplings.
    import torch
    from .inr import Inverter, checkpoint_path, load_model, train_one
    torch.set_num_threads(1)
    root = args.work_dir
    config = read_json(root/'config.json')
    budgets = config['budgets'] if args.budget is None else [args.budget]
    seeds = config['seeds'] if args.seed is None else [args.seed]
    targets = range(config['n_test']) if args.target is None else [args.target]
    if not set(budgets) <= set(config['budgets']) or not set(seeds) <= set(config['seeds']):
        raise ValueError('Unknown training budget or seed.')
    if not all(0 <= target < config['n_test'] for target in targets):
        raise ValueError('Unknown test target.')
    for budget in budgets:
        for seed in seeds:
            if args.command == 'train':
                train_one(root,config,budget,5,seed,args.device)
                continue
            checkpoint = checkpoint_path(root,budget,5,seed)
            model, _ = load_model(checkpoint,args.device)
            inverter = Inverter(model,np.load(root/'data/test/omega.npy'),0.,args.device,config['n_sites'])
            for target in targets:
                path = root/f'results/b{budget}_s{seed}_h{target:03d}.json'
                source = root/f'data/test/shards/{target:05d}.npz'
                hashes = dict(checkpoint_sha256=digest(checkpoint),spectrum_sha256=digest(source))
                if path.exists():
                    saved = read_json(path)
                    assert all(saved[key] == value for key,value in hashes.items())
                    continue
                with np.load(source) as shard:
                    clean, theta = shard['spectra'].astype(np.float64)[shard['mapping']], shard['theta']
                gain, inverse_seed = config['count_inr']/clean.sum(), seed_for(941,budget,seed,target)  # Intensity scale; no noise draw.
                estimate, info = inverter.fit(gain*clean,gain,config,inverse_seed)
                write_json(path,dict(budget=budget,seed=seed,target=target,theta=theta.tolist(),
                    estimate=estimate.tolist(),input_kind='noiseless',gain=gain,inversion_seed=inverse_seed,**hashes,**info))
                print(f'fit b={budget} seed={seed} target={target}: {info["seconds"]:.1f}s',flush=True)


def collect(root):  # Combine all fits and references.
    from .physics import layouts
    config, truth = read_json(root/'config.json'), np.load(root/'data/test/theta.npy')
    estimates = [[[read_json(root/f'results/b{b}_s{s}_h{h:03d}.json')['estimate']
                   for h in range(config['n_test'])] for s in config['seeds']] for b in config['budgets']]
    records = []
    for target, theta in enumerate(truth):
        with np.load(root/f'reference_shards/{target:03d}.npz') as data:
            np.testing.assert_array_equal(data['theta'],theta)
            records.append(dict(data))
    output = root/'summary'
    output.mkdir(exist_ok=True)
    np.savez_compressed(output/'fits.npz',budgets=config['budgets'],seeds=config['seeds'],truth=truth,estimates=estimates)
    protocol = dict(layouts(),theta=truth)
    protocol.update({key: records[0][key] if key == 'fd_row_labels' else np.array([r[key] for r in records])
                     for key in records[0] if key != 'theta'})
    np.savez_compressed(output/'protocols.npz',**protocol)
    write_json(output/'settings.json',config)
    rows = summaries(output)
    with (output/'plotted.csv').open('w',newline='') as handle:
        writer = csv.DictWriter(handle,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def summaries(data=DATA):  # Medians and central 25% ranges.
    """Return the exact 39 plotted records from individual estimates and moments."""
    with np.load(Path(data)/'fits.npz') as fits:
        budgets, truth = fits['budgets'], fits['truth']
        estimates = fits['estimates'].reshape(len(budgets), -1, 3)
        repeated_truth = np.tile(truth, (len(fits['seeds']), 1))
    components = np.abs(estimates-repeated_truth)/np.linalg.norm(repeated_truth, axis=1)[None, :, None]
    rows = []
    values = [('a', 'total', np.linalg.norm(components, axis=2))]+[
        ('b', name, components[:, :, j]) for j, name in enumerate(('J', 'K', 'Gamma'))]
    for panel, method, errors in values:
        low, median, high = np.quantile(errors, QUANTILES, axis=1)  # Variation across targets and seeds.
        rows += [dict(panel=panel, method=method, input='noiseless', x=int(x),
                      median=m, low=l, high=h) for x, l, m, h in zip(budgets, low, median, high)]
    with np.load(Path(data)/'protocols.npz') as reference:
        for method, key in [('sf', 'sf_estimate'), ('ht', 'ht_estimate'), ('fd', 'fd_estimates')]:
            errors = np.linalg.norm(reference[key]-truth, axis=1)/np.linalg.norm(truth, axis=1)
            low, median, high = np.quantile(errors, QUANTILES)
            rows.append(dict(panel='a', method=method+'_reference', input='noiseless',
                             x='', median=median, low=low, high=high))
    return rows


def style():  # Set the paper fonts.
    import matplotlib.pyplot as plt
    from matplotlib.font_manager import FontProperties, fontManager
    available = {font.name for font in fontManager.ttflist}
    title_font = 'Avenir' if 'Avenir' in available else 'DejaVu Sans'
    axis_font = 'Times New Roman' if 'Times New Roman' in available else 'STIXGeneral'
    plt.rcParams.update({'font.family': 'serif', 'font.serif': [axis_font],
        'mathtext.fontset': 'stix', 'font.size': 14, 'axes.labelsize': 15,
        'xtick.labelsize': 14, 'ytick.labelsize': 14, 'axes.linewidth': .8,
        'text.color': '#23252F', 'axes.labelcolor': '#23252F', 'axes.edgecolor': '#23252F',
        'xtick.color': '#23252F', 'ytick.color': '#23252F', 'pdf.fonttype': 42,
        'figure.facecolor': 'white', 'savefig.facecolor': 'white'})
    return FontProperties(family=title_font), dict(titles=title_font, axes=axis_font)


def network_diagram(ax):  # Draw the sine-network schematic.
    from matplotlib.colors import to_rgb
    from matplotlib.offsetbox import AnnotationBbox, OffsetImage
    ax.set(xlim=(0, 1), ylim=(-.10, 1.15)); ax.axis('off')
    layers = [(np.linspace(.20, .80, 12), .96)]+[
        (np.array([.27, .40, .60, .73]), y) for y in (.80, .66, .52, .38, .24)]+[(np.array([.5]), .075)]
    for (xs, y), (next_xs, next_y) in zip(layers[:-1], layers[1:]):
        for x in xs:
            for nx in next_xs:
                ax.plot([x, nx], [y, next_y], color='#98ACBC', lw=.45, alpha=.28, zorder=1)
    u, v = np.meshgrid(np.linspace(-1, 1, 96), np.linspace(1, -1, 96))
    for index, (xs, y) in enumerate(layers):
        base = np.array(to_rgb('#78B4DE' if index == 0 else '#D3AD46' if index == 6 else '#398BCC'))
        rgb = base+.12*((v+1)/2)[..., None]*(1-base)
        node = np.dstack((rgb, np.clip((1-np.sqrt(u*u+v*v))*48, 0, 1)))
        diameter = 6.5 if index == 0 else 12 if index == 6 else 10.5
        for x in xs:
            ax.add_artist(AnnotationBbox(OffsetImage(node, zoom=diameter/96, interpolation='hanning'),
                                        (x, y), frameon=False, pad=0, zorder=3))
        if 0 < index < 6:
            ax.text(.5, y, r'$\cdots$', fontsize=12, ha='center', va='center', color='#667785')
    ax.text(.777, .24, r'$\times128$', fontsize=10, ha='left', va='center', color='black')
    ax.text(.5, 1.095, r'$(\mathbf{q},\omega,\hat{\mathbf{p}},\boldsymbol{\lambda})$', ha='center', va='center', fontsize=11)
    ax.text(.5, -.075, 'spectral-bin weight',
            ha='center', va='center', fontsize=11)


def build(data=DATA):  # Assemble the two-panel figure.
    import matplotlib.pyplot as plt
    from matplotlib.ticker import NullLocator
    rows = summaries(data)
    settings = read_json(Path(data)/'settings.json')
    sans, fonts = style()
    fig = plt.figure(figsize=(12.3, 3.9))
    positions = [[.31, .20, .265, .61], [.715, .20, .265, .61]]
    axes = [fig.add_axes(position) for position in positions]
    for i, (ax, title) in enumerate(zip(axes, ['Implicit neural representations', 'individual couplings'])):
        ax.set_title(title, fontproperties=sans, fontsize=15, pad=14)
        fig.text(positions[i][0]-.058, .965, f"({'ab'[i]})", fontproperties=sans, fontsize=15,
                 ha='left', va='center')
        ax.set(xscale='log', yscale='log', xlim=(8, 2048), ylim=settings['display_ylim'])
        ax.set_xticks([8, 32, 128, 512, 2048], ['8', '32', '128', '512', '2048'])
        ax.xaxis.set_minor_locator(NullLocator())
        ax.set_axisbelow(True)
        ax.grid(which='major', color='#E6E8EC', linewidth=.6)
        ax.grid(which='minor', axis='y', color='#F1F2F4', linewidth=.4)
        ax.tick_params(direction='out', length=3, pad=3)
        ax.tick_params(axis='x', labelsize=12)
        ax.spines[['top', 'right']].set_visible(False)
        ax.set_xlabel(r'$N_{\rm train}$'); ax.yaxis.labelpad = 4
    for ax, method, color, label in [(axes[0], 'total', '#3279B5', None),
            (axes[1], 'J', '#3279B5', '$J$'), (axes[1], 'K', '#2E7D4F', '$K$'),
            (axes[1], 'Gamma', '#B98200', r'$\Gamma$')]:
        selected = [r for r in rows if r['method'] == method]
        x, low, med, high = [np.array([r[k] for r in selected]) for k in ('x', 'low', 'median', 'high')]
        if len(np.unique(x)) < 6:
            raise ValueError('A publication curve needs at least six computed budgets.')
        ax.fill_between(x, low, high, color=color, alpha=.12, linewidth=0)
        ax.plot(x, med, color=color, lw=1.6, marker='o', mfc=color, ms=3.5, alpha=.8, label=label, zorder=3)
    for method, label, below in [('sf_reference', r'SF tomography, $B=32$', True),
                                 ('ht_reference', r'HT tomography, $\beta=0.05$', False)]:
        value = next(r['median'] for r in rows if r['method'] == method)
        axes[0].axhline(value, color='black', ls='--', lw=1.7)
        axes[0].text(10., value*(1/1.2 if below else 1.14), label, color='black', fontsize=11,
                     ha='left', va='top' if below else 'bottom')
    axes[0].annotate('FD tomography', xy=(.42, .015), xycoords='axes fraction',
                     xytext=(.42, .11), textcoords='axes fraction', ha='center', va='bottom',
                     fontsize=11, color='black', annotation_clip=False,
                     arrowprops=dict(arrowstyle='-|>', color='black', lw=1.2, shrinkA=1, shrinkB=0))
    axes[0].set_ylabel(r'$|\boldsymbol{\lambda}_{\mathrm{pred.}}-\boldsymbol{\lambda}_{\mathrm{true}}|'
                       r'/|\boldsymbol{\lambda}_{\mathrm{true}}|$', fontsize=14)
    axes[0].text(.97, .86, r'$J$-$K$-$\Gamma$ model', transform=axes[0].transAxes,
                 fontsize=13, ha='right', va='bottom')
    network_diagram(fig.add_axes([.015, .20, .205, .61]))
    axes[1].set_ylabel(r'$|\Delta\lambda_j|/|\boldsymbol{\lambda}_{\rm true}|$', fontsize=14)
    axes[1].legend(frameon=False, loc='upper right', fontsize=12)
    return fig, rows, fonts


def render(output, data=DATA):  # Export PDF, PNG, and values.
    import matplotlib.pyplot as plt
    output = Path(output); output.mkdir(parents=True, exist_ok=True)
    fig, rows, fonts = build(data)
    stem = output/'inr_benchmark_N12'
    for suffix in ('pdf', 'png'):
        fig.savefig(stem.with_suffix('.'+suffix), dpi=220, bbox_inches='tight', facecolor='white')
    plt.close(fig)
    with stem.with_suffix('.csv').open('w', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
    stem.with_suffix('.json').write_text(json.dumps(dict(fonts=fonts, data_directory=str(Path(data).name),
        noise='none added', ribbon_quantiles=[.375, .625], computed_budgets=9), indent=2)+'\n')
    print(stem.with_suffix('.pdf'))


def main():  # Select a benchmark stage.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['check','plot','smoke','init','generate','train','fit','references','collect'])
    for name, default in [('work-dir',RUNS/'work'),('data',DATA),('output',RUNS/'figures')]:
        parser.add_argument('--'+name,type=Path,default=default)
    parser.add_argument('--workers',type=int,choices=range(1,5),default=4)
    parser.add_argument('--device',choices=['cpu','cuda','mps','auto'],default='auto')
    for name in ('budget','seed','target','limit'):
        parser.add_argument('--'+name,type=int)
    parser.add_argument('--split',choices=['train','validation','test'])
    parser.add_argument('--shards',type=int,default=1)
    parser.add_argument('--shard',type=int,default=0)
    parser.add_argument('--physics',action='store_true')
    args = parser.parse_args()
    if not 0 <= args.shard < args.shards or (args.limit is not None and args.limit < 1):
        parser.error('Invalid shard or limit.')
    if args.command in ('check','smoke'):
        from .test import check, smoke
        check(args.physics) if args.command == 'check' else smoke()
    elif args.command == 'plot':
        render(args.output,args.data)
    elif args.command == 'init':
        initialize(args.work_dir)
    elif args.command in ('generate','references'):
        compute(args)
    elif args.command in ('train','fit'):
        learn(args)
    else:
        collect(args.work_dir)


if __name__ == '__main__':
    main()
