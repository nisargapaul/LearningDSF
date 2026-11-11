"""Independent numerical checks: python inr/test.py."""

import csv
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

if not __package__:
    sys.path[0] = str(Path(__file__).resolve().parent.parent)
    __package__ = Path(__file__).resolve().parent.name
from .run import DATA, HERE, digest, read_json, seed_for, summaries
import numpy as np


def check(physics=False):  # Replay saved fits and checksums.
    manifest = read_json(DATA/'provenance.json')['files_sha256']
    for name, expected in manifest.items():
        if digest(DATA/name) != expected:
            raise ValueError(f'Data checksum mismatch: {name}')
    rows = summaries()
    with (DATA/'plotted.csv').open() as handle:
        expected = list(csv.DictReader(handle))
    assert len(rows) == len(expected) == 39
    for actual, saved in zip(rows, expected):
        assert all(str(actual[k]) == saved[k] for k in ('panel', 'method', 'input', 'x'))
        np.testing.assert_allclose([actual[k] for k in ('low', 'median', 'high')],
                                  [float(saved[k]) for k in ('low', 'median', 'high')], atol=1e-14, rtol=0.)
    with np.load(DATA/'fits.npz') as data:
        assert data['estimates'].shape == (9, 2, 16, 3)
        assert np.isfinite(data['estimates']).all() and (np.abs(data['estimates']) <= 1.).all()
        with np.load(DATA/'populations.npz') as populations:
            np.testing.assert_array_equal(data['truth'], populations['test'])
    with np.load(DATA/'protocols.npz') as data:
        for method, moments, factor in [('sf', 'sf_moments', 1.), ('ht', 'ht_correlations', -.05)]:
            estimate = data[moments]@np.linalg.pinv(data[method+'_design']).T/factor
            np.testing.assert_allclose(estimate, data[method+'_estimate'], atol=1e-12, rtol=0.)
        mu, nu = data['fd_row_labels'].T
        first = data['fd_first_moments']
        sym = first[:,mu,nu]+first[:,nu,mu]
        np.testing.assert_array_equal(data['fd_rhs'], np.concatenate([sym.real, sym.imag], axis=1))
        for matrix, rhs, truth, estimate in zip(data['fd_designs'], data['fd_rhs'], data['theta'], data['fd_estimates']):
            assert np.linalg.matrix_rank(matrix) == 3
            assert np.linalg.norm(matrix@truth-rhs)/np.linalg.norm(rhs) < 1e-9
            np.testing.assert_allclose(np.linalg.lstsq(matrix,rhs,rcond=1e-12)[0], estimate, atol=1e-13)
    if physics:
        from .physics import layouts, one_target
        with np.load(DATA/'protocols.npz') as data:
            layout = layouts()
            for key in ('sf_design', 'sf_coefficients', 'sf_settings', 'ht_design', 'ht_rows'):
                np.testing.assert_allclose(layout[key], data[key], atol=1e-10, rtol=0.)
            result = one_target(data['theta'][0])
            for key in result:
                expected = data[key] if key == 'fd_row_labels' else data[key][0]
                np.testing.assert_allclose(result[key], expected, atol=1e-9, rtol=1e-9)
    print('PASS: 288 saved fits, 39 plotted records, HT/SF/FD inverses and data checksums.')
    if physics:
        print('PASS: regenerated all measurement maps and one complete N=12 reference.')


def smoke():  # Check sampling, training, and inversion.
    """Synthetic sampling/training/inversion plumbing, not a benchmark result."""
    import torch
    from .inr import Coordinates, train_one, load_model, Inverter
    from .physics import channels
    torch.set_num_threads(1)
    config = dict(read_json(DATA/'settings.json'), profile='smoke', steps=4, batch_size=128,
                  screening=8, restarts=2, fit_steps=2, polish_steps=0, n_sites=8)
    omega = np.arange(-20, 41)*.05
    mapping = np.arange(len(channels(8))) % 2
    with tempfile.TemporaryDirectory(prefix='inr-smoke-') as temporary:
        root = Path(temporary)
        for split, count in [('train', 8), ('validation', 4)]:
            directory = root/'data'/split
            (directory/'shards').mkdir(parents=True)
            np.save(directory/'theta.npy', np.random.default_rng(count).uniform(-1,1,(count,3)))
            np.save(directory/'omega.npy', omega)
            for i in range(count):
                spectra = np.stack([np.exp(-((omega-.3-.03*i)/.15)**2),
                                    .7*np.exp(-((omega-1.2+.02*i)/.2)**2)]).astype(np.float32)
                np.savez(directory/f'shards/{i:05d}.npz', spectra=spectra, mapping=mapping, n_sites=8)
        data = Coordinates(root/'data/train', 8)
        _, values, weights = data.sample(np.random.default_rng(7), 200000)
        samples = values*weights
        exact = data.spectra[:,mapping].mean(dtype=float)
        z = abs(samples.mean()-exact)/(samples.std()/np.sqrt(len(samples)))
        assert z < 6
        train_one(root, config, 8, 5, 0, 'cpu')
        model, _ = load_model(root/'checkpoints/b8_d5_w128_s0.pt')
        clean = data.spectra[0,mapping].astype(float); gain = 100000/clean.sum()
        estimate, diagnostic = Inverter(model, omega, 0., 'cpu', n_sites=8).fit(gain*clean, gain, config, 11)
        assert np.isfinite(estimate).all() and (np.abs(estimate) <= 1).all()
        assert np.isfinite(diagnostic['objective'])
    print(f'PASS: CPU sampling/train/fit smoke test; sampler deviation {z:.2f} standard errors.')


class FrozenDataTests(unittest.TestCase):
    def test_plot_values(self):  # Replay all plotted values.
        check()

    def test_populations(self):  # Verify independent Sobol populations.
        from scipy.stats import qmc
        with np.load(DATA/'populations.npz') as data:
            for split, key in [('train', 11), ('validation', 12), ('test', 13)]:
                n = len(data[split])
                expected = 2*qmc.Sobol(3, scramble=True, seed=seed_for(key)).random_base2(
                    int(np.ceil(np.log2(n))))-1
                np.testing.assert_array_equal(data[split], expected)
            for left, right in [('train', 'validation'), ('train', 'test'), ('validation', 'test')]:
                self.assertFalse(set(map(tuple, data[left])) & set(map(tuple, data[right])))

    def test_curve_density(self):  # Require nine computed training budgets.
        rows = summaries()
        for method in ('total', 'J', 'K', 'Gamma'):
            self.assertEqual(len({row['x'] for row in rows if row['method'] == method}), 9)

    def test_reference_maps(self):  # Rebuild the protocol measurement maps.
        from .physics import layouts
        with np.load(DATA/'protocols.npz') as data:
            for key, value in layouts().items():
                np.testing.assert_allclose(value, data[key], atol=1e-10, rtol=0.)

    def test_cli_init_does_not_touch_frozen_inputs(self):  # Protect the saved scientific inputs.
        from .run import initialize
        with tempfile.TemporaryDirectory() as directory:
            initialize(directory)
            initialize(directory)
            config = read_json(Path(directory)/'config.json')
            self.assertEqual(config['n_sites'], 12)
        with self.assertRaises(ValueError):
            initialize(DATA)

    def test_detached_folder(self):  # Check standalone package use.
        with tempfile.TemporaryDirectory() as directory:
            detached = Path(directory)/'inr'
            shutil.copytree(HERE, detached, ignore=shutil.ignore_patterns(
                '__pycache__', '.venv'))
            env = dict(os.environ, PYTHONPATH='')
            result = subprocess.run([sys.executable, '-B', str(detached/'run.py'), 'check'],
                                    cwd=directory, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('PASS:', result.stdout)

    def test_interrupted_spectrum_write(self):  # Resume a shard missing its report.
        from .run import calculate, initialize
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); initialize(root)
            task = (root, 'train', 0)
            with patch('inr.physics.spectrum', return_value=(np.ones((1,3)), np.array([0]), {})) as forward:
                calculate(task)
                (root/'data/train/shards/00000.json').unlink()
                calculate(task)
                calculate(task)
                self.assertEqual(forward.call_count, 2)
            self.assertTrue((root/'data/train/shards/00000.json').exists())

    @unittest.skipUnless(shutil.which('git'), 'Git is optional for numerical reproduction.')
    def test_compact_inputs_are_not_gitignored(self):  # Track inputs, exclude generated files.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(['git','init','-q',directory],check=True)
            (root/'.gitignore').write_text('*.npz\n*.pt\n'+(HERE.parent/'.gitignore').read_text())
            study = root/'inr'; (study/'data').mkdir(parents=True)
            (study/'data/fits.npz').touch()
            work = root/'runs/inr/work'; work.mkdir(parents=True)
            (work/'cache.npz').touch()
            allowed = subprocess.run(['git','check-ignore','-q','inr/data/fits.npz'],cwd=root)
            ignored = subprocess.run(['git','check-ignore','-q','runs/inr/work/cache.npz'],cwd=root)
            self.assertEqual(allowed.returncode,1)
            self.assertEqual(ignored.returncode,0)


class PhysicsTests(unittest.TestCase):
    def test_lanczos_against_dense_ed(self):  # Compare spectra with exact diagonalization.
        from .physics import hamiltonian, operators, spectrum, unique_probes, broaden_poles, difference
        theta, n = [.4, -.7, .2], 8
        omega = np.arange(-20, 2001)*.05
        h = hamiltonian(theta, n)
        energy, states = np.linalg.eigh(h.toarray())
        rank = np.count_nonzero(energy-energy[0] <= 1e-10)
        ground = states[:,:rank]
        local, _, _ = operators(n)
        coefficients, mapping = unique_probes(n)
        exact = np.zeros((len(coefficients),len(omega)))
        for state in ground.T:
            acted = np.array([[op@state for op in site] for site in local])
            vectors = np.einsum('lia,iad->ld', coefficients, acted, optimize=True).T
            vectors -= ground@(ground.conj().T@vectors)
            weights = abs(states[:,rank:].conj().T@vectors)**2
            for line in range(len(coefficients)):
                exact[line] += broaden_poles(energy[rank:]-energy[0], weights[:,line], omega)/rank
        computed, actual_mapping, _ = spectrum(theta,n,omega)
        np.testing.assert_array_equal(actual_mapping,mapping)
        l1, gkl = difference(computed[mapping],exact[mapping])
        self.assertLess(l1,1e-3); self.assertLess(gkl,1.)

    def test_pauli_commutator(self):  # Check Pauli algebra conventions.
        from .physics import multiply, commutator
        self.assertEqual(multiply((1,0),(2,0)),(1j,(3,0)))
        self.assertEqual(commutator({(1,0):1.},(2,0)),{(3,0):2j})


class NetworkTests(unittest.TestCase):
    def test_train_and_inverse_smoke(self):  # Exercise training and coupling fitting.
        smoke()

    def test_dimensions_and_positive_output(self):  # Check architecture and positive spectra.
        import torch
        from .inr import FieldINR
        model = FieldINR()
        self.assertEqual([(layer.linear.in_features,layer.linear.out_features) for layer in model.body],
                         [(12,128)]+[(128,128)]*4)
        values = model(torch.zeros((4,12)))
        self.assertTrue(torch.isfinite(values).all() and (values >= 0).all())

    def test_generalized_kl(self):  # Check GKL values and scaling.
        import torch
        from .inr import generalized_kl
        truth = torch.tensor([0.,.2,1.],dtype=torch.float64)
        np.testing.assert_allclose(generalized_kl(truth,truth).numpy(),0.,atol=1e-12)
        prediction = torch.tensor([.1,.4,2.],dtype=torch.float64)
        self.assertTrue((generalized_kl(prediction,truth) >= 0).all())
        np.testing.assert_allclose(generalized_kl(7*prediction,7*truth).numpy(),
                                   7*generalized_kl(prediction,truth).numpy(),atol=1e-12)


if __name__ == '__main__':
    unittest.main()
