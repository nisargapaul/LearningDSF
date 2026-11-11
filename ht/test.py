"""Portable checks of the compact implementation and its frozen results."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import numpy as np
from scipy.linalg import eigh
from scipy.optimize import least_squares

from itertools import product
from scipy import sparse
from ht.run import (load, spins, geometry, honeycomb_basis, jkg_design, bond_layout,
    thermal_pairs, dsf_layout, chain_map, chain_trial, chain_summary, moment_sweep,
    feature_comparison, parameter_summary, calculate_cell, digest, DATA, SEED)


def chain_coefficients(theta, n=12):
    """Independent matrix traces: twelve full and twelve diagonal coefficients.

    Parameter order: b_x,b_y,b_z, then row-major Lambda. If C_j=[sigma_j,H],
    the second-moment intercept is -Tr(C_0 C_d)/D and its slope is Tr(C_0 C_d H)/D.
    """
    local, dimension = spins(n), 2**n
    h = sparse.csr_matrix((dimension, dimension), dtype=complex)
    for i in range(n):
        for a in range(3):
            h += theta[a]*local[i][a]
            for b in range(3):
                h += theta[3+3*a+b]*(local[i][a] @ local[(i+1) % n][b])
    def trace(a, b):
        return a.T.multiply(b).sum()/dimension
    static = np.array([-trace(local[0][a] @ local[1][b], h)
                       for a, b in product(range(3), repeat=2)])
    onsite = np.array([-trace(local[0][a] @ local[0][b], h)
                       for a, b in ((1, 2), (2, 0), (0, 1))])
    comm = [[op @ h-h @ op for op in local[i]] for i in (0, 1)]
    second = [-trace(comm[0][a], comm[1][a]) for a in range(3)]
    slope = [trace(comm[0][a] @ comm[1][a], h) for a in range(3)]
    self_second = [-trace(c, c) for c in comm[0]]
    return np.r_[onsite.imag, static.real], np.r_[static[[0, 4, 8]], second, slope, self_second].real

def population(count=64, seed=SEED):
    """Nested random supports, other couplings zero, norm one, support known."""
    rng = np.random.default_rng(seed)
    raw = rng.normal(size=(count, 27))
    order = np.array([rng.permutation(27) for _ in range(count)])
    counts = np.r_[1, np.arange(3, 28, 3)]
    theta = np.zeros((len(counts), count, 27))
    for ip, p in enumerate(counts):
        for member in range(count):
            ids = order[member, :p]
            theta[ip, member, ids] = raw[member, ids]
            theta[ip, member] /= np.linalg.norm(theta[ip, member])
    return counts, theta, order



class HTTests(unittest.TestCase):
    def test_data_checksums(self):
        import json
        manifest = json.loads((DATA/'provenance.json').read_text())
        for name, expected in manifest['files_sha256'].items():
            self.assertEqual(digest(DATA/name), expected, name)

    def test_checkpoint_resume(self):
        with TemporaryDirectory() as folder:
            task = ('coefficients', 0, Path(folder))
            actual = calculate_cell(task)
            np.testing.assert_allclose(actual, load('chain')['errors'][0], rtol=1e-6, atol=1e-7)
            with patch('ht.run.chain_trial', side_effect=AssertionError('Checkpoint was not reused')):
                np.testing.assert_array_equal(actual, calculate_cell(task))
            path = Path(folder)/'coefficients_0000.npz'
            with np.load(path) as saved:
                records = dict(saved)
            self.assertEqual(records['estimates'].shape, (95, 12))
            self.assertEqual(records['statuses'].shape, (95,))
            records['signature'] = 'different source'
            np.savez_compressed(path, **records)
            with self.assertRaisesRegex(ValueError, 'Stale checkpoint'):
                calculate_cell(task)

    def test_pauli_conventions(self):
        x, y, z = [op.toarray() for op in spins(1)[0]]
        np.testing.assert_array_equal(x @ y, 1j*z)
        for op in (x, y, z):
            np.testing.assert_array_equal(op @ op, np.eye(2))

    def test_chain_data_against_independent_traces(self):
        data = load('chain')
        f, _ = chain_map()
        for index in (0, 7, 999):
            theta = data['theta'][index]
            full, diagonal = chain_coefficients(theta, 6)
            np.testing.assert_allclose(full, -theta, atol=1e-12)
            np.testing.assert_allclose(diagonal, f(theta), atol=1e-11)
            np.testing.assert_allclose(diagonal, data['diagonal_coefficients'][index], atol=1e-11)

    def test_analytic_jacobian_and_clean_inverse(self):
        theta = load('chain')['theta'][0]
        f, jac = chain_map()
        step = 1e-6
        finite = np.column_stack([(f(theta+step*e)-f(theta-step*e))/(2*step) for e in np.eye(12)])
        np.testing.assert_allclose(jac(theta), finite, rtol=1e-7, atol=1e-8)
        fit = least_squares(lambda x: f(x)-f(theta), theta+.0001, jac=jac,
                            ftol=1e-12, xtol=1e-12, gtol=1e-12)
        np.testing.assert_allclose(fit.x, theta, atol=1e-9)

    def test_original_local_fits_and_shared_noise(self):
        data = load('chain')
        for index in (0, 7):
            with self.subTest(hamiltonian=index):
                result = chain_trial(index, data['theta'][index], data['sigmas'])
                # Linear inversion is reproducible to roundoff. Iterative LM
                # stopping points vary slightly between BLAS implementations.
                np.testing.assert_allclose(result['errors'][:, 0], data['errors'][index, :, 0],
                                           rtol=1e-11, atol=1e-12)
                np.testing.assert_allclose(result['errors'][:, 1], data['errors'][index, :, 1],
                                           rtol=1e-6, atol=1e-7)

    def test_original_bootstrap_summary(self):
        data = load('chain')
        for key, values in chain_summary(data['errors']).items():
            np.testing.assert_allclose(values, data[key], rtol=1e-13, atol=1e-14)

    def test_supplement_matrices_and_statistics(self):
        data = load('supplement')
        rows, design, sets = bond_layout()
        for size, ids in sets.items():
            np.testing.assert_array_equal(rows[ids], data[f'rows_{size}'])
            np.testing.assert_array_equal(design[ids], data[f'design_{size}'])
            inverse = np.linalg.pinv(design[ids])
            np.testing.assert_allclose(inverse @ design[ids], np.eye(3), atol=1e-14)
        for key, values in feature_comparison(data).items():
            np.testing.assert_allclose(values, data[key], rtol=1e-13, atol=1e-14)

    def test_full_DSF_design(self):
        _, weights, design = dsf_layout()
        self.assertEqual(design.shape, (270, 3))
        self.assertEqual(weights.shape[0], 270)
        np.testing.assert_allclose(design, load('temperature')['design'], rtol=1e-13, atol=1e-14)
        np.testing.assert_allclose(np.linalg.pinv(design) @ design, np.eye(3), atol=1e-14)

    def test_complete_thermal_ED_and_slope(self):
        data = load('supplement')
        theta = jkg_design() @ data['theta']
        values, energies = thermal_pairs(theta, [1e-6, .05])
        self.assertEqual(len(energies), 4096)
        np.testing.assert_allclose(np.mean(energies**2), 6*np.dot(theta, theta), atol=1e-10)
        np.testing.assert_allclose(-values[0]/1e-6, theta, atol=5e-6)
        np.testing.assert_allclose(values[1, bond_layout()[2][15]],
            data['correlations_15'][np.flatnonzero(data['betas'] == .05)[0]], atol=1e-11)

    def test_thermal_ED_against_full_matrix(self):
        n, betas = 8, np.array([.01, .2])
        theta = np.random.default_rng(53012).uniform(-.2, .2, 27)
        actual, energies = thermal_pairs(theta, betas, n=n)
        h = sum(t*b for t, b in zip(theta, honeycomb_basis(n))).toarray()
        e, v = eigh(h)
        np.testing.assert_allclose(np.sort(energies), e, atol=1e-11)
        w = np.exp(-betas[:, None]*(e-e.min())); w /= w.sum(axis=1, keepdims=True)
        local = spins(n)
        direct = np.array([w @ np.einsum('ij,ij->j', v.conj(), (local[i][a] @ local[j][b]) @ v)
                          for _, i, j, a, b in bond_layout(n)[0]]).T
        np.testing.assert_allclose(actual, direct, atol=1e-11)

    def test_general_exchange_thermal_data(self):
        data = load('parameters')
        for ip in (0, 9):
            values, energies = thermal_pairs(data['theta'][ip, 0], [data['betas'][ip]])
            self.assertEqual(len(energies), 4096)
            np.testing.assert_allclose(values[0], data['moments'][ip, 0], atol=1e-11)

    def test_full_DSF_integral_independently(self):
        n, beta = 8, .3
        theta = jkg_design() @ [.31, -.27, .15]
        pairs, weights, _ = dsf_layout(n)
        values, _ = thermal_pairs(theta, [beta], pairs, n)
        local, g = spins(n), geometry(n)
        h = sum(t*b for t, b in zip(theta, honeycomb_basis(n))).toarray()
        e, v = eigh(h)
        p = np.exp(-beta*(e-e.min())); p /= p.sum()
        for row, axis in enumerate(range(3)):
            op = sum(np.exp(-1j*g['positions'][i] @ g['momenta'][0])*local[i][axis]
                     for i in range(n))/np.sqrt(n)
            spectral = np.sum(abs(v.conj().T @ op @ v)**2, axis=0) @ p
            self.assertAlmostEqual(spectral, 1+values[0] @ weights[row], places=11)

    def test_main_temperature_noise_replay(self):
        data = load('temperature')
        draws = np.random.default_rng(20261056).normal(size=(5000, 270))
        result = moment_sweep(data['moments'], data['design'], data['betas'],
                              data['theta'], data['sigmas'], draws)
        for key in ('estimates', 'clean', 'bands'):
            np.testing.assert_allclose(result[key], data[key], atol=2e-14, rtol=1e-12)

    def test_parameter_population_and_noise_replay(self):
        data = load('parameters')
        _, theta, order = population()
        np.testing.assert_array_equal(theta != 0, data['theta'] != 0)
        np.testing.assert_allclose(theta, data['theta'], rtol=0., atol=1e-15)
        np.testing.assert_array_equal(order, data['order'])
        result = parameter_summary(theta, data['moments'], order, data['betas'], data['sigmas'])
        for key, values in result.items():
            np.testing.assert_allclose(values, data[key], rtol=1e-13, atol=1e-14)


if __name__ == '__main__':
    unittest.main()
