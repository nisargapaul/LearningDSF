import DSFTomography.HighTemperature
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! Construct the Gibbs DSF directly from the physical parameters via the
spectral theorem. The estimator never takes an eigensystem as an input. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
variable (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ)

def qubitH := realH (qubitSpins (1 : (Op (Config S))ˣ)) R h J

omit [AddCommGroup S] in
private theorem inBasis_one (A : Op (Config S)) : inBasis 1 A = A := by simp [inBasis]

theorem qubitH_hermitian : (qubitH R h J).IsHermitian := by
  unfold Matrix.IsHermitian qubitH realH
  rw [H_words (qubitSpins 1) 1 (fun _ _ => rfl)]
  simp [string, inBasis_one, Matrix.conjTranspose_sum, word_hermitian]

theorem rotate_H (U : (Op (Config S))ˣ) :
    realH (qubitSpins U) R h J = inBasis U (qubitH R h J) := by
  unfold qubitH realH
  rw [H_words (qubitSpins U) U (fun _ _ => rfl),
      H_words (qubitSpins 1) 1 (fun _ _ => rfl)]
  simp only [string, inBasis_one]
  simp [inBasis, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul]

def energyBasis : (Op (Config S))ˣ :=
  (unitary.toUnits (qubitH_hermitian R h J).eigenvectorUnitary)⁻¹

def energies : Config S → ℝ := (qubitH_hermitian R h J).eigenvalues

theorem diagonalized :
    realH (qubitSpins (energyBasis R h J)) R h J =
      Matrix.diagonal (fun m => (energies R h J m : ℂ)) := by
  rw [rotate_H]
  simpa only [energyBasis, inBasis, inv_inv, energies] using
    (qubitH_hermitian R h J).star_mul_self_mul_eq_diagonal

/-- The normalized static DSF specified solely by the Hamiltonian. -/
def gibbsStaticDSF : StaticScan S := fun β =>
  (momentumMoments (qubitSpins (energyBasis R h J)) β (energies R h J)).static

/-- Full-access HT recovery for every real one- and two-body Hamiltonian.
There are no hypotheses on its eigenvalues, gaps, couplings or feature ranks. -/
theorem fullAccessHT :
    (∀ d ∈ R.dirs, exchange (gibbsStaticDSF R h J) d = fun a b => (J d a b : ℂ)) ∧
      field (gibbsStaticDSF R h J) = fun a => (h a : ℂ) :=
  htFromDSF (qubitSpins (energyBasis R h J)) (energyBasis R h J) (fun _ _ => rfl)
    R h J (energies R h J) (diagonalized R h J) _ (Filter.Eventually.of_forall (fun _ => rfl))

/-- Equality of the full static scans implies equality of the physical parameters. -/
theorem fullAccessHT_identifiable (h' : Axis → ℝ) (J' : S → Matrix Axis Axis ℝ)
    (same : gibbsStaticDSF R h J = gibbsStaticDSF R h' J') :
    (∀ d ∈ R.dirs, J d = J' d) ∧ h = h' := by
  obtain ⟨bonds, fields⟩ := fullAccessHT R h J
  rw [same] at bonds fields
  obtain ⟨bonds', fields'⟩ := fullAccessHT R h' J'
  constructor
  · intro d hd
    funext a b
    exact Complex.ofReal_injective (congrFun (congrFun ((bonds d hd).symm.trans (bonds' d hd)) a) b)
  · funext a
    exact Complex.ofReal_injective (congrFun (fields.symm.trans fields') a)

end DSFTomography.HT
