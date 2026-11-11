import DSFTomography.HTBoxes
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! A periodic static DSF harmonic is the Gibbs expectation of one fixed local
observable. All translations, including the ones across the seam, are identical. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

private def translateConfig (t : S) : Config S ≃ Config S where
  toFun x r := x (r - t)
  invFun x r := x (r + t)
  left_inv x := by ext r; simp
  right_inv x := by ext r; simp

def translate (t : S) : Op (Config S) ≃ₐ[ℂ] Op (Config S) :=
  Matrix.reindexAlgEquiv ℂ ℂ (translateConfig t)

private abbrev spin (r : S) (a : Axis) := (qubitSpins (1 : (Op (Config S))ˣ)).σ r a

theorem translate_spin (t r : S) (a : Axis) :
    translate t (spin r a) = spin (r+t) a := by
  have raw (i : S) : spin i a = word (oneLabel i a) := by simp [spin, qubitSpins, string, inBasis]
  rw [raw, raw]
  ext x y
  change (∏ j, pauli (oneLabel r a j) (x (j+t)) (y (j+t))) =
    ∏ j, pauli (oneLabel (r+t) a j) (x j) (y j)
  rw [← Equiv.prod_comp (Equiv.addRight t) (fun j => pauli (oneLabel (r+t) a j) (x j) (y j))]
  simp [oneLabel]

theorem translate_H (V : Volume S) (t : S) :
    translate t (qubitH V.R V.h V.J) = qubitH V.R V.h V.J := by
  change translate t ((∑ i, ∑ a, (V.h a : ℂ) • spin i a) +
    ∑ d ∈ V.R.dirs, ∑ i, ∑ a, ∑ b, (V.J d a b : ℂ) • (spin i a * spin (i+d) b)) = _
  simp only [map_add, map_sum, map_smul, map_mul, translate_spin, add_right_comm _ _ t]
  apply congrArg₂ (· + ·)
  · exact Equiv.sum_comp (Equiv.addRight t) (fun i => ∑ a, (V.h a : ℂ) • spin i a)
  · apply Finset.sum_congr rfl
    intro d _
    exact Equiv.sum_comp (Equiv.addRight t)
      (fun i => ∑ a, ∑ b, (V.J d a b : ℂ) • (spin i a * spin (i+d) b))

namespace Volume

/-- Unnormalized Boltzmann weights in the physical tensor-product basis. -/
def boltzmann (V : Volume S) (z : ℂ) : Op (Config S) :=
  NormedSpace.exp ℂ ((-z) • qubitH V.R V.h V.J)

def partition (V : Volume S) (z : ℂ) : ℂ := (V.boltzmann z).trace

/-- The local pair of probes with the same order as the DSF. -/
def probe (c : Channel S) (r : S) : Op (Config S) := match c with
  | .bond d a b => spin r a * spin (r+d) b
  | .onsite k => spin r (k+1) * spin r (k+2)

/-- A single translated copy suffices. This normalized trace is holomorphic
where the finite-volume partition function is nonzero. -/
def localGibbs (V : Volume S) (c : Channel S) (z : ℂ) : ℂ :=
  (V.boltzmann z * probe c 0).trace / V.partition z

theorem trace_translate (t : S) (A : Op (Config S)) : (translate t A).trace = A.trace :=
  Equiv.sum_comp (translateConfig t).symm (fun x => A x x)

theorem translate_boltzmann (V : Volume S) (z : ℂ) (t : S) :
    translate t (V.boltzmann z) = V.boltzmann z := by
  open scoped Matrix.Norms.Operator in
  have cont : Continuous (translate t) := (translate t).toLinearMap.continuous_of_finiteDimensional
  open scoped Matrix.Norms.Operator in
  simp only [boltzmann, NormedSpace.map_exp ℂ _ cont, map_smul, translate_H]

private theorem translate_probe (c : Channel S) (t : S) :
    translate t (probe c 0) = probe c t := by
  cases c <;> simp [probe, map_mul, translate_spin, add_comm]

theorem trace_probe_eq_origin (V : Volume S) (c : Channel S) (z : ℂ) (t : S) :
    (V.boltzmann z * probe c t).trace = (V.boltzmann z * probe c 0).trace := by
  simpa only [map_mul, translate_boltzmann, translate_probe] using
    trace_translate t (V.boltzmann z * probe c 0)

private abbrev U (V : Volume S) := energyBasis V.R V.h V.J
private abbrev E (V : Volume S) := energies V.R V.h V.J

theorem boltzmann_diagonal (V : Volume S) (z : ℂ) :
    inBasis V.U (V.boltzmann z) = Matrix.diagonal (fun j => Complex.exp (-z * V.E j)) := by
  have diag : inBasis V.U (qubitH V.R V.h V.J) =
      Matrix.diagonal (fun m => (V.E m : ℂ)) :=
    (rotate_H V.R V.h V.J V.U).symm.trans (diagonalized V.R V.h V.J)
  have hs : inBasis V.U ((-z) • qubitH V.R V.h V.J) =
      Matrix.diagonal (fun j => -z * V.E j) := by
    rw [show inBasis V.U ((-z) • qubitH V.R V.h V.J) =
      (-z) • inBasis V.U (qubitH V.R V.h V.J) by simp [inBasis], diag, ← Matrix.diagonal_smul]
    rfl
  change _ * NormedSpace.exp ℂ _ * _ = _
  rw [← Matrix.exp_units_conj, ← inBasis, hs, Matrix.exp_diagonal]
  congr 1
  funext j
  simp [Complex.exp_eq_exp_ℂ]

theorem partition_eq_sum (V : Volume S) (z : ℂ) :
    V.partition z = ∑ j, Complex.exp (-z * V.E j) := by
  rw [partition, ← Matrix.trace_units_conj V.U (V.boltzmann z),
    ← inBasis, boltzmann_diagonal, Matrix.trace_diagonal]

theorem trace_test_eq_sum (V : Volume S) (A : Op (Config S)) (z : ℂ) :
    (V.boltzmann z * A).trace =
    ∑ j, Complex.exp (-z * V.E j) * inBasis V.U A j j := by
  rw [← Matrix.trace_units_conj V.U (V.boltzmann z * A),
    ← inBasis, ← inBasis_mul, boltzmann_diagonal]
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

private theorem trace_probe_eq_sum (V : Volume S) (c : Channel S) (z : ℂ) (t : S) :
    (V.boltzmann z * probe c t).trace =
    ∑ j, Complex.exp (-z * V.E j) * inBasis V.U (probe c t) j j :=
  V.trace_test_eq_sum _ _

theorem localGibbs_differentiableOn (V : Volume S) (c : Channel S) {D : Set ℂ}
    (regular : ∀ z ∈ D, V.partition z ≠ 0) : DifferentiableOn ℂ (V.localGibbs c) D := by
  change DifferentiableOn ℂ (fun z => (V.boltzmann z * probe c 0).trace / V.partition z) D
  simp only [trace_probe_eq_sum, partition_eq_sum] at *
  exact DifferentiableOn.div
    (DifferentiableOn.fun_sum fun j _ => by fun_prop)
    (DifferentiableOn.fun_sum fun j _ => by fun_prop) regular

private theorem gibbs_trace_real (V : Volume S) (c : Channel S) (β : ℝ) (t : S) :
    mean (gibbs β V.E) (inBasis V.U (probe c t)) = V.localGibbs c β := by
  rw [localGibbs, ← trace_probe_eq_origin V c _ t, partition_eq_sum, trace_probe_eq_sum]
  simp only [mean, gibbs, Complex.ofReal_div, Complex.ofReal_sum, ← Complex.ofReal_exp,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, div_mul_eq_mul_div, Finset.sum_div]

private theorem probe_energy (V : Volume S) (t s : S) (a b : Axis) :
    inBasis V.U (spin t a * spin s b) =
      (qubitSpins V.U).σ t a * (qubitSpins V.U).σ s b := by
  rw [← inBasis_mul]
  simp [qubitSpins, spin, string, inBasis]

/-- From the measured Lehmann sum on the reciprocal grid to the normalized
Gibbs trace of one probe at the origin, at every real inverse temperature. -/
theorem observable_eq_localGibbs (V : Volume S) (c : Channel S) (β : ℝ) :
    V.observable c β = V.localGibbs c β := by
  have each (t : S) := V.gibbs_trace_real c β t
  cases c with
  | bond d a b =>
    change harmonic (toMomentum _) d = _
    rw [harmonic_toMomentum]
    change avg (fun t => m₀ _ _ _) = _
    simp only [probe, probe_energy] at each
    simp [avg, zeroMoment, each, Fintype.card_ne_zero]
  | onsite k =>
    change harmonic (toMomentum _) 0 = _
    rw [harmonic_toMomentum]
    change avg (fun t => m₀ _ _ _) = _
    simp only [probe, probe_energy] at each
    simp [avg, zeroMoment, add_zero, each, Fintype.card_ne_zero]

/-- Every channel used by the readout has zero infinite-temperature intercept. -/
theorem observable_zero (V : Volume S) (c : Channel S) (hc : V.valid c) :
    V.observable c 0 = 0 := by
  have orth (i j : S) (a b : Axis) (ne : oneLabel i a ≠ oneLabel j b) :
      (spin i a * spin j b).trace = 0 := by
    change (string 1 (oneLabel i a) * string 1 (oneLabel j b)).trace = 0
    simp [string_overlap, ne]
  have traceless : (probe c (0 : S)).trace = 0 := by
    cases c with
    | bond d a b =>
      apply orth
      intro eq
      have hd : d ≠ 0 := V.R.nonzero d hc
      simpa [oneLabel, hd.symm] using congrFun eq 0
    | onsite k =>
      apply orth
      intro eq
      have atOrigin := congrFun eq 0
      fin_cases k <;> simp [oneLabel] at atOrigin
  simp [observable_eq_localGibbs, localGibbs, boltzmann, traceless]


end Volume
end DSFTomography.HT
