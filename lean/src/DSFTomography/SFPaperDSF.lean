import DSFTomography.SFPaperFinite
import DSFTomography.SFProjectors

/-! The finite-volume end point starts with the complete ground-state
Lehmann lines and retains only the specified Fourier amplitudes. All moments
are divided by 2π. Spin labels in the spectra are laboratory labels. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {R : Bonds S}

def inChart (i a : Axis) := a-(i+1)
private theorem chart_lab (i a : Axis) : inChart i (axisInLab i a) = a := by fin_cases i <;> fin_cases a <;> decide
private theorem chart_cyclic (i a : Axis) : inChart i (a+1) = inChart i a+1 ∧
    inChart i (a+2) = inChart i a+2 := by fin_cases i <;> fin_cases a <;> decide

def unitHamiltonian (R : Bonds S) (i : Axis) (p : Params R.dirs) : Op (Config S) :=
  Matrix.diagonal flipGap + fieldFrame (withParams R p) i

theorem unitHamiltonian_self (i : Axis) (p : Params R.dirs) : (unitHamiltonian R i p).IsHermitian := by
  apply Matrix.IsHermitian.add _ (qubitH_hermitian ..)
  unfold Matrix.IsHermitian; ext x y
  by_cases eq : x=y
  · subst y; simp [Matrix.conjTranspose_apply,flipGap]
  · simp [Matrix.conjTranspose_apply,eq,Ne.symm eq]

omit [AddCommGroup S] in
/-- The field term in the cyclic chart is the Zeeman Hamiltonian plus the
constant number of spins. Thus flipGap measures actual transition energies. -/
theorem field_gap_matrix : Matrix.diagonal (flipGap (S := S)) =
    (Fintype.card S : ℂ) • (1:Op (Config S)) + zeeman 1 2 := by
  ext x y
  have spin (r : S) : spinAt r 2 x y =
      if x=y then (1 - 2*(if x r=1 then (1:ℂ) else 0)) else 0 := by
    rw [spinAt,word_one]
    by_cases eq : x=y
    · subst y; have h : x r=0 ∨ x r=1 := by have := (x r).isLt; omega
      rcases h with z|z <;> norm_num [z,pauliValues]
    · rw [if_neg eq]
      split_ifs with off
      · have ne : x r ≠ y r := fun same => eq (funext (fun t => by
          by_cases h : t=r; subst t; exact same; exact off t h))
        have cases (j : Fin 2) : j=0 ∨ j=1 := by fin_cases j <;> decide
        rcases cases (x r) with h1|h1 <;> rcases cases (y r) with h2|h2 <;> simp_all [pauliValues]
      · rfl
  simp only [zeeman,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_apply,Matrix.one_apply,spin]
  by_cases eq : x=y
  · simp [eq,flipGap,Finset.sum_sub_distrib,← Finset.sum_filter]; ring
  · simp [eq]

/-- In the physical field units the same matrix is the driven Pauli
Hamiltonian, up to a scalar identity that cancels in all frequencies. -/
theorem driven_frame (i : Axis) {B : ℝ} (hB : 0 < B) (p : Params R.dirs) :
    (B:ℂ) • unitHamiltonian R i (B⁻¹ • p) =
      ((B:ℂ) * Fintype.card S) • (1:Op (Config S)) + zeeman B 2 + fieldFrame (withParams R p) i := by
  obtain ⟨L,hL⟩ := frame_linear R i
  rw [unitHamiltonian,smul_add,field_gap_matrix,smul_add,smul_smul,← hL,← hL,map_smul]
  have field : (B:ℂ) • zeeman (S := S) 1 2 = zeeman B 2 := by
    simp [zeeman,Finset.smul_sum]
  rw [field]
  congr 1
  funext x y
  simp [Complex.real_smul,hB.ne']

namespace GroundChart
variable {i : Axis} (g : GroundChart R i)
private def lines (p : Params R.dirs) (r s : S) (a b : Axis) :=
  intensity (unitHamiltonian_self i p) (g.ψ p) (spinAt r (inChart i a)) (spinAt s (inChart i b))

/-- Local moments formed by summing **all** lines, including the elastic
line. The unit-field frequencies are E_j-E_g. -/
def linesData (p : Params R.dirs) : Data S where
  static d a b := avg (fun r => ∑ j, g.lines p r (r+d) a b j)
  first d a b := avg (fun r => ∑ j, (((unitHamiltonian_self i p).eigenvalues j:ℂ) -
    g.E p)*g.lines p r (r+d) a b j)

theorem static_lines (p : Params R.dirs) (d : S) (a b : Axis) :
    (g.linesData p).static d a b = avg (fun r => sandwich (g.ψ p)
      (spinAt r (inChart i a)*spinAt (r+d) (inChart i b)) (g.ψ p)) := by
  unfold linesData lines; simp only [lehmann_static]

theorem first_lines (p : Params R.dirs) (d : S) (a b : Axis) :
    (g.linesData p).first d a b = avg (fun r => sandwich (g.ψ p)
      (spinAt r (inChart i a)*(unitHamiltonian R i p - g.E p • 1)*spinAt (r+d) (inChart i b)) (g.ψ p)) := by
  unfold linesData lines; simp only [lehmann_first]

private theorem mag_lines (p : Params R.dirs) (a : Axis) :
    (g.linesData p).mag a = g.meanAt p (inChart i a) := by
  let w := g.ψ p
  let ev : Op (Config S) →ₗ[ℂ] ℂ := {
    toFun := fun T => sandwich w T w
    map_add' := by intros; simp [sandwich,mul_add,add_mul,Finset.sum_add_distrib]
    map_smul' := by intros; simp [sandwich,← Finset.mul_sum,mul_left_comm,mul_assoc] }
  let k := inChart i a
  have atR (r : S) : ev (spinAt r (k+1)*spinAt r (k+2)) - ev (spinAt r (k+2)*spinAt r (k+1)) =
      2*Complex.I*ev (spinAt r k) := by
    have spin := (qubitSpins (1 : (Op (Config S))ˣ)).pauli r (k+1) r (k+2)
    have axes : sign (k+1) (k+2)=1 ∧ third (k+1) (k+2)=k := by
      exact (show ∀ k : Axis, sign (k+1) (k+2)=1 ∧ third (k+1) (k+2)=k by intro k; fin_cases k <;> exact ⟨rfl,rfl⟩) k
    simp only [phase,axes,mul_one,qubitSpins,string,inBasis,Units.val_one,one_mul,inv_one,mul_one] at spin
    rw [← map_sub]
    exact (congrArg ev spin).trans (ev.map_smul _ _)
  unfold Data.mag
  simp only [static_lines,add_zero,(chart_cyclic i a).1,(chart_cyclic i a).2]
  change (avg (fun r => ev (spinAt r (k+1)*spinAt r (k+2))) -
    avg (fun r => ev (spinAt r (k+2)*spinAt r (k+1))))/(2*Complex.I) = avg (fun r => ev (spinAt r k))
  simp only [avg,← sub_div,← Finset.sum_sub_distrib,atR,← Finset.mul_sum]; field_simp

private def rawCov (p : Params R.dirs) (r s : S) (a b : Axis) :=
  sandwich (g.ψ p) (spinAt r a*spinAt s b) (g.ψ p) - g.meanAt p a*g.meanAt p b

private theorem cov_agrees (p : Params R.dirs) {r s : S} (ne : r≠s) (a b : Axis) :
    g.rawCov p r s a b = g.staticAt p r s a b := by
  have eq := string_pair (1 : (Op (Config S))ˣ) ne a b
  simp [string,inBasis] at eq
  simp [rawCov,staticAt,spinAt,eq]

private theorem cov_comm (p : Params R.dirs) {r s : S} (ne : r≠s) (a b : Axis) :
    g.rawCov p r s a b = g.rawCov p s r b a := by
  have eq := (qubitSpins (1 : (Op (Config S))ˣ)).pauli r a s b
  simp [ne,qubitSpins,string,inBasis,bracket] at eq
  simp [rawCov,spinAt,sub_eq_zero.mp eq,mul_comm]

omit [DecidableEq S] in
private theorem avg_constant (f : S → ℂ) (k : ℂ) :
    avg f - k = avg (fun r => f r-k) := by simp [avg,Finset.sum_sub_distrib,sub_div,Fintype.card_ne_zero]

private theorem centered_lines (p : Params R.dirs) (d : S) :
    (connected (g.linesData p)).first d (i+1) (i+1) - 2*(connected (g.linesData p)).static d (i+1) (i+1) =
      avg fun r => g.centeredAt p r (r+d) := by
  let w := g.ψ p
  let h := unitHamiltonian_self i p
  have one (r : S) : (∑ j, ((h.eigenvalues j:ℂ)-g.E p)*g.lines p r (r+d) (i+1) (i+1) j) -
      2*(∑ j, g.lines p r (r+d) (i+1) (i+1) j) =
      sandwich (g.applied p r 0) (Matrix.diagonal (fun x => flipGap x - g.E p - 2) + fieldFrame (withParams R p) i) (g.applied p (r+d) 0) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    have freq (j : Config S) (z : ℂ) : ((h.eigenvalues j:ℂ)-g.E p)*z-2*z =
        ((h.eigenvalues j:ℂ)-(g.E p+2))*z := by ring
    simp_rw [freq]
    unfold lines
    rw [lehmann_first,sandwich_probes _ _ _ _ (word_hermitian _)]
    have shift : unitHamiltonian R i p - (g.E p+2) • (1:Op (Config S)) =
        Matrix.diagonal (fun x => flipGap x - g.E p - 2) + fieldFrame (withParams R p) i := by
      ext x y
      by_cases eq : x=y <;> simp [unitHamiltonian,eq]; ring
    rw [shift]
    simp only [inChart,sub_self]; rfl
  have j0 : inChart i (i+1) = 0 := by simp [inChart]
  simp only [connected,mag_lines,j0]
  change avg (fun r => ∑ j, ((h.eigenvalues j:ℂ)-g.E p)*g.lines p r (r+d) (i+1) (i+1) j) -
    2*(avg (fun r => ∑ j, g.lines p r (r+d) (i+1) (i+1) j) - _) = _
  rw [mul_sub,sub_sub_eq_add_sub,add_sub_right_comm]
  unfold centeredAt
  simp only [avg,Finset.sum_add_distrib,← Finset.mul_sum,add_div]
  have eq := congrArg (fun f : S → ℂ => (∑ r, f r)/(Fintype.card S:ℂ)) (funext one)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,sub_div] at eq
  field_simp [Fintype.card_ne_zero] at eq ⊢
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at *
  linear_combination eq

end GroundChart

/-- The spatial Fourier transform of the calibrated physical spectra.
Transition frequencies are multiplied by B and the ground state and
intensities are evaluated at the rescaled couplings λ/B. -/
def paperSpectra (G : ∀ i, GroundChart R i) (B : ℝ) (p : Params R.dirs) (i : Axis) : Data (Momentum S) :=
  let A := energyScale B ((G i).linesData (B⁻¹ • p))
  { static := fun q a b => toMomentum (fun d => A.static d a b) q
    first := fun q a b => toMomentum (fun d => A.first d a b) q }

theorem exact_spectral_readout (G : ∀ i, GroundChart R i) (B : ℝ) (p : Params R.dirs) :
    paperFromDSF Subtype.val B (paperSpectra G B p) = atField (unitReadout G) B p := by
  let x := B⁻¹ • p
  let A := fun i => connected ((G i).linesData x)
  have extract (i) : connected (paperSpectra G B p i).harmonics = energyScale B (A i) := by
    simp [paperSpectra,Data.harmonics,harmonic_toMomentum,connected,energyScale,Data.mag,A,x]
  simp only [paperFromDSF,extract,harmonics_energyScale,atField]
  apply congrArg (B • ·)
  have stat (i : Axis) (d : S) (a b : Axis) :
      (A i).static d (axisInLab i a) (axisInLab i b) = avg fun r => (G i).rawCov x r (r+d) a b := by
    simp [A,connected,GroundChart.static_lines,GroundChart.mag_lines,chart_lab,GroundChart.rawCov,
      GroundChart.avg_constant]
  rw [localReadout_eq_paper R 1 A (fun i => (G i).centeredAt x) (fun i => (G i).rawCov x)
    (fun i d => by simpa using (G i).centered_lines x d) stat (fun i _ _ h a b => (G i).cov_comm x h a b)]
  apply Prod.ext
  · rfl
  · funext d i k
    have ne (r : S) : r≠r+d.val := Ne.symm (by simpa using R.nonzero _ d.property)
    simp only [localReadout,unitReadout,Complex.ofReal_one,one_mul,GroundChart.cov_agrees _ _ (ne _),x]

/-- Self-contained finite-volume theorem, with the field threshold uniform
over all couplings in the cube. The estimator sees only the indicated
Fourier amplitudes of the zeroth and first Lehmann moments. -/
theorem fullAccessSF_paper_finite (R : Bonds S) :
    let G := fun i => (groundChart_exists R i).some
    let M := fun B p => paperFromDSF Subtype.val B (paperSpectra G B p)
    ∃ C ≥ (0:ℝ), ∃ B₀ > (0:ℝ), ∀ B ≥ B₀,
      (∀ p ∈ couplingCube R.dirs, ∀ i,
        IsGroundPair R i (B⁻¹ • p) ((G i).ψ (B⁻¹ • p)) ((G i).E (B⁻¹ • p))) ∧
      Set.InjOn (M B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs, DifferentiableAt ℝ (M B) p ∧
        ‖fderiv ℝ (fun q => M B q - leading q) p‖ ≤ C/B ∧
        ‖M B p - leading p‖ ≤ (C/B)*‖p‖ := by
  dsimp only
  simp only [exact_spectral_readout]
  let G := fun i => (groundChart_exists R i).some
  obtain ⟨C,hC,b,hb,estimate⟩ := paper_finite G
  obtain ⟨a,ha,physical⟩ := groundChart_cube G
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  exact ⟨physical B ((le_max_left ..).trans large),estimate B ((le_max_right ..).trans large)⟩

end DSFTomography.SF
