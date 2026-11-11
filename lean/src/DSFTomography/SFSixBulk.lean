import DSFTomography.SFSixFinite
import DSFTomography.SFClusterBulk

/-! Volume-first six-direction tomography. The expansion, its uniform radius,
and the finite-volume ground states are constructed by the existing cluster
proof; no convergence hypothesis is added to the final theorem. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Filter
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν))

theorem rotate_box (n : ℕ) (t : Pair) (p : Params R.dirs) :
    rotate t (boxParams R n p)=boxParams R n (rotate t p) := rfl

theorem combine_labels (n : ℕ) (v : Bundle (periodicBonds R n).dirs) :
    originalLabels R n (combine v)=
      combine (originalLabels R n v.1,fun t => originalLabels R n (v.2 t)) := rfl

/-- Physical six-field moments converge before taking their coupling
 derivatives. The limiting inverse and its remainder are uniform in volume. -/
theorem diagonalSF_limit {G : BoxCharts R} (A : LocalGroundExpansion R G) :
    ∃ M : ℝ → Params R.dirs → Harmonics R.dirs,
      ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
        Set.InjOn (M B) (couplingCube R.dirs) ∧ ∀ p ∈ couplingCube R.dirs,
          Tendsto (fun n => originalLabels R n
            (finiteReadout (periodicBonds R n) B (boxParams R n p))) atTop (𝓝 (M B p)) ∧
          DifferentiableAt ℝ (M B) p ∧
          ‖fderiv ℝ (fun q => M B q-leading q) p‖ ≤ C/B ∧
          ‖M B p-leading p‖ ≤ (C/B)*‖p‖ := by
  have smooth : ContDiffAt ℝ 2 A.limitSeries.sum 0 := A.bulk_series.analyticAt.contDiffAt
  obtain ⟨C,hC,b,hb,result⟩ := six_rescaled smooth A.bulk_zero A.bulk_slope
  let U : Set (Params R.dirs) := {p | ‖p‖ < A.radius ∧ ∀ t, ‖rotate t p‖ < A.radius}
  have near : U ∈ 𝓝 0 := by
    have ball : {p : Params R.dirs | ‖p‖ < A.radius} ∈ 𝓝 0 := by
      simpa [Metric.ball,dist_zero_right] using Metric.ball_mem_nhds (0:Params R.dirs) (show 0<(A.radius:ℝ) from A.positive)
    apply Filter.Eventually.and ball
    apply eventually_all.mpr; intro t
    have tend : Tendsto (rotate (D := R.dirs) t) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (rotate (D := R.dirs) t).continuous.continuousAt (x := 0) |>.tendsto
    exact tend.eventually ball
  obtain ⟨a,ha,inside⟩ := scaled_neighborhood near
  refine ⟨atField (sixFunction A.limitSeries.sum),C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  have la := (le_max_left ..).trans large
  have lb := (le_max_right ..).trans large
  have pos := ha.trans_le la
  refine ⟨(result B lb).1,?_⟩
  intro p hp
  have small := (inside B la p hp).self_of_nhds
  change ‖B⁻¹ • p‖ < A.radius ∧ ∀ t, ‖rotate t (B⁻¹ • p)‖ < A.radius at small
  have convergence : Tendsto (fun n => sixFunction (boxReadout R G n) (B⁻¹ • p)) atTop
      (𝓝 (sixFunction A.limitSeries.sum (B⁻¹ • p))) := by
    apply combine.continuous.continuousAt.tendsto.comp
    exact (A.bulk_readout small.1).prodMk_nhds (tendsto_pi_nhds.mpr fun t => A.bulk_readout (small.2 t))
  refine ⟨?_,(result B lb).2 p hp⟩
  apply (convergence.const_smul B).congr'
  apply Eventually.of_forall; intro n
  have base := A.physical n (B⁻¹ • p) small.1
  have tilted (t : Pair) := A.physical n (rotate t (B⁻¹ • p)) (small.2 t)
  change B • sixFunction (boxReadout R G n) (B⁻¹ • p) = originalLabels R n (finiteReadout (periodicBonds R n) B (boxParams R n p))
  rw [finite_eq_chart (periodicBonds R n) (G n) pos (boxParams R n p)
    (by simpa only [map_smul] using base)
    (by intro t; simpa only [map_smul,rotate_box] using tilted t)]
  simp only [atField,sixFunction,← map_smul,combine_labels,map_smul,rotate_box,boxReadout]

/-- Self-contained thermodynamic theorem for the six-direction protocol. -/
theorem diagonalSF_thermodynamic :
    ∃ M : ℝ → Params R.dirs → Harmonics R.dirs,
      ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
        Set.InjOn (M B) (couplingCube R.dirs) ∧ ∀ p ∈ couplingCube R.dirs,
          Tendsto (fun n => originalLabels R n
            (finiteReadout (periodicBonds R n) B (boxParams R n p))) atTop (𝓝 (M B p)) ∧
          DifferentiableAt ℝ (M B) p ∧
          ‖fderiv ℝ (fun q => M B q-leading q) p‖ ≤ C/B ∧
          ‖M B p-leading p‖ ≤ (C/B)*‖p‖ := by
  obtain ⟨G,⟨A⟩⟩ := periodic_ground_expansion R
  exact diagonalSF_limit R A

end DSFTomography.SF.DiagonalSix
