import DSFTomography.SFSixAnalytic
import DSFTomography.SFLaboratory

/-! The six-setting readout of finite-volume ground-state DSF moments.
The tilted entries are expressed in their orthonormal measurement frames. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def finiteReadout (R : Bonds S) (B : ℝ) : Params R.dirs → Harmonics R.dirs :=
  sixFunction (fun p => groundPaperReadout (withParams R p) B Subtype.val)

theorem finite_eq_chart (R : Bonds S) (G : ∀ i, GroundChart R i) {B : ℝ} (hB : 0<B)
    (p : Params R.dirs)
    (base : ∀ i, IsGroundPair R i (B⁻¹ • p) ((G i).ψ (B⁻¹ • p)) ((G i).E (B⁻¹ • p)))
    (tilted : ∀ t i, IsGroundPair R i (B⁻¹ • rotate t p)
      ((G i).ψ (B⁻¹ • rotate t p)) ((G i).E (B⁻¹ • rotate t p))) :
    finiteReadout R B p = atField (sixFunction (unitReadout G)) B p := by
  rw [six_field]
  unfold finiteReadout sixFunction
  congr 1
  exact Prod.ext (laboratory_readout G hB p base)
    (funext fun t => laboratory_readout G hB (rotate t p) (tilted t))

/-- For a fixed lattice, the exact diagonal readout is injective at every
sufficiently large field, uniformly over the complete coupling cube. -/
theorem diagonalSF_finite (R : Bonds S) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (finiteReadout R B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        DifferentiableAt ℝ (finiteReadout R B) p ∧
        ‖fderiv ℝ (fun q => finiteReadout R B q-leading q) p‖ ≤ C/B ∧
        ‖finiteReadout R B p-leading p‖ ≤ (C/B)*‖p‖ := by
  let G := fun i => (groundChart_exists R i).some
  let U : Set (Params R.dirs) := {p | ∀ i, IsGroundPair R i p ((G i).ψ p) ((G i).E p)}
  have near : U ∈ 𝓝 0 := eventually_all.mpr fun i => (G i).physical
  have rotated : {p | p∈U ∧ ∀ t, rotate t p∈U} ∈ 𝓝 (0:Params R.dirs) := by
    apply Filter.Eventually.and near
    apply eventually_all.mpr; intro t
    have tend : Tendsto (rotate (D := R.dirs) t) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (rotate (D := R.dirs) t).continuous.continuousAt (x := 0) |>.tendsto
    exact tend.eventually near
  obtain ⟨a,ha,physical⟩ := scaled_neighborhood rotated
  obtain ⟨C,hC,b,hb,result⟩ := six_chart R G
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  have la := (le_max_left ..).trans large
  have lb := (le_max_right ..).trans large
  have pos := ha.trans_le la
  have eq (p : Params R.dirs) (hp : p∈couplingCube R.dirs) :
      finiteReadout R B =ᶠ[𝓝 p] atField (sixFunction (unitReadout G)) B := by
    filter_upwards [physical B la p hp] with q hq
    apply finite_eq_chart R G pos q hq.1
    simpa only [map_smul] using hq.2
  obtain ⟨inj,est⟩ := result B lb
  refine ⟨fun p hp q hq same => inj hp hq
    ((eq p hp).self_of_nhds.symm.trans (same.trans (eq q hq).self_of_nhds)),?_⟩
  intro p hp
  refine ⟨(est p hp).1.congr_of_eventuallyEq (eq p hp),?_⟩
  have diff : (fun q => finiteReadout R B q-leading q) =ᶠ[𝓝 p]
      (fun q => atField (sixFunction (unitReadout G)) B q-leading q) := (eq p hp).sub EventuallyEq.rfl
  rw [diff.fderiv_eq,(eq p hp).self_of_nhds]
  exact (est p hp).2

end DSFTomography.SF.DiagonalSix
