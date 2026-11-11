import DSFTomography.SFSixBulk
import DSFTomography.DSFInfiniteSF

/-! Six-direction readout of the infinite-volume real-time DSF. Its spectral
moments are constructed as distributions, not assumed moment arrays. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT HT.LocalWord Spectral Filter
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν))

def infiniteReadout (B : ℝ) : Params R.dirs → Harmonics R.dirs :=
  sixFunction (fun p => infiniteSFReadout R p.1 (parameterExchanges R p) B)

theorem infinite_eq_series {G : BoxCharts R} (A : LocalGroundExpansion R G)
    {B : ℝ} (pos : 0<B) (q : Params R.dirs) (small : ‖B⁻¹ • q‖ < A.radius) :
    infiniteSFReadout R q.1 (parameterExchanges R q) B = atField A.limitSeries.sum B q := by
  apply infiniteSFReadout_eq_limit
  apply ((A.bulk_readout small).const_smul B).congr'
  apply Eventually.of_forall; intro n
  change B • boxReadout R G n (B⁻¹ • q) = groundPaperReadout (periodicVolume R q.1 (parameterExchanges R q) n) B (fun d : R.dirs => place R n d)
  rw [periodicVolume_parameters]
  have eq := laboratory_readout (G n) pos (boxParams R n q)
    (by simpa only [map_smul] using A.physical n (B⁻¹ • q) small)
  change B • boxReadout R G n (B⁻¹ • q) = _
  change _ = originalLabels R n
    (groundPaperReadout (withParams (periodicBonds R n) (boxParams R n q)) B Subtype.val)
  rw [eq]
  simp only [boxReadout,atField,map_smul]

/-- From the real-time DSF to unique couplings, in the thermodynamic limit.
The error bound is for the explicit leading linear inverse; the exact
finite-field measurement map itself is injective. -/
theorem diagonalSF_infinite_DSF :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (infiniteReadout R B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        DifferentiableAt ℝ (infiniteReadout R B) p ∧
        ‖fderiv ℝ (fun q => infiniteReadout R B q-leading q) p‖ ≤ C/B ∧
        ‖infiniteReadout R B p-leading p‖ ≤ (C/B)*‖p‖ := by
  obtain ⟨G,⟨A⟩⟩ := periodic_ground_expansion R
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
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  have la := (le_max_left ..).trans large
  have lb := (le_max_right ..).trans large
  have pos := ha.trans_le la
  have eq (p : Params R.dirs) (hp : p∈couplingCube R.dirs) :
      infiniteReadout R B =ᶠ[𝓝 p] atField (sixFunction A.limitSeries.sum) B := by
    filter_upwards [inside B la p hp] with q hq
    rw [six_field]
    unfold infiniteReadout sixFunction
    apply congrArg combine
    refine Prod.ext (infinite_eq_series R A pos q hq.1) ?_
    funext t
    exact infinite_eq_series R A pos (rotate t q) (by simpa only [map_smul] using hq.2 t)
  obtain ⟨inj,est⟩ := result B lb
  refine ⟨fun p hp q hq same => inj hp hq
    ((eq p hp).self_of_nhds.symm.trans (same.trans (eq q hq).self_of_nhds)),?_⟩
  intro p hp
  refine ⟨(est p hp).1.congr_of_eventuallyEq (eq p hp),?_⟩
  have diff : (fun q => infiniteReadout R B q-leading q) =ᶠ[𝓝 p]
      (fun q => atField (sixFunction A.limitSeries.sum) B q-leading q) := (eq p hp).sub EventuallyEq.rfl
  rw [diff.fderiv_eq,(eq p hp).self_of_nhds]
  exact (est p hp).2

/-- The implemented linear estimator, including additive readout error. -/
theorem diagonalSF_reconstruction :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube R.dirs,
      ∀ η : Harmonics R.dirs,
        ‖decoder (infiniteReadout R B p+η)-p‖ ≤
          ‖(decoder (D := R.dirs))‖*((C/B)*‖p‖+‖η‖) := by
  obtain ⟨C,hC,b,hb,result⟩ := diagonalSF_infinite_DSF R
  refine ⟨C,hC,b,hb,?_⟩
  intro B large p hp η
  have eq : decoder (infiniteReadout R B p+η)-p =
      decoder ((infiniteReadout R B p-leading p)+η) := by
    rw [map_add,map_add,map_sub,show decoder (leading p)=p from readout_leading p]
    abel
  rw [eq]
  exact (decoder.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add_right ((result B large).2 p hp).2.2 _)) (norm_nonneg _))

/-- Exact inverse on the physical cube. This is a mathematical inverse,
not a claim about the runtime of a nonlinear reconstruction algorithm. -/
def exactRecover (B : ℝ) : Harmonics R.dirs → Params R.dirs :=
  Function.invFunOn (infiniteReadout R B) (couplingCube R.dirs)

theorem exact_recovery :
    ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube R.dirs,
      exactRecover R B (infiniteReadout R B p)=p := by
  obtain ⟨C,hC,b,hb,result⟩ := diagonalSF_infinite_DSF R
  exact ⟨b,hb,fun B large p hp => (result B large).1.leftInvOn_invFunOn hp⟩

end DSFTomography.SF.DiagonalSix
