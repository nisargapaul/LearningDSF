import DSFTomography.SFPaperDSF
import DSFTomography.SFTaylorBound
import Mathlib.Analysis.Normed.Group.Tannery

/-! Volume limit for the manuscript harmonics. The many-body input is stated
as a convergent local expansion on a common coupling ball. Its linear
coefficient, the limiting readout and the finite-field error are outputs. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Filter
open scoped Topology NNReal ENNReal
variable {ν : ℕ} (R : Bonds (Site ν))

/-- Once the period distinguishes directed bonds, the physical bond labels
in every DSF can be compared in exactly the same order. -/
def bondInBox (n : ℕ) : R.dirs ≃ (periodicBonds R n).dirs :=
  Equiv.ofBijective (fun d => ⟨periodicSite R n d,Finset.mem_image_of_mem _ d.property⟩) (by
    constructor
    · intro d e same
      exact Subtype.ext (injects_dirs R n d.property e.property (congrArg Subtype.val same))
    · intro e
      obtain ⟨d,hd,he⟩ := Finset.mem_image.mp e.property
      exact ⟨⟨d,hd⟩,Subtype.ext he⟩)

def boxParams (n : ℕ) : Params R.dirs →L[ℝ] Params (periodicBonds R n).dirs :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => (p.1, fun d => p.2 ((bondInBox R n).symm d))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def originalLabels (n : ℕ) : Harmonics (periodicBonds R n).dirs →L[ℝ] Harmonics R.dirs :=
  LinearMap.toContinuousLinearMap {
    toFun := fun y => (y.1, fun d => y.2 (bondInBox R n d))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

abbrev BoxCharts := ∀ (n : ℕ) (i : Axis), GroundChart (periodicBonds R n) i

def boxReadout (G : BoxCharts R) (n : ℕ) (p : Params R.dirs) :=
  originalLabels R n (unitReadout (G n) (boxParams R n p))

theorem boxReadout_dsf (G : BoxCharts R) (n : ℕ) (B : ℝ) (p : Params R.dirs) :
    atField (boxReadout R G n) B p = originalLabels R n
      (paperFromDSF Subtype.val B (paperSpectra (G n) B (boxParams R n p))) := by
  rw [exact_spectral_readout]
  simp [atField,boxReadout]

theorem boxReadout_derivative (G : BoxCharts R) (n : ℕ) :
    HasFDerivAt (boxReadout R G n) leadingCLM 0 := by
  let a := boxParams R n
  let b := originalLabels R n
  have df : HasFDerivAt (unitReadout (G n)) leadingCLM (a 0) := by
    rw [map_zero,← unitReadout_slope (G n)]
    exact ((unitReadout_smooth (G n)).differentiableAt (by norm_num)).hasFDerivAt
  have total := b.hasFDerivAt.comp 0 (df.comp 0 a.hasFDerivAt)
  have eq : b.comp (leadingCLM.comp a) = leadingCLM := by
    apply ContinuousLinearMap.ext; intro p; apply Prod.ext
    · funext i
      change -2*p.1 i - 4*∑ d, p.2 ((bondInBox R n).symm d) i i = _
      rw [(bondInBox R n).symm.sum_comp (fun d => p.2 d i i)]
      rfl
    · funext d i k
      simp [a,b,boxParams,originalLabels,leadingCLM,leading]
  exact eq ▸ total

/-- Local ground-state expansion input. It requires no specified values for
the Taylor coefficients. The charts must be physical throughout the common
ball. Coefficient convergence can in particular be supplied by stabilization
of connected clusters of each fixed order. -/
structure LocalGroundExpansion (G : BoxCharts R) where
  radius : ℝ≥0
  positive : 0 < radius
  finiteSeries : ℕ → FormalMultilinearSeries ℝ (Params R.dirs) (Harmonics R.dirs)
  limitSeries : FormalMultilinearSeries ℝ (Params R.dirs) (Harmonics R.dirs)
  physical : ∀ n p, ‖p‖ < radius → ∀ i,
    let x := boxParams R n p
    IsGroundPair (periodicBonds R n) i x ((G n i).ψ x) ((G n i).E x)
  expansion : ∀ n, HasFPowerSeriesOnBall (boxReadout R G n) (finiteSeries n) 0 radius
  converges : ∀ k, Tendsto (fun n => finiteSeries n k) atTop (𝓝 (limitSeries k))
  envelope : ∃ K : ℝ, ∀ n k, ‖finiteSeries n k‖ * (radius:ℝ)^k ≤ K

namespace LocalGroundExpansion
variable {R} {G : BoxCharts R} (A : LocalGroundExpansion R G)

theorem bulk_series : HasFPowerSeriesAt A.limitSeries.sum A.limitSeries 0 := by
  obtain ⟨K,bound⟩ := A.envelope
  have rad := A.limitSeries.le_radius_of_bound K (r := A.radius) (fun k =>
    le_of_tendsto ((A.converges k).norm.mul_const ((A.radius:ℝ)^k)) (Eventually.of_forall fun n => bound n k))
  exact (A.limitSeries.hasFPowerSeriesOnBall ((ENNReal.coe_pos.mpr A.positive).trans_le rad)).hasFPowerSeriesAt

theorem bulk_readout {x : Params R.dirs} (hx : ‖x‖ < A.radius) :
    Tendsto (fun n => boxReadout R G n x) atTop (𝓝 (A.limitSeries.sum x)) := by
  obtain ⟨K,bound⟩ := A.envelope
  have pos : 0 < (A.radius:ℝ) := A.positive
  let ratio := ‖x‖ / (A.radius:ℝ)
  have sum := (summable_geometric_of_lt_one (show 0 ≤ ratio by positivity)
    (show ratio < 1 from (div_lt_one pos).mpr hx)).mul_left K
  have each (k : ℕ) := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Params R.dirs)
      (Harmonics R.dirs) (fun _ => x)).continuous.continuousAt.tendsto.comp (A.converges k)
  have major (n k : ℕ) : ‖A.finiteSeries n k (fun _ => x)‖ ≤ K*ratio^k := by
    have e := (A.finiteSeries n k).le_opNorm (fun _ => x)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at e
    apply e.trans
    have prod := mul_le_mul_of_nonneg_right (bound n k) (pow_nonneg (a := ratio) (by positivity) k)
    have cancel : (A.radius:ℝ)*ratio = ‖x‖ := by dsimp [ratio]; field_simp
    simpa only [mul_assoc,← mul_pow,cancel] using prod
  have lim := tendsto_tsum_of_dominated_convergence sum each (Eventually.of_forall major)
  have mem : x ∈ EMetric.ball 0 (A.radius:ℝ≥0∞) := by
    rw [EMetric.mem_ball, edist_zero_right]; exact ENNReal.coe_lt_coe.mpr hx
  apply lim.congr'
  exact Eventually.of_forall (fun n => by simpa using ((A.expansion n).hasSum mem).tsum_eq)

theorem bulk_slope : fderiv ℝ A.limitSeries.sum 0 = leadingCLM := by
  let curry := continuousMultilinearCurryFin1 ℝ (Params R.dirs) (Harmonics R.dirs)
  have finite (n : ℕ) : curry (A.finiteSeries n 1) = leadingCLM :=
    ((A.expansion n).hasFPowerSeriesAt.hasFDerivAt).unique (boxReadout_derivative R G n)
  have cv := curry.continuous.continuousAt.tendsto.comp (A.converges 1)
  exact A.bulk_series.hasFDerivAt.fderiv.trans (tendsto_nhds_unique cv
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (finite n).symm))))

/-- The same explicit two-point bound holds for every periodic DSF and for
its thermodynamic limit. B need only reach 2/r for this error estimate. -/
theorem shared_field_bound {K B : ℝ} (hK : 0 ≤ K)
    (bound : ∀ n k, ‖A.finiteSeries n k‖*(A.radius:ℝ)^k ≤ K)
    (large : 2/(A.radius:ℝ) ≤ B) {p q : Params R.dirs}
    (hp : p ∈ couplingCube R.dirs) (hq : q ∈ couplingCube R.dirs) :
    let measured := fun n v => originalLabels R n
      (paperFromDSF Subtype.val B (paperSpectra (G n) B (boxParams R n v)))
    let error := fun (M : Params R.dirs → Harmonics R.dirs) =>
      ‖(M p - leading p) - (M q - leading q)‖
    let upper := 6*K/(A.radius:ℝ)^2/B*‖p-q‖
    (∀ n, error (measured n) ≤ upper) ∧ error (atField A.limitSeries.sum B) ≤ upper := by
  dsimp only
  simp_rw [← boxReadout_dsf]
  have finite (n : ℕ) := field_tail_bound (A.expansion n) (show 0 < (A.radius:ℝ) from A.positive)
    hK (bound n) (boxReadout_derivative R G n).fderiv large hp hq
  have hr : 0 < (A.radius:ℝ) := A.positive
  have hB : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2/(A.radius:ℝ)) large
  have limit {v : Params R.dirs} (hv : v ∈ couplingCube R.dirs) :
      Tendsto (fun n => atField (boxReadout R G n) B v) atTop (𝓝 (atField A.limitSeries.sum B v)) := by
    apply (A.bulk_readout (x := B⁻¹ • v) ?_).const_smul B
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hB)]
    apply (mul_le_of_le_one_right (inv_nonneg.mpr hB.le) (show ‖v‖ ≤ 1 by simpa [couplingCube] using hv)).trans_lt
    rw [inv_eq_one_div,div_lt_iff₀ hB]
    linarith [(div_le_iff₀ hr).mp large,mul_comm B (A.radius:ℝ)]
  exact ⟨finite, le_of_tendsto (((limit hp).sub_const _).sub ((limit hq).sub_const _)).norm
    (Eventually.of_forall finite)⟩

theorem bulk_zero : A.limitSeries.sum 0 = 0 := by
  have lim := A.bulk_readout (x := 0) (by simpa using (show 0 < (A.radius:ℝ) from A.positive))
  apply tendsto_nhds_unique lim
  apply tendsto_const_nhds.congr'
  exact Eventually.of_forall (fun n => by simp [boxReadout,unitReadout_zero])

end LocalGroundExpansion

/-- Thermodynamic result conditional only on the stated local expansion.
The data in the limit are the measured Fourier projections of the periodic
ground-state DSFs. The field threshold is independent of both λ and n. -/
theorem fullAccessSF_paper_limit {G : BoxCharts R} (A : LocalGroundExpansion R G) :
    let M := atField A.limitSeries.sum
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (M B) (couplingCube R.dirs) ∧ ∀ p ∈ couplingCube R.dirs,
        (∀ n i, let x := boxParams R n (B⁻¹ • p)
                IsGroundPair (periodicBonds R n) i x ((G n i).ψ x) ((G n i).E x)) ∧
        Tendsto (fun n => originalLabels R n (paperFromDSF Subtype.val B
          (paperSpectra (G n) B (boxParams R n p)))) atTop (𝓝 (M B p)) ∧
        DifferentiableAt ℝ (M B) p ∧
        ‖fderiv ℝ (fun q => M B q - leading q) p‖ ≤ C/B ∧ ‖M B p - leading p‖ ≤ (C/B)*‖p‖ := by
  dsimp only
  have sm : ContDiffAt ℝ 2 A.limitSeries.sum 0 := A.bulk_series.analyticAt.contDiffAt
  obtain ⟨C,hC,b₁,hb₁,est⟩ := scaled_bounds _ sm A.bulk_zero A.bulk_slope
  obtain ⟨b₂,_,inj⟩ := rescaled_injective _ sm A.bulk_slope
  let r : ℝ := A.radius
  have hr : 0 < r := A.positive
  refine ⟨C,hC,max (max b₁ b₂) (2/r),hb₁.trans_le ((le_max_left ..).trans (le_max_left ..)),?_⟩
  intro B large
  have l₁ := (le_max_left ..).trans ((le_max_left ..).trans large)
  have l₂ := (le_max_right ..).trans ((le_max_left ..).trans large)
  have lr : 2/r ≤ B := (le_max_right ..).trans large
  have pos : 0 < B := hb₁.trans_le l₁
  refine ⟨inj B l₂,?_⟩
  intro p hp
  have small : B⁻¹ < r := by
    rw [inv_eq_one_div,div_lt_iff₀ pos]
    linarith [(div_le_iff₀ hr).mp lr,mul_comm B r]
  have cube : ‖p‖ ≤ 1 := by simpa [couplingCube] using hp
  have inside : ‖B⁻¹ • p‖ < r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos)]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr pos.le) cube).trans_lt small
  refine ⟨fun n => A.physical n _ inside,?_,est B l₁ p hp⟩
  simp_rw [← boxReadout_dsf]
  exact (A.bulk_readout inside).const_smul B

end DSFTomography.SF
