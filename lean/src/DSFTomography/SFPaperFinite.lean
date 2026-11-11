import DSFTomography.SFSmallFieldModel
import DSFTomography.SFLehmann

/-! Finite-box certification of the compressed manuscript readout. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {R : Bonds S}

@[local fun_prop] private theorem re_smooth (x : ℂ) : ContDiffAt ℝ 2 Complex.re x :=
  Complex.reCLM.contDiff.contDiffAt
@[local fun_prop] private theorem im_smooth (x : ℂ) : ContDiffAt ℝ 2 Complex.im x :=
  Complex.imCLM.contDiff.contDiffAt
@[local fun_prop] private theorem star_smooth (x : ℂ) : ContDiffAt ℝ 2 (star : ℂ → ℂ) x :=
  Complex.conjCLE.contDiff.contDiffAt

namespace GroundChart
variable {i : Axis}
def ray (g : GroundChart R i) (p : Params R.dirs) : EigenRay (withParams R p) i where
  ψ := fun t => g.ψ (t • p)
  E := fun t => g.E (t • p)
  vacuum_at := by simp [g.vac]
  energy_at := by simp [g.E0]
  smooth_ket := fun k => by
    have s : ContDiffAt ℝ 2 (fun x => g.ψ x k) 0 :=
      (ContinuousLinearMap.proj k : (Config S → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt.comp _ g.smoothψ
    have sr : DifferentiableAt ℝ (fun x => g.ψ x k) ((0:ℝ) • p) := by simpa using s.differentiableAt (by norm_num)
    exact sr.comp 0 (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => t • p) 0)
  smooth_energy := by
    have sr : DifferentiableAt ℝ g.E ((0:ℝ) • p) := by simpa using g.smoothE.differentiableAt (by norm_num)
    exact sr.comp 0 (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => t • p) 0)
  eigen := by
    obtain ⟨L,hL⟩ := frame_linear R i
    have tend : Tendsto (fun t : ℝ => t • p) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.smul continuous_const : Continuous (fun t : ℝ => t • p)).continuousAt (x := 0) |>.tendsto
    filter_upwards [tend.eventually g.physical] with t ht k
    have eq := ht.2.1 k
    rw [← hL,map_smul] at eq
    simpa [← hL,Complex.real_smul,mul_assoc,Finset.mul_sum] using eq

def meanAt (g : GroundChart R i) (p : Params R.dirs) (a : Axis) :=
  avg fun r => sandwich (g.ψ p) (spinAt r a) (g.ψ p)

def applied (g : GroundChart R i) (p : Params R.dirs) (r : S) (a : Axis) (x : Config S) :=
  ∑ y, spinAt r a x y * g.ψ p y

def centeredAt (g : GroundChart R i) (p : Params R.dirs) (r s : S) :=
  sandwich (g.applied p r 0)
    (Matrix.diagonal (fun x => flipGap x - g.E p - 2) + fieldFrame (withParams R p) i)
    (g.applied p s 0) + 2*(g.meanAt p 0*g.meanAt p 0)

def staticAt (g : GroundChart R i) (p : Params R.dirs) (r s : S) (a b : Axis) :=
  sandwich (g.ψ p) (word (twoLabel r s a b)) (g.ψ p) - g.meanAt p a*g.meanAt p b

end GroundChart

def unitReadout (G : ∀ i, GroundChart R i) (p : Params R.dirs) : Harmonics R.dirs :=
  localReadout R (fun i => (G i).centeredAt p) (fun i => (G i).staticAt p)

theorem unitReadout_zero (G : ∀ i, GroundChart R i) : unitReadout G 0 = 0 := by
  let ray := fun i => (G i).ray (0 : Params R.dirs)
  have mean (i a : Axis) (ha : a=0 ∨ a=1) : (G i).meanAt 0 a = 0 := by
    simpa [ray,GroundChart.ray,EigenRay.meanProbe,GroundChart.meanAt] using (ray i).transverse_mean_zero a ha
  have probe (i : Axis) (r : S) : (G i).applied 0 r 0 = ket (flip r) := by
    simpa [ray,GroundChart.ray,EigenRay.probeKet,GroundChart.applied] using (ray i).probe_at r
  have cen (i : Axis) (r s : S) : (G i).centeredAt 0 r s = 0 := by
    obtain ⟨L,hL⟩ := frame_linear R i
    simp only [GroundChart.centeredAt,probe,(G i).E0,sub_zero,← hL,map_zero,mean i 0 (Or.inl rfl)]
    change sandwich (ket (flip r)) (Matrix.diagonal (fun x => flipGap x-2) + 0) (ket (flip s)) + _ = 0
    by_cases same : flip r = flip s <;> simp [sandwich,ket,apply_ite,ite_mul,
      Matrix.diagonal_apply,same,flip,flipGap_bits] at *
  have st (i : Axis) {r s : S} (ne : r≠s) (a b : Axis) (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
      (G i).staticAt 0 r s a b = 0 := by
    have diff : vacuum S ≠ bitConfig {r,s} := by
      intro same
      have h := bitConfig_injective (show bitConfig ∅ = bitConfig {r,s} from same)
      simpa using congrArg (fun A : Finset S => r ∈ A) h
    simp [GroundChart.staticAt,(G i).vac,mean i a ha,mean i b hb,sandwich,ket,apply_ite,ite_mul,
      transverse_pair_column ne a b ha hb,diff]
  apply Prod.ext
  · funext i; simp [unitReadout,localReadout,cen,avg]
  · funext d i k
    have ne (r : S) : r≠r+d.val := Ne.symm (by simpa using R.nonzero _ d.property)
    fin_cases k <;> simp [unitReadout,localReadout,cen,st i (ne _) 0 0 (Or.inl rfl) (Or.inl rfl),
      st i (ne _) 1 1 (Or.inr rfl) (Or.inr rfl),st i (ne _) 0 1 (Or.inl rfl) (Or.inr rfl),
      st i (ne _) 1 0 (Or.inr rfl) (Or.inl rfl),avg,cosAmp,sinAmp]

theorem unitReadout_smooth (G : ∀ i, GroundChart R i) : ContDiffAt ℝ 2 (unitReadout G) 0 := by
  have ket' (i : Axis) (k : Config S) : ContDiffAt ℝ 2 (fun p => (G i).ψ p k) 0 :=
    (ContinuousLinearMap.proj k : (Config S → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt.comp 0 (G i).smoothψ
  have energy (i : Axis) := (G i).smoothE
  have frame (i : Axis) (x y : Config S) :
      ContDiffAt ℝ 2 (fun p => fieldFrame (withParams R p) i x y) 0 := by
    obtain ⟨L,hL⟩ := frame_linear R i
    simp_rw [← hL]
    fun_prop
  have mean (i a : Axis) : ContDiffAt ℝ 2 (fun p => (G i).meanAt p a) 0 := by
    unfold GroundChart.meanAt avg sandwich; fun_prop
  have applied (i : Axis) (r : S) (a : Axis) (x : Config S) : ContDiffAt ℝ 2 (fun p => (G i).applied p r a x) 0 := by
    unfold GroundChart.applied; fun_prop
  have diag (i : Axis) (x y : Config S) :
      ContDiffAt ℝ 2 (fun p => if x=y then flipGap x - (G i).E p - 2 else 0) 0 := by
    by_cases same : x=y <;> simp only [same,if_true,if_false] <;> fun_prop
  have cen (i : Axis) (r s : S) : ContDiffAt ℝ 2 (fun p => (G i).centeredAt p r s) 0 := by
    unfold GroundChart.centeredAt sandwich
    simp only [Matrix.add_apply,Matrix.diagonal_apply]
    fun_prop (disch := first | assumption | positivity)
  have st (i : Axis) (r s : S) (a b : Axis) : ContDiffAt ℝ 2 (fun p => (G i).staticAt p r s a b) 0 := by
    unfold GroundChart.staticAt sandwich; fun_prop
  unfold unitReadout localReadout
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr; intro i; unfold avg; fun_prop
  · apply contDiffAt_pi.mpr; intro d
    apply contDiffAt_pi.mpr; intro i
    apply contDiffAt_pi.mpr; intro k
    fin_cases k
    · change ContDiffAt ℝ 2 (fun p => (avg (fun r => (G i).centeredAt p r (r+d.val)) + avg (fun r => (G i).centeredAt p (r+d.val) r)).re) 0
      unfold avg; fun_prop
    · change ContDiffAt ℝ 2 (fun p => (avg (fun r => (G i).centeredAt p (r+d.val) r) - avg (fun r => (G i).centeredAt p r (r+d.val))).im) 0
      unfold avg; fun_prop
    · change ContDiffAt ℝ 2 (fun p => (avg (fun r => (G i).staticAt p r (r+d.val) 0 0) - avg (fun r => (G i).staticAt p r (r+d.val) 1 1)).re) 0
      unfold avg; fun_prop
    · change ContDiffAt ℝ 2 (fun p => (avg (fun r => (G i).staticAt p r (r+d.val) 0 1) + avg (fun r => (G i).staticAt p r (r+d.val) 1 0)).re) 0
      unfold avg; fun_prop

theorem unitReadout_slope (G : ∀ i, GroundChart R i) : fderiv ℝ (unitReadout G) 0 = leadingCLM := by
  apply ContinuousLinearMap.ext; intro p
  let g := fun i => (G i).ray p
  have equal : (fun t : ℝ => unitReadout G (t • p)) = rayReadout (withParams R p) g := by
    funext t
    have scale (i : Axis) : fieldFrame (withParams R (t • p)) i = (t:ℂ) • fieldFrame (withParams R p) i := by
      obtain ⟨L,hL⟩ := frame_linear R i
      rw [← hL,← hL,map_smul]
      funext x y; simp [Complex.real_smul]
    unfold unitReadout rayReadout
    congr 1
    funext i r s
    simp only [GroundChart.centeredAt,EigenRay.connectedCentered,EigenRay.centeredPair,scale]
    rfl
  have der := (paper_directional_slope (withParams R p) g).congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun equal))
  have inner : HasDerivAt (fun t : ℝ => t • p) p 0 := by simpa using (hasDerivAt_id (0:ℝ)).smul_const p
  have h := (unitReadout_smooth G).differentiableAt (by norm_num) |>.hasFDerivAt
  have h' : HasFDerivAt (unitReadout G) (fderiv ℝ (unitReadout G) 0) ((0:ℝ) • p) := by simpa using h
  have composite : HasDerivAt (fun t : ℝ => unitReadout G (t • p)) (fderiv ℝ (unitReadout G) 0 p) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := unitReadout G) (l' := fderiv ℝ (unitReadout G) 0) (f := fun t : ℝ => t • p) 0 h' inner
  simpa only [parameters_withParams] using composite.unique der

/-- For one finite lattice, a single pair of constants controls both the
absolute bias and the derivative throughout the physical coupling cube. -/
theorem paper_finite (G : ∀ i, GroundChart R i) :
    ∃ C ≥ (0:ℝ), ∃ B₀ > (0:ℝ), ∀ B ≥ B₀,
      Set.InjOn (atField (unitReadout G) B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        DifferentiableAt ℝ (atField (unitReadout G) B) p ∧
        ‖fderiv ℝ (fun q => atField (unitReadout G) B q - leading q) p‖ ≤ C/B ∧
        ‖atField (unitReadout G) B p - leading p‖ ≤ (C/B)*‖p‖ := by
  have sm := unitReadout_smooth G
  have jet := unitReadout_slope G
  obtain ⟨C,hC,a,ha,est⟩ := scaled_bounds _ sm (unitReadout_zero G) jet
  obtain ⟨b,hb,inj⟩ := rescaled_injective _ sm jet
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  exact ⟨inj B ((le_max_right ..).trans large),est B ((le_max_left ..).trans large)⟩

end DSFTomography.SF
