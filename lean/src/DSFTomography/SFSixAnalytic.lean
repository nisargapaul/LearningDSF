import DSFTomography.SFDiagonalSix

/-! The six-setting readout reuses the certified ground-state expansion.
Its linear processing reproduces the full-access leading map while using
only diagonal channels of each experiment. -/
noncomputable section
set_option maxHeartbeats 800000
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Filter
open scoped Topology
variable {D : Type*} [Fintype D]

abbrev Bundle (D : Type*) := Harmonics D × (Pair → Harmonics D)

def combine : Bundle D →L[ℝ] Harmonics D := LinearMap.toContinuousLinearMap {
  toFun v := assemble v.1 (fun t d => (v.2 t).2 d 2 0)
  map_add' := by
    intro v w; apply Prod.ext
    · rfl
    · funext d i k; by_cases h : k=3 <;> simp [assemble,diagonal,h] <;> ring
  map_smul' := by
    intro c v; apply Prod.ext
    · rfl
    · funext d i k; by_cases h : k=3 <;> simp [assemble,diagonal,h] <;> ring }

def sixFunction (Φ : Params D → Harmonics D) (p : Params D) : Harmonics D :=
  combine (Φ p, fun t => Φ (rotate t p))

def bundleLinear (L : Params D →L[ℝ] Harmonics D) : Params D →L[ℝ] Bundle D :=
  L.prod (ContinuousLinearMap.pi fun t => L.comp (rotate t))

theorem combine_linear : combine.comp (bundleLinear (leadingCLM (D := D))) = leadingCLM := by
  apply ContinuousLinearMap.ext
  intro p
  exact assemble_leading p

theorem six_zero {Φ : Params D → Harmonics D} (zero : Φ 0=0) : sixFunction Φ 0=0 := by
  unfold sixFunction
  simp only [map_zero,zero]
  exact (combine (D := D)).map_zero

theorem six_smooth {Φ : Params D → Harmonics D} (smooth : ContDiffAt ℝ 2 Φ 0) :
    ContDiffAt ℝ 2 (sixFunction Φ) 0 := by
  change ContDiffAt ℝ 2 ((combine (D := D)) ∘ (fun p => (Φ p, fun t => Φ (rotate t p)))) 0
  apply (combine (D := D)).contDiff.contDiffAt.comp
  apply smooth.prodMk
  apply contDiffAt_pi.mpr
  intro t
  exact (by simpa using smooth : ContDiffAt ℝ 2 Φ (rotate t 0)).comp 0 (rotate (D := D) t).contDiff.contDiffAt

theorem six_slope {Φ : Params D → Harmonics D} (smooth : ContDiffAt ℝ 2 Φ 0)
    (slope : fderiv ℝ Φ 0=leadingCLM) : fderiv ℝ (sixFunction Φ) 0=leadingCLM := by
  have der : HasFDerivAt Φ leadingCLM 0 := slope ▸ (smooth.differentiableAt (by norm_num)).hasFDerivAt
  have tilted (t : Pair) : HasFDerivAt (fun p => Φ (rotate t p)) (leadingCLM.comp (rotate t)) 0 :=
    (by simpa using der : HasFDerivAt Φ leadingCLM (rotate t 0)).comp 0 (rotate (D := D) t).hasFDerivAt
  have total := combine.hasFDerivAt.comp 0 (der.prodMk (hasFDerivAt_pi.mpr tilted))
  exact total.fderiv.trans combine_linear

/-- The diagonal-only assembled readout has the same exact leading inverse,
finite-field injectivity, and O(1/B) remainder as the full-access protocol. -/
theorem six_rescaled {Φ : Params D → Harmonics D}
    (smooth : ContDiffAt ℝ 2 Φ 0) (zero : Φ 0=0) (slope : fderiv ℝ Φ 0=leadingCLM) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (atField (sixFunction Φ) B) (couplingCube D) ∧
      ∀ p ∈ couplingCube D,
        DifferentiableAt ℝ (atField (sixFunction Φ) B) p ∧
        ‖fderiv ℝ (fun q => atField (sixFunction Φ) B q-leading q) p‖ ≤ C/B ∧
        ‖atField (sixFunction Φ) B p-leading p‖ ≤ (C/B)*‖p‖ := by
  obtain ⟨C,hC,a,ha,est⟩ := scaled_bounds _ (six_smooth smooth) (six_zero zero) (six_slope smooth slope)
  obtain ⟨b,hb,inj⟩ := rescaled_injective _ (six_smooth smooth) (six_slope smooth slope)
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  exact ⟨inj B ((le_max_right ..).trans large),est B ((le_max_left ..).trans large)⟩

theorem six_field (Φ : Params D → Harmonics D) (B : ℝ) (p : Params D) :
    atField (sixFunction Φ) B p = combine (atField Φ B p,fun t => atField Φ B (rotate t p)) := by
  change B • combine (Φ (B⁻¹ • p),fun t => Φ (rotate t (B⁻¹ • p))) = _
  rw [← map_smul]
  apply congrArg combine
  refine Prod.ext rfl ?_
  funext t
  simp only [Prod.smul_snd,Pi.smul_apply,atField,map_smul]

/-- Scaling a bounded coupling cube enters any fixed neighborhood of zero,
including a neighborhood on which every rotated experiment is physical. -/
theorem scaled_neighborhood {U : Set (Params D)} (near : U ∈ 𝓝 0) :
    ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube D,
      ∀ᶠ q in 𝓝 p, B⁻¹ • q ∈ U := by
  obtain ⟨r,hr,inside⟩ := Metric.mem_nhds_iff.mp (eventually_eventually_nhds.mpr near)
  refine ⟨2/r,by positivity,?_⟩
  intro B large p hp
  have pos : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2/r) large
  have cube : ‖p‖ ≤ 1 := by simpa [couplingCube] using hp
  have small : B⁻¹ < r := by
    rw [inv_eq_one_div,div_lt_iff₀ pos]
    linarith [(div_le_iff₀ hr).mp large,mul_comm B r]
  have belongs : B⁻¹ • p ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos)]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr pos.le) cube).trans_lt small
  exact (continuous_const.smul continuous_id).continuousAt.tendsto.eventually (inside belongs)

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

theorem six_chart (R : Bonds S) (G : ∀ i, GroundChart R i) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (atField (sixFunction (unitReadout G)) B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        DifferentiableAt ℝ (atField (sixFunction (unitReadout G)) B) p ∧
        ‖fderiv ℝ (fun q => atField (sixFunction (unitReadout G)) B q-leading q) p‖ ≤ C/B ∧
        ‖atField (sixFunction (unitReadout G)) B p-leading p‖ ≤ (C/B)*‖p‖ :=
  six_rescaled (unitReadout_smooth G) (unitReadout_zero G) (unitReadout_slope G)

end DSFTomography.SF.DiagonalSix
