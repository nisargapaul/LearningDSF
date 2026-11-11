import DSFTomography.SFHarmonics
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! For a Hamiltonian linear in its couplings write x = λ/B. The physical
readout is B Φ(x), where Φ is the unit-field readout. Two derivatives of Φ
near the polarized point suffice, on the *whole* closed coupling cube. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography Filter
open scoped Topology
variable {D : Type*} [Fintype D]

def leadingCLM : Params D →L[ℝ] Harmonics D := LinearMap.toContinuousLinearMap {
  toFun := leading
  map_add' := by
    intro p q
    apply Prod.ext
    · funext i; simp [leading, Finset.sum_add_distrib]; ring
    · funext d i k; fin_cases k <;> simp [leading] <;> ring
  map_smul' := by
    intro t p
    apply Prod.ext
    · funext i; simp [leading, ← Finset.mul_sum]; ring
    · funext d i k; fin_cases k <;> simp [leading] <;> ring }

/-- In the sup norm on the fields and all exchange entries, the unit ball
is exactly the physical coupling cube. -/
def couplingCube (D : Type*) [Fintype D] : Set (Params D) := Metric.closedBall 0 1

def atField (Φ : Params D → Harmonics D) (B : ℝ) (p : Params D) : Harmonics D :=
  B • Φ (B⁻¹ • p)

/-- The chain rule cancels the two field factors in the Jacobian. -/
theorem derivative_atField (Φ : Params D → Harmonics D) {B : ℝ} (hB : 0 < B)
    {p : Params D} (h : DifferentiableAt ℝ Φ (B⁻¹ • p)) :
    HasFDerivAt (atField Φ B) (fderiv ℝ Φ (B⁻¹ • p)) p := by
  let scale := B⁻¹ • ContinuousLinearMap.id ℝ (Params D)
  have inn := scale.hasFDerivAt (x := p)
  have chain := ((h.hasFDerivAt.comp p inn).const_smul B)
  have cancel : B • (fderiv ℝ Φ (B⁻¹ • p)).comp scale = fderiv ℝ Φ (B⁻¹ • p) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [scale,smul_smul,hB.ne']
  rw [cancel] at chain
  exact chain

/-- Uniform finite-field derivative estimate from local C² regularity.
No estimate on the remainder or its derivatives is an input. -/
theorem rescaled_remainder (Φ : Params D → Harmonics D) (smooth : ContDiffAt ℝ 2 Φ 0) :
    ∃ C ≥ (0:ℝ), ∃ B₀ > (0:ℝ), ∀ B ≥ B₀, ∀ p ∈ couplingCube D,
      HasFDerivAt (fun q => atField Φ B q - (fderiv ℝ Φ 0) q)
        (fderiv ℝ Φ (B⁻¹ • p) - fderiv ℝ Φ 0) p ∧
      ‖fderiv ℝ Φ (B⁻¹ • p) - fderiv ℝ Φ 0‖ ≤ C / B := by
  have ds : ContDiffAt ℝ 1 (fderiv ℝ Φ) 0 := smooth.fderiv_right (by norm_num)
  obtain ⟨K,U,hU,lip⟩ := ds.exists_lipschitzOnWith
  have near := smooth.eventually (by simp)
  obtain ⟨r,hr,inside⟩ := Metric.mem_nhds_iff.mp (inter_mem hU near)
  refine ⟨K,K.coe_nonneg,2/r,by positivity,?_⟩
  intro B large p hp
  have hB : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2/r) large
  have hp' : ‖p‖ ≤ 1 := by simpa [couplingCube] using hp
  have scale : ‖B⁻¹ • p‖ ≤ B⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    simpa using mul_le_mul_of_nonneg_left hp' (inv_nonneg.mpr hB.le)
  have small : B⁻¹ < r := by
    rw [inv_eq_one_div,div_lt_iff₀ hB]
    have := (div_le_iff₀ hr).mp large
    linarith [mul_comm B r]
  have atp := inside (Metric.mem_ball.mpr (by simpa using scale.trans_lt small))
  have at0 := inside (Metric.mem_ball_self hr)
  have regular : ContDiffAt ℝ 2 Φ (B⁻¹ • p) := atp.2
  refine ⟨(derivative_atField Φ hB (regular.differentiableAt (by norm_num))).sub
    (fderiv ℝ Φ 0).hasFDerivAt,?_⟩
  have bound := lip.dist_le_mul _ atp.1 _ at0.1
  rw [dist_eq_norm,dist_zero_right] at bound
  exact bound.trans (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left scale K.coe_nonneg)

/-- A useful form of the estimate when the raw polarized readout is zero.
It controls the bias of the leading readout as well as its derivative. -/
theorem scaled_bounds (Φ : Params D → Harmonics D) (smooth : ContDiffAt ℝ 2 Φ 0)
    (vac : Φ 0 = 0) (jet : fderiv ℝ Φ 0 = leadingCLM) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube D,
      DifferentiableAt ℝ (atField Φ B) p ∧
      ‖fderiv ℝ (fun q => atField Φ B q - leading q) p‖ ≤ C/B ∧
      ‖atField Φ B p - leading p‖ ≤ (C/B)*‖p‖ := by
  obtain ⟨C,hC,b,hb,est⟩ := rescaled_remainder Φ smooth
  refine ⟨C,hC,b,hb,?_⟩
  intro B large p hp
  let d := fun q : Params D => fderiv ℝ Φ (B⁻¹ • q) - leadingCLM
  have point (q : Params D) (hq : q ∈ couplingCube D) :
      HasFDerivAt (fun y => atField Φ B y - leading y) (d q) q ∧ ‖d q‖ ≤ C/B := by
    simpa only [d,jet] using est B large q hq
  have regular := (point p hp).1.differentiableAt.add (leadingCLM.differentiableAt (x := p))
  have reg : DifferentiableAt ℝ (atField Φ B) p := by
    convert regular using 1; funext q
    change atField Φ B q = (atField Φ B q-leading q)+leading q
    abel
  refine ⟨reg,(point p hp).1.fderiv.symm ▸ (point p hp).2,?_⟩
  have h0 : (0:Params D) ∈ couplingCube D := by simp [couplingCube]
  have e := (convex_closedBall (0:Params D) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun q hq => (point q hq).1.hasFDerivWithinAt) (fun q hq => (point q hq).2) h0 hp
  have base : leading (0:Params D) = 0 := leadingCLM.map_zero
  simpa only [atField,smul_zero,vac,base,sub_zero,sub_self] using e

/-- Injectivity on the entire physical cube once the polarized derivative is
identified. No numerical singular-value or threshold assumptions are needed. -/
theorem rescaled_injective (Φ : Params D → Harmonics D) (smooth : ContDiffAt ℝ 2 Φ 0)
    (jet : fderiv ℝ Φ 0 = leadingCLM) :
    ∃ B₀ > (0:ℝ), ∀ B ≥ B₀, Set.InjOn (atField Φ B) (couplingCube D) := by
  obtain ⟨C,hC,b,hb,est⟩ := rescaled_remainder Φ smooth
  refine ⟨max b (‖(decoder (D := D))‖*C + 1),hb.trans_le (le_max_left ..),?_⟩
  intro B large
  have base := (le_max_left ..).trans large
  have slack := (le_max_right ..).trans large
  apply finiteField_injective (convex_closedBall ..) (atField Φ B)
    (fun p => fderiv ℝ Φ (B⁻¹ • p) - fderiv ℝ Φ 0) (hb.trans_le base) (by linarith : ‖(decoder (D := D))‖*C < B)
  · intro p hp
    have eq : (fun q => (fderiv ℝ Φ 0) q) = leading := by rw [jet]; rfl
    simpa only [eq] using (est B base p hp).1.hasFDerivWithinAt (s := couplingCube D)
  · intro p hp; exact (est B base p hp).2

end DSFTomography.SF
