import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Topology

/-! From a single regular point of a real analytic square map to local inverses
almost everywhere. Restriction to a line reduces the null-set step to isolated
zeros in one variable. Fubini and invariance of null sets under affine
dilations transfer the conclusion to the full parameter space. -/
noncomputable section
namespace DSFTomography.HT.Diagonal
open MeasureTheory Filter Set
open scoped Topology ContDiff
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev V (I : Type*) := I → ℝ

omit [DecidableEq I] in
theorem ae_ne_of_regular_value {g : V I → ℝ} (smooth : ContDiff ℝ ω g) {w : V I} (hw : g w ≠ 0) :
    ∀ᵐ x ∂volume, g x ≠ 0 := by
  have lines (x : V I) : ∀ᵐ t : ℝ, g (w + t • x) ≠ 0 := by
    have h : ContDiff ℝ ω (fun t : ℝ => g (w + t • x)) := smooth.comp (by fun_prop)
    have dich := (h.analyticOnNhd (s := univ)).eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
    rcases dich with zero | nonzero
    · exact False.elim (hw (by simpa using zero (mem_univ (0:ℝ))))
    · simpa using (ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ nonzero)
  have both : ∀ᵐ t : ℝ, ∀ᵐ x : V I, g (w + t • x) ≠ 0 := by
    apply (Measure.ae_ae_comm (p := fun (x : V I) (t : ℝ) => g (w + t • x) ≠ 0) ?_).mp
      (Eventually.of_forall lines)
    exact (isOpen_ne_fun (smooth.continuous.comp (by fun_prop)) continuous_const).measurableSet
  have nonzero : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
  obtain ⟨t, ht, h⟩ := (nonzero.and both).exists
  have q := (Measure.quasiMeasurePreserving_smul (volume : Measure (V I)) (inv_ne_zero ht)).comp
    (quasiMeasurePreserving_add_left (volume : Measure (V I)) (-w))
  filter_upwards [q.ae h] with x hx
  simpa [Function.comp_def,smul_smul,ht] using hx

def LocallySolvable (F : V I → V I) (x : V I) : Prop :=
  ∃ G : V I → V I, ContinuousAt G (F x) ∧
    (∀ᶠ y in 𝓝 x, G (F y) = y) ∧ (∀ᶠ c in 𝓝 (F x), F (G c) = c)

omit [DecidableEq I] in
theorem det_iff (L : V I →L[ℝ] V I) :
    LinearMap.det L.toLinearMap ≠ 0 ↔ Function.Injective L := by
  rw [ne_eq,LinearMap.det_eq_zero_iff_ker_ne_bot,not_ne_iff,LinearMap.ker_eq_bot]
  rfl

omit [DecidableEq I] in
theorem local_of_regular {F : V I → V I} (smooth : ContDiff ℝ ω F)
    {x : V I} (inj : Function.Injective (fderiv ℝ F x)) : LocallySolvable F x := by
  let e := (LinearEquiv.ofBijective (fderiv ℝ F x).toLinearMap
    ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
  have deriv : HasStrictFDerivAt F (e : V I →L[ℝ] V I) x :=
    smooth.contDiffAt.hasStrictFDerivAt (by simp)
  exact ⟨deriv.localInverse _ _ _,deriv.localInverse_continuousAt,
    deriv.eventually_left_inverse,deriv.eventually_right_inverse⟩

theorem generic_of_witness {F : V I → V I} (smooth : ContDiff ℝ ω F)
    {w : V I} (hw : Function.Injective (fderiv ℝ F w)) :
    ∀ᵐ x ∂volume, LocallySolvable F x := by
  let jac := fun x => LinearMap.det (fderiv ℝ F x).toLinearMap
  have jacSmooth : ContDiff ℝ ω jac := by
    have hd : ContDiff ℝ ω (fderiv ℝ F) := smooth.fderiv_right (by simp)
    simp only [jac,← LinearMap.det_toMatrix',Matrix.det_apply',LinearMap.toMatrix'_apply,ContinuousLinearMap.coe_coe]
    fun_prop
  filter_upwards [ae_ne_of_regular_value jacSmooth ((det_iff _).2 hw)] with x hx
  exact local_of_regular smooth ((det_iff _).1 hx)
end DSFTomography.HT.Diagonal
