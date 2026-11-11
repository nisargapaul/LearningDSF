import DSFTomography.DSFTimeCompact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The infinite-volume frequency distribution is constructed from the limiting
real-time correlation, independently of its moments. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography Filter MeasureTheory
open scoped Topology

theorem angularTest_integrable (f : SchwartzMap ℝ ℂ) : Integrable (angularTest f) := by
  simpa using angular_integrable f 0

def timeTransform (C : C(ℝ,ℂ)) (f : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ t, C t*angularTest f t

variable {I : ℕ → Type*} [∀ n, Fintype (I n)]

theorem distribution_tendsto (L : ∀ n, Lines (I n)) (C : C(ℝ,ℂ)) (M : ℝ)
    (mass : ∀ n, (L n).absMoment 0 ≤ M)
    (limit : ∀ t, Tendsto (fun n => (L n).correlation t) atTop (𝓝 (C t)))
    (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (L n).distribution f) atTop (𝓝 (timeTransform C f)) := by
  simp_rw [← time_fourier_eq_lines]
  apply tendsto_integral_of_dominated_convergence (fun t => M*‖angularTest f t‖)
  · intro n
    exact ((L n).timeMap.continuous.aestronglyMeasurable.mul (angularTest_integrable f).aestronglyMeasurable)
  · exact (angularTest_integrable f).norm.const_mul M
  · intro n; exact ae_of_all _ fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (((L n).correlation_bound t).trans (mass n)) (norm_nonneg _)
  · exact ae_of_all _ fun t => (limit t).mul_const _

theorem Lines.distribution_bound {T : Type*} [Fintype T] (L : Lines T) (f : SchwartzMap ℝ ℂ) :
    ‖L.distribution f‖ ≤ (2*Real.pi)*L.absMoment 0*SchwartzMap.seminorm ℂ 0 0 f := by
  simp only [Lines.distribution,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    SchwartzMap.delta_apply,smul_eq_mul]
  calc
    _ ≤ ∑ i, ‖(2*Real.pi:ℂ)*L.weight i*f (L.frequency i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (2*Real.pi)*‖L.weight i‖*SchwartzMap.seminorm ℂ 0 0 f := Finset.sum_le_sum fun i _ => by
      rw [norm_mul,norm_mul,show ‖(2*Real.pi:ℂ)‖=2*Real.pi by norm_cast; rw [Real.norm_eq_abs,abs_of_pos (by positivity)]]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ f _) (by positivity)
    _ = _ := by simp [Lines.absMoment,Finset.sum_mul,Finset.mul_sum,mul_assoc]

theorem timeTransform_bound (L : ∀ n, Lines (I n)) (C : C(ℝ,ℂ)) (M : ℝ)
    (mass : ∀ n, (L n).absMoment 0 ≤ M)
    (limit : ∀ t, Tendsto (fun n => (L n).correlation t) atTop (𝓝 (C t)))
    (f : SchwartzMap ℝ ℂ) :
    ‖timeTransform C f‖ ≤ (2*Real.pi)*M*SchwartzMap.seminorm ℂ 0 0 f := by
  apply le_of_tendsto ((distribution_tendsto L C M mass limit f).norm)
  exact Eventually.of_forall fun n => ((L n).distribution_bound f).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mass n) (by positivity)) (apply_nonneg _ _))

/-- The limiting time-Fourier DSF is a continuous linear functional on
Schwartz test functions. Its definition uses only the real-time correlation. -/
def limitDistribution (L : ∀ n, Lines (I n)) (C : C(ℝ,ℂ)) (M : ℝ) (positive : 0 ≤ M)
    (mass : ∀ n, (L n).absMoment 0 ≤ M)
    (limit : ∀ t, Tendsto (fun n => (L n).correlation t) atTop (𝓝 (C t))) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (timeTransform C)
    (by
      intro f g
      have eq (h : SchwartzMap ℝ ℂ) := distribution_tendsto L C M mass limit h
      have point : ∀ n, (L n).distribution (f+g) = (L n).distribution f+(L n).distribution g := fun n => map_add _ _ _
      exact tendsto_nhds_unique (eq (f+g)) (by simpa only [point] using (eq f).add (eq g)))
    (by
      intro c f
      have eq (h : SchwartzMap ℝ ℂ) := distribution_tendsto L C M mass limit h
      have point : ∀ n, (L n).distribution (c • f) = c • (L n).distribution f := fun n => map_smul _ _ _
      exact tendsto_nhds_unique (eq (c • f)) (by simpa only [point] using (eq f).const_smul c))
    (by
      refine ⟨{(0,0)},(2*Real.pi)*M,by positivity,?_⟩
      intro f
      simpa using timeTransform_bound L C M mass limit f)

theorem limitDistribution_eq_time (L : ∀ n, Lines (I n)) (C : C(ℝ,ℂ)) (M : ℝ) (positive : 0 ≤ M)
    (mass : ∀ n, (L n).absMoment 0 ≤ M)
    (limit : ∀ t, Tendsto (fun n => (L n).correlation t) atTop (𝓝 (C t))) (f : SchwartzMap ℝ ℂ) :
    limitDistribution L C M positive mass limit f = ∫ t, C t*angularTest f t := rfl

end DSFTomography.Spectral
