import DSFTomography.DSFInfiniteBounds
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Compactness of physical real-time correlations on every bounded time
interval, simultaneously for countably many local channels. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography Filter Set
open scoped Topology

def controlled (M : ℝ) (K : NNReal) : Set C(ℝ,ℂ) :=
  {f | (∀ t, ‖f t‖ ≤ M) ∧ LipschitzWith K f}

theorem controlled_compact (M : ℝ) (K : NNReal) : IsCompact (controlled M K) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have eq : ContinuousMap.toFun '' controlled M K =
        (Set.univ.pi fun _ : ℝ => Metric.closedBall (0:ℂ) M) ∩ {f | LipschitzWith K f} := by
      ext f
      constructor
      · rintro ⟨g,hg,rfl⟩
        exact ⟨fun t _ => by simpa using hg.1 t,hg.2⟩
      · rintro ⟨hb,hl⟩
        refine ⟨⟨f,hl.continuous⟩,⟨?_,hl⟩,rfl⟩
        intro t; simpa using hb t (mem_univ t)
    rw [eq]
    exact (isCompact_univ_pi fun _ => isCompact_closedBall 0 M).inter_right
      (isClosed_setOf_lipschitzWith K)
  · apply Metric.equicontinuous_of_continuity_modulus (fun δ : ℝ => (K:ℝ)*δ)
    · simpa using ((show Continuous (fun δ : ℝ => (K:ℝ)*δ) from continuous_const.mul continuous_id).continuousAt (x := 0)).tendsto
    · intro x y f; exact f.property.2.dist_le_mul x y

variable {I : Type*} [Fintype I]
theorem exp_frequency_norm (ω t : ℝ) : ‖Complex.exp (-Complex.I*(ω:ℂ)*t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

theorem Lines.correlation_bound (L : Lines I) (t : ℝ) : ‖L.correlation t‖ ≤ L.absMoment 0 := by
  calc
    _ ≤ ∑ i, ‖L.weight i*Complex.exp (-Complex.I*(L.frequency i:ℂ)*t)‖ := norm_sum_le _ _
    _ = _ := by simp only [Lines.absMoment,norm_mul,exp_frequency_norm,pow_zero,mul_one]

def Lines.velocity (L : Lines I) (t : ℝ) : ℂ :=
  ∑ i, L.weight i*(-Complex.I*(L.frequency i:ℂ))*Complex.exp (-Complex.I*(L.frequency i:ℂ)*t)

theorem Lines.correlation_deriv (L : Lines I) (t : ℝ) : HasDerivAt L.correlation (L.velocity t) t := by
  unfold Lines.correlation Lines.velocity
  apply HasDerivAt.fun_sum
  intro i _
  convert (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-Complex.I*(L.frequency i:ℂ))).cexp.const_mul (L.weight i)) using 1 <;>
    simp <;> ring

theorem Lines.velocity_bound (L : Lines I) (t : ℝ) : ‖L.velocity t‖ ≤ L.absMoment 1 := by
  calc
    _ ≤ ∑ i, ‖L.weight i*(-Complex.I*(L.frequency i:ℂ))*Complex.exp (-Complex.I*(L.frequency i:ℂ)*t)‖ := norm_sum_le _ _
    _ = _ := by simp only [Lines.absMoment,norm_mul,exp_frequency_norm,Complex.norm_real,Real.norm_eq_abs,norm_neg,Complex.norm_I,one_mul,mul_one,pow_one]

def Lines.timeMap (L : Lines I) : C(ℝ,ℂ) := ⟨L.correlation,continuous_iff_continuousAt.mpr fun t => (L.correlation_deriv t).continuousAt⟩

theorem Lines.timeMap_controlled (L : Lines I) (M : ℝ) (K : NNReal)
    (mass : L.absMoment 0 ≤ M) (first : L.absMoment 1 ≤ K) : L.timeMap ∈ controlled M K := by
  refine ⟨fun t => (L.correlation_bound t).trans mass,?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change ‖L.correlation x-L.correlation y‖ ≤ _
  exact convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (L.correlation_deriv t).hasDerivWithinAt)
    (fun t _ => (L.velocity_bound t).trans first) (mem_univ y) (mem_univ x)

/-- Simultaneous convergence of all local channels on compact time intervals. -/
theorem time_subsequence {D : Type*} [Countable D] (f : ℕ → D → C(ℝ,ℂ))
    (M : ℝ) (K : NNReal) (bound : ∀ n d, f n d ∈ controlled M K) :
    ∃ C : D → C(ℝ,ℂ), ∃ seq : ℕ → ℕ, StrictMono seq ∧
      (∀ d, C d ∈ controlled M K) ∧ Tendsto (fun n => f (seq n)) atTop (𝓝 C) := by
  have compact : IsCompact (Set.univ.pi fun _ : D => controlled M K) :=
    isCompact_univ_pi fun _ => controlled_compact M K
  obtain ⟨C,mem,seq,inc,lim⟩ := compact.tendsto_subseq (fun n d _ => bound n d)
  exact ⟨C,seq,inc,fun d => mem d (mem_univ d),lim⟩

end DSFTomography.Spectral
