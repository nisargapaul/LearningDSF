import DSFTomography.DSFLimitDistribution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Moments are defined by smooth spectral cutoffs of the constructed DSF.
Uniform absolute-moment bounds justify removing the cutoffs. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography Filter MeasureTheory
open scoped Topology

def cutoffBump (N : ℕ) : ContDiffBump (0:ℝ) where
  rIn := N+1
  rOut := 2*(N+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith

def momentTest (k N : ℕ) : SchwartzMap ℝ ℂ :=
  ((cutoffBump N).hasCompactSupport.smul_right (f' := fun ω : ℝ => (ω:ℂ)^k)).toSchwartzMap
    ((cutoffBump N).contDiff.smul ((Complex.ofRealCLM.contDiff).pow k))

theorem momentTest_apply (k N : ℕ) (ω : ℝ) :
    momentTest k N ω = (cutoffBump N ω:ℂ)*(ω:ℂ)^k := rfl

theorem cutoff_error (k N : ℕ) (ω : ℝ) :
    ‖(ω:ℂ)^k-momentTest k N ω‖ ≤ |ω|^(k+1)/(N+1) := by
  have pos : (0:ℝ) < N+1 := by positivity
  rw [momentTest_apply,← one_sub_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  by_cases small : |ω| ≤ N+1
  · have one := (cutoffBump N).one_of_mem_closedBall (by simpa [cutoffBump,Real.dist_eq] using small)
    rw [one]; simp; positivity
  · have big : (N:ℝ)+1 ≤ |ω| := (not_le.mp small).le
    have nz := (cutoffBump N).nonneg (x := ω)
    have le := (cutoffBump N).le_one (x := ω)
    have abs : ‖1-(cutoffBump N ω:ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      linarith
    apply (mul_le_mul_of_nonneg_right abs (pow_nonneg (abs_nonneg _) _)).trans
    rw [one_mul,le_div_iff₀ pos,pow_succ]
    exact mul_le_mul_of_nonneg_left big (pow_nonneg (abs_nonneg _) _)

variable {I : Type*} [Fintype I]
theorem Lines.moment_cutoff_bound (L : Lines I) (k N : ℕ) :
    ‖L.moment k-L.distribution (momentTest k N)‖ ≤
      (2*Real.pi)*L.absMoment (k+1)/(N+1) := by
  have eq : L.moment k-L.distribution (momentTest k N) =
      (2*Real.pi:ℂ)*∑ i, L.weight i*((L.frequency i:ℂ)^k-momentTest k N (L.frequency i)) := by
    simp [Lines.moment,Lines.distribution,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub,mul_assoc]
  rw [eq,norm_mul,show ‖(2*Real.pi:ℂ)‖=2*Real.pi by norm_cast; rw [Real.norm_eq_abs,abs_of_pos (by positivity)]]
  calc
    _ ≤ (2*Real.pi)*(∑ i, ‖L.weight i*((L.frequency i:ℂ)^k-momentTest k N (L.frequency i))‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2*Real.pi)*(∑ i, ‖L.weight i‖*(|L.frequency i|^(k+1)/(N+1))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (cutoff_error k N _) (norm_nonneg _)) (by positivity)
    _ = _ := by simp [Lines.absMoment,Finset.sum_div,mul_div_assoc]

/-- A spectral moment of an infinite distribution, read without access to any
finite-volume moments. The smooth cutoffs tend to the polynomial ω^k. -/
def HasSpectralMoment (D : SchwartzMap ℝ ℂ →L[ℂ] ℂ) (k : ℕ) (m : ℂ) : Prop :=
  Tendsto (fun N => D (momentTest k N)) atTop (𝓝 m)

variable {T : ℕ → Type*} [∀ n, Fintype (T n)]
/-- The independently constructed limiting spectrum has the certified
thermodynamic moment. The bound one order higher prevents escaping tails. -/
theorem limit_spectral_moment (L : ∀ n, Lines (T n)) (D : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (spectra : ∀ f, Tendsto (fun n => (L n).distribution f) atTop (𝓝 (D f)))
    (k : ℕ) (m : ℂ) (moments : Tendsto (fun n => (L n).moment k) atTop (𝓝 m))
    (M : ℝ) (bound : ∀ n, (L n).absMoment (k+1) ≤ M) : HasSpectralMoment D k m := by
  have estimate (N : ℕ) : ‖m-D (momentTest k N)‖ ≤ (2*Real.pi)*M/(N+1) := by
    apply le_of_tendsto ((moments.sub (spectra _)).norm)
    exact Eventually.of_forall fun n => ((L n).moment_cutoff_bound k N).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (bound n) (by positivity)) (by positivity))
  have vanish : Tendsto (fun N : ℕ => (2*Real.pi)*M/((N:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  rw [HasSpectralMoment,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) vanish
  simpa only [norm_sub_rev] using estimate N

end DSFTomography.Spectral
