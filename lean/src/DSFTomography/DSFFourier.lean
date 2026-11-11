import DSFTomography.HTDiagonalMoments
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The angular-frequency DSF as a tempered distribution. Its time-Fourier
definition is paired with Schwartz test functions; ordinary integration of
an undamped finite-system correlation would not define the delta peaks. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography MeasureTheory Complex
open scoped FourierTransform

def angularTest (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  Real.fourierIntegralInv f (t/(2*Real.pi))

theorem angularTest_integral (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    angularTest f t = ∫ ω : ℝ, Complex.exp (Complex.I*(ω:ℂ)*t)*f ω := by
  rw [angularTest,Real.fourierIntegralInv_eq']
  apply integral_congr_ae; filter_upwards [] with ω
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero] <;> ring

private theorem inv_integrable (f : SchwartzMap ℝ ℂ) : Integrable (Real.fourierIntegralInv f) := by
  have h : Integrable (fun t : ℝ => Real.fourierIntegral f (-t)) :=
    (SchwartzMap.fourierTransformCLM ℂ f).integrable.comp_neg
  have eq : Real.fourierIntegralInv f = (fun t : ℝ => Real.fourierIntegral f (-t)) :=
    funext fun t => Real.fourierIntegralInv_eq_fourierIntegral_neg f t
  rw [eq]; exact h

private theorem integrand_scaled (f : SchwartzMap ℝ ℂ) (ω t : ℝ) :
    Complex.exp (-Complex.I*(ω:ℂ)*((2*Real.pi*t:ℝ):ℂ))*angularTest f (2*Real.pi*t) =
      Complex.exp (((-2*Real.pi*t*ω:ℝ):ℂ)*Complex.I)*Real.fourierIntegralInv f t := by
  have pi : (2*Real.pi:ℝ) ≠ 0 := by positivity
  simp only [angularTest,mul_div_cancel_left₀ t pi]
  congr 2 <;> push_cast <;> ring

theorem angular_integrable (f : SchwartzMap ℝ ℂ) (ω : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-Complex.I*(ω:ℂ)*t)*angularTest f t) := by
  have h := (Real.fourierIntegral_convergent_iff (f := Real.fourierIntegralInv f) ω).2 (inv_integrable f)
  rw [← MeasureTheory.integrable_comp_mul_left_iff _ (show (2*Real.pi:ℝ) ≠ 0 by positivity)]
  simp_rw [integrand_scaled]
  convert h using 1
  simp [Real.fourierChar_apply,RCLike.inner_apply,smul_eq_mul]
  congr 1; funext t; congr 2 <;> push_cast <;> ring

/-- The positive-sign time Fourier transform of exp(-iωt) is 2π δω. -/
theorem angular_fourier_atom (f : SchwartzMap ℝ ℂ) (ω : ℝ) :
    (∫ t : ℝ, Complex.exp (-Complex.I*(ω:ℂ)*t)*angularTest f t) =
      (2*Real.pi:ℂ)*f ω := by
  let h := fun t : ℝ => Complex.exp (-Complex.I*(ω:ℂ)*t)*angularTest f t
  have scaled : (∫ t : ℝ, h (2*Real.pi*t)) = f ω := by
    simp only [h,integrand_scaled]
    change (∫ t : ℝ, Complex.exp (((-2*Real.pi*t*ω:ℝ):ℂ)*Complex.I) • Real.fourierIntegralInv f t) = _
    rw [← Real.fourierIntegral_real_eq_integral_exp_smul]
    exact f.integrable.fourier_inversion_inv (SchwartzMap.fourierTransformCLM ℂ f).integrable f.continuous.continuousAt
  rw [MeasureTheory.Measure.integral_comp_mul_left] at scaled
  have pi : (0:ℝ) < 2*Real.pi := by positivity
  simp only [abs_of_pos (inv_pos.mpr pi),Complex.real_smul,Complex.ofReal_inv] at scaled
  have nonzero : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt pi
  change ∫ t, h t = _
  apply (inv_mul_eq_iff_eq_mul₀ nonzero).mp
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using scaled

/-- A finite atomic spectrum, including signed/complex crossed-channel weights. -/
structure Lines (I : Type*) where
  frequency : I → ℝ
  weight : I → ℂ

variable {I : Type*} [Fintype I]
def Lines.correlation (L : Lines I) (t : ℝ) : ℂ :=
  ∑ i, L.weight i*Complex.exp (-Complex.I*(L.frequency i:ℂ)*t)
def Lines.distribution (L : Lines I) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  ∑ i, ((2*Real.pi:ℂ)*L.weight i) • SchwartzMap.delta ℂ ℂ (L.frequency i)
def Lines.moment (L : Lines I) (n : ℕ) : ℂ :=
  (2*Real.pi:ℂ)*∑ i, L.weight i*(L.frequency i:ℂ)^n

/-- Integration against the finite atomic complex spectrum. Writing it as
a finite linear combination of Dirac integrals also covers crossed channels. -/
def Lines.integral (L : Lines I) (f : ℝ → ℂ) : ℂ :=
  (2*Real.pi:ℂ)*∑ i, L.weight i*(∫ ω, f ω ∂MeasureTheory.Measure.dirac (L.frequency i))

theorem distribution_eq_integral (L : Lines I) (f : SchwartzMap ℝ ℂ) :
    L.distribution f = L.integral f := by
  simp [Lines.distribution,Lines.integral,Finset.mul_sum,mul_assoc]

theorem moment_eq_integral (L : Lines I) (n : ℕ) :
    L.moment n = L.integral (fun ω => (ω:ℂ)^n) := by
  simp [Lines.moment,Lines.integral]

/-- Equality of the time-Fourier definition and the Lehmann delta spectrum,
with the manuscript's sign and raw 2π normalization. -/
theorem time_fourier_eq_lines (L : Lines I) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, L.correlation t*angularTest f t) = L.distribution f := by
  simp only [Lines.correlation,Finset.sum_mul]
  rw [integral_finset_sum]
  · simp only [Lines.distribution,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      SchwartzMap.delta_apply,smul_eq_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [show (fun t : ℝ => L.weight i*Complex.exp (-Complex.I*(L.frequency i:ℂ)*t)*angularTest f t) =
      (fun t : ℝ => L.weight i*(Complex.exp (-Complex.I*(L.frequency i:ℂ)*t)*angularTest f t)) from funext fun _ => mul_assoc ..,
      integral_const_mul,angular_fourier_atom]
    ring
  · intro i _
    simpa only [mul_assoc] using (angular_integrable f (L.frequency i)).const_mul (L.weight i)

end DSFTomography.Spectral
