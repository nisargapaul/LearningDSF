import DSFTomography.DSFFourier
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! The exact Heisenberg correlation, its time-Fourier DSF, and moments.
No spectral sum rule is a hypothesis. All transition weights and frequencies
are obtained from the observables and the Hamiltonian in its energy basis. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography MeasureTheory Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lehmann (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) : Lines (ι × ι) where
  frequency ij := E ij.2-E ij.1
  weight ij := w ij.1*A ij.1 ij.2*B ij.2 ij.1

def propagator (E : ι → ℝ) (t : ℝ) : Op ι :=
  Matrix.diagonal fun i => Complex.exp (Complex.I*(t:ℂ)*(E i:ℂ))
def evolved (E : ι → ℝ) (t : ℝ) (A : Op ι) : Op ι :=
  propagator E t*A*propagator E (-t)
def timeCorrelation (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) (t : ℝ) : ℂ :=
  mean w (evolved E t A*B)

open scoped Matrix.Norms.Operator in
theorem propagator_eq_exp (E : ι → ℝ) (t : ℝ) :
    propagator E t = NormedSpace.exp ℂ ((Complex.I*(t:ℂ)) • Matrix.diagonal (fun i => (E i:ℂ))) := by
  rw [← Matrix.diagonal_smul,Matrix.exp_diagonal]
  simp only [propagator,Pi.exp_def,Pi.smul_apply,smul_eq_mul,Complex.exp_eq_exp_ℂ]

/-- Direct derivation of the Lehmann frequencies and weights from Heisenberg evolution. -/
theorem timeCorrelation_eq (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) :
    timeCorrelation w E A B = (lehmann w E A B).correlation := by
  funext t
  simp only [timeCorrelation,mean,evolved,propagator,Matrix.mul_apply,
    Matrix.diagonal_apply,mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq',
    Finset.sum_ite_eq,Finset.mem_univ,if_true,Lines.correlation,lehmann,
    Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have exp : Complex.exp (Complex.I*(t:ℂ)*E i)*Complex.exp (Complex.I*((-t:ℝ):ℂ)*E j) =
      Complex.exp (-Complex.I*((E j-E i:ℝ):ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  calc
    _ = (w i*A i j*B j i)*(Complex.exp (Complex.I*(t:ℂ)*E i)*Complex.exp (Complex.I*((-t:ℝ):ℂ)*E j)) := by ring
    _ = _ := by rw [exp]

/-- The manuscript time-Fourier definition equals the exact Lehmann DSF. -/
theorem dsf_definition (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, timeCorrelation w E A B t*angularTest f t) = (lehmann w E A B).distribution f := by
  rw [timeCorrelation_eq]; exact time_fourier_eq_lines _ _

theorem zeroth_moment (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) :
    (lehmann w E A B).moment 0 = (2*Real.pi:ℂ)*m₀ w A B := by
  simp only [Lines.moment,lehmann,pow_zero,mul_one,Fintype.sum_prod_type,m₀,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring
theorem first_moment (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) :
    (lehmann w E A B).moment 1 = (2*Real.pi:ℂ)*m₁ w (fun i => (E i:ℂ)) A B := by
  simp only [Lines.moment,lehmann,pow_one,Fintype.sum_prod_type,m₁,Finset.mul_sum,Complex.ofReal_sub]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring
theorem second_moment (w : ι → ℂ) (E : ι → ℝ) (A B : Op ι) :
    (lehmann w E A B).moment 2 = (2*Real.pi:ℂ)*HT.Diagonal.second w (fun i => (E i:ℂ)) A B := by
  simp only [Lines.moment,lehmann,Fintype.sum_prod_type,HT.Diagonal.second,Complex.ofReal_sub]
  congr 1; apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

end DSFTomography.Spectral
