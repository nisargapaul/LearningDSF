import DSFTomography.Fourier
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace DSFTomography.HT
open DSFTomography
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem gibbs_slope (E : ι → ℝ) (hE : ∑ m, E m = 0) (m : ι) :
    HasDerivAt (fun β => gibbs β E m) (-(E m : ℂ) / Fintype.card ι) 0 := by
  have term (j : ι) : HasDerivAt (fun β : ℝ => Real.exp (-β * E j)) (-E j) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).neg.mul_const (E j)).exp)
  have partition := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => term j)
  have hd := (term m).div partition (by simp [Fintype.card_ne_zero])
  simp [Finset.sum_neg_distrib, hE] at hd
  convert hd.ofReal_comp using 1
  · funext β; simp [gibbs, Pi.div_apply]
  · push_cast; field_simp

/-- Differentiating the normalized thermal trace, for the traceless Hamiltonians
used here. The traceless condition removes the partition-function derivative. -/
theorem mean_slope (E : ι → ℝ) (A H : Op ι)
    (hH : H = Matrix.diagonal (fun m => (E m : ℂ))) (htr : H.trace = 0) :
    HasDerivAt (fun β => mean (gibbs β E) A) (-(H * A).trace / Fintype.card ι) 0 := by
  have hE : ∑ m, E m = 0 := by
    rw [hH, Matrix.trace_diagonal] at htr
    exact_mod_cast htr
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun m _ => (gibbs_slope E hE m).mul_const (A m m))
  convert hd using 1
  rw [hH]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, div_eq_mul_inv]
  simp only [mul_right_comm _ (Fintype.card ι : ℂ)⁻¹, ← Finset.sum_mul,
    neg_mul, Finset.sum_neg_distrib]

end DSFTomography.HT
