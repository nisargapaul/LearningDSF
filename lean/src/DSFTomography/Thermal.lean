import DSFTomography.FD
import Mathlib.Analysis.Complex.Exponential

noncomputable section
namespace DSFTomography
variable {S ι : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
  [Fintype ι] [DecidableEq ι]

/-- Finite-volume Gibbs populations for real energies and inverse temperature β. -/
def gibbs (β : ℝ) (E : ι → ℝ) (m : ι) : ℂ :=
  (Real.exp (-β * E m) / ∑ j, Real.exp (-β * E j) : ℝ)

omit [DecidableEq ι] in
theorem gibbs_normalized [Nonempty ι] (β : ℝ) (E : ι → ℝ) : ∑ m, gibbs β E m = 1 := by
  have hZ : 0 < ∑ j, Real.exp (-β * E j) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold gibbs
  rw [← Complex.ofReal_sum]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ (ne_of_gt hZ), Complex.ofReal_one]

def thermalMoments (P : Spins S ι) (β : ℝ) (E : ι → ℝ) : Data S :=
  measured P (gibbs β E) (fun m => (E m : ℂ))

/-- Finite-temperature FD reconstruction with real energies, fields, and exchanges.
All functions in the conclusion take only the two DSF moments, bond directions,
and the index of a nonzero magnetization component as input. -/
theorem fdGibbs (P : Spins S ι) (R : Bonds S) (β : ℝ) (E : ι → ℝ)
    (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ)
    (hH : H P R (fun a => (h a : ℂ)) (fun d a b => (J d a b : ℂ)) =
      Matrix.diagonal (fun m => (E m : ℂ)))
    (hdet : ∀ d ∈ R.dirs, ((thermalMoments P β E).static d).det ≠ 0)
    (k : Axis) (hk : (thermalMoments P β E).mag k ≠ 0) :
    (∀ d ∈ R.dirs, (thermalMoments P β E).exchange d = fun a b => (J d a b : ℂ)) ∧
      (thermalMoments P β E).field R k = fun a => (h a : ℂ) :=
  fdTomography P R _ _ _ _ hH hdet k hk

end DSFTomography
