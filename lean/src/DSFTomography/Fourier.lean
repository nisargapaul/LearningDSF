import DSFTomography.Thermal
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

noncomputable section
namespace DSFTomography
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

/-- A momentum is a character q(d) = exp(i q·d) of the periodic site group. -/
abbrev Momentum (S : Type*) [AddCommGroup S] := AddChar S ℂ

def toMomentum (f : S → ℂ) (q : Momentum S) : ℂ := ∑ d, q d * f d

def harmonic (g : Momentum S → ℂ) (d : S) : ℂ :=
  (∑ q, q (-d) * g q) / (Fintype.card S : ℂ)

/-- Orthogonality on the complete reciprocal grid recovers each oriented displacement. -/
theorem harmonic_toMomentum (f : S → ℂ) (d : S) : harmonic (toMomentum f) d = f d := by
  classical
  unfold harmonic toMomentum
  simp_rw [Finset.mul_sum, ← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, neg_add_eq_zero, ite_mul, zero_mul]
  simp [Fintype.card_ne_zero]

/-- Momentum-resolved normalized Gibbs moments. Expanding thermalMoments gives
the double sum over sites r and r+d with phase exp(i q·d) and the Lehmann weights. -/
def momentumMoments {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Spins S ι)
    (β : ℝ) (E : ι → ℝ) : Data (Momentum S) where
  static q a b := toMomentum (fun d => (thermalMoments P β E).static d a b) q
  first q a b := toMomentum (fun d => (thermalMoments P β E).first d a b) q

def Data.harmonics (D : Data (Momentum S)) : Data S where
  static d a b := harmonic (fun q => D.static q a b) d
  first d a b := harmonic (fun q => D.first q a b) d

theorem harmonics_momentumMoments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Spins S ι) (β : ℝ) (E : ι → ℝ) :
    (momentumMoments P β E).harmonics = thermalMoments P β E := by
  cases eqn : thermalMoments P β E with
  | mk C F => simp [Data.harmonics, momentumMoments, eqn, harmonic_toMomentum]

/-- FD tomography directly from calibrated, momentum-resolved zeroth and first
Lehmann moments on the complete reciprocal grid. D is the only measured input. -/
theorem fdFromDSF {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Spins S ι) (R : Bonds S)
    (β : ℝ) (E : ι → ℝ) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ)
    (hH : H P R (fun a => (h a : ℂ)) (fun d a b => (J d a b : ℂ)) =
      Matrix.diagonal (fun m => (E m : ℂ)))
    (D : Data (Momentum S)) (observed : D = momentumMoments P β E)
    (hdet : ∀ d ∈ R.dirs, (D.harmonics.static d).det ≠ 0)
    (k : Axis) (hk : D.harmonics.mag k ≠ 0) :
    (∀ d ∈ R.dirs, D.harmonics.exchange d = fun a b => (J d a b : ℂ)) ∧
      D.harmonics.field R k = fun a => (h a : ℂ) := by
  subst D
  rw [harmonics_momentumMoments] at hdet hk ⊢
  exact fdGibbs P R β E h J hH hdet k hk

end DSFTomography
