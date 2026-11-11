import DSFTomography.DSFMomentum
import DSFTomography.HTLocalGibbs

/-! Identification with the manuscript's normalized Gibbs trace in the
physical tensor-product basis, before any spectral decomposition. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT Matrix
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def physicalEvolution (V : Volume S) (t : ℝ) (A : Op (Config S)) : Op (Config S) :=
  V.boltzmann (-Complex.I*t)*A*V.boltzmann (Complex.I*t)
def physicalCorrelation (V : Volume S) (β t : ℝ) (A B : Op (Config S)) : ℂ :=
  (V.boltzmann β*(physicalEvolution V t A*B)).trace/V.partition β

theorem evolution_in_energy_basis (V : Volume S) (t : ℝ) (A : Op (Config S)) :
    inBasis (energyBasis V.R V.h V.J) (physicalEvolution V t A) =
      evolved (energies V.R V.h V.J) t (inBasis (energyBasis V.R V.h V.J) A) := by
  simp only [physicalEvolution,← inBasis_mul,Volume.boltzmann_diagonal,evolved,propagator]
  simp only [neg_mul,neg_neg,Complex.ofReal_neg,mul_neg]

/-- Gibbs expectation of exp(itH) A exp(-itH) B equals its energy-basis
correlation. This discharges the physical-state input of the Fourier bridge. -/
theorem physicalCorrelation_eq (V : Volume S) (β t : ℝ) (A B : Op (Config S)) :
    physicalCorrelation V β t A B =
      timeCorrelation (gibbs β (energies V.R V.h V.J)) (energies V.R V.h V.J)
        (inBasis (energyBasis V.R V.h V.J) A) (inBasis (energyBasis V.R V.h V.J) B) t := by
  rw [physicalCorrelation,Volume.trace_test_eq_sum,Volume.partition_eq_sum]
  simp only [← inBasis_mul,evolution_in_energy_basis,timeCorrelation,mean,gibbs,
    Complex.ofReal_div,Complex.ofReal_sum,← Complex.ofReal_exp,← Complex.ofReal_neg,
    ← Complex.ofReal_mul,div_mul_eq_mul_div,Finset.sum_div]

/-- Literal normalized-trace/time-Fourier definition with raw 2π intensity. -/
theorem physical_dsf_definition (V : Volume S) (β : ℝ) (A B : Op (Config S)) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, physicalCorrelation V β t A B*angularTest f t) =
      (lehmann (gibbs β (energies V.R V.h V.J)) (energies V.R V.h V.J)
        (inBasis (energyBasis V.R V.h V.J) A) (inBasis (energyBasis V.R V.h V.J) B)).distribution f := by
  simp only [physicalCorrelation_eq]
  exact dsf_definition _ _ _ _ _

def physicalMomentum (V : Volume S) (β : ℝ) (q : Momentum S) (a b : Axis) (t : ℝ) : ℂ :=
  (∑ r, ∑ s, q (s-r)*physicalCorrelation V β t (word (oneLabel r a)) (word (oneLabel s b)))/(Fintype.card S:ℂ)

theorem physicalMomentum_eq (V : Volume S) (β : ℝ) (q : Momentum S) (a b : Axis) :
    physicalMomentum V β q a b = momentumTime (qubitSpins (energyBasis V.R V.h V.J))
      (gibbs β (energies V.R V.h V.J)) (energies V.R V.h V.J) q a b := by
  funext t
  simp only [physicalMomentum,momentumTime,physicalCorrelation_eq,qubitSpins,string]

/-- The paper's DSF definition, with physical Heisenberg evolution, normalized
Gibbs trace, the double-site sum, and its spatial Fourier phase. -/
theorem physical_momentum_dsf_definition (V : Volume S) (β : ℝ)
    (q : Momentum S) (a b : Axis) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, physicalMomentum V β q a b t*angularTest f t) =
      (momentumLines (qubitSpins (energyBasis V.R V.h V.J))
        (gibbs β (energies V.R V.h V.J)) (energies V.R V.h V.J) q a b).distribution f := by
  rw [physicalMomentum_eq]
  exact momentum_dsf_definition _ _ _ _ _ _ _

end DSFTomography.Spectral
