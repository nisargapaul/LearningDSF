import DSFTomography.DSFLehmann

/-! Calibrated momentum-resolved DSF, with the paper's 1/N double-site sum.
The translation variable is d=r'-r, so its Fourier phase is q(d).
The zeroth, first and second spectral integrals agree with the inputs of the
FD, SF and HT theorems, including their normalization. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography MeasureTheory
variable {S ι : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
  [Fintype ι] [DecidableEq ι]

def momentumLines (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ)
    (q : Momentum S) (a b : Axis) : Lines (S × S × ι × ι) where
  frequency t := E t.2.2.2-E t.2.2.1
  weight t := q t.1/(Fintype.card S:ℂ)*w t.2.2.1*
    P.σ t.2.1 a t.2.2.1 t.2.2.2*P.σ (t.2.1+t.1) b t.2.2.2 t.2.2.1

def momentumTime (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ)
    (q : Momentum S) (a b : Axis) (t : ℝ) : ℂ :=
  (∑ r, ∑ s, q (s-r)*timeCorrelation w E (P.σ r a) (P.σ s b) t)/(Fintype.card S:ℂ)

theorem momentumTime_eq (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ)
    (q : Momentum S) (a b : Axis) : momentumTime P w E q a b = (momentumLines P w E q a b).correlation := by
  funext t
  have shift (r : S) : (∑ s, q (s-r)*timeCorrelation w E (P.σ r a) (P.σ s b) t) =
      ∑ d, q d*timeCorrelation w E (P.σ r a) (P.σ (r+d) b) t := by
    have eq := Equiv.sum_comp (Equiv.addLeft r) (fun s => q (s-r)*timeCorrelation w E (P.σ r a) (P.σ s b) t)
    simpa using eq.symm
  simp only [momentumTime,shift]
  rw [Finset.sum_comm]
  simp only [timeCorrelation_eq,Lines.correlation,lehmann,momentumLines,Fintype.sum_prod_type,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Exactly the paper's double-space-sum, positive-sign time-Fourier DSF. -/
theorem momentum_dsf_definition (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ)
    (q : Momentum S) (a b : Axis) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, momentumTime P w E q a b t*angularTest f t) =
      (momentumLines P w E q a b).distribution f := by
  rw [momentumTime_eq]; exact time_fourier_eq_lines _ _

theorem momentum_zeroth (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ) (q : Momentum S) (a b : Axis) :
    (momentumLines P w E q a b).moment 0 =
      (2*Real.pi:ℂ)*toMomentum (fun d => (measured P w (fun i => (E i:ℂ))).static d a b) q := by
  simp only [Lines.moment,momentumLines,pow_zero,mul_one,toMomentum,measured,avg,m₀,
    Fintype.sum_prod_type,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem momentum_first (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ) (q : Momentum S) (a b : Axis) :
    (momentumLines P w E q a b).moment 1 =
      (2*Real.pi:ℂ)*toMomentum (fun d => (measured P w (fun i => (E i:ℂ))).first d a b) q := by
  simp only [Lines.moment,momentumLines,pow_one,toMomentum,measured,avg,m₁,
    Fintype.sum_prod_type,Finset.sum_div,Finset.mul_sum,Complex.ofReal_sub]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem momentum_second (P : Spins S ι) (β : ℝ) (E : ι → ℝ) (q : Momentum S) (a : Axis) :
    (momentumLines P (gibbs β E) E q a a).moment 2 =
      (2*Real.pi:ℂ)*HT.Diagonal.scan P E β q a := by
  simp only [Lines.moment,momentumLines,HT.Diagonal.scan,HT.Diagonal.localSecond,
    HT.Diagonal.second,toMomentum,avg,Fintype.sum_prod_type,Finset.sum_div,
    Finset.mul_sum,Complex.ofReal_sub]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

def rawData (P : Spins S ι) (β : ℝ) (E : ι → ℝ) : Data (Momentum S) where
  static q a b := (momentumLines P (gibbs β E) E q a b).moment 0/(2*Real.pi)
  first q a b := (momentumLines P (gibbs β E) E q a b).moment 1/(2*Real.pi)

theorem rawData_eq (P : Spins S ι) (β : ℝ) (E : ι → ℝ) : rawData P β E = momentumMoments P β E := by
  have nonzero : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (show (2*Real.pi:ℝ) ≠ 0 by positivity)
  apply congrArg₂ Data.mk <;> funext q a b
  · simp only [rawData,momentum_zeroth,mul_div_cancel_left₀ _ nonzero,momentumMoments,thermalMoments]
  · simp only [rawData,momentum_first,mul_div_cancel_left₀ _ nonzero,momentumMoments,thermalMoments]

end DSFTomography.Spectral
