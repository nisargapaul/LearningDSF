import DSFTomography.HTProjection
import DSFTomography.GibbsSlope

noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

/-- A temperature-dependent normalized static DSF on the reciprocal grid. -/
abbrev StaticScan (S : Type*) [AddCommGroup S] := ℝ → Momentum S → Tensor

def staticHarmonic (D : StaticScan S) (d : S) (a b : Axis) (β : ℝ) : ℂ :=
  harmonic (fun q => D β q a b) d

def staticSlope (D : StaticScan S) (d : S) (a b : Axis) : ℂ :=
  derivWithin (staticHarmonic D d a b) (Set.Ici 0) 0

/-- The two readouts depend only on the measured static DSF. -/
def exchange (D : StaticScan S) (d : S) : Tensor := fun a b => -staticSlope D d a b
def field (D : StaticScan S) (k : Axis) : ℂ := Complex.I * staticSlope D 0 (k+1) (k+2)

variable (P : Spins S (Config S)) (U : (Op (Config S))ˣ) (frame : IsQubitFrame P U)
  (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ) (E : Config S → ℝ)
abbrev realH := H P R (fun a => (h a : ℂ)) (fun d a b => (J d a b : ℂ))
variable (hH : realH P R h J = Matrix.diagonal (fun m => (E m : ℂ)))

omit [DecidableEq S] in
private theorem avg_deriv {f : S → ℝ → ℂ} {v : ℂ} (hf : ∀ t, HasDerivAt (f t) v 0) :
    HasDerivAt (fun β => avg (fun t => f t β)) v 0 := by
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun t _ => hf t)).div_const
    (Fintype.card S : ℂ)
  simpa [avg, Fintype.card_ne_zero] using hs

include frame hH in
theorem static_bond_deriv {d : S} (hd : d ∈ R.dirs) (a b : Axis) :
    HasDerivAt (fun β => (thermalMoments P β E).static d a b) (-(J d a b : ℂ)) 0 := by
  apply avg_deriv
  intro t
  have dist : t ≠ t+d := Ne.symm (by simpa using R.nonzero d hd)
  have val : (realH P R h J * (P.σ t a * P.σ (t+d) b)).trace = (J d a b : ℂ) * Fintype.card (Config S) := by
    rw [frame t a, frame (t+d) b, string_pair U dist]
    exact project_bond P U frame R _ _ hd t a b
  have dim : (Fintype.card (Config S) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [zeroMoment, val, neg_div, mul_div_cancel_right₀ _ dim] using
    mean_slope E (P.σ t a * P.σ (t+d) b) (realH P R h J) hH (H_traceless P U frame R _ _)

include frame hH in
theorem static_onsite_deriv (a b : Axis) :
    HasDerivAt (fun β => (thermalMoments P β E).static 0 a b)
      (-(Complex.I * sign a b * h (third a b))) 0 := by
  apply avg_deriv
  intro t
  have val : (realH P R h J * (P.σ t a * P.σ t b)).trace =
      (Complex.I * sign a b) * ((h (third a b) : ℂ) * Fintype.card (Config S)) := by
    by_cases hab : a=b
    · subst b
      have hs : sign a a = 0 := by fin_cases a <;> rfl
      rw [frame t a, string_square, Matrix.mul_one, realH, H_traceless P U frame R, hs]
      simp
    · rw [realH, frame t a, frame t b, string_same_site U t a b hab, Matrix.mul_smul,
        Matrix.trace_smul, project_field P U frame R _ _]
      rfl
  have hs := mean_slope E (P.σ t a * P.σ t b) (realH P R h J) hH (H_traceless P U frame R _ _)
  rw [val] at hs
  have dim : (Fintype.card (Config S) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [zeroMoment, add_zero, ← mul_assoc, neg_div, mul_div_cancel_right₀ _ dim] using hs

include frame hH in
theorem static_field_deriv (k : Axis) :
    HasDerivAt (fun β => (thermalMoments P β E).static 0 (k+1) (k+2))
      (-(Complex.I * h k)) 0 := by
  have hs : sign (k+1) (k+2) = 1 := by fin_cases k <;> rfl
  have ht : third (k+1) (k+2) = k := by fin_cases k <;> rfl
  simpa only [hs, ht, mul_one] using static_onsite_deriv P U frame R h J E hH (k+1) (k+2)

/-- Calibration is needed only near zero on the physical side of inverse temperature. -/
def Calibrated (P : Spins S (Config S)) (E : Config S → ℝ) (D : StaticScan S) :=
  ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ici 0), D β = (momentumMoments P β E).static

private theorem measured_slope {D : StaticScan S} (data : Calibrated P E D) (d : S)
    (a b : Axis) {v : ℂ} (hv : HasDerivAt (fun β => (thermalMoments P β E).static d a b) v 0) :
    staticSlope D d a b = v := by
  apply HasDerivWithinAt.derivWithin _ (uniqueDiffWithinAt_Ici 0)
  apply hv.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ Set.left_mem_Ici
  filter_upwards [data] with β hβ
  simp only [staticHarmonic, hβ, momentumMoments, harmonic_toMomentum]

include frame hH in
theorem htFromDSF (D : StaticScan S) (data : Calibrated P E D) :
    (∀ d ∈ R.dirs, exchange D d = fun a b => (J d a b : ℂ)) ∧
      field D = fun k => (h k : ℂ) := by
  constructor
  · intro d hd
    funext a b
    rw [exchange, measured_slope P E data d a b (static_bond_deriv P U frame R h J E hH hd a b)]
    exact neg_neg _
  · funext k
    rw [field, measured_slope P E data 0 _ _ (static_field_deriv P U frame R h J E hH k)]
    simp [← mul_assoc, Complex.I_mul_I]

end DSFTomography.HT
