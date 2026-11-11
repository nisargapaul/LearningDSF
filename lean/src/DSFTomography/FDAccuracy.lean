import DSFTomography.FDPhysicalCorrelation

noncomputable section
set_option maxHeartbeats 2000000
namespace DSFTomography.FD.Accuracy
open DSFTomography HT SF Matrix Filter
open scoped Topology Matrix.Norms.Frobenius
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def thermalData (V : Volume S) (β : ℝ) : Data S :=
  (momentumMoments (qubitSpins (energyBasis V.R V.h V.J)) β (energies V.R V.h V.J)).harmonics
def staticReal (V : Volume S) (β : ℝ) (d : S) : Mat := (thermalData V β).static d |>.map Complex.re
def forceReal (V : Volume S) (β : ℝ) (d : S) : Mat := (thermalData V β).force d |>.map Complex.re
def population (V : Volume S) (β : ℝ) (m : Config S) :=
  Real.exp (-β*energies V.R V.h V.J m) / ∑ j, Real.exp (-β*energies V.R V.h V.J j)

theorem population_pos (V : Volume S) (β : ℝ) (m : Config S) : 0 ≤ population V β m := by
  unfold population; positivity
theorem population_sum (V : Volume S) (β : ℝ) : ∑ m, population V β m = 1 := by
  have pos : 0 < ∑ j, Real.exp (-β*energies V.R V.h V.J j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  unfold population
  rw [← Finset.sum_div,div_self (ne_of_gt pos)]

theorem static_mixture (V : Volume S) (β : ℝ) (d : S) :
    staticReal V β d = ∑ r : S, (1/(Fintype.card S:ℝ)) •
      (∑ m, population V β m • correlation (eigenState V m) r (r+d)) := by
  let U := energyBasis V.R V.h V.J
  have op (r : S) (a b : Axis) :
      (qubitSpins U).σ r a*(qubitSpins U).σ (r+d) b = inBasis U (spinAt r a*spinAt (r+d) b) := by
    simp only [qubitSpins,string,spinAt,← inBasis_mul]
  have site (r : S) (a b : Axis) :
      (m₀ (gibbs β (energies V.R V.h V.J)) ((qubitSpins U).σ r a) ((qubitSpins U).σ (r+d) b)).re =
        ∑ m, population V β m*correlation (eigenState V m) r (r+d) a b := by
    rw [zeroMoment]
    simp only [mean,op,Complex.re_sum]
    apply Finset.sum_congr rfl; intro m _
    change ((population V β m:ℂ)*inBasis U (spinAt r a*spinAt (r+d) b) m m).re = _
    rw [Complex.re_ofReal_mul]
    rfl
  ext a b
  simp only [staticReal,thermalData,harmonics_momentumMoments,thermalMoments,measured,
    Matrix.map_apply,avg,← Complex.ofReal_natCast,Complex.div_ofReal_re,Complex.re_sum,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  change (∑ r, (m₀ _ ((qubitSpins U).σ r a) ((qubitSpins U).σ (r+d) b)).re) / _ = _
  simp_rw [site]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro r _; rw [one_div,div_eq_mul_inv,mul_comm]

theorem static_bilinear (V : Volume S) (β : ℝ) (d : S) : BilinearBound (staticReal V β d) := by
  rw [static_mixture]
  apply bilinear_mixture _ (fun _ : S => 1/(Fintype.card S:ℝ)) (fun _ => by positivity)
  · simp [Fintype.card_ne_zero]
  · intro r
    exact bilinear_mixture _ _ (population_pos V β) (population_sum V β)
      (fun m => correlation_bound (eigenState V m) r (r+d))

theorem bond_real (C : Tensor) (J : Mat) :
    (bondMap C (J.map Complex.ofReal)).map Complex.re = bond (C.map Complex.re) J := by
  ext a b
  have axes (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;>
    simp [bondMap,bond,Fin.sum_univ_three,axisTable,Complex.mul_re]

theorem thermal_equation (V : Volume S) (β : ℝ) {d : S} (hd : d ∈ V.R.dirs) :
    forceReal V β d = bond (staticReal V β d) (V.J d) := by
  unfold forceReal staticReal thermalData
  rw [harmonics_momentumMoments]
  change ((measured _ _ _).force d).map Complex.re = _
  rw [measured_bond _ _ _ _ _ _ (diagonalized V.R V.h V.J) hd]
  exact bond_real _ _

/-- The manuscript accuracy corollary, for real measured correlation/force
matrices of the physical Gibbs DSF. No norm or contraction bound is assumed. -/
theorem fd_accuracy (V : Volume S) (β : ℝ) {d : S} (hd : d ∈ V.R.dirs)
    (small : ∀ a b, |V.J d a b| ≤ 1) (Chat Fhat : Mat) (ε γ : ℝ)
    (noise : max ‖Chat-staticReal V β d‖ ‖Fhat-forceReal V β d‖ ≤ ε)
    (positive : 0 < γ) (det : γ ≤ |Chat.det|) :
    ∀ a b, |estimate Chat Fhat a b-V.J d a b| ≤ 25*(1+ε)^2/(4*γ)*ε :=
  accuracy _ _ _ _ _ ε γ (thermal_equation V β hd) small
    (bilinear_contracts _ (static_bilinear V β d))
    (bilinear_contracts _ (bilinear_transpose _ (static_bilinear V β d))) noise positive det

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

theorem limiting_bilinear (β : ℝ) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A))
    (d : R.dirs) : BilinearBound ((A.1 d).map Complex.re) := by
  intro u v
  have cont : Continuous (fun P : Packet R.dirs => |bil ((P.1 d).map Complex.re) u v|) := by
    unfold bil; fun_prop
  apply le_of_tendsto (cont.continuousAt.tendsto.comp data)
  exact Eventually.of_forall fun n => static_bilinear (periodicVolume R h J (seq n)) β
    (periodicSite R (seq n) d) u v

/-- The same accuracy corollary for thermodynamic-limit data. Its constant
has no volume or temperature dependence. -/
theorem fd_accuracy_thermodynamic (β : ℝ) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A))
    (d : R.dirs) (small : ∀ a b, |J d a b| ≤ 1) (Chat Fhat : Mat) (ε γ : ℝ)
    (noise : max ‖Chat-(A.1 d).map Complex.re‖ ‖Fhat-(A.2.1 d).map Complex.re‖ ≤ ε)
    (positive : 0 < γ) (det : γ ≤ |Chat.det|) :
    ∀ a b, |estimate Chat Fhat a b-J d a b| ≤ 25*(1+ε)^2/(4*γ)*ε := by
  have eq := congrArg (fun P : Packet R.dirs => P.2.1 d)
    (thermodynamic_equations R h J β A seq data)
  have equation : (A.2.1 d).map Complex.re = bond ((A.1 d).map Complex.re) (J d) := by
    change A.2.1 d = bondMap (A.1 d) ((J d).map Complex.ofReal) at eq
    rw [eq,bond_real]
  have bound := limiting_bilinear R h J β A seq data d
  exact accuracy _ _ _ _ _ ε γ equation small (bilinear_contracts _ bound)
    (bilinear_contracts _ (bilinear_transpose _ bound)) noise positive det

end DSFTomography.FD.Accuracy
