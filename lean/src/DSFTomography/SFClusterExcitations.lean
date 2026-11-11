import DSFTomography.SFClusterEigen

/-! The dressed Hamiltonian on a flipped configuration relative to the
vacuum. The excited-state column is divided by its own unperturbed energy.
This is a local norm estimate even for macroscopic excitations. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT NormedSpace
variable {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]

theorem translate_bound (r : S) : ‖(translateAmp r : Operator S)‖ ≤ 1 :=
  columns_norm_le _ zero_le_one (by simp)

def excitedColumn (D : List S) (u : Amp S) (x : Config S) : Amp S :=
  (2*(flipCount x : ℂ))⁻¹ • ∑ t : S, (phase D (translated (-t) x)-1) • flip x (translateAmp t u)

def excitation (D : List S) : Amp S →L[ℂ] Operator S :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => columns (excitedColumn D u)
    map_add' := by intro u v; apply operator_ext; intro x; simp [excitedColumn,map_add,smul_add,Finset.sum_add_distrib]
    map_smul' := by
      intro c u; apply operator_ext; intro x
      simp only [columns_basis,ContinuousLinearMap.smul_apply,excitedColumn,map_smul,RingHom.id_apply]
      rw [smul_comm c (2*(flipCount x:ℂ))⁻¹]; apply congrArg (_ • ·)
      rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro r _; exact smul_comm .. }

theorem excitation_bound (D : List S) : ‖excitation (S := S) D‖ ≤ D.length := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply columns_norm_le _ (by positivity); intro x
  unfold excitedColumn; rw [norm_smul]
  by_cases hx : flipCount x=0
  · simp [hx]; positivity
  have pos : 0 < (2:ℝ)*flipCount x := by positivity
  simp only [norm_inv,norm_mul,Complex.norm_two,Complex.norm_natCast]
  rw [← div_eq_inv_mul,div_le_iff₀ pos]
  have shifts (r : S) : ‖flip x (translateAmp r u)‖ ≤ ‖u‖ := by
    calc _ ≤ ‖flip x‖ * ‖translateAmp r u‖ := (flip x).le_opNorm _
         _ ≤ ‖translateAmp r u‖ := mul_le_of_le_one_left (norm_nonneg _) (flip_bound x)
         _ ≤ ‖translateAmp r‖ * ‖u‖ := (translateAmp r).le_opNorm _
         _ ≤ ‖u‖ := mul_le_of_le_one_left (norm_nonneg _) (translate_bound r)
  have cost := Equiv.sum_comp (Equiv.neg S) (fun t => ‖phase D (translated t x)-1‖)
  calc
    _ ≤ ∑ t : S, ‖(phase D (translated (-t) x)-1) • flip x (translateAmp t u)‖ := norm_sum_le _ _
    _ ≤ ∑ t : S, ‖phase D (translated (-t) x)-1‖ * ‖u‖ := by
      apply Finset.sum_le_sum; intro t _; rw [norm_smul]; gcongr; exact shifts t
    _ = (∑ t : S, ‖phase D (translated t x)-1‖) * ‖u‖ := by rw [← Finset.sum_mul]; exact congrArg (· * ‖u‖) cost
    _ ≤ (2*D.length*flipCount x)*‖u‖ := mul_le_mul_of_nonneg_right (phase_cost D x) (norm_nonneg _)
    _ = _ := by ring

def excitationEnergy (x : Config S) : ℂ := 2*(flipCount x : ℂ)

theorem excited_action (D : List S) (u : Amp S) (x : Config S) :
    excitationEnergy x • excitation D u (basis x) =
      ∑ t : S, (phase D (translated (-t) x)-1) • flip x (translateAmp t u) := by
  change excitationEnergy x • columns _ (basis x) = _
  rw [columns_basis,excitedColumn,smul_smul]
  by_cases hz : x=0
  · subst x; simp [show ∀ r : S, translated r (0 : Config S)=0 from fun _ => rfl]
  · have ex : ∃ t, x t ≠ 0 := by simpa [funext_iff] using hz
    have size : flipCount x ≠ 0 := Finset.card_ne_zero.mpr (by
      obtain ⟨t,ht⟩ := ex; exact ⟨t,by simp [ht]⟩)
    have ne : (2*(flipCount x : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast size)
    rw [excitationEnergy,mul_inv_cancel₀ ne,one_smul]

theorem flip_exp_comm (x : Config S) (v : Amp S) :
    Commute (flip x) (exp ℂ (convolute (generator v))) :=
  ((convolution_basis x) ▸ convolution_comm (basis x) (generator v)).exp_right ℂ

omit [AddCommGroup S] in
private theorem local_flip_phase (y x : Config S) (D : List S) :
    pauliOp y D * flip x = phase D x • (flip x * pauliOp y D) := by
  have h := sign_convolve D (basis x)
  rw [convolution_basis,sign_basis,map_smul,convolution_basis] at h
  apply operator_ext; intro z
  have v := congrArg (fun L : Operator S => L (basis z)) h
  change flip y (signOp D (flip x (basis z))) = _
  simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply] at v
  simp only [pauliOp,ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply,v,map_smul]
  exact congrArg (phase D x • ·) (congrArg (fun L : Operator S => L _) (flip_comm y x).eq)

private theorem translate_flip (r : S) (x : Config S) (u : Amp S) :
    translateAmp r (flip x u) = flip (translated r x) (translateAmp r u) :=
  congrArg (fun L : Operator S => L u) (translation_flip r x)

theorem term_excited (y x : Config S) (D : List S) (v : Amp S) :
    let U := exp ℂ (convolute (generator v))
    let u := flip y (ampExp (response D v))
    periodicTerm y D (U (basis x)) =
      U (flip x (orbit u) + excitationEnergy x • excitation D u (basis x)) := by
  intro U u
  have ket : U (basis x) = flip x (eigenKet v) := by
    simpa [ContinuousLinearMap.mul_apply,U,eigenKet,ampExp] using
      (congrArg (fun L : Operator S => L (basis 0)) (flip_exp_comm x v).eq).symm
  have step (t : S) : translateAmp t (pauliOp y D (translateAmp (-t) (U (basis x)))) =
      U (phase D (translated (-t) x) • flip x (translateAmp t u)) := by
    rw [ket,translate_flip,ket_invariant]
    have h := congrArg (fun L : Operator S => L (eigenKet v)) (local_flip_phase y (translated (-t) x) D)
    simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply] at h
    rw [h,word_eigenKet,map_smul,translate_flip,translated_add,add_neg_cancel]
    have tr : translated (0:S) x = x := by funext a; simp [translated]
    rw [tr,map_smul]
    have commute1 := congrArg (fun L : Operator S => L u) (translate_commutes t v).eq
    have commute2 := congrArg (fun L : Operator S => L (translateAmp t u)) (flip_exp_comm x v).eq
    exact congrArg (_ • ·) ((congrArg (flip x) commute1).trans commute2)
  rw [excited_action]
  simp only [periodicTerm,ContinuousLinearMap.sum_apply,ContinuousLinearMap.mul_apply,step]
  rw [← map_sum]; congr 1
  simp only [orbit,map_sum,sub_smul,one_smul,Finset.sum_sub_distrib,add_sub_cancel]

end DSFTomography.SF.Cluster
