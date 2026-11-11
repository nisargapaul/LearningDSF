import DSFTomography.SFClusterBra

/-! Translation covariance of the dressed measurement in a periodic box. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT NormedSpace
variable {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
variable {J : Type*} [Fintype J]

local instance : SMul (Operator S) (Operator S) := ⟨(· * ·)⟩
local instance : IsScalarTower ℂ (Operator S) (Operator S) := ⟨fun _ _ _ => rfl⟩
local instance : SMulCommClass ℂ (Operator S) (Operator S) := ⟨fun z A B => by ext x : 1; exact (A.map_smul z (B x)).symm⟩

def shiftEquiv (r : S) : Config S ≃ Config S where
  toFun := translated r
  invFun := translated (-r)
  left_inv := fun x => by rw [translated_add,neg_add_cancel]; funext j; simp [translated]
  right_inv := fun x => by rw [translated_add,add_neg_cancel]; funext j; simp [translated]

theorem shift_at (r : S) (v : Amp S) (x : Config S) :
    translateAmp r v ((shiftEquiv r) x) = v x := by
  let π := (PiLp.proj 1 (fun _ : Config S => ℂ) ((shiftEquiv r) x) : Amp S →L[ℂ] ℂ)
  change π (∑ y, v y • basis (shiftEquiv r y)) = _
  simp only [map_sum,map_smul]; change ∑ y, v y * (if shiftEquiv r x=shiftEquiv r y then 1 else 0) = _
  simp [mul_ite]

theorem bra_shift (r : S) (v w : Amp S) :
    bra (translateAmp r v) (translateAmp r w) = bra v w := by
  rw [bra_apply,bra_apply]
  change (∑ x, star (translateAmp r v x)*translateAmp r w x) = ∑ x, star (v x)*w x
  rw [← (shiftEquiv r).sum_comp]; simp only [shift_at]

theorem shift_product (r s : S) :
    (translateAmp r : Operator S)*translateAmp s = translateAmp (r+s) := by
  apply operator_ext; intro x; simp only [ContinuousLinearMap.mul_apply,translate_basis,translated_add]

theorem periodic_commutes (r : S) (x : Config S) (D : List S) :
    Commute (translateAmp r) (periodicTerm x D) := by
  unfold Commute SemiconjBy periodicTerm; rw [Finset.mul_sum,Finset.sum_mul]
  let f := fun t : S => translateAmp t * pauliOp x D * translateAmp (-t+r)
  calc
    _ = ∑ t, f (r+t) := by
      apply Finset.sum_congr rfl; intro t _
      simp only [f,show -(r+t)+r = -t by abel,← mul_assoc,shift_product]
    _ = ∑ t, f t := Equiv.sum_comp (Equiv.addLeft r) f
    _ = _ := by apply Finset.sum_congr rfl; intro t _; rw [mul_assoc _ (translateAmp (-t)) _,shift_product]

theorem clusterH_commutes (r : S) (A : J → Config S) (D : J → List S) (p : J → ℂ) :
    Commute (translateAmp r) (clusterH A D p) := by
  apply Commute.add_right
  · exact ((Commute.one_right _).smul_right _).sub_right (periodic_commutes r _ _)
  · exact Commute.sum_right _ _ _ fun j _ => (periodic_commutes r _ _).smul_right _

theorem shift_spin (r s : S) (a : Axis) :
    translateAmp r * asOperator (spinAt s a) = asOperator (spinAt (s+r) a) * translateAmp r := by
  rw [spin_signed,spin_signed,mul_smul_comm,smul_mul_assoc]
  apply congrArg (_ • ·)
  have h := congrArg (· * translateAmp r) (translate_word r (toggle s a) (sites s a))
  dsimp only at h
  rw [tr_bit,tr_site,mul_assoc _ (translateAmp (-r)) _,shift_product,neg_add_cancel] at h
  have id : (translateAmp (0:S) : Operator S)=1 := by
    apply operator_ext; intro x; rw [translate_basis]; apply congrArg basis; funext j; simp [translated]
  simpa [id] using h

end DSFTomography.SF.Cluster
