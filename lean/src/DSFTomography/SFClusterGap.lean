import DSFTomography.SFClusterExcitations
import DSFTomography.SFClusterPeriodic

/-! Separation of the dressed vacuum using the ℓ¹ norm of the perturbation
relative to excitation energy, uniformly in the box. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology
variable {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
variable {J : Type*} [Fintype J]

def gapOp : Operator S := columns (fun x => excitationEnergy x • basis x)

def correction (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S) : Operator S :=
  -excitation [0] (ampExp (response [0] v) - basis 0) +
    ∑ j, p j • excitation (D j) (flip (A j) (ampExp (response (D j) v)))

theorem gap_identity (x : Config S) :
    excitationEnergy x • excitation [0] (basis (0 : Config S)) (basis x) =
      -excitationEnergy x • basis x := by
  rw [excited_action]
  simp only [translate_basis,show ∀ t : S, translated t (0:Config S) = 0 from fun _ => rfl,
    flip_basis,add_zero,← Finset.sum_smul]
  have h := Equiv.sum_comp (Equiv.neg S) (fun t => phase [0] (translated t x)-1)
  rw [show (∑ t : S, (phase [0] (translated (-t) x)-1)) = _ from h,sum_sign]
  simp [excitationEnergy]

theorem dressed_H (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S)
    (sol : FiniteEquation A D p v) :
    let U := exp ℂ (convolute (generator v))
    let E := -(Fintype.card S : ℂ) * v 0
    clusterH A D p * U = U * (E • 1 + (1 + correction A D p v) * gapOp) := by
  intro U E
  let w := fun j => flip (A j) (ampExp (response (D j) v))
  let f := ampExp (response [0] v)
  let N := (Fintype.card S : ℂ)
  have h0 := vacuum_balance A D p v sol
  apply operator_ext; intro x
  have c := congrArg (flip x) h0
  simp only [map_smul,map_sub,map_sum,map_add,flip_basis,add_zero] at c
  change clusterH A D p (U (basis x)) = U ((E • 1 + (1 + correction A D p v) * gapOp : Operator S) (basis x))
  have part (y D) : periodicTerm y D (U (basis x)) =
      U (flip x (orbit (flip y (ampExp (response D v)))) + excitationEnergy x •
        excitation D (flip y (ampExp (response D v))) (basis x)) := term_excited y x D v
  simp only [clusterH,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
    part,flip_zero]
  have extU (a b : Amp S) (eq : a=b) : U a = U b := congrArg U eq
  simp only [← map_smul U,← map_sum U,← map_sub U,← map_add U]
  apply extU
  change N • basis x - (flip x (orbit f) + excitationEnergy x • excitation [0] f (basis x)) +
    ∑ j, p j • (flip x (orbit (w j)) + excitationEnergy x • excitation (D j) (w j) (basis x)) =
    E • basis x + (1 + correction A D p v) (gapOp (basis x))
  simp only [gapOp,columns_basis,correction,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.sum_apply,map_smul,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,map_sub,ContinuousLinearMap.sub_apply,smul_add,smul_neg,
    smul_sub,Finset.sum_add_distrib,Finset.smul_sum,gap_identity,neg_smul]
  change N • basis x - flip x (orbit f) + (∑ j, p j • flip x (orbit (w j))) = E • basis x at c
  rw [← c]
  unfold w f
  simp only [smul_comm (excitationEnergy x) (p _)]
  abel

omit [AddCommGroup S] in
theorem diag_apply (v : Amp S) (x : Config S) : gapOp v x = excitationEnergy x * v x := by
  let π := PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Config S => ℂ) 1 x
  change π (∑ y, v y • (excitationEnergy y • basis y)) = _
  simp only [map_sum,map_smul]
  change (∑ y, v y * (excitationEnergy y * (if x=y then 1 else 0))) = _
  simp [mul_ite,mul_comm]

omit [AddCommGroup S] in
/-- For a relative error below 1/2, every eigenvector of energy less
than one above the dressed vacuum lies in the vacuum line. -/
theorem low_line (T : Operator S) (hT : ‖T‖ < 1/2) (ξ : Amp S) (μ : ℂ) (low : μ.re ≤ 1)
    (eig : (1 + T) (gapOp ξ) = μ • ξ) : ξ = ξ 0 • basis 0 := by
  let w := gapOp ξ
  have error : T w = μ • ξ - w := by
    have h : w + T w = μ • ξ := eig
    rw [← h]; abel
  have bound : ‖w‖ ≤ 2*‖T w‖ := by
    simp only [error,PiLp.norm_eq_of_L1,Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    change ‖gapOp ξ x‖ ≤ 2*‖μ * ξ x - gapOp ξ x‖
    rw [diag_apply,← sub_mul,norm_mul,norm_mul,← mul_assoc]
    gcongr
    by_cases eq : x=0
    · simp [eq,excitationEnergy,flipCount]
    · have ex : ∃ t, x t ≠ 0 := by simpa [funext_iff] using eq
      have k : 1 ≤ flipCount x := Finset.card_pos.mpr (by obtain ⟨t,ht⟩ := ex; exact ⟨t,by simp [ht]⟩)
      have re := Complex.re_le_norm (excitationEnergy x-μ)
      rw [norm_sub_rev] at re
      norm_num [excitationEnergy,Complex.mul_re] at re ⊢
      have kn : (1:ℝ) ≤ flipCount x := by exact_mod_cast k
      linarith
  have zero : w=0 := by
    by_contra hw
    have h := T.le_opNorm w
    nlinarith [mul_lt_mul_of_pos_right hT (norm_pos_iff.mpr hw)]
  apply WithLp.ofLp_injective; funext x
  by_cases hx : x=0
  · simp [hx,PiLp.smul_apply]
  · have eq := congrArg (fun z : Amp S => z x) zero
    change gapOp ξ x = 0 at eq
    rw [diag_apply,mul_eq_zero] at eq
    have ex : ∃ t, x t ≠ 0 := by simpa [funext_iff] using hx
    have k : flipCount x ≠ 0 := Finset.card_ne_zero.mpr (by obtain ⟨t,ht⟩ := ex; exact ⟨t,by simp [ht]⟩)
    have ne : excitationEnergy x ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast k)
    change ξ x = ξ 0*(if x=0 then 1 else 0)
    simp [hx,eq.resolve_left ne]

end DSFTomography.SF.Cluster
