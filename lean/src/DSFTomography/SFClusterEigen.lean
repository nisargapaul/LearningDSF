import DSFTomography.SFClusterDressing

/-! The finite-volume cluster fixed point gives an exact eigenket. All
extensive terms cancel before estimating perturbations on excited columns. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT NormedSpace
variable {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
private abbrev O := Operator S

theorem translation_flip (r : S) (x : Config S) :
    translateAmp r * flip x = flip (translated r x) * translateAmp r := by
  apply operator_ext; intro y
  simp only [ContinuousLinearMap.mul_apply,translate_basis,flip_basis]; rfl

theorem translation_convolute (r : S) (v : Amp S) :
    translateAmp r * convolute v = convolute (translateAmp r v) * translateAmp r := by
  conv_rhs => rw [← sum_basis v,map_sum,map_sum]
  change translateAmp r * (∑ x, v x • flip x) = _
  apply operator_ext; intro y
  simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,map_sum,map_smul,translate_basis,convolution_basis,flip_basis]; rfl

def orbit (v : Amp S) := ∑ t : S, translateAmp t v
private theorem orbit_shift (s : S) (v : Amp S) : orbit (translateAmp s v) = orbit v := by
  have tr (t : S) : translateAmp t (translateAmp s v) = translateAmp (t+s) v := by
    conv_lhs => rw [← sum_basis v]
    conv_rhs => rw [← sum_basis v]
    simp [translate_basis,translated_add]
  simp only [orbit,tr]
  exact Equiv.sum_comp (Equiv.addRight s) (fun t => translateAmp t v)

omit [DecidableEq S] in
theorem sum_sign (x : Config S) :
    (∑ t : S, (phase [0] (translated t x) - 1)) = -2*(flipCount x : ℂ) := by
  let e := Equiv.neg S
  have reindex := Equiv.sum_comp e (fun t => if x t=0 then (0:ℂ) else -2)
  have count : (∑ t : S, if x t=0 then (0:ℂ) else -2) = -2*(flipCount x : ℂ) := by
    simp [flipCount,← Finset.sum_boole, Finset.mul_sum,mul_ite]
  calc
    _ = ∑ t : S, (if x (e t)=0 then (0:ℂ) else -2) := by
      apply Finset.sum_congr rfl; intro t _
      simp only [phase,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,translated,zero_sub]
      change (if x (-t)=0 then (1:ℂ) else -1)-1 = if x (-t)=0 then 0 else -2
      split <;> norm_num
    _ = _ := reindex.trans count

theorem orbit_response (v : Amp S) :
    orbit (response [0] v) = -orbit v + (Fintype.card S : ℂ) • (v 0 • basis 0) := by
  let T : Operator S := ∑ r : S, translateAmp r
  have TV (w) : T w = orbit w := ContinuousLinearMap.sum_apply ..
  have single (x : Config S) : T (response [0] (basis x)) =
      - T (basis x) + (Fintype.card S : ℂ) • ((basis x 0) • basis 0) := by
    rw [response,columns_basis,responseColumn,map_smul,map_sum]
    have same (r : S) : T (basis (translated r x)) = T (basis x) := by
      rw [← translate_basis,TV,TV]; exact orbit_shift .. 
    simp only [map_smul,same,← Finset.sum_smul,sum_sign,smul_smul]
    by_cases hx : x=0
    · subst x
      have T0 : T (basis 0) = (Fintype.card S : ℂ) • basis 0 := by
        simp only [TV,orbit,translate_basis,show ∀ r : S, translated r (0:Config S)=0 from fun _ => rfl,
          Finset.sum_const,Finset.card_univ,Nat.cast_smul_eq_nsmul]
      simp [flipCount,basis_at,T0]
    · have existsSite : ∃ t, x t ≠ 0 := by simpa [funext_iff] using hx
      have size : flipCount x ≠ 0 := Finset.card_ne_zero.mpr (by
        obtain ⟨t,ht⟩ := existsSite; exact ⟨t,by simp [ht]⟩)
      rw [basis_at,if_neg (Ne.symm hx),mul_zero,zero_smul,add_zero]
      have fact : (2*(flipCount x:ℂ))⁻¹ * (-2*flipCount x) = -1 := by
        field_simp [show (flipCount x : ℂ) ≠ 0 by exact_mod_cast size]
      rw [fact,neg_one_smul]
  rw [← TV,← TV]
  conv_lhs => rw [← sum_basis v,map_sum,map_sum]
  simp only [map_smul,single,smul_add,smul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  congr 1
  · simp_rw [← map_smul,← map_sum,sum_basis]
  · simp only [basis_at,ite_smul,one_smul,zero_smul,smul_ite,smul_zero]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]; exact smul_comm ..

def ampExp (v : Amp S) := exp ℂ (convolute v) (basis 0)

def pauliOp (x : Config S) (D : List S) := flip x * signOp D

/-- The propagated spin-flip cluster ket in the ordinary polarized basis. -/
def eigenKet (v : Amp S) := ampExp (generator v)

private theorem intertwine_word (x : Config S) (D : List S) (v : Amp S) :
    pauliOp x D * exp ℂ (convolute (generator v)) =
      exp ℂ (convolute (generator v)) * (flip x * exp ℂ (convolute (response D v)) * signOp D) := by
  let K := convolute (generator v)
  have comm : Commute (flip x) (exp ℂ K) :=
    ((convolution_basis x) ▸ convolution_comm (basis x) (generator v)).exp_right ℂ
  have sign := exp_intertwine (sign_convolve D (generator v))
  have add : K + convolute (response D v) = convolute (signOp D (generator v)) := by
    rw [response_eq,map_sub]; abel
  have eq := exp_add_of_commute (𝕂 := ℂ) (convolution_comm (generator v) (response D v))
  rw [← add,eq] at sign
  simp only [pauliOp, mul_assoc,sign]
  change flip x * (exp ℂ K * _) = exp ℂ K * (flip x * _)
  rw [← mul_assoc,comm.eq,mul_assoc]

theorem word_eigenKet (x : Config S) (D : List S) (v : Amp S) :
    pauliOp x D (eigenKet v) =
      exp ℂ (convolute (generator v)) (flip x (ampExp (response D v))) := by
  have h := congrArg (fun A : Operator S => A (basis 0)) (intertwine_word x D v)
  simpa [ContinuousLinearMap.mul_apply,eigenKet,ampExp] using h

theorem ket_nonzero (v : Amp S) : eigenKet v ≠ 0 := by
  intro h
  let K := convolute (generator v)
  have h' := congrArg (fun w : Amp S => (exp ℂ (-K)) w) h
  have eq : exp ℂ (-K)*exp ℂ K = 1 := by rw [← exp_add_of_commute (Commute.refl K).neg_left]; simp
  change (exp ℂ (-K)*exp ℂ K) (basis 0) = exp ℂ (-K) (0 : Amp S) at h'
  rw [eq,map_zero] at h'
  have q := congrArg norm h'
  simp at q

theorem translate_commutes (t : S) (v : Amp S) : Commute (translateAmp t) (exp ℂ (convolute (generator v))) := by
  apply Commute.exp_right
  exact (translation_convolute t (generator v)).trans (by rw [generator_invariant])

@[simp] theorem ket_invariant (t : S) (v : Amp S) : translateAmp t (eigenKet v) = eigenKet v := by
  have h := congrArg (fun L : Operator S => L (basis 0)) (translate_commutes t v).eq
  simpa [ContinuousLinearMap.mul_apply,eigenKet,ampExp,
    show translated t (0:Config S) = 0 from rfl] using h

/-- Sum over lattice translates of one interaction in the field frame. -/
def periodicTerm (A : Config S) (D : List S) : Operator S :=
  ∑ r : S, translateAmp r * pauliOp A D * translateAmp (-r)

theorem periodicTerm_ket (A : Config S) (D : List S) (v : Amp S) :
    periodicTerm A D (eigenKet v) =
      exp ℂ (convolute (generator v)) (orbit (flip A (ampExp (response D v)))) := by
  simp only [periodicTerm,ContinuousLinearMap.sum_apply,ContinuousLinearMap.mul_apply,ket_invariant,
    word_eigenKet,orbit,map_sum]
  apply Finset.sum_congr rfl; intro r _
  exact congrArg (fun L : Operator S => L _) (translate_commutes r v).eq

variable {J : Type*} [Fintype J]
/-- Vacuum-shifted polarizing field and a finite list of Pauli interactions.
The complex source includes the phase i for each Y. -/
def clusterH (A : J → Config S) (D : J → List S) (p : J → ℂ) : Operator S :=
  (Fintype.card S : ℂ) • 1 - periodicTerm 0 [0] + ∑ j, p j • periodicTerm (A j) (D j)

omit [AddCommGroup S] in
theorem flip_zero : flip (0 : Config S) = 1 := by
  apply operator_ext; intro x; simp

def FiniteEquation (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S) : Prop :=
  v = ampExp (response [0] v) - basis 0 - response [0] v -
      ∑ j, p j • flip (A j) (ampExp (response (D j) v))

theorem vacuum_balance (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S)
    (sol : FiniteEquation A D p v) : (Fintype.card S : ℂ) • basis 0 - orbit (ampExp (response [0] v)) +
        ∑ j, p j • orbit (flip (A j) (ampExp (response (D j) v))) =
        (-(Fintype.card S : ℂ)*v 0) • basis 0 := by
  let T : Operator S := ∑ t : S, translateAmp t
  have TV (w : Amp S) : orbit w = T w := (ContinuousLinearMap.sum_apply ..).symm
  have T0 : T (basis 0) = (Fintype.card S : ℂ) • basis 0 := by
    simp only [T,ContinuousLinearMap.sum_apply,translate_basis,show ∀ r : S, translated r (0:Config S)=0 from fun _ => rfl,
      Finset.sum_const,Finset.card_univ,Nat.cast_smul_eq_nsmul]
  have ht := congrArg T (show v = _ from sol)
  simp only [map_sub,map_sum,map_smul,T0] at ht
  simp only [← TV,orbit_response] at ht

  rw [neg_mul,neg_smul,← smul_smul]
  have cancelEq (o a b c d : Amp S)
      (h : o = a - b - (-o + d) - c) : b - a + c = -d := by
    calc b-a+c = b-a+c + (o-o) := by abel
         _ = b-a+c + ((a-b-(-o+d)-c)-o) := by nth_rw 1 [h]
         _ = -d := by abel
  exact cancelEq (orbit v) _ _ _ _ ht

/-- The energy shift per site is minus the vacuum coefficient of the
solution. No approximation or volume-dependent remainder enters here. -/
theorem exact_eigenpair (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S)
    (sol : FiniteEquation A D p v) :
    eigenKet v ≠ 0 ∧ clusterH A D p (eigenKet v) =
      (- (Fintype.card S : ℂ) * v 0) • eigenKet v := by
  refine ⟨ket_nonzero _,?_⟩
  let U : Operator S := exp ℂ (convolute (generator v))
  have cancel := vacuum_balance A D p v sol
  simp only [clusterH,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    periodicTerm_ket,flip_zero]
  exact (by simpa [U,map_sum,eigenKet,ampExp] using congrArg U cancel)

end DSFTomography.SF.Cluster
