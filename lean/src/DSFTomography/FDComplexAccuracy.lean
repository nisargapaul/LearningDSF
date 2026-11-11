import DSFTomography.FDAccuracy

/-! The same accuracy bound permits complex-valued measurement errors.
The exact distinct-site Pauli correlation matrix is real. -/
noncomputable section
namespace DSFTomography.FD.ComplexAccuracy
open DSFTomography Matrix
open scoped Matrix.Norms.Frobenius
abbrev realPart (A : Tensor) : Accuracy.Mat := A.map Complex.re
abbrev imagPart (A : Tensor) : Accuracy.Mat := A.map Complex.im
def lift (A : Accuracy.Mat) : Tensor := A.map Complex.ofReal

theorem norm_sq (A : Tensor) : ‖A‖^2 = ∑ a, ∑ b, ‖A a b‖^2 := by
  change ‖WithLp.toLp 2 (fun a => WithLp.toLp 2 (fun b => A a b))‖^2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [PiLp.toLp_apply,PiLp.norm_sq_eq_of_L2]
theorem norm_split (A : Tensor) : ‖A‖^2 = ‖realPart A‖^2+‖imagPart A‖^2 := by
  simp only [norm_sq,Accuracy.norm_sq,realPart,imagPart,Matrix.map_apply,Complex.sq_norm,
    Complex.normSq_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _; ring
theorem entry_le (A : Tensor) (a b : Axis) : ‖A a b‖ ≤ ‖A‖ :=
  (PiLp.norm_apply_le (WithLp.toLp 2 (fun b => A a b)) b).trans
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun a => WithLp.toLp 2 (fun b => A a b))) a)

def halfTrace (X : Tensor) : Tensor := (X.trace/2) • 1-X
theorem halfTrace_parts (X : Tensor) :
    realPart (halfTrace X) = Accuracy.halfTrace (realPart X) ∧
    imagPart (halfTrace X) = Accuracy.halfTrace (imagPart X) := by
  constructor <;> ext a b <;> by_cases eq : a=b <;>
    simp [halfTrace,Accuracy.halfTrace,eq,Matrix.trace,Matrix.diag,
      Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,Complex.mul_im]
theorem halfTrace_bound (X : Tensor) : ‖halfTrace X‖ ≤ ‖X‖ := by
  have re := Accuracy.halfTrace_bound (realPart X)
  have im := Accuracy.halfTrace_bound (imagPart X)
  have sq := norm_split (halfTrace X)
  rw [(halfTrace_parts X).1,(halfTrace_parts X).2] at sq
  have le₁ := pow_le_pow_left₀ (norm_nonneg _) re 2
  have le₂ := pow_le_pow_left₀ (norm_nonneg _) im 2
  nlinarith [norm_split X,norm_nonneg X,norm_nonneg (halfTrace X)]

theorem lift_mul_parts (C : Accuracy.Mat) (X : Tensor) :
    realPart (lift C*X) = C*realPart X ∧ imagPart (lift C*X) = C*imagPart X ∧
    realPart (X*lift C) = realPart X*C ∧ imagPart (X*lift C) = imagPart X*C := by
  and_intros <;> ext a b <;>
    simp [lift,Matrix.mul_apply,Complex.mul_re,Complex.mul_im]
theorem lift_contracts (C : Accuracy.Mat) (left : Accuracy.Contracts C) (right : Accuracy.Contracts C.transpose) :
    (∀ X : Tensor, ‖lift C*X‖ ≤ ‖X‖) ∧ (∀ X : Tensor, ‖X*lift C‖ ≤ ‖X‖) := by
  constructor
  · intro X
    have re := pow_le_pow_left₀ (norm_nonneg _) (Accuracy.left_contract C left (realPart X)) 2
    have im := pow_le_pow_left₀ (norm_nonneg _) (Accuracy.left_contract C left (imagPart X)) 2
    have sq := norm_split (lift C*X)
    rw [(lift_mul_parts C X).1,(lift_mul_parts C X).2.1] at sq
    nlinarith [norm_split X,norm_nonneg X,norm_nonneg (lift C*X)]
  · intro X
    have re := pow_le_pow_left₀ (norm_nonneg _) (Accuracy.right_contract C right (realPart X)) 2
    have im := pow_le_pow_left₀ (norm_nonneg _) (Accuracy.right_contract C right (imagPart X)) 2
    have sq := norm_split (X*lift C)
    rw [(lift_mul_parts C X).2.2.1,(lift_mul_parts C X).2.2.2] at sq
    nlinarith [norm_split X,norm_nonneg X,norm_nonneg (X*lift C)]

theorem bond_parts (C : Tensor) (J : Accuracy.Mat) :
    realPart (bondMap C (lift J)) = Accuracy.bond (realPart C) J ∧
    imagPart (bondMap C (lift J)) = Accuracy.bond (imagPart C) J := by
  have axes (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
  constructor <;> ext a b <;> rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;>
    simp [bondMap,Accuracy.bond,lift,Fin.sum_univ_three,axisTable,Complex.mul_re,Complex.mul_im]
theorem bond_bound (C : Tensor) (J : Accuracy.Mat) (small : ∀ a b, |J a b| ≤ 1) :
    ‖bondMap C (lift J)‖ ≤ 24*‖C‖ := by
  have re := pow_le_pow_left₀ (norm_nonneg _) (Accuracy.bond_bound (realPart C) J small) 2
  have im := pow_le_pow_left₀ (norm_nonneg _) (Accuracy.bond_bound (imagPart C) J small) 2
  have sq := norm_split (bondMap C (lift J))
  rw [(bond_parts C J).1,(bond_parts C J).2] at sq
  nlinarith [norm_split C,norm_nonneg C,norm_nonneg (bondMap C (lift J))]

theorem bond_sub (C D J : Tensor) : bondMap (C-D) J = bondMap C J-bondMap D J := by
  ext a b; simp only [bondMap,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem error_formula (C F J : Tensor) (regular : C.det ≠ 0) :
    recoverBond C F-J = (1/(4*C.det)) • (C*halfTrace ((F-bondMap C J).transpose*C)) := by
  have numsub : numerator C (F-bondMap C J) = numerator C F-(8*C.det) • J := by
    have eq : numerator C (bondMap C J) = (8*C.det) • J := by
      ext a b; simpa [smul_eq_mul,mul_comm] using numerator_bondMap C J a b
    rw [← eq]
    simp [numerator,Matrix.transpose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,sub_smul,smul_sub]
    abel
  have factor (E : Tensor) : numerator C E = (2:ℂ) • (C*halfTrace (E.transpose*C)) := by
    simp only [numerator,halfTrace,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,smul_sub,smul_smul,Matrix.mul_assoc]
    ext a b; simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]; ring
  rw [factor] at numsub
  ext a b
  have eq := congrFun (congrFun numsub a) b
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at eq ⊢
  unfold recoverBond
  field_simp [regular]
  linear_combination -4*eq

/-- The manuscript bound, allowing complex noisy matrices and determinant.
Only the exact physical correlation is real. -/
theorem accuracy (C F J : Accuracy.Mat) (Chat Fhat : Tensor) (ε γ : ℝ)
    (equation : F = Accuracy.bond C J) (small : ∀ a b, |J a b| ≤ 1)
    (left : Accuracy.Contracts C) (right : Accuracy.Contracts C.transpose)
    (noise : max ‖Chat-lift C‖ ‖Fhat-lift F‖ ≤ ε) (positive : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(J a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
  have nc : ‖Chat-lift C‖ ≤ ε := (le_max_left ..).trans noise
  have nf : ‖Fhat-lift F‖ ≤ ε := (le_max_right ..).trans noise
  have ep : 0 ≤ ε := (norm_nonneg _).trans nc
  have regular : Chat.det ≠ 0 := by intro eq; simp [eq] at det; linarith
  obtain ⟨left,right⟩ := lift_contracts C left right
  have lm (X : Tensor) : ‖Chat*X‖ ≤ (1+ε)*‖X‖ := by
    have split : Chat*X = lift C*X+(Chat-lift C)*X := by noncomm_ring
    rw [split]
    calc
      _ ≤ ‖lift C*X‖+‖(Chat-lift C)*X‖ := norm_add_le _ _
      _ ≤ ‖X‖+‖Chat-lift C‖*‖X‖ := add_le_add (left X) (Matrix.frobenius_norm_mul _ _)
      _ ≤ (1+ε)*‖X‖ := by nlinarith [norm_nonneg X]
  have rm (X : Tensor) : ‖X*Chat‖ ≤ (1+ε)*‖X‖ := by
    have split : X*Chat = X*lift C+X*(Chat-lift C) := by noncomm_ring
    rw [split]
    calc
      _ ≤ ‖X*lift C‖+‖X*(Chat-lift C)‖ := norm_add_le _ _
      _ ≤ ‖X‖+‖X‖*‖Chat-lift C‖ := add_le_add (right X) (Matrix.frobenius_norm_mul _ _)
      _ ≤ (1+ε)*‖X‖ := by nlinarith [norm_nonneg X]
  let E := Fhat-bondMap Chat (lift J)
  have residual : E = (Fhat-lift F)-bondMap (Chat-lift C) (lift J) := by
    have eq : bondMap (lift C) (lift J) = lift (Accuracy.bond C J) := Accuracy.bond_complex C J
    rw [bond_sub,equation,← eq]
    dsimp [E]; abel
  have err : ‖E‖ ≤ 25*ε := by
    rw [residual]
    calc
      _ ≤ ‖Fhat-lift F‖+‖bondMap (Chat-lift C) (lift J)‖ := norm_sub_le _ _
      _ ≤ ‖Fhat-lift F‖+24*‖Chat-lift C‖ := add_le_add_left (bond_bound _ _ small) _
      _ ≤ 25*ε := by linarith
  have cap : ‖Chat*halfTrace (E.transpose*Chat)‖ ≤ 25*(1+ε)^2*ε := by
    calc
      _ ≤ (1+ε)*‖halfTrace (E.transpose*Chat)‖ := lm _
      _ ≤ (1+ε)*‖E.transpose*Chat‖ := mul_le_mul_of_nonneg_left (halfTrace_bound _) (by linarith)
      _ ≤ (1+ε)*((1+ε)*‖E‖) := mul_le_mul_of_nonneg_left (by simpa using rm E.transpose) (by linarith)
      _ ≤ 25*(1+ε)^2*ε := by nlinarith [sq_nonneg (1+ε),mul_nonneg (sq_nonneg (1+ε)) (sub_nonneg.mpr err)]
  have bound : ‖recoverBond Chat Fhat-lift J‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
    rw [error_formula _ _ _ regular,norm_smul,norm_div,norm_one,norm_mul,show ‖(4:ℂ)‖=4 by norm_num]
    change (1/(4*‖Chat.det‖))*‖Chat*halfTrace (E.transpose*Chat)‖ ≤ _
    calc
      _ ≤ (1/(4*‖Chat.det‖))*(25*(1+ε)^2*ε) := mul_le_mul_of_nonneg_left cap (by positivity)
      _ ≤ (1/(4*γ))*(25*(1+ε)^2*ε) := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) (by linarith)) (by positivity)
      _ = _ := by ring
  intro a b
  exact (entry_le (recoverBond Chat Fhat-lift J) a b).trans bound

end DSFTomography.FD.ComplexAccuracy
