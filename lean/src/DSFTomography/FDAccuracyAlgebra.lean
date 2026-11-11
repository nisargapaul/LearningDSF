import DSFTomography.Inverse
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace DSFTomography.FD.Accuracy
open Matrix
open scoped Matrix.Norms.Frobenius
abbrev Mat := Matrix Axis Axis ℝ
private theorem axes (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
private theorem cycles : (1:Axis)+1=2 ∧ (1:Axis)+2=0 ∧ (2:Axis)+1=0 ∧ (2:Axis)+2=1 := by decide

theorem norm_sq (A : Mat) : ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A i j))‖^2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [PiLp.toLp_apply,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]

theorem entry_le (A : Mat) (i j : Axis) : |A i j| ≤ ‖A‖ := by
  exact (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => A i j)) j).trans
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A i j))) i)

def halfTrace (X : Mat) : Mat := (X.trace/2) • 1-X
theorem halfTrace_sq (X : Mat) : ‖halfTrace X‖^2 = ‖X‖^2-X.trace^2/4 := by
  simp only [norm_sq,halfTrace,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.trace,Matrix.diag,Fin.sum_univ_three,Matrix.one_apply]
  norm_num (config := {decide := true}); ring
theorem halfTrace_bound (X : Mat) : ‖halfTrace X‖ ≤ ‖X‖ := by
  have eq := halfTrace_sq X
  nlinarith [sq_nonneg X.trace,norm_nonneg (halfTrace X),norm_nonneg X]

def bond (C J : Mat) : Mat := fun a b => ∑ u, ∑ v,
  J u v * ((-4*(sign a u).re*(sign v b).re)*C (third a u) (third v b))
def num (C F : Mat) : Mat := (F.transpose*C).trace • C - (2:ℝ) • (C*F.transpose*C)
def estimate (C F : Mat) : Mat := fun a b => num C F a b/(8*C.det)

theorem bond_complex (C J : Mat) :
    bondMap (C.map Complex.ofReal) (J.map Complex.ofReal) = (bond C J).map Complex.ofReal := by
  ext a b
  rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;>
    simp [bond,bondMap,Fin.sum_univ_three,axisTable,Matrix.map_apply]

set_option maxHeartbeats 8000000 in
theorem num_bond (C J : Mat) : num C (bond C J) = (8*C.det) • J := by
  ext a b
  rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;>
    norm_num (config := {decide := true}) [num,bond,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.det_fin_three,Fin.sum_univ_three,axisTable,smul_eq_mul] <;> ring

theorem bond_sub (C D J : Mat) : bond (C-D) J = bond C J-bond D J := by
  ext a b
  simp only [bond,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]
theorem num_sub (C F G : Mat) : num C (F-G) = num C F-num C G := by
  simp [num,Matrix.transpose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,sub_smul,smul_sub]
  abel

theorem error_formula (C F J : Mat) (regular : C.det ≠ 0) :
    estimate C F-J = (1/(4*C.det)) • (C*halfTrace ((F-bond C J).transpose*C)) := by
  have n := num_sub C F (bond C J)
  rw [num_bond] at n
  have factor (E : Mat) : num C E = (2:ℝ) • (C*halfTrace (E.transpose*C)) := by
    simp only [num,halfTrace,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,smul_sub,smul_smul,Matrix.mul_assoc]
    ext a b
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [factor] at n
  ext a b
  have e := congrFun (congrFun n a) b
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at e ⊢
  unfold estimate
  field_simp [regular]
  nlinarith

/-- The two Euclidean contraction inequalities supplied by a physical spin correlation. -/
def Contracts (C : Mat) : Prop :=
  ∀ v : Axis → ℝ, ∑ a, (∑ b, C a b*v b)^2 ≤ ∑ a, (v a)^2

theorem left_contract (C : Mat) (h : Contracts C) (X : Mat) : ‖C*X‖ ≤ ‖X‖ := by
  have sq : ‖C*X‖^2 ≤ ‖X‖^2 := by
    rw [norm_sq,norm_sq,Finset.sum_comm,Finset.sum_comm (f := fun i j => (X i j)^2)]
    exact Finset.sum_le_sum fun j _ => h (fun i => X i j)
  nlinarith [norm_nonneg (C*X),norm_nonneg X]

theorem right_contract (C : Mat) (h : Contracts C.transpose) (X : Mat) : ‖X*C‖ ≤ ‖X‖ := by
  have bound := left_contract C.transpose h X.transpose
  simpa [← Matrix.transpose_mul,Matrix.frobenius_norm_transpose] using bound

private theorem four_bound (u v : Fin 4 → ℝ) (small : ∀ i, |u i| ≤ 1) :
    (∑ i, u i*v i)^2 ≤ 4*∑ i, (v i)^2 := by
  have sq (i) : (u i)^2 ≤ 1 := by nlinarith [sq_abs (u i),sq_nonneg (u i),abs_nonneg (u i),small i]
  have sum : ∑ i, (u i)^2 ≤ 4 := by
    calc
      _ ≤ ∑ _ : Fin 4, (1:ℝ) := Finset.sum_le_sum fun i _ => sq i
      _ = 4 := by norm_num
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v).trans
    (mul_le_mul_of_nonneg_right sum (Finset.sum_nonneg fun i _ => sq_nonneg (v i)))

theorem bond_bound (C J : Mat) (small : ∀ a b, |J a b| ≤ 1) : ‖bond C J‖ ≤ 24*‖C‖ := by
  have row (a b : Axis) : (bond C J a b)^2 ≤ 64*
      ((C (a+1) (b+1))^2+(C (a+1) (b+2))^2+(C (a+2) (b+1))^2+(C (a+2) (b+2))^2) := by
    let u : Fin 4 → ℝ := ![J (a+2) (b+2),-J (a+2) (b+1),-J (a+1) (b+2),J (a+1) (b+1)]
    let v : Fin 4 → ℝ := ![C (a+1) (b+1),C (a+1) (b+2),C (a+2) (b+1),C (a+2) (b+2)]
    have hu (i) : |u i| ≤ 1 := by fin_cases i <;> simp [u,small]
    have bound := four_bound u v hu
    have formula : bond C J a b = 4*∑ i, u i*v i := by
      rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;>
        norm_num [bond,u,v,Fin.sum_univ_three,Fin.sum_univ_succ,axisTable,cycles] <;> ring
    rw [formula]
    norm_num [Fin.sum_univ_succ,u,v] at bound ⊢
    nlinarith
  have all := Finset.sum_le_sum (s := Finset.univ) fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) fun b _ => row a b
  have cap : ‖bond C J‖^2 ≤ 256*‖C‖^2 := by
    rw [norm_sq,norm_sq]
    convert all using 1
    norm_num [Fin.sum_univ_three,cycles]; ring
  nlinarith [norm_nonneg C,norm_nonneg (bond C J)]

/-- Accuracy corollary with exactly the manuscript constant. The two
contraction hypotheses are discharged for physical Pauli correlations below. -/
theorem accuracy (C F J Chat Fhat : Mat) (ε γ : ℝ)
    (equation : F = bond C J) (small : ∀ a b, |J a b| ≤ 1)
    (left : Contracts C) (right : Contracts C.transpose)
    (noise : max ‖Chat-C‖ ‖Fhat-F‖ ≤ ε) (positive : 0 < γ) (det : γ ≤ |Chat.det|) :
    ∀ a b, |estimate Chat Fhat a b-J a b| ≤ 25*(1+ε)^2/(4*γ)*ε := by
  have nc : ‖Chat-C‖ ≤ ε := (le_max_left ..).trans noise
  have nf : ‖Fhat-F‖ ≤ ε := (le_max_right ..).trans noise
  have ep : 0 ≤ ε := (norm_nonneg _).trans nc
  have regular : Chat.det ≠ 0 := by intro eq; simp [eq] at det; linarith
  have lm (X : Mat) : ‖Chat*X‖ ≤ (1+ε)*‖X‖ := by
    have split : Chat*X = C*X+(Chat-C)*X := by noncomm_ring
    rw [split]
    calc
      _ ≤ ‖C*X‖+‖(Chat-C)*X‖ := norm_add_le _ _
      _ ≤ ‖X‖+‖Chat-C‖*‖X‖ := add_le_add (left_contract C left X) (Matrix.frobenius_norm_mul _ _)
      _ ≤ (1+ε)*‖X‖ := by nlinarith [norm_nonneg X]
  have rm (X : Mat) : ‖X*Chat‖ ≤ (1+ε)*‖X‖ := by
    have split : X*Chat = X*C+X*(Chat-C) := by noncomm_ring
    rw [split]
    calc
      _ ≤ ‖X*C‖+‖X*(Chat-C)‖ := norm_add_le _ _
      _ ≤ ‖X‖+‖X‖*‖Chat-C‖ := add_le_add (right_contract C right X) (Matrix.frobenius_norm_mul _ _)
      _ ≤ (1+ε)*‖X‖ := by nlinarith [norm_nonneg X]
  let E := Fhat-bond Chat J
  have residual : E = (Fhat-F)-bond (Chat-C) J := by rw [bond_sub,equation]; dsimp [E]; abel
  have err : ‖E‖ ≤ 25*ε := by
    rw [residual]
    calc
      _ ≤ ‖Fhat-F‖+‖bond (Chat-C) J‖ := norm_sub_le _ _
      _ ≤ ‖Fhat-F‖+24*‖Chat-C‖ := add_le_add_left (bond_bound _ _ small) _
      _ ≤ 25*ε := by linarith
  have cap : ‖Chat*halfTrace (E.transpose*Chat)‖ ≤ 25*(1+ε)^2*ε := by
    calc
      _ ≤ (1+ε)*‖halfTrace (E.transpose*Chat)‖ := lm _
      _ ≤ (1+ε)*‖E.transpose*Chat‖ := mul_le_mul_of_nonneg_left (halfTrace_bound _) (by linarith)
      _ ≤ (1+ε)*((1+ε)*‖E‖) := mul_le_mul_of_nonneg_left (by simpa using rm E.transpose) (by linarith)
      _ ≤ 25*(1+ε)^2*ε := by nlinarith [sq_nonneg (1+ε),mul_nonneg (sq_nonneg (1+ε)) (sub_nonneg.mpr err)]
  have bound : ‖estimate Chat Fhat-J‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
    rw [error_formula _ _ _ regular,norm_smul,Real.norm_eq_abs,abs_div,abs_one,abs_mul,show |(4:ℝ)|=4 by norm_num]
    change (1/(4*|Chat.det|))*‖Chat*halfTrace (E.transpose*Chat)‖ ≤ _
    have denom : 0 < 4*|Chat.det| := by positivity
    have denγ : 0 < 4*γ := by positivity
    calc
      _ ≤ (1/(4*|Chat.det|))*(25*(1+ε)^2*ε) := mul_le_mul_of_nonneg_left cap (by positivity)
      _ ≤ (1/(4*γ))*(25*(1+ε)^2*ε) := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le denγ (by linarith)) (by positivity)
      _ = _ := by ring
  intro a b
  exact (entry_le (estimate Chat Fhat-J) a b).trans bound

end DSFTomography.FD.Accuracy
