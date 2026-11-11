import DSFTomography.SFPaperDSF

/-! Identify the cyclic field-frame matrices with the laboratory Hamiltonian
and its spin probes by an explicit on-site unitary, including the sign of Y. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Matrix
variable {S : Type*} [Fintype S] [DecidableEq S]

private def turn : Qubit :=
  (1/2:ℂ) • !![1-Complex.I,-1-Complex.I;1-Complex.I,1+Complex.I]

private theorem turn_unit : turn.conjTranspose*turn = 1 ∧ turn*turn.conjTranspose = 1 := by
  constructor <;> ext x y <;> fin_cases x <;> fin_cases y <;> apply Complex.ext <;>
    norm_num [turn,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,
      Complex.mul_re,Complex.mul_im]

private theorem turn_spin (a : Axis) : turn*pauli (some a)*turn.conjTranspose = pauli (some (a+1)) := by
  rcases (show a=0 ∨ a=1 ∨ a=2 by fin_cases a <;> decide) with rfl|rfl|rfl <;> ext x y <;> fin_cases x <;> fin_cases y <;> apply Complex.ext <;>
    norm_num [turn,pauliValues,Matrix.vecMul,dotProduct,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_two,
      Complex.mul_re,Complex.mul_im,show (2:Axis)+1=0 by decide,show (1:Axis)+1=2 by decide]

/-- Rotation taking chart spin X,Y,Z to laboratory axes i+1,i+2,i. -/
private def localFrame (i : Axis) : Qubit := ![turn,turn*turn,1] i

private theorem local_unit (i : Axis) : (localFrame i).conjTranspose*(localFrame i) = 1 ∧
    localFrame i*(localFrame i).conjTranspose = 1 := by
  fin_cases i <;> simp [localFrame,Matrix.conjTranspose_mul,Matrix.mul_assoc,turn_unit]
  constructor
  · rw [← Matrix.mul_assoc turn.conjTranspose turn,turn_unit.1,one_mul,turn_unit.1]
  · rw [← Matrix.mul_assoc turn turn.conjTranspose,turn_unit.2,one_mul,turn_unit.2]

private theorem local_spin (i a : Axis) :
    localFrame i*pauli (some a)*(localFrame i).conjTranspose = pauli (some (axisInLab i a)) := by
  have axes (i : Axis) : axisInLab i a = a+(i+1) := by fin_cases i <;> fin_cases a <;> decide
  fin_cases i
  · simpa [localFrame,axes] using turn_spin a
  · change turn*turn*pauli (some a)*(turn*turn).conjTranspose = _
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc turn turn,← Matrix.mul_assoc _ turn.conjTranspose,
      Matrix.mul_assoc turn,turn_spin,turn_spin,axes]
    congr 2
    fin_cases a <;> decide
  · simp [localFrame,axes,show (2:Axis)+1=0 by decide]

def toLab (i : Axis) : Op (Config S) := tensor (fun _ : S => localFrame i)

omit [DecidableEq S] in
private theorem toLab_star (i : Axis) : (toLab (S := S) i).conjTranspose =
    tensor (fun _ : S => (localFrame i).conjTranspose) := by
  ext x y
  simp [toLab,Matrix.conjTranspose_apply,tensor,star_prod]

theorem toLab_unit (i : Axis) : (toLab (S := S) i).conjTranspose*toLab i=1 ∧
    toLab i*(toLab (S := S) i).conjTranspose=1 := by
  have one : tensor (fun _ : S => (1:Qubit))=1 := by
    ext x y; simp [tensor,Matrix.one_apply,Fintype.prod_ite_zero,funext_iff]
  rw [toLab_star]
  simp only [toLab,tensor_mul,(local_unit i).1,(local_unit i).2,one,and_self]

theorem toLab_probe (i : Axis) (r : S) (a : Axis) :
    toLab i*spinAt r a*(toLab i).conjTranspose = spinAt r (axisInLab i a) := by
  rw [toLab_star]
  simp only [toLab,spinAt,word,tensor_mul]
  congr 1; funext t
  by_cases h : t=r <;> simp [oneLabel,h,pauliValues,local_spin,local_unit]

variable [AddCommGroup S]
set_option maxHeartbeats 1000000 in
theorem toLab_interaction (V : Volume S) (i : Axis) :
    toLab i*fieldFrame V i*(toLab i).conjTranspose = qubitH V.R V.h V.J := by
  let T := toLab (S := S) i
  let cyc : Axis ≃ Axis := Equiv.addRight (i+1)
  have axis (a : Axis) : axisInLab i a = cyc a := by fin_cases i <;> fin_cases a <;> decide
  have prod (A C : Op (Config S)) : T*(A*C)*T.conjTranspose = (T*A*T.conjTranspose)*(T*C*T.conjTranspose) := by
    symm
    calc
      _ = T*A*(T.conjTranspose*T)*C*T.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [(toLab_unit i).1,Matrix.mul_one,Matrix.mul_assoc T A C]
  have geom (r : S) (a : Axis) : (qubitSpins (1:(Op (Config S))ˣ)).σ r a = spinAt r a := by
    simp [qubitSpins,string,inBasis,spinAt]
  change T*fieldFrame V i*T.conjTranspose = _
  simp only [fieldFrame,qubitH,realH,H,geom,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  · apply Finset.sum_congr rfl; intro r _
    simp only [T,toLab_probe,axis]
    exact cyc.sum_comp (fun a => (V.h a:ℂ) • spinAt r a)
  · apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro r _
    have pair (a b : Axis) : T*(spinAt r a*spinAt (r+d) b)*T.conjTranspose =
        spinAt r (cyc a)*spinAt (r+d) (cyc b) := by rw [prod]; simp only [T,toLab_probe,axis]
    simp only [pair,axis]
    have inner (a : Axis) : (∑ b, (V.J d (cyc a) (cyc b):ℂ) • (spinAt r (cyc a)*spinAt (r+d) (cyc b))) =
        ∑ b, (V.J d (cyc a) b:ℂ) • (spinAt r (cyc a)*spinAt (r+d) b) :=
      cyc.sum_comp (fun b => (V.J d (cyc a) b:ℂ) • (spinAt r (cyc a)*spinAt (r+d) b))
    simp_rw [inner]
    exact cyc.sum_comp (fun a => ∑ b, (V.J d a b:ℂ) • (spinAt r a*spinAt (r+d) b))

theorem toLab_driven (R : Bonds S) (i : Axis) {B : ℝ} (hB : 0 < B) (p : Params R.dirs) :
    toLab i*((B:ℂ) • unitHamiltonian R i (B⁻¹ • p))*(toLab i).conjTranspose =
      let W := driven (withParams R p) B i
      ((B:ℂ)*Fintype.card S) • (1:Op (Config S)) + qubitH W.R W.h W.J := by
  dsimp only
  rw [driven_frame i hB,Matrix.mul_add,Matrix.mul_add,Matrix.add_mul,Matrix.add_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,(toLab_unit i).2,toLab_interaction,driven_matrix]
  have iz : axisInLab i 2 = i := rfl
  simp [zeeman,Matrix.mul_sum,Matrix.sum_mul,toLab_probe,iz,add_assoc]

end DSFTomography.SF
