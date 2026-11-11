import DSFTomography.SFSixFrame
import DSFTomography.DSFPhysical

/-! Lift the explicit spin rotations to the many-spin laboratory Hamiltonian.
The tilted experiment changes the applied field and probe direction, not the
unknown Hamiltonian. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Matrix
variable {S : Type*} [Fintype S] [DecidableEq S]

private def atSite (r : S) : Qubit →ₗ[ℂ] Op (Config S) where
  toFun A x y := if ∀ s ≠ r, x s=y s then A (x r) (y r) else 0
  map_add' A B := by
    ext x y
    change (if ∀ s ≠ r, x s=y s then A (x r) (y r)+B (x r) (y r) else 0) =
      (if ∀ s ≠ r, x s=y s then A (x r) (y r) else 0)+
      (if ∀ s ≠ r, x s=y s then B (x r) (y r) else 0)
    split_ifs <;> simp
  map_smul' c A := by ext x y; split_ifs <;> simp_all

private theorem atSite_tensor (r : S) (A : Qubit) :
    atSite r A = tensor (fun s => if s=r then A else 1) := by
  ext x y
  change (if ∀ s ≠ r, x s=y s then _ else _) = ∏ s, _
  split_ifs with outside
  · rw [Finset.prod_eq_single r]
    · simp
    · intro s _ ne; simp [ne,Matrix.one_apply,outside s ne]
    · simp
  · push_neg at outside
    obtain ⟨s,ne,diff⟩ := outside
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (by simp [ne,Matrix.one_apply_ne diff])).symm

private theorem atSite_pauli (r : S) (a : Axis) : atSite r (pauli (some a)) = spinAt r a := by
  ext x y
  exact (word_one r a x y).symm

def labFrame (t : Pair) : Op (Config S) := tensor (fun _ : S => qubitFrame t)

private theorem labFrame_star (t : Pair) : (labFrame (S := S) t).conjTranspose =
    tensor (fun _ : S => (qubitFrame t).conjTranspose) := by
  ext x y; simp [labFrame,Matrix.conjTranspose_apply,tensor,star_prod]

theorem labFrame_unit (t : Pair) : (labFrame (S := S) t).conjTranspose*labFrame t=1 ∧
    labFrame t*(labFrame (S := S) t).conjTranspose=1 := by
  have one : tensor (fun _ : S => (1:Qubit))=1 := by
    ext x y; simp [tensor,Matrix.one_apply,Fintype.prod_ite_zero,funext_iff]
  rw [labFrame_star]
  simp only [labFrame,tensor_mul,(qubitFrame_unit t).1,(qubitFrame_unit t).2,one,and_self]

/-- The laboratory probe along a frame column is its literal Pauli combination. -/
theorem labFrame_probe (t : Pair) (r : S) (a : Axis) :
    labFrame t*spinAt r a*(labFrame t).conjTranspose =
      ∑ b : Axis, (frame t b a:ℂ) • spinAt r b := by
  rw [← atSite_pauli,atSite_tensor,labFrame_star]
  simp only [labFrame,tensor_mul]
  have eq : (fun s : S => qubitFrame t*(if s=r then pauli (some a) else 1)*(qubitFrame t).conjTranspose) =
      (fun s => if s=r then ∑ b : Axis, (frame t b a:ℂ) • pauli (some b) else 1) := by
    funext s; by_cases h : s=r <;> simp [h,qubitFrame_spin,qubitFrame_unit]
  rw [eq,← atSite_tensor,map_sum]
  simp only [map_smul,atSite_pauli]

/-- The transport is a unitary change of basis in the full Hilbert space. -/
def labUnit (t : Pair) : (Op (Config S))ˣ where
  val := labFrame t
  inv := (labFrame t).conjTranspose
  val_inv := (labFrame_unit t).2
  inv_val := (labFrame_unit t).1

/-- A linear combination in laboratory coordinates, represented in the
measurement frame. -/
def backProbe (t : Pair) (r : S) (b : Axis) : Op (Config S) :=
  ∑ a : Axis, (frame t b a:ℂ) • spinAt r a

theorem labFrame_backProbe (t : Pair) (r : S) (b : Axis) :
    inBasis (labUnit t) (backProbe t r b)=spinAt r b := by
  have orth (c : Axis) : ∑ a, frame t b a*frame t c a = if b=c then 1 else 0 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using
      congrFun (congrFun (frame_orthogonal t).2 b) c
  change labFrame t * backProbe t r b * (labFrame t).conjTranspose = spinAt r b
  simp only [backProbe,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.mul_smul,Matrix.smul_mul,labFrame_probe,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,← Complex.ofReal_mul,← Complex.ofReal_sum,orth]
  simp

theorem inverse_probe (t : Pair) (r : S) (b : Axis) :
    inBasis (labUnit t)⁻¹ (spinAt r b)=backProbe t r b := by
  rw [← labFrame_backProbe t r b]
  simp [inBasis,Matrix.mul_assoc]

variable [AddCommGroup S]

def rotatedField (t : Pair) (h : Axis → ℝ) : Axis → ℝ :=
  fun a => ∑ u, frame t u a*h u

def rotatedExchange (t : Pair) (J : S → Matrix Axis Axis ℝ) : S → Matrix Axis Axis ℝ :=
  fun d a b => ∑ u, ∑ v, frame t u a*J d u v*frame t v b

private theorem linear_change (t : Pair) (h : Axis → ℝ) (A : Axis → Op (Config S)) :
    (∑ a, (∑ u, frame t u a*h u:ℝ) • A a) =
      ∑ u, h u • ∑ a, frame t u a • A a := by
  simp only [Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

set_option maxHeartbeats 1000000 in
/-- Literal laboratory Hamiltonian covariance, including every independent
oriented exchange entry. -/
theorem Hamiltonian_rotation (R : Bonds S) (t : Pair) (h : Axis → ℝ)
    (J : S → Matrix Axis Axis ℝ) :
    qubitH R (rotatedField t h) (rotatedExchange t J) =
      inBasis (labUnit t)⁻¹ (qubitH R h J) := by
  have geom (r : S) (a : Axis) : (qubitSpins (1:(Op (Config S))ˣ)).σ r a=spinAt r a := by
    simp [qubitSpins,string,inBasis,spinAt]
  simp only [qubitH,realH,H,geom,inBasis,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  change (∑ r, ∑ a, (rotatedField t h a:ℂ) • spinAt r a)+
    (∑ d ∈ R.dirs, ∑ r, ∑ a, ∑ b, (rotatedExchange t J d a b:ℂ) • (spinAt r a*spinAt (r+d) b)) =
    (∑ r, ∑ a, (h a:ℂ) • inBasis (labUnit t)⁻¹ (spinAt r a))+
    (∑ d ∈ R.dirs, ∑ r, ∑ a, ∑ b, (J d a b:ℂ) • inBasis (labUnit t)⁻¹ (spinAt r a*spinAt (r+d) b))
  simp only [← inBasis_mul,inverse_probe,backProbe]
  congr 1
  · apply Finset.sum_congr rfl; intro r _
    simpa only [rotatedField,Complex.real_smul] using linear_change t h (spinAt r)
  · apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro r _
    simp only [rotatedExchange,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_smul,
      Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    congr 1
    ring

/-- The actual tilted experiment: the unknown Hamiltonian is unchanged. -/
def tiltedVolume (V : Volume S) (t : Pair) (B : ℝ) : Volume S :=
  {V with h := fun a => V.h a-B*frame t a 2}

def rotatedVolume (V : Volume S) (t : Pair) : Volume S :=
  {R := V.R, h := rotatedField t V.h, J := rotatedExchange t V.J}

theorem rotate_withParams (R : Bonds S) (p : Params R.dirs) (t : Pair) :
    rotatedVolume (withParams R p) t = withParams R (rotate t p) := by
  have ex : rotatedExchange t (withParams R p).J=(withParams R (rotate t p)).J := by
    funext d a b
    by_cases hd : d∈R.dirs <;> simp [rotatedExchange,withParams,rotate,hd]
  exact congrArg (fun J => ({R:=R,h:=rotatedField t p.1,J:=J}:Volume S)) ex

theorem rotated_driven (t : Pair) (h : Axis → ℝ) (B : ℝ) :
    rotatedField t (fun a => h a-B*frame t a 2) =
      fun a => rotatedField t h a-if a=2 then B else 0 := by
  funext a
  have orth : ∑ u, frame t u a*frame t u 2 = if a=2 then 1 else 0 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using
      congrFun (congrFun (frame_orthogonal t).1 a) 2
  simp only [rotatedField,mul_sub,Finset.sum_sub_distrib]
  congr 1
  simp_rw [mul_left_comm (frame t _ a) B,← Finset.mul_sum,orth]
  split_ifs <;> simp

theorem tiltedHamiltonian (V : Volume S) (t : Pair) (B : ℝ) :
    let W := driven (rotatedVolume V t) B 2
    inBasis (labUnit t)⁻¹ (qubitH (tiltedVolume V t B).R (tiltedVolume V t B).h (tiltedVolume V t B).J) =
      qubitH W.R W.h W.J := by
  dsimp only
  rw [← Hamiltonian_rotation]
  simp only [tiltedVolume,rotatedVolume,driven,rotated_driven]

/-- The frame-column probe is a single diagonal polarization direction. -/
def laboratoryProbe (t : Pair) (r : S) (a : Axis) : Op (Config S) :=
  ∑ b : Axis, (frame t b a:ℂ) • spinAt r b

theorem inverse_laboratoryProbe (t : Pair) (r : S) (a : Axis) :
    inBasis (labUnit t)⁻¹ (laboratoryProbe t r a)=spinAt r a := by
  rw [laboratoryProbe,← labFrame_probe]
  change inBasis (labUnit t)⁻¹ (inBasis (labUnit t) (spinAt r a)) = _
  simp [inBasis,Matrix.mul_assoc]

def tiltedBasis (V : Volume S) (t : Pair) (B : ℝ) : (Op (Config S))ˣ :=
  let W := driven (rotatedVolume V t) B 2
  energyBasis W.R W.h W.J*(labUnit t)⁻¹

private theorem compose_basis (U V : (Op (Config S))ˣ) (A : Op (Config S)) :
    inBasis (U*V) A=inBasis U (inBasis V A) := by
  simp [inBasis,Matrix.mul_assoc]

/-- The transported basis diagonalizes the literal tilted laboratory
Hamiltonian, with precisely the energies used in the certified DSF. -/
theorem tilted_diagonalized (V : Volume S) (t : Pair) (B : ℝ) :
    let L := tiltedVolume V t B
    let W := driven (rotatedVolume V t) B 2
    inBasis (tiltedBasis V t B) (qubitH L.R L.h L.J)=
      Matrix.diagonal (fun j => (energies W.R W.h W.J j:ℂ)) := by
  dsimp only
  rw [tiltedBasis,compose_basis,tiltedHamiltonian]
  exact (rotate_H _ _ _ _).symm.trans (diagonalized _ _ _)

theorem tilted_probe_in_basis (V : Volume S) (t : Pair) (B : ℝ) (r : S) (a : Axis) :
    let W := driven (rotatedVolume V t) B 2
    inBasis (tiltedBasis V t B) (laboratoryProbe t r a)=
      (qubitSpins (energyBasis W.R W.h W.J)).σ r a := by
  dsimp only
  rw [tiltedBasis,compose_basis,inverse_laboratoryProbe]
  rfl

/-- Equality of complete Lehmann spectra, not just their leading moments.
For a=b this is one diagonal laboratory polarization channel. -/
theorem tilted_Lehmann (V : Volume S) (t : Pair) (B : ℝ) (r s : S) (a b : Axis) :
    let W := driven (rotatedVolume V t) B 2
    Spectral.lehmann (pureWeight (lowest W)) (energies W.R W.h W.J)
      (inBasis (tiltedBasis V t B) (laboratoryProbe t r a))
      (inBasis (tiltedBasis V t B) (laboratoryProbe t s b)) =
    Spectral.lehmann (pureWeight (lowest W)) (energies W.R W.h W.J)
      ((qubitSpins (energyBasis W.R W.h W.J)).σ r a)
      ((qubitSpins (energyBasis W.R W.h W.J)).σ s b) := by
  simp only [tilted_probe_in_basis]

private theorem inverse_star (t : Pair) (A : Op (Config S)) :
    inBasis (labUnit t)⁻¹ A.conjTranspose=(inBasis (labUnit t)⁻¹ A).conjTranspose := by
  change (labFrame t).conjTranspose*A.conjTranspose*labFrame t =
    ((labFrame t).conjTranspose*A*labFrame t).conjTranspose
  simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- The normalized laboratory state used in the tilted spectral sum. -/
def tiltedState (V : Volume S) (t : Pair) (B : ℝ) : State (Config S) :=
  let W := driven (rotatedVolume V t) B 2
  let ρ := eigenState W (lowest W)
  {ev := ρ.ev.comp ({
      toFun := inBasis (labUnit t)⁻¹
      map_add' A C := by simp [inBasis,Matrix.mul_add,Matrix.add_mul]
      map_smul' c A := by simp [inBasis] } : Op (Config S) →ₗ[ℂ] Op (Config S))
   normed := by
      change ρ.ev (inBasis (labUnit t)⁻¹ 1)=1
      simpa [inBasis] using ρ.normed
   cs A C := by
      have h := ρ.cs (inBasis (labUnit t)⁻¹ A) (inBasis (labUnit t)⁻¹ C)
      simpa only [LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk,← inverse_star,inBasis_mul] using h}

/-- The state in the tilted DSF is a ground state of the literal laboratory
Hamiltonian, not of a different member of the family. -/
theorem tiltedState_ground (V : Volume S) (t : Pair) (B : ℝ) :
    (tiltedState V t B).Ground
      (qubitH (tiltedVolume V t B).R (tiltedVolume V t B).h (tiltedVolume V t B).J) := by
  let W := driven (rotatedVolume V t) B 2
  let L := qubitH (tiltedVolume V t B).R (tiltedVolume V t B).h (tiltedVolume V t B).J
  have sub (A C : Op (Config S)) : inBasis (labUnit t)⁻¹ (A-C)=
      inBasis (labUnit t)⁻¹ A-inBasis (labUnit t)⁻¹ C := by
    simp [inBasis,Matrix.mul_sub,Matrix.sub_mul]
  intro A
  have h := eigenState_ground W (lowest W) (lowest_le W) (inBasis (labUnit t)⁻¹ A)
  rw [← tiltedHamiltonian V t B] at h
  change ((eigenState W (lowest W)).ev
    ((inBasis (labUnit t)⁻¹ A).conjTranspose *
      (inBasis (labUnit t)⁻¹ A*inBasis (labUnit t)⁻¹ L-
       inBasis (labUnit t)⁻¹ L*inBasis (labUnit t)⁻¹ A))).re ≤ 0 at h
  rw [← inverse_star,inBasis_mul,inBasis_mul,← sub,inBasis_mul] at h
  exact h

end DSFTomography.SF.DiagonalSix
