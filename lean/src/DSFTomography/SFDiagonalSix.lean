import DSFTomography.SFClusterBulk

/-! The paper's six directions and its diagonal-only leading inverse.
The tilted settings are xy, xz, yz. Their first transverse axis is
(eₐ+e_b)/√2 and their field is (eₐ-e_b)/√2. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Matrix
open scoped Topology

private theorem axisArithmetic :
    (1+1:Axis)=2 ∧ (1+2:Axis)=0 ∧ (2+1:Axis)=0 ∧ (2+2:Axis)=1 ∧
    (0:Axis)≠1 ∧ (0:Axis)≠2 ∧ (1:Axis)≠0 ∧ (1:Axis)≠2 ∧ (2:Axis)≠0 ∧ (2:Axis)≠1 := by decide

private theorem axes (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide

abbrev Pair := Fin 3
def firstAxis : Pair → Axis := ![0,0,1]
def secondAxis : Pair → Axis := ![1,2,2]
def otherAxis : Pair → Axis := ![2,1,0]
def invSqrtTwo : ℝ := (Real.sqrt 2)⁻¹

theorem invSqrtTwo_sq : invSqrtTwo^2 = 1/2 := by
  rw [invSqrtTwo,inv_pow,Real.sq_sqrt (by norm_num)]
  norm_num

/-- Columns are the transverse axes u,v and applied-field direction n. -/
def frame (t : Pair) : Matrix Axis Axis ℝ :=
  ![!![invSqrtTwo,0,invSqrtTwo; invSqrtTwo,0,-invSqrtTwo; 0,1,0],
    !![invSqrtTwo,0,invSqrtTwo; 0,-1,0; invSqrtTwo,0,-invSqrtTwo],
    !![0,1,0; invSqrtTwo,0,invSqrtTwo; invSqrtTwo,0,-invSqrtTwo]] t

theorem frame_axes (t : Pair) (a : Axis) :
    frame t a 0 = invSqrtTwo*((if a=firstAxis t then 1 else 0)+(if a=secondAxis t then 1 else 0)) ∧
    frame t a 2 = invSqrtTwo*((if a=firstAxis t then 1 else 0)-(if a=secondAxis t then 1 else 0)) := by
  rcases axes t with rfl|rfl|rfl <;> rcases axes a with rfl|rfl|rfl <;> norm_num [frame,firstAxis,secondAxis,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Matrix.transpose,axisArithmetic]

theorem frame_orthogonal (t : Pair) : (frame t).transpose*frame t = 1 ∧
    frame t*(frame t).transpose = 1 := by
  have sq := invSqrtTwo_sq
  constructor <;> ext a b <;> rcases axes t with rfl|rfl|rfl <;> rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;>
    norm_num [frame,Matrix.mul_apply,Fin.sum_univ_three,Matrix.transpose_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Matrix.transpose,axisArithmetic] <;> nlinarith

variable {D : Type*} [Fintype D]

/-- The same physical Hamiltonian, expressed in a tilted spin frame. -/
def rotate (t : Pair) : Params D →L[ℝ] Params D := LinearMap.toContinuousLinearMap {
  toFun p := (fun a => ∑ u, frame t u a*p.1 u,
    fun d a b => ∑ u, ∑ v, frame t u a*p.2 d u v*frame t v b)
  map_add' := by
    intro p q; apply Prod.ext
    · funext a; simp [mul_add,Finset.sum_add_distrib]
    · funext d a b; simp [mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro c p; apply Prod.ext
    · funext a; simp [mul_left_comm,← Finset.mul_sum]
    · funext d a b; simp [mul_left_comm,mul_assoc,← Finset.mul_sum] }

/-- Recover a diagonal exchange from diagonal transverse channels. -/
def diagonal (v : Harmonics D) (d : D) (a : Axis) : ℝ :=
  v.2 d (a+2) 0/4-v.2 d (a+2) 2/2

theorem diagonal_leading (p : Params D) (d : D) (a : Axis) :
    diagonal (leading p) d a = p.2 d a a := by
  rcases axes a with rfl|rfl|rfl <;> norm_num [diagonal,leading,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Matrix.transpose,axisArithmetic] <;> ring

/-- The tilted cosine supplies the symmetric exchange after subtracting
three diagonal entries already known from the coordinate experiments. -/
theorem tilted_cosine (p : Params D) (t : Pair) (d : D) :
    (leading (rotate t p)).2 d 2 0 =
      p.2 d (firstAxis t) (firstAxis t)+p.2 d (secondAxis t) (secondAxis t)+
      p.2 d (firstAxis t) (secondAxis t)+p.2 d (secondAxis t) (firstAxis t)+
      2*p.2 d (otherAxis t) (otherAxis t) := by
  have sq := invSqrtTwo_sq
  rcases axes t with rfl|rfl|rfl <;>
    simp [rotate,leading,frame,firstAxis,secondAxis,otherAxis,Fin.sum_univ_three,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Matrix.transpose,axisArithmetic] <;>
    ring_nf <;> simp [sq] <;> ring

def missingPair : Axis → Pair := ![2,1,0]

/-- Replace the unavailable cross-channel amplitude by tilted diagonal data.
Only slots 0,1,2 of the coordinate readout are used. -/
def assemble (v : Harmonics D) (tilted : Pair → D → ℝ) : Harmonics D :=
  (v.1, fun d i k => if k=3 then
    diagonal v d (i+1)+diagonal v d (i+2)+2*diagonal v d i-tilted (missingPair i) d
    else v.2 d i k)

theorem assemble_leading (p : Params D) :
    assemble (leading p) (fun t d => (leading (rotate t p)).2 d 2 0) = leading p := by
  refine Prod.ext rfl ?_
  funext d i k
  dsimp [assemble]
  split
  · subst k
    simp only [diagonal_leading,tilted_cosine]
    rcases axes i with rfl|rfl|rfl <;> norm_num [missingPair,firstAxis,secondAxis,otherAxis,leading,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Matrix.transpose,axisArithmetic,Fin.reduceFinMk] <;> ring
  · rfl

/-- Every field and exchange is recovered from the leading diagonal data. -/
theorem recover_leading (p : Params D) :
    readout (assemble (leading p) (fun t d => (leading (rotate t p)).2 d 2 0)) = p := by
  rw [assemble_leading,readout_leading]

end DSFTomography.SF.DiagonalSix
