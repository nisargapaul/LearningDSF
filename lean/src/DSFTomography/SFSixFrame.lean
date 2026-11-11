import DSFTomography.SFDiagonalSix

/-! Explicit qubit rotations for the three tilted laboratory fields.
No covariance of measured spectra is assumed. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Matrix

/-- Columns transport the chart axes to (u,v,n); entries are expanded to
keep the elementary 2-by-2 verification small. -/
def qubitFrame (t : Pair) : Qubit :=
  let s := invSqrtTwo
  ![!![⟨s,0⟩,⟨0,-s⟩; ⟨1/2,-1/2⟩,⟨1/2,1/2⟩],
    !![⟨-s/2,s/2-1/2⟩,⟨-s/2-1/2,-s/2⟩;
       ⟨-s/2-1/2,-s/2⟩,⟨s/2,-s/2+1/2⟩],
    !![⟨s/2-1/2,-s/2⟩,⟨-s/2,-s/2-1/2⟩;
       ⟨s/2+1/2,-s/2⟩,⟨-s/2,-s/2+1/2⟩]] t

private theorem choices (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide

set_option maxHeartbeats 2000000 in
theorem qubitFrame_unit (t : Pair) : (qubitFrame t).conjTranspose*qubitFrame t=1 ∧
    qubitFrame t*(qubitFrame t).conjTranspose=1 := by
  have sq := invSqrtTwo_sq
  constructor <;> ext x y <;> rcases choices t with rfl|rfl|rfl <;>
    fin_cases x <;> fin_cases y <;> apply Complex.ext <;>
    norm_num [qubitFrame,pauliValues,Matrix.conjTranspose_apply,Matrix.mul_apply,
      Matrix.smul_apply,Fin.sum_univ_two,Matrix.one_apply,Matrix.cons_val_two,
      Complex.mul_re,Complex.mul_im,map_ofNat,Complex.div_re,Complex.div_im,Complex.normSq_apply] <;> nlinarith [sq]

set_option maxHeartbeats 3000000 in
theorem qubitFrame_spin (t : Pair) (a : Axis) :
    qubitFrame t*pauli (some a)*(qubitFrame t).conjTranspose =
      ∑ b : Axis, (frame t b a:ℂ) • pauli (some b) := by
  have sq := invSqrtTwo_sq
  ext x y
  rcases choices t with rfl|rfl|rfl <;> rcases choices a with rfl|rfl|rfl <;>
    fin_cases x <;> fin_cases y <;> apply Complex.ext <;>
    norm_num [qubitFrame,frame,pauliValues,Matrix.conjTranspose_apply,Matrix.mul_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_two,Fin.sum_univ_three,Matrix.cons_val_two,
      Matrix.vecHead,Matrix.vecTail,Complex.mul_re,Complex.mul_im,map_ofNat,Complex.div_re,Complex.div_im,Complex.normSq_apply] <;> nlinarith [sq]

end DSFTomography.SF.DiagonalSix
