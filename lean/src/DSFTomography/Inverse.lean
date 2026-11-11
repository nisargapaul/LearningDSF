import DSFTomography.Spin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace DSFTomography
/-- The measured bond map, with the Pauli factor four included and unscaled J. -/
def bondMap (C J : Tensor) : Tensor := fun a b =>
  ∑ u, ∑ v, J u v * ((-4 * sign a u * sign v b) * C (third a u) (third v b))

theorem phase_mul (a u v b : Axis) :
    phase a u * phase v b = -4 * sign a u * sign v b := by
  unfold phase
  calc
    _ = 4 * (Complex.I * Complex.I) * sign a u * sign v b := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

def numerator (C F : Tensor) : Tensor :=
  (F.transpose * C).trace • C - (2 : ℂ) • (C * F.transpose * C)

def recoverBond (C F : Tensor) : Tensor := fun a b => numerator C F a b / (8 * C.det)

private theorem axes (u : Axis) : u = 0 ∨ u = 1 ∨ u = 2 := by
  fin_cases u <;> decide

set_option maxHeartbeats 8000000 in
theorem numerator_bondMap (C J : Tensor) (a b : Axis) :
    numerator C (bondMap C J) a b = J a b * (8 * C.det) := by
  rcases axes a with rfl | rfl | rfl <;> rcases axes b with rfl | rfl | rfl <;>
    norm_num [numerator, bondMap, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.det_fin_three, Fin.sum_univ_three, axisTable, smul_eq_mul] <;> ring

theorem recoverBond_exact (C J : Tensor) (h : C.det ≠ 0) :
    recoverBond C (bondMap C J) = J := by
  ext a b
  exact (div_eq_iff (mul_ne_zero (by norm_num) h)).2 (numerator_bondMap C J a b)

def fieldMap (M h : Axis → ℂ) : Tensor := fun a b =>
  ∑ u, h u * ((-4 * sign a u * sign (third a u) b) * M (third (third a u) b))

def recoverField (M : Axis → ℂ) (G : Tensor) (k : Axis) : Axis → ℂ :=
  fun b => (2 * G k b - (if k = b then G.trace else 0)) / (8 * M k)

private theorem axisNe : (0 : Axis) ≠ 1 ∧ (0 : Axis) ≠ 2 ∧ (1 : Axis) ≠ 0 ∧
    (1 : Axis) ≠ 2 ∧ (2 : Axis) ≠ 0 ∧ (2 : Axis) ≠ 1 := by decide

theorem recoverField_exact (M h : Axis → ℂ) (k : Axis) (hk : M k ≠ 0) :
    recoverField M (fieldMap M h) k = h := by
  funext b
  apply (div_eq_iff (mul_ne_zero (by norm_num) hk)).2
  rcases axes k with rfl | rfl | rfl <;> rcases axes b with rfl | rfl | rfl <;>
    norm_num [fieldMap, Matrix.trace, Matrix.diag, Fin.sum_univ_three, axisTable, axisNe] <;> ring

end DSFTomography
