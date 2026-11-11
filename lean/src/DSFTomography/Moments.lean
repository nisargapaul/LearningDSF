import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-! Normalized real-space Lehmann moments (the paper's moments divided by 2π).
The basis labels are energy eigenstates. Diagonal weights include every Gibbs state. -/
namespace DSFTomography

abbrev Op (ι : Type*) := Matrix ι ι ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bracket (A B : Op ι) := A * B - B * A

def mean (w : ι → ℂ) (A : Op ι) : ℂ := ∑ i, w i * A i i

def m₀ (w : ι → ℂ) (A B : Op ι) : ℂ :=
  ∑ i, w i * ∑ j, A i j * B j i

def m₁ (w E : ι → ℂ) (A B : Op ι) : ℂ :=
  ∑ i, w i * ∑ j, (E j - E i) * A i j * B j i

omit [DecidableEq ι] in
theorem zeroMoment (w : ι → ℂ) (A B : Op ι) :
    m₀ w A B = mean w (A * B) := rfl

theorem firstMoment (w E : ι → ℂ) (A B : Op ι) :
    m₁ w E A B = mean w (bracket A (Matrix.diagonal E) * B) := by
  unfold m₁ mean bracket
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_ite,
    ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  ext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem stationary (w E : ι → ℂ) (A : Op ι) :
    mean w (bracket A (Matrix.diagonal E)) = 0 := by
  simp [mean, bracket, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

omit [DecidableEq ι] in
@[simp] theorem mean_zero (w : ι → ℂ) : mean w 0 = 0 := by simp [mean]

omit [DecidableEq ι] in
@[simp] theorem mean_add (w : ι → ℂ) (A B : Op ι) :
    mean w (A + B) = mean w A + mean w B := by
  simp [mean, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
@[simp] theorem mean_sub (w : ι → ℂ) (A B : Op ι) :
    mean w (A - B) = mean w A - mean w B := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
@[simp] theorem mean_smul (w : ι → ℂ) (k : ℂ) (A : Op ι) :
    mean w (k • A) = k * mean w A := by
  simp [mean, Finset.mul_sum, mul_left_comm]

/-- The symmetrized first moment as a stationary double commutator. -/
theorem momentRule (w E : ι → ℂ) (A B H : Op ι) (hH : H = Matrix.diagonal E) :
    m₁ w E A B + m₁ w E B A = mean w (bracket (bracket A H) B) := by
  rw [firstMoment, firstMoment, ← hH, ← mean_add]
  have h := stationary w E (B * A)
  rw [← hH] at h
  rw [← add_zero (mean w (bracket (bracket A H) B)), ← h, ← mean_add]
  congr 1
  unfold bracket
  noncomm_ring

end DSFTomography
