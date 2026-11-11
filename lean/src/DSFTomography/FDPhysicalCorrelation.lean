import DSFTomography.FDAccuracyAlgebra
import DSFTomography.FDBulk

/-! The physical contraction bound used in the manuscript accuracy proof. -/
noncomputable section
namespace DSFTomography.FD.Accuracy
open DSFTomography HT SF Matrix
open scoped Matrix.Norms.Frobenius

def vnorm (v : Axis → ℝ) := ‖WithLp.toLp 2 v‖
theorem vnorm_sq (v : Axis → ℝ) : vnorm v ^ 2 = ∑ a, (v a)^2 := by
  simp [vnorm,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs]
def bil (C : Mat) (u v : Axis → ℝ) := ∑ a, ∑ b, u a*C a b*v b
def BilinearBound (C : Mat) : Prop := ∀ u v, |bil C u v| ≤ vnorm u*vnorm v

theorem bilinear_contracts (C : Mat) (bound : BilinearBound C) : Contracts C := by
  intro v
  let u := fun a => ∑ b, C a b*v b
  have eq : bil C u v = ∑ a, (u a)^2 := by
    simp only [bil,mul_assoc,← Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _; dsimp [u]; ring
  have h := bound u v
  rw [eq,← vnorm_sq] at h
  have un : 0 ≤ vnorm u := norm_nonneg _
  have vn : 0 ≤ vnorm v := norm_nonneg _
  have uv : vnorm u ≤ vnorm v := by rw [abs_of_nonneg (sq_nonneg _)] at h; nlinarith
  change ∑ a, (u a)^2 ≤ _
  rw [← vnorm_sq,← vnorm_sq]
  nlinarith

theorem bilinear_transpose (C : Mat) (h : BilinearBound C) : BilinearBound C.transpose := by
  intro u v
  have eq : bil C.transpose u v = bil C v u := by
    unfold bil; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _; simp only [transpose_apply]; ring
  rw [eq,mul_comm]; exact h v u

theorem bilinear_mixture {T : Type*} [Fintype T] (C : T → Mat) (p : T → ℝ)
    (positive : ∀ i, 0 ≤ p i) (normed : ∑ i, p i = 1)
    (bound : ∀ i, BilinearBound (C i)) :
    BilinearBound (∑ i, p i • C i) := by
  intro u v
  have eq : bil (∑ i, p i • C i) u v = ∑ i, p i*bil (C i) u v := by
    simp only [bil,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
    calc
      _ = ∑ a, ∑ i, ∑ b, u a*(p i*C i a b)*v b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, u a*(p i*C i a b)*v b := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring
  rw [eq]
  calc
    _ ≤ ∑ i, |p i*bil (C i) u v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i*(vnorm u*vnorm v) := Finset.sum_le_sum fun i _ => by
      rw [abs_mul,abs_of_nonneg (positive i)]
      exact mul_le_mul_of_nonneg_left (bound i u v) (positive i)
    _ = vnorm u*vnorm v := by rw [← Finset.sum_mul,normed,one_mul]

variable {S : Type*} [Fintype S] [DecidableEq S]
def spinAlong (r : S) (v : Axis → ℝ) : Op (Config S) := ∑ a, (v a:ℂ) • spinAt r a

theorem spinAlong_star (r : S) (v : Axis → ℝ) : (spinAlong r v).conjTranspose = spinAlong r v := by
  simp [spinAlong,spinAt,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,word_hermitian]

theorem spinAlong_square (r : S) (v : Axis → ℝ) :
    spinAlong r v*spinAlong r v = ((∑ a, (v a)^2 : ℝ):ℂ) • 1 := by
  have square (a : Axis) : spinAt r a*spinAt r a = 1 := by
    simpa [spinAt,string,inBasis] using string_square (1:(Op (Config S))ˣ) r a
  have diff (a b : Axis) (ne : a ≠ b) : spinAt r a*spinAt r b =
      (Complex.I*sign a b) • spinAt r (third a b) := by
    simpa [spinAt,string,inBasis] using string_same_site (1:(Op (Config S))ˣ) r a b ne
  have ne : (0:Axis) ≠ 1 ∧ (0:Axis) ≠ 2 ∧ (1:Axis) ≠ 0 ∧ (1:Axis) ≠ 2 ∧
      (2:Axis) ≠ 0 ∧ (2:Axis) ≠ 1 := by decide
  simp only [spinAlong,Fin.sum_univ_three,Matrix.add_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,square,diff _ _ ne.1,diff _ _ ne.2.1,
    diff _ _ ne.2.2.1,diff _ _ ne.2.2.2.1,diff _ _ ne.2.2.2.2.1,diff _ _ ne.2.2.2.2.2,
    axisTable,smul_smul]
  push_cast
  match_scalars <;> ring

def correlation (ρ : State (Config S)) (r s : S) : Mat :=
  fun a b => (ρ.ev (spinAt r a*spinAt s b)).re

theorem correlation_bound (ρ : State (Config S)) (r s : S) : BilinearBound (correlation ρ r s) := by
  intro u v
  have cs := ρ.cs (spinAlong r u) (spinAlong s v)
  simp only [spinAlong_star,spinAlong_square,map_smul,ρ.normed] at cs
  simp only [smul_eq_mul,mul_one,Complex.ofReal_re] at cs
  have eq : (ρ.ev (spinAlong r u*spinAlong s v)).re = bil (correlation ρ r s) u v := by
    simp [spinAlong,Fin.sum_univ_three,Matrix.add_mul,Matrix.mul_add,
      Matrix.smul_mul,Matrix.mul_smul,map_add,map_smul,smul_eq_mul,
      Complex.mul_re,bil,correlation]
    ring
  have re := Complex.abs_re_le_norm (ρ.ev (spinAlong r u*spinAlong s v))
  rw [eq] at re
  rw [← vnorm_sq,← vnorm_sq] at cs
  have un : 0 ≤ vnorm u := norm_nonneg _
  have vn : 0 ≤ vnorm v := norm_nonneg _
  have h : ‖ρ.ev (spinAlong r u*spinAlong s v)‖ ≤ vnorm u*vnorm v := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg un vn)).mp
    simpa only [mul_pow] using cs
  exact re.trans h

end DSFTomography.FD.Accuracy
