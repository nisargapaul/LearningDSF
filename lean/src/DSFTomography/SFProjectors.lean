import DSFTomography.SFLehmann

/-! Basis-invariant evaluation of the DSF of a supplied normalized ground
ket. The excitation projectors are constructed by the spectral theorem. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Op ι}

def spectralLine (h : H.IsHermitian) (j : ι) : Op ι :=
  let U : Op ι := h.eigenvectorUnitary
  U * Matrix.diagonal (ket j) * U.conjTranspose

theorem weighted_lines (h : H.IsHermitian) (f : ι → ℂ) :
    ∑ j, f j • spectralLine h j =
      let U : Op ι := h.eigenvectorUnitary
      U * Matrix.diagonal f * U.conjTranspose := by
  let U : Op ι := h.eigenvectorUnitary
  have diag : (∑ j, f j • Matrix.diagonal (ket j)) = Matrix.diagonal f := by
    ext x y
    by_cases eq : x=y
    · subst y; simp [Matrix.sum_apply,ket,Matrix.smul_apply,mul_ite]
    · simp [Matrix.sum_apply,Matrix.diagonal_apply_ne _ eq]
  change (∑ j, f j • (U * Matrix.diagonal (ket j) * U.conjTranspose)) = _
  have pull (j : ι) : f j • (U * Matrix.diagonal (ket j) * U.conjTranspose) =
      U * (f j • Matrix.diagonal (ket j)) * U.conjTranspose := by simp
  simp_rw [pull,← Matrix.sum_mul,← Matrix.mul_sum,diag]
  rfl

theorem sum_lines (h : H.IsHermitian) : ∑ j, spectralLine h j = 1 := by
  have eq := weighted_lines h (fun _ => 1)
  simp only [one_smul,Matrix.diagonal_one,mul_one] at eq
  exact eq.trans (unitary.coe_mul_star_self h.eigenvectorUnitary)

theorem energy_lines (h : H.IsHermitian) : ∑ j, (h.eigenvalues j : ℂ) • spectralLine h j = H := by
  rw [weighted_lines]
  have eq := h.star_mul_self_mul_eq_diagonal
  let U : Op ι := h.eigenvectorUnitary
  change U * Matrix.diagonal (fun j => (h.eigenvalues j : ℂ)) * U.conjTranspose = H
  change U.conjTranspose * H * U = Matrix.diagonal (fun j => (h.eigenvalues j : ℂ)) at eq
  have unit : U*U.conjTranspose = 1 := unitary.coe_mul_star_self _
  rw [← eq,← Matrix.mul_assoc,← Matrix.mul_assoc,unit,one_mul,Matrix.mul_assoc,unit,mul_one]

/-- Intensity of one transition, in the order A on the bra and C on the ket. -/
def intensity (h : H.IsHermitian) (ψ : ι → ℂ) (A C : Op ι) (j : ι) :=
  sandwich ψ (A * spectralLine h j * C) ψ

theorem spectral_sum (h : H.IsHermitian) (ψ : ι → ℂ) (A C : Op ι) (f : ι → ℂ) :
    ∑ j, f j * intensity h ψ A C j = sandwich ψ (A * (∑ j, f j • spectralLine h j) * C) ψ := by
  let L : Op ι →ₗ[ℂ] ℂ := {
    toFun := fun T => sandwich ψ (A*T*C) ψ
    map_add' := by intros; simp [sandwich,mul_add,add_mul,Finset.sum_add_distrib]
    map_smul' := by intros; simp [sandwich,← Finset.mul_sum,mul_left_comm,mul_assoc] }
  change _ = L (∑ j, f j • spectralLine h j)
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

theorem lehmann_static (h : H.IsHermitian) (ψ : ι → ℂ) (A C : Op ι) :
    ∑ j, intensity h ψ A C j = sandwich ψ (A*C) ψ := by
  simpa [sum_lines] using spectral_sum h ψ A C (fun _ => 1)

theorem lehmann_first (h : H.IsHermitian) (ψ : ι → ℂ) (E : ℂ) (A C : Op ι) :
    ∑ j, ((h.eigenvalues j:ℂ)-E)*intensity h ψ A C j =
      sandwich ψ (A*(H-E • (1:Op ι))*C) ψ := by
  rw [spectral_sum]
  simp only [sub_smul,Finset.sum_sub_distrib,energy_lines,← Finset.smul_sum,sum_lines]

omit [DecidableEq ι] in
theorem sandwich_probes (ψ : ι → ℂ) (A T C : Op ι) (self : A.IsHermitian) :
    sandwich ψ (A*T*C) ψ = sandwich (A *ᵥ ψ) T (C *ᵥ ψ) := by
  have eq (v : ι → ℂ) (M : Op ι) (w : ι → ℂ) :
      sandwich v M w = dotProduct (star v) (M *ᵥ w) := by
    simp [sandwich,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  simp only [eq,star_mulVec,Matrix.mulVec_mulVec,← dotProduct_mulVec,self.eq,Matrix.mul_assoc]

end DSFTomography.SF
