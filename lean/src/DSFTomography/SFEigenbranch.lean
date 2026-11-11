import DSFTomography.SFResponse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! A finite-volume eigenpair near the polarized state, constructed by the
inverse function theorem. In the vacuum-amplitude-one chart the unknown at
the vacuum index stores the energy; the other entries store ket amplitudes. -/
noncomputable section
namespace DSFTomography.SF.Perturbation
open DSFTomography Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Entries (ι : Type*) := ι → ι → ℂ
abbrev Chart (ι : Type*) := Entries ι × (ι → ℂ)

def mask (o : ι) (v : ι → ℂ) (k : ι) := if k=o then 0 else v k
def vector (o : ι) (v : ι → ℂ) (k : ι) := ket o k + mask o v k

private def tailAction (o : ι) (z : Chart ι) (k : ι) := ∑ j, z.1 k j * mask o z.2 j

private def changeChart (o : ι) (gap : ι → ℂ) (z : Chart ι) : Chart ι :=
  (z.1, fun k => z.2 k + if k=o then -tailAction o z k else (tailAction o z k - z.2 o*z.2 k)/gap k)

private def source (o : ι) (gap : ι → ℂ) (A : Entries ι) : Chart ι :=
  (A, fun k => if k=o then A k o else -A k o/gap k)

private theorem change_smooth (o : ι) (gap : ι → ℂ) : ContDiff ℂ 2 (changeChart o gap) := by
  have tail (k : ι) : ContDiff ℂ 2 (fun z : Chart ι => tailAction o z k) := by
    apply ContDiff.sum; intro j _
    unfold mask; split_ifs <;> fun_prop
  apply ContDiff.prodMk contDiff_fst
  apply contDiff_pi.mpr; intro k
  by_cases eq : k=o <;> simp only [eq,if_true,if_false] <;> fun_prop

private theorem change_deriv (o : ι) (gap : ι → ℂ) :
    HasFDerivAt (changeChart o gap) (ContinuousLinearMap.id ℂ (Chart ι)) 0 := by
  have A (k j : ι) := ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).comp
    ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ (Entries ι) (ι → ℂ)))).hasFDerivAt (x := 0)
  have v (k : ι) := ((ContinuousLinearMap.proj k : (ι → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.snd ℂ (Entries ι) (ι → ℂ))).hasFDerivAt (x := 0)
  have tail (k : ι) : HasFDerivAt (𝕜 := ℂ) (fun z : Chart ι => tailAction o z k) 0 0 := by
    have term (j : ι) : HasFDerivAt (𝕜 := ℂ) (fun z : Chart ι => z.1 k j * mask o z.2 j) 0 0 := by
      by_cases hj : j=o
      · simpa [mask,hj] using hasFDerivAt_const (𝕜 := ℂ) (0:ℂ) (0 : Chart ι)
      · have h := (A k j).mul (v j)
        convert h using 1
        · funext w; simp [mask,hj]
        · apply ContinuousLinearMap.ext; intro w; simp
    simpa [tailAction] using HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => term j)
  have quad (k : ι) : HasFDerivAt (𝕜 := ℂ) (fun z : Chart ι => z.2 o*z.2 k) 0 0 := by
    convert (v o).mul (v k) using 1
    apply ContinuousLinearMap.ext; intro w; simp
  have zero (k : ι) : HasFDerivAt (𝕜 := ℂ) (fun z : Chart ι =>
      if k=o then -tailAction o z k else (tailAction o z k-z.2 o*z.2 k)/gap k) 0 0 := by
    by_cases eq : k=o
    · simpa [eq] using (tail o).neg
    · simpa [eq,div_eq_mul_inv] using ((tail k).sub (quad k)).mul_const (gap k)⁻¹
  have all := hasFDerivAt_pi.mpr zero
  have rest : HasFDerivAt (𝕜 := ℂ) (fun z : Chart ι => ((0 : Entries ι), fun k =>
      if k=o then -tailAction o z k else (tailAction o z k-z.2 o*z.2 k)/gap k)) 0 0 := by
    convert (hasFDerivAt_const (𝕜 := ℂ) (0 : Entries ι) (0 : Chart ι)).prodMk all using 1
  convert (hasFDerivAt_id (𝕜 := ℂ) (0 : Chart ι)).add rest using 1
  · funext x
    apply Prod.ext
    · exact (add_zero _).symm
    · rfl
  · simp

/-- A smooth branch before fixing the norm. All comparisons with another
eigenvector use this chart only near the unperturbed Hamiltonian. -/
theorem finite_branch (o : ι) (gap : ι → ℂ) (g0 : gap o=0) (nz : ∀ k ≠ o, gap k≠0) :
    ∃ v : Entries ι → ι → ℂ, ContDiffAt ℂ 2 v 0 ∧ v 0 = 0 ∧
    (∀ᶠ A in 𝓝 0, ∀ k, gap k * vector o (v A) k +
      (∑ j, A k j*vector o (v A) j) = v A o * vector o (v A) k) := by
  let f := changeChart o gap
  have smooth := (change_smooth o gap).contDiffAt (x := 0)
  have df : HasFDerivAt f (ContinuousLinearEquiv.refl ℂ (Chart ι)).toContinuousLinearMap 0 :=
    change_deriv o gap
  have one : (1:WithTop ℕ∞) ≤ 2 := by norm_num
  let inv := smooth.localInverse df one
  have f0 : changeChart o gap 0 = 0 := by ext <;> simp [changeChart,tailAction,mask]
  have s0 : source o gap 0=0 := by ext <;> simp [source]
  have src : ContDiff ℂ 2 (source o gap) := by
    apply ContDiff.prodMk contDiff_id
    apply contDiff_pi.mpr; intro k
    by_cases h : k=o <;> simp only [h,if_true,if_false] <;> fun_prop
  have sm : ContDiffAt ℂ 2 inv 0 := by simpa only [f0] using smooth.to_localInverse df one
  have inv0 : inv 0 = 0 := by simpa only [f0] using smooth.localInverse_apply_image df one
  have srcsmooth : ContDiffAt ℂ 2 inv (source o gap 0) := s0.symm ▸ sm
  refine ⟨fun A => (inv (source o gap A)).2,
    contDiffAt_snd.comp _ (srcsmooth.comp _ src.contDiffAt),by simp [s0,inv0],?_⟩
  · have right := (smooth.hasStrictFDerivAt' df one).eventually_right_inverse
    rw [show changeChart o gap 0 = 0 from f0] at right
    have near := (src.continuous.continuousAt (x := 0)).tendsto
    rw [s0] at near
    filter_upwards [near.eventually right] with A h
    change f (inv (source o gap A)) = source o gap A at h
    have fst := congrArg Prod.fst h
    change (inv (source o gap A)).1 = A at fst
    intro k
    have row := congrFun (congrArg Prod.snd h) k
    change (inv (source o gap A)).2 k + (if k=o then -tailAction o (inv (source o gap A)) k
      else (tailAction o (inv (source o gap A)) k - (inv (source o gap A)).2 o*(inv (source o gap A)).2 k)/gap k) =
        (if k=o then A k o else -A k o/gap k) at row
    simp only [tailAction,fst] at row
    simp only [vector,mul_add,Finset.sum_add_distrib,ket,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    by_cases hko : k=o
    · subst k
      simp [g0,mask] at row ⊢
      linear_combination -row
    · simp [hko,mask] at row ⊢
      field_simp [nz k hko] at row
      linear_combination row

/-- Separation of the low eigenline, with an explicit finite-matrix
sufficient condition. The factor card(ι) here is volume dependent. -/
theorem low_eigenline (o : ι) (gap : ι → ℂ) (A : Entries ι) (ψ ξ : ι → ℂ)
    {e μ : ℂ} (vac : ψ o = 1) (gapped : ∀ k ≠ o, 2 ≤ (gap k).re)
    (bare : ∀ k, gap k*ψ k + ∑ j, A k j*ψ j = e*ψ k)
    (test : ∀ k, gap k*ξ k + ∑ j, A k j*ξ j = μ*ξ k)
    (small : 2*(Fintype.card ι:ℝ)*‖A‖ < 1) (close : ∀ k≠o, ‖ψ k‖ ≤ 1)
    (low : μ.re ≤ 1) : ∀ k, ξ k = ξ o * ψ k := by
  let η := fun k => ξ k - ξ o * ψ k
  have origin : η o = 0 := by simp [η,vac]
  have residual (k : ι) : ∑ j, A k j*η j =
      (μ-gap k)*η k + (μ-e)*ξ o*ψ k := by
    simp only [η,mul_sub,Finset.sum_sub_distrib]
    have factor (j : ι) : A k j * (ξ o*ψ j) = ξ o*(A k j * ψ j) := by ring
    simp_rw [factor,← Finset.mul_sum]
    linear_combination test k - ξ o * bare k
  have cancel (k : ι) : (μ-gap k)*η k =
      ∑ j, (A k j-ψ k*A o j)*η j := by
    have r0 := residual o
    rw [origin,vac] at r0
    simp only [mul_zero,zero_add,mul_one] at r0
    simp only [sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [r0,residual]
    ring
  have point (k : ι) (nk : k≠o) : ‖η k‖ ≤ 2*(Fintype.card ι:ℝ)*‖A‖ * ‖η‖ := by
    have sep : 1 ≤ ‖μ - gap k‖ := by
      have g := gapped k nk
      have lower := (abs_le.mp (Complex.abs_re_le_norm (μ-gap k))).1
      rw [Complex.sub_re] at lower
      linarith
    have entry (k j : ι) := (norm_le_pi_norm (A k) j).trans (norm_le_pi_norm A k)
    calc
      ‖η k‖ ≤ ‖(μ-gap k)*η k‖ := by rw [norm_mul]; nlinarith [norm_nonneg (η k)]
      _ ≤ ∑ j, ‖(A k j-ψ k*A o j)*η j‖ := by rw [cancel]; exact norm_sum_le .. 
      _ ≤ ∑ _j : ι, (2*‖A‖)*‖η‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        apply mul_le_mul _ (norm_le_pi_norm η j) (norm_nonneg _) (by positivity)
        apply (norm_sub_le ..).trans
        rw [norm_mul]
        linarith [entry k j, mul_le_mul (close k nk) (entry o j) (norm_nonneg _) zero_le_one]
      _ = _ := by simp; ring
  have bound : ‖η‖ ≤ 2*(Fintype.card ι:ℝ)*‖A‖ * ‖η‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    by_cases h : k=o
    · subst k; rw [origin,norm_zero]; positivity
    · exact point k h
  have zero : η = 0 := by
    by_contra hz
    have pos := norm_pos_iff.mpr hz
    linarith [mul_lt_mul_of_pos_right small pos]
  intro k; exact sub_eq_zero.mp (congrFun zero k)

end DSFTomography.SF.Perturbation
