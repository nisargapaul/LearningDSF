import DSFTomography.SFClusterPauli
import DSFTomography.SFClusterGap

/-! The physical bra in dressed coordinates. Although the dressed ket may
have a large norm, the normalized expectation only uses the inverse of the
bounded relative correction and evaluation at the vacuum. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Matrix NormedSpace
variable {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]
variable {J : Type*} [Fintype J]

def bra (u : Amp S) : Amp S →L[ℂ] ℂ :=
  ∑ x, (star (u x)) • (PiLp.proj 1 (fun _ : Config S => ℂ) x)

omit [AddCommGroup S] in
theorem bra_apply (u w : Amp S) : bra u w = dotProduct (star (WithLp.ofLp u)) (WithLp.ofLp w) := by
  simp only [bra,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]; rfl

omit [AddCommGroup S] in
theorem bra_matrix (u w : Amp S) (M : Op (Config S)) :
    sandwich (WithLp.ofLp u) M (WithLp.ofLp w) = bra u (asOperator M w) := by
  rw [bra_apply,asOp_apply]; simp [sandwich,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

omit [AddCommGroup S] in
theorem bra_selfadj (M : Op (Config S)) (h : M.IsHermitian) (u w : Amp S) :
    bra u (asOperator M w) = bra (asOperator M u) w := by
  rw [bra_apply,bra_apply]; change star (WithLp.ofLp u) ⬝ᵥ (M *ᵥ WithLp.ofLp w) = star (M *ᵥ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp w
  simp only [dotProduct_mulVec,star_mulVec,h.eq]

omit [AddCommGroup S] in
theorem bra_smul (c : ℂ) (u w : Amp S) : bra (c • u) w = star c * bra u w := by
  rw [bra_apply,bra_apply]; change (∑ x, star (c*u x)*w x) = star c * ∑ x, star (u x)*w x
  simp [Finset.mul_sum,mul_assoc]

omit [AddCommGroup S] in
theorem bra_left (M : Op (Config S)) (h : M.IsHermitian) (u : Amp S) {E : ℂ}
    (hu : asOperator M u = E • u) (normed : bra u u = 1) (w : Amp S) :
    bra u (asOperator M w) = E * bra u w := by
  have same := bra_selfadj M h u u
  rw [hu,map_smul,smul_eq_mul,bra_smul,normed,mul_one,mul_one] at same
  rw [bra_selfadj M h,hu,bra_smul,← same]

private theorem correction_vac (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S) :
    correction A D p v (basis 0) = 0 := by
  have z (D : List S) (w : Amp S) : excitation D w (basis 0) = 0 := by
    change columns _ (basis 0) = _; rw [columns_basis]; simp [excitedColumn,flipCount]
  simp [correction,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,z]

/-- For any test column, the normalized left eigenvector applied to
the dressed relative Hamiltonian gives its bare vacuum coefficient. -/
theorem left_column (A : J → Config S) (D : J → List S) (p : J → ℂ) (v : Amp S)
    (eqn : FiniteEquation A D p v) (M : Op (Config S)) (mh : M.IsHermitian)
    (matrix : clusterH A D p = asOperator M) (u : Amp S) (c : ℂ)
    (ket : u = c • eigenKet v) (normed : bra u u = 1) (y : Amp S) :
    let U := exp ℂ (convolute (generator v))
    let T := correction A D p v
    c * bra u (U ((1+T) y)) = y 0 := by
  intro U T
  let E := -(Fintype.card S:ℂ)*v 0
  let H := clusterH A D p
  let L := c • ((bra u).comp U)
  have hu : H u = E • u := by
    rw [ket,map_smul,(exact_eigenpair A D p v eqn).2,smul_comm]
  have left (w) : bra u (H w) = E * bra u w := by
    change bra u (clusterH A D p w) = _; rw [matrix]
    exact bra_left M mh u (by rw [← matrix]; exact hu) normed w
  have vac : L (basis 0)=1 := by
    change c * bra u (eigenKet v) = 1
    simpa only [← smul_eq_mul,← map_smul,← ket] using normed
  have kill (x : Config S) : L ((1+T) (gapOp (basis x))) = 0 := by
    have step := congrArg (fun K : Operator S => K (basis x)) (dressed_H A D p v eqn)
    change H (U (basis x)) = U (E • basis x + (1+T) (gapOp (basis x))) at step
    have h := congrArg (bra u) step
    rw [left,map_add,map_smul,map_add,map_smul,smul_eq_mul] at h
    have z : bra u (U ((1+T) (gapOp (basis x)))) = 0 := by linear_combination -h
    change c * bra u (U ((1+T) (gapOp (basis x)))) = 0; rw [z,mul_zero]
  have col (x : Config S) : L ((1+T) (basis x)) = basis x 0 := by
    by_cases hz : x=0
    · subst x; simp [ContinuousLinearMap.add_apply,T,correction_vac,vac]
    · have ne : excitationEnergy x ≠ 0 := by
        have ex : ∃ t, x t ≠ 0 := by simpa [funext_iff] using hz
        have k : flipCount x ≠ 0 := Finset.card_ne_zero.mpr (by obtain ⟨t,h⟩ := ex; exact ⟨t,by simp [h]⟩)
        exact mul_ne_zero (by norm_num) (by exact_mod_cast k)
      have h := kill x
      simp only [gapOp,columns_basis,map_smul,smul_eq_mul,mul_eq_zero] at h
      simpa [basis_at,Ne.symm hz] using h.resolve_left ne
  let K := L.comp (1+T)
  let π := (PiLp.proj 1 (fun _ : Config S => ℂ) (0 : Config S) : Amp S →L[ℂ] ℂ)
  have equal : K = π := by
    ext z : 1; rw [← sum_basis z,map_sum,map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_smul,map_smul]; exact congrArg (_ • ·) (col x)
  exact congrArg (fun f : Amp S →L[ℂ] ℂ => f y) equal

end DSFTomography.SF.Cluster
