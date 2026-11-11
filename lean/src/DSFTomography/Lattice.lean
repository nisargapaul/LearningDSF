import DSFTomography.Inverse

noncomputable section
namespace DSFTomography
variable {S ι : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
  [Fintype ι] [DecidableEq ι]

/-- Each nonzero physical bond has a single orientation, including modulo the periods. -/
structure Bonds (S : Type*) [AddCommGroup S] [DecidableEq S] where
  dirs : Finset S
  nonzero : ∀ d ∈ dirs, d ≠ 0
  oriented : ∀ d ∈ dirs, ∀ e ∈ dirs, d + e ≠ 0

def H (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor) : Op ι :=
  (∑ i, ∑ u, h u • P.σ i u) +
  ∑ e ∈ R.dirs, ∑ i, ∑ u, ∑ v, J e u v • (P.σ i u * P.σ (i+e) v)

/-- A matrix of first moments, symmetrized in the two space-spin labels. -/
def firstData (P : Spins S ι) (w E : ι → ℂ) (r s : S) : Tensor :=
  fun a b => m₁ w E (P.σ r a) (P.σ s b) + m₁ w E (P.σ s b) (P.σ r a)

/-- Contribution of all exchanges to the on-site first moment. -/
def background (C : S → S → Tensor) (R : Bonds S) (J : S → Tensor) : Tensor :=
  fun a b => ∑ e ∈ R.dirs, ∑ i, ∑ u, ∑ v, J e u v * pair C 0 0 i (i+e) a b u v

omit [Fintype S] in
private theorem off_single (M : S → Axis → ℂ) (d i : S) (hd : d ≠ 0) (a b u : Axis) :
    single M 0 d i a b u = 0 := by
  by_cases hi : i = 0
  · subst i; simp [single, coeff, Ne.symm hd]
  · simp [single, coeff, Ne.symm hi]

omit [Fintype S] in
private theorem off_pair (C : S → S → Tensor) (R : Bonds S) {d e : S}
    (hd : d ∈ R.dirs) (he : e ∈ R.dirs) (i : S) (a b u v : Axis) :
    pair C 0 d i (i+e) a b u v =
      if e = d then if i = 0 then
        (-4 * sign a u * sign v b) * C 0 d (third a u) (third v b)
      else 0 else 0 := by
  have hd0 := R.nonzero d hd
  have he0 := R.nonzero e he
  have hde := R.oriented d hd e he
  by_cases hi : i = 0
  · subst i; by_cases hed : e = d <;>
      simp_all [pair, coeff, ← mul_assoc, phase_mul, eq_comm]
  · by_cases hid : i = d <;> by_cases hiz : i + e = 0 <;>
      simp_all [pair, coeff, eq_comm]

theorem site_bond (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (w E : ι → ℂ) (hH : H P R h J = Matrix.diagonal E) {d : S} (hd : d ∈ R.dirs) :
    firstData P w E 0 d = bondMap (corr P w 0 d) (J d) := by
  ext a b
  rw [firstData, momentRule w E _ _ _ hH]
  change response w _ _ (H P R h J) = _
  simp only [H, response_add, response_sum, response_smul, response_single, response_pair,
    off_single _ _ _ (R.nonzero d hd), mul_zero, Finset.sum_const_zero, zero_add]
  apply Eq.trans (Finset.sum_eq_single d ?_ ?_)
  · simp_rw [off_pair _ R hd hd]
    simp [bondMap, mul_ite]
  · intro e he hne
    simp_rw [off_pair _ R hd he]
    simp [hne]
  · simp [hd]

theorem site_field (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (w E : ι → ℂ) (hH : H P R h J = Matrix.diagonal E) (a b : Axis) :
    firstData P w E 0 0 a b =
      fieldMap (magnet P w 0) h a b + background (corr P w) R J a b := by
  rw [firstData, momentRule w E _ _ _ hH]
  change response w _ _ (H P R h J) = _
  simp only [H, response_add, response_sum, response_smul, response_single, response_pair,
    background]
  congr 1
  rw [Finset.sum_eq_single (0 : S)]
  · simp [fieldMap, single, coeff, phase_mul]
  · intro i _ hi
    simp [single, coeff, hi, Ne.symm hi]
  · simp

end DSFTomography
