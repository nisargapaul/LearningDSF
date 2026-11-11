import DSFTomography.Lattice

noncomputable section
namespace DSFTomography
variable {S ι : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
  [Fintype ι] [DecidableEq ι]

/-- The experimental inputs, normalized by 2π. -/
structure Data (S : Type*) where
  static : S → Tensor
  first : S → Tensor

def avg (f : S → ℂ) : ℂ := (∑ t, f t) / (Fintype.card S : ℂ)

omit [AddCommGroup S] [DecidableEq S] in
private theorem avg_add (f g : S → ℂ) :
    avg (fun t => f t + g t) = avg f + avg g := by simp [avg, Finset.sum_add_distrib, add_div]
omit [AddCommGroup S] [DecidableEq S] in
private theorem avg_sub (f g : S → ℂ) :
    avg (fun t => f t - g t) = avg f - avg g := by simp [avg, Finset.sum_sub_distrib, sub_div]
omit [AddCommGroup S] [DecidableEq S] in
private theorem avg_mul (k : ℂ) (f : S → ℂ) :
    avg (fun t => k * f t) = k * avg f := by simp [avg, ← Finset.mul_sum, mul_div_assoc]
omit [AddCommGroup S] [DecidableEq S] in
private theorem avg_div (k : ℂ) (f : S → ℂ) :
    avg (fun t => f t / k) = avg f / k := by
  simp only [avg, div_eq_mul_inv, ← Finset.sum_mul]
  ring
omit [AddCommGroup S] [DecidableEq S] in
private theorem avg_sum {α : Type*} (s : Finset α) (f : α → S → ℂ) :
    avg (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, avg (f i) := by
  simp only [avg, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_comm
omit [DecidableEq S] in
private theorem avg_shift (i : S) (f : S → ℂ) :
    avg (fun t => f (t+i)) = avg f := by
  unfold avg
  rw [show (∑ t, f (t+i)) = ∑ t, f t from Equiv.sum_comp (Equiv.addRight i) f]

def measured (P : Spins S ι) (w E : ι → ℂ) : Data S where
  static d a b := avg (fun t => m₀ w (P.σ t a) (P.σ (t+d) b))
  first d a b := avg (fun t => m₁ w E (P.σ t a) (P.σ (t+d) b))

def Data.force (D : Data S) (d : S) : Tensor :=
  fun a b => D.first d a b + D.first (-d) b a
def Data.mag (D : Data S) (k : Axis) :=
  (D.static 0 (k+1) (k+2) - D.static 0 (k+2) (k+1)) / (2 * Complex.I)
def Data.exchange (D : Data S) (d : S) := recoverBond (D.static d) (D.force d)
def Data.residual (D : Data S) (R : Bonds S) : Tensor :=
  D.force 0 - background (fun i j => D.static (j-i)) R D.exchange
def Data.field (D : Data S) (R : Bonds S) (k : Axis) :=
  recoverField D.mag (D.residual R) k

private def shift (P : Spins S ι) (t : S) : Spins S ι where
  σ i := P.σ (t+i)
  pauli := by intros; simp [P.pauli]

private theorem H_shift (P : Spins S ι) (t : S) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor) :
    H (shift P t) R h J = H P R h J := by
  unfold H
  congr 1
  · exact Equiv.sum_comp (Equiv.addLeft t) (fun i => ∑ u, h u • P.σ i u)
  · apply Finset.sum_congr rfl
    intro e _
    simp only [shift, ← add_assoc]
    exact Equiv.sum_comp (Equiv.addLeft t) (fun i => ∑ u, ∑ v, J e u v • (P.σ i u * P.σ (i+e) v))

private theorem avg_corr (P : Spins S ι) (w E : ι → ℂ) (i j : S) (a b : Axis) :
    avg (fun t => corr (shift P t) w i j a b) = (measured P w E).static (j-i) a b := by
  change avg (fun t => m₀ w (P.σ (t+i) a) (P.σ (t+j) b)) =
    avg (fun t => m₀ w (P.σ t a) (P.σ (t+(j-i)) b))
  rw [← avg_shift i (fun t => m₀ w (P.σ t a) (P.σ (t+(j-i)) b))]
  have hj (t : S) : t+i+(j-i) = t+j := by abel
  simp only [hj]

private theorem avg_magnet (P : Spins S ι) (w E : ι → ℂ) (i : S) (k : Axis) :
    avg (fun t => magnet (shift P t) w i k) = (measured P w E).mag k := by
  simp only [magnet, avg_div, avg_sub, avg_corr P w E, sub_self, Data.mag]

private theorem avg_first (P : Spins S ι) (w E : ι → ℂ) (d : S) (a b : Axis) :
    avg (fun t => firstData (shift P t) w E 0 d a b) = (measured P w E).force d a b := by
  simp only [firstData, shift, add_zero, avg_add, Data.force, measured]
  congr 1
  rw [← avg_shift d (fun t => m₁ w E (P.σ t b) (P.σ (t + -d) a))]
  simp [add_assoc]

private theorem avg_background (P : Spins S ι) (w E : ι → ℂ) (R : Bonds S) (J : S → Tensor)
    (a b : Axis) :
    avg (fun t => background (corr (shift P t) w) R J a b) =
      background (fun i j => (measured P w E).static (j-i)) R J a b := by
  simp only [background, pair, avg_sum, avg_mul, avg_add, avg_corr P w E]

theorem measured_bond (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (w E : ι → ℂ) (hH : H P R h J = Matrix.diagonal E) {d : S} (hd : d ∈ R.dirs) :
    (measured P w E).force d = bondMap ((measured P w E).static d) (J d) := by
  ext a b
  rw [← avg_first]
  have step (t : S) := congrFun (congrFun
    (site_bond (shift P t) R h J w E ((H_shift P t R h J).trans hH) hd) a) b
  simp_rw [step]
  simp only [bondMap, avg_sum, avg_mul, avg_corr P w E, sub_zero]

theorem measured_onsite (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (w E : ι → ℂ) (hH : H P R h J = Matrix.diagonal E) (a b : Axis) :
    (measured P w E).force 0 a b = fieldMap (measured P w E).mag h a b +
      background (fun i j => (measured P w E).static (j-i)) R J a b := by
  rw [← avg_first]
  have step (t : S) := site_field (shift P t) R h J w E ((H_shift P t R h J).trans hH) a b
  simp_rw [step]
  simp only [avg_add, fieldMap, avg_sum, avg_mul, avg_magnet P w E, avg_background P w E]

/-- Each nonsingular correlation matrix determines the exchange on that bond. -/
theorem fdExchange (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (w E : ι → ℂ) (hH : H P R h J = Matrix.diagonal E) {d : S} (hd : d ∈ R.dirs)
    (hdet : ((measured P w E).static d).det ≠ 0) :
    (measured P w E).exchange d = J d := by
  unfold Data.exchange
  rw [measured_bond P R h J w E hH hd]
  exact recoverBond_exact _ _ hdet

/-- Complete FD reconstruction on a finite periodic lattice from its two measured moments. -/
theorem fdTomography (P : Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (w E : ι → ℂ) (hH : H P R h J = Matrix.diagonal E)
    (hdet : ∀ d ∈ R.dirs, ((measured P w E).static d).det ≠ 0)
    (k : Axis) (hk : (measured P w E).mag k ≠ 0) :
    (∀ d ∈ R.dirs, (measured P w E).exchange d = J d) ∧
      (measured P w E).field R k = h := by
  have bonds := fun d hd => fdExchange P R h J w E hH (d := d) hd (hdet d hd)
  refine ⟨bonds, ?_⟩
  have bg : background (fun i j => (measured P w E).static (j-i)) R (measured P w E).exchange =
      background (fun i j => (measured P w E).static (j-i)) R J := by
    ext a b
    apply Finset.sum_congr rfl
    intro e he
    rw [bonds e he]
  have res : (measured P w E).residual R = fieldMap (measured P w E).mag h := by
    ext a b
    simp only [Data.residual, Matrix.sub_apply, bg, measured_onsite P R h J w E hH, add_sub_cancel_right]
  unfold Data.field
  rw [res]
  exact recoverField_exact _ _ k hk

/-- Two Hamiltonians with identical measured moments have identical couplings
under the FD rank conditions. Each model may use its own energy eigenbasis. -/
theorem fdIdentifiable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Spins S ι) (Q : Spins S κ) (R : Bonds S)
    (h h' : Axis → ℂ) (J J' : S → Tensor) (w E : ι → ℂ) (w' E' : κ → ℂ)
    (hP : H P R h J = Matrix.diagonal E) (hQ : H Q R h' J' = Matrix.diagonal E')
    (same : measured P w E = measured Q w' E')
    (hdet : ∀ d ∈ R.dirs, ((measured P w E).static d).det ≠ 0)
    (k : Axis) (hk : (measured P w E).mag k ≠ 0) :
    (∀ d ∈ R.dirs, J d = J' d) ∧ h = h' := by
  obtain ⟨bonds, fields⟩ := fdTomography P R h J w E hP hdet k hk
  rw [same] at bonds fields hdet hk
  obtain ⟨bonds', fields'⟩ := fdTomography Q R h' J' w' E' hQ hdet k hk
  exact ⟨fun d hd => (bonds d hd).symm.trans (bonds' d hd), fields.symm.trans fields'⟩

end DSFTomography
