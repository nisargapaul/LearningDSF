import DSFTomography.HTPeriodicBounds
import DSFTomography.SFThreeFields

/-! Local ground-state stability implies polarization uniformly in the volume.
The probe raising operator removes a reversed spin at cost 2B. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT HT.Pauli
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Cauchy–Schwarz for a normalized state, in a form valid also for mixtures. -/
structure State (ι : Type*) [Fintype ι] [DecidableEq ι] where
  ev : Op ι →ₗ[ℂ] ℂ
  normed : ev 1 = 1
  cs : ∀ A B, ‖ev (A.conjTranspose*B)‖^2 ≤ (ev (A.conjTranspose*A)).re * (ev (B.conjTranspose*B)).re

/-- Local stability is the usual ground-state inequality
Re ω(A†[H,A]) ≥ 0, with ad(A) = [A,H] in this package. -/
def State.Ground (ρ : State ι) (H : Op ι) := ∀ A, (ρ.ev (A.conjTranspose * ad H A)).re ≤ 0

def indexState (m : ι) : State ι where
  ev := { toFun := fun A => A m m, map_add' := by simp, map_smul' := by simp }
  normed := by simp
  cs A B := by
    let col (X : Op ι) (j : ι) := ‖X j m‖
    have sq (X : Op ι) : ((X.conjTranspose*X) m m).re = ∑ j, (col X j)^2 := by
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,col]
      apply Finset.sum_congr rfl
      intro j _; rw [Complex.sq_norm,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re]
    have b : ‖(A.conjTranspose*B) m m‖ ≤ ∑ j, col A j*col B j := by
      simpa [Matrix.mul_apply,col] using norm_sum_le Finset.univ (fun j => star (A j m)*B j m)
    change ‖(A.conjTranspose*B) m m‖^2 ≤ _
    change _ ≤ ((A.conjTranspose*A) m m).re * ((B.conjTranspose*B) m m).re
    rw [sq,sq]
    exact (pow_le_pow_left₀ (norm_nonneg _) b 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

theorem indexGround (m : ι) (E : ι → ℝ) (lowest : ∀ j, E m ≤ E j) :
    (indexState m).Ground (Matrix.diagonal fun j => (E j : ℂ)) := by
  intro A
  change ((A.conjTranspose * (A * Matrix.diagonal (fun j => (E j : ℂ)) - Matrix.diagonal (fun j => (E j : ℂ)) * A)) m m).re ≤ 0
  rw [Matrix.mul_apply]
  simp only [Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,Complex.re_sum,
    Matrix.conjTranspose_apply]
  apply Finset.sum_nonpos
  intro j _
  have eq : star (A j m) * (A j m * (E m : ℂ) - (E j : ℂ) * A j m) =
      (star (A j m)*A j m) * ((E m:ℂ)-E j) := by ring
  rw [eq,Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  simpa [← Complex.ofReal_sub] using mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg (A j m)) (sub_nonpos.mpr (lowest j))

theorem State.unit_bound (ρ : State ι) {A : Op ι} (unit : A.conjTranspose*A=1) : ‖ρ.ev A‖ ≤ 1 := by
  have h := ρ.cs 1 A
  simp [unit,ρ.normed] at h
  nlinarith [norm_nonneg (ρ.ev A)]

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem word_unit (w : Label S) : (word w).conjTranspose * word w = 1 := by
  have square (l : Letter) : pauli l * pauli l = 1 := by
    cases l with
    | none => simp [pauli]
    | some a =>
      have : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
      rcases this with rfl|rfl|rfl <;> ext j k <;> fin_cases j <;> fin_cases k <;>
        norm_num [pauliValues,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,Complex.I_mul_I]
  rw [word_hermitian,word,tensor_mul]
  simp_rw [square]
  exact word_empty (S := S)

abbrev spinAt (r : S) (i : Axis) := word (oneLabel r i)
def raise (r : S) (i : Axis) : Op (Config S) :=
  (1/2 : ℂ) • spinAt r (i+1) + (Complex.I/2) • spinAt r (i+2)
def zeeman (B : ℝ) (i : Axis) : Op (Config S) := -(B : ℂ) • ∑ r, spinAt r i

private theorem raise_star (r : S) (i : Axis) : (raise r i).conjTranspose =
    (1/2 : ℂ) • spinAt r (i+1) - (Complex.I/2) • spinAt r (i+2) := by
  simp [raise,spinAt,Matrix.conjTranspose_smul,word_hermitian,sub_eq_add_neg,neg_div]

private theorem cyclic_product (r : S) (a : Axis) : spinAt r a * spinAt r (a+1) = Complex.I • spinAt r (a+2) := by
  have ne : a ≠ a+1 := by fin_cases a <;> decide
  have signs : sign a (a+1) = 1 ∧ third a (a+1) = a+2 := by fin_cases a <;> exact ⟨rfl,rfl⟩
  simpa [spinAt,signs,string,inBasis] using string_same_site (1 : (Op (Config S))ˣ) r a (a+1) ne

private theorem cycle (i : Axis) : (i+1)+1=i+2 ∧ (i+1)+2=i ∧ (i+2)+1=i ∧ (i+2)+2=i+1 := by fin_cases i <;> decide

private theorem raise_norm (r : S) (i : Axis) :
    (raise r i).conjTranspose * raise r i = (1/2 : ℂ) • (1-spinAt r i) := by
  have pq : spinAt r (i+1) * spinAt r (i+2) = Complex.I • spinAt r i := by
    simpa only [(cycle i).1,(cycle i).2.1] using cyclic_product r (i+1)
  have qp := congrArg Matrix.conjTranspose pq
  simp only [spinAt,Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,word_hermitian,
    Complex.star_def,Complex.conj_I,neg_smul] at qp
  have sq (a : Axis) : spinAt r a * spinAt r a = 1 := by simpa [word_hermitian] using word_unit (oneLabel r a)
  rw [raise_star,raise,Matrix.sub_mul,Matrix.mul_add,Matrix.mul_add]
  simp only [Matrix.smul_mul,Matrix.mul_smul,sq,pq,qp,smul_smul,smul_sub,smul_neg]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

private theorem zeeman_raise (r : S) (i : Axis) (B : ℝ) :
    ad (zeeman B i) (raise r i) = (2*(B:ℂ)) • raise r i := by
  have spin (a : Axis) : ad (zeeman B i) (spinAt r a) = (-(B:ℂ)*phase a i) • spinAt r (third a i) := by
    change bracket (spinAt r a) (zeeman B i) = _
    have atSite (j : S) : bracket (spinAt r a) (spinAt j i) = if r=j then phase a i • spinAt j (third a i) else 0 := by
      simpa [qubitSpins,string,inBasis,spinAt] using (qubitSpins (1 : (Op (Config S))ˣ)).pauli r a j i
    rw [zeeman,bracket_smul]
    simp only [bracket,Matrix.mul_sum,Matrix.sum_mul,← Finset.sum_sub_distrib]
    change -(B:ℂ) • (∑ j, bracket (spinAt r a) (spinAt j i)) = _
    simp [atSite,smul_smul]
  have phases : phase (i+1) i = -(2*Complex.I) ∧ third (i+1) i = i+2 ∧
      phase (i+2) i=2*Complex.I ∧ third (i+2) i=i+1 := by
    have signs : sign (i+1) i = -1 ∧ third (i+1) i = i+2 ∧ sign (i+2) i = 1 ∧ third (i+2) i = i+1 := by fin_cases i <;> exact ⟨rfl,rfl,rfl,rfl⟩
    simp [phase,signs]
  simp only [raise,map_add,map_smul,spin,phases,smul_smul,smul_add]
  match_scalars <;> ring_nf
  norm_num [Complex.I_sq]

private theorem raise_test {T : Type*} [Fintype T] (ρ : State (Config S)) (I : PauliInteraction S T)
    {g : ℝ} (hg : 0≤g) (incident : I.SiteBound g) (r : S) (i : Axis) :
    ‖ρ.ev ((raise r i).conjTranspose * ad I.matrix (raise r i))‖ ≤ 2*g := by
  let L := ρ.ev.comp (LinearMap.mulLeft ℂ (raise r i).conjTranspose)
  have productBound (a : Axis) (w : Label S) : ‖ρ.ev (spinAt r a * word w)‖ ≤ 1 := by
    rw [spinAt,product,map_smul,norm_smul,phase_norm,one_mul]
    exact ρ.unit_bound (word_unit _)
  have cap (w : Label S) : ‖L (word w)‖ ≤ 1 := by
    simp only [L,LinearMap.comp_apply,LinearMap.mulLeft_apply,raise_star,Matrix.sub_mul,Matrix.smul_mul,map_sub,map_smul]
    apply (norm_sub_le ..).trans
    simp only [norm_smul,norm_div,norm_one,Complex.norm_I,Complex.norm_ofNat]
    linarith [productBound (i+1) w,productBound (i+2) w]
  have one (a : Axis) : ‖L (ad I.matrix (spinAt r a))‖ ≤ 2*g := by
    simpa [spinAt] using I.iter_bound hg (by norm_num : (0:ℝ)≤1) incident L cap 1 (oneLabel r a) 1 (by simp [supp_one])
  change ‖L (ad I.matrix (raise r i))‖ ≤ _
  simp only [raise,map_add,map_smul]
  apply (norm_add_le ..).trans
  simp only [norm_smul,norm_div,norm_one,Complex.norm_I,Complex.norm_ofNat]
  linarith [one (i+1),one (i+2)]

theorem ground_polarization {T : Type*} [Fintype T] (ρ : State (Config S))
    (I : PauliInteraction S T) {g B : ℝ} (hB : 0 < B) (hg : 0≤g) (incident : I.SiteBound g)
    (i : Axis) (ground : ρ.Ground (zeeman B i + I.matrix)) (r : S) :
    1 - (ρ.ev (spinAt r i)).re ≤ 2*g/B := by
  have hs := ground (raise r i)
  have split : ad (zeeman B i + I.matrix) (raise r i) =
      ad (zeeman B i) (raise r i) + ad I.matrix (raise r i) := bracket_add .. 
  rw [split,zeeman_raise,Matrix.mul_add,Matrix.mul_smul,raise_norm,smul_smul,map_add,map_smul,map_sub,ρ.normed] at hs
  have le := raise_test ρ I hg incident r i
  have low := (abs_le.mp (Complex.abs_re_le_norm (ρ.ev ((raise r i).conjTranspose * ad I.matrix (raise r i))))).1
  simp [Complex.mul_re,Complex.sub_re] at hs
  apply (le_div_iff₀ hB).mpr
  nlinarith
end DSFTomography.SF
