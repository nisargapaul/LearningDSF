import DSFTomography.HTDiagonalMoments

/-! Basis-free formulas for the four measured rows of the paper's diagonal map. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace DSFTomography.HT.Diagonal
open DSFTomography HT
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

abbrev spin (r : S) (a : Axis) := word (oneLabel r a)
abbrev dim (S : Type*) [Fintype S] [DecidableEq S] := (Fintype.card (Config S) : ℂ)

def quadraticCorrelation (K : Op (Config S)) (d : S) : Tensor := fun u v =>
  avg fun r => (K*K * (spin r u * spin (r+d) v)).trace / (2 * dim S)

def onsiteRow (K : Op (Config S)) (a : Axis) : ℝ :=
  (avg fun r => -(K * bracket (bracket (spin r a) K) (spin r a)).trace / dim S).re

private theorem axCases (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
private theorem axisAdd : (1+1:Axis)=2 ∧ (1+2:Axis)=0 ∧ (2+1:Axis)=0 ∧ (2+2:Axis)=1 := by decide

def contract (C J : Axis → Axis → ℝ) (a : Axis) : ℝ :=
  let b := a+1
  let c := a+2
  4*(J b b*C c c + J c c*C b b - J b c*C c b - J c b*C b c)

theorem bond_diag (C : Tensor) (J : Matrix Axis Axis ℝ) (a : Axis) :
    (bondMap C (fun u v => (J u v : ℂ)) a a).re = contract (fun u v => (C u v).re) J a := by
  rcases axCases a with rfl|rfl|rfl <;> norm_num [bondMap,contract,axisAdd,axisTable,Fin.sum_univ_three, Complex.re_ofReal_mul,
    Complex.mul_re,Complex.mul_im] <;> ring

variable (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ)
local notation "K" => qubitH R h J
local notation "U" => energyBasis R h J
local notation "E" => energies R h J
local notation "P" => qubitSpins U
local notation "e" => (fun i => (E i : ℂ))
private theorem traceEnergy : ∑ i, E i = 0 := by
  have tr := H_traceless P U (fun _ _ => rfl) R (fun a => (h a : ℂ)) (fun d a b => (J d a b : ℂ))
  change (realH P R h J).trace = 0 at tr
  rw [diagonalized,Matrix.trace_diagonal] at tr
  exact_mod_cast tr

private theorem spinHerm (r : S) (a : Axis) : ((P).σ r a).IsHermitian := by
  let V := (qubitH_hermitian R h J).eigenvectorUnitary
  change ((V : Op (Config S)).conjTranspose * spin r a * V).conjTranspose = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,spin,word_hermitian,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]; rfl

theorem coeff₂_zero_real (d : S) (a : Axis) : (coeff₂ P E d a 0).im = 0 := by
  rw [coeff₂_eq]
  have pop : gibbs 0 E = fun _ => Complex.ofReal ((Fintype.card (Config S) : ℝ)⁻¹) := by ext; simp [gibbs]
  simp only [pop,localSecond,avg,← Complex.ofReal_natCast,Complex.div_ofReal_im,Complex.im_sum]
  rw [Finset.sum_eq_zero (fun r _ => second_uniform_real _ E _ _ (spinHerm R h J r a) (spinHerm R h J (r+d) a)),zero_div]

private theorem diagK : inBasis U K = Matrix.diagonal e :=
  (rotate_H R h J U).symm.trans (diagonalized R h J)

private theorem firstWeight (T : Op (Config S)) :
    mean (fun i => -(dim S)⁻¹ * E i) (inBasis U T) = -(K*T).trace / dim S := by
  have tr : (K*T).trace = (Matrix.diagonal e * inBasis U T).trace := by
    rw [← diagK, inBasis_mul,inBasis,Matrix.trace_units_conj]
  rw [tr]
  simp only [mean,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,div_eq_mul_inv,
    Finset.sum_mul,← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem secondWeight (T : Op (Config S)) :
    mean (fun i => (dim S)⁻¹ * (E i : ℂ)^2/2) (inBasis U T) = (K*K*T).trace / (2*dim S) := by
  have tr : (K*K*T).trace = (Matrix.diagonal e * Matrix.diagonal e * inBasis U T).trace := by
    rw [← diagK, inBasis_mul,inBasis_mul,inBasis,Matrix.trace_units_conj]
  rw [tr,Matrix.diagonal_mul_diagonal]
  simp only [mean,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,div_eq_mul_inv,
    Finset.sum_mul,mul_inv_rev]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem staticW₁ {d : S} (hd : d ∈ R.dirs) :
    (measured P (fun i => -(dim S)⁻¹ * E i) e).static d = fun u v => -(J d u v : ℂ) := by
  funext a b
  have atSite (r : S) : m₀ (fun i => -(dim S)⁻¹ * E i) ((P).σ r a) ((P).σ (r+d) b) = -(J d a b : ℂ) := by
    have dist : r ≠ r+d := Ne.symm (by simpa using R.nonzero d hd)
    rw [zeroMoment]
    change mean _ (inBasis U _ * inBasis U _) = _
    rw [inBasis_mul,firstWeight]
    have pr := project_bond (qubitSpins (1 : (Op (Config S))ˣ)) 1 (fun _ _ => rfl) R
      (fun a => (h a : ℂ)) (fun d u v => (J d u v : ℂ)) hd r a b
    have two := string_pair (1 : (Op (Config S))ˣ) dist a b
    simp only [string,inBasis,Units.val_one,inv_one,one_mul,mul_one] at pr two
    change - (K * (spin r a * spin (r+d) b)).trace / _ = _
    rw [two,show (K * word (twoLabel r (r+d) a b)).trace = _ from pr]
    rw [neg_div,mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  change (∑ r, _) / _ = _
  simp_rw [atSite]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem bond_zero {d : S} (hd : d ∈ R.dirs) (a : Axis) :
    (coeff₂ P E d a 0).re = -8*(J d (a+1) (a+1)*J d (a+2) (a+2) -
      J d (a+1) (a+2)*J d (a+2) (a+1)) := by
  rw [coeff₂_zero,measured_bond P R _ _ _ _ (diagonalized R h J) hd,
    staticW₁ R h J hd,bond_diag]
  simp [contract]; ring

theorem bond_slope {d : S} (hd : d ∈ R.dirs) (a : Axis) :
    (derivWithin (coeff₂ P E d a) (Set.Ici 0) 0).re =
      contract (fun u v => (quadraticCorrelation K d u v).re) (J d) a := by
  rw [coeff₂_slope P E (traceEnergy R h J) (spinHerm R h J),
    measured_bond P R _ _ _ _ (diagonalized R h J) hd,bond_diag]
  congr 1
  funext u v
  congr 1
  apply congrArg avg
  funext r
  rw [zeroMoment]
  change mean _ (inBasis U _ * inBasis U _) = _
  rw [inBasis_mul,secondWeight]

private theorem bracket_basis (A B : Op (Config S)) :
    bracket (inBasis U A) (inBasis U B) = inBasis U (bracket A B) := by
  unfold bracket
  rw [inBasis_mul,inBasis_mul]
  simp only [inBasis, Matrix.mul_sub,Matrix.sub_mul]

theorem onsite_zero (a : Axis) : (coeff₂ P E 0 a 0).re = onsiteRow K a := by
  rw [coeff₂_zero,← avg_pair]
  unfold onsiteRow
  apply congrArg Complex.re; apply congrArg avg; funext r
  simp only [add_zero]
  rw [momentRule _ _ _ _ _ (diagK R h J)]
  change mean _ (bracket (bracket (inBasis U _) (inBasis U K)) (inBasis U _)) = _
  rw [bracket_basis,bracket_basis,firstWeight]

theorem onsite_field (a : Axis) :
    onsiteRow (qubitH R h (fun _ => 0)) a = 4*((h (a+1))^2+(h (a+2))^2) := by
  let P₀ := qubitSpins (energyBasis R h (fun _ => 0))
  let E₀ := energies R h (fun _ => 0)
  let w := fun i => -(dim S)⁻¹ * E₀ i
  let D := measured P₀ w (fun i => (E₀ i : ℂ))
  have mag (k : Axis) : D.mag k = -(h k : ℂ) := by
    have flip : ∀ u v, D.static 0 u v = -(Complex.I * sign u v * h (third u v)) := by
      intro u v
      have hv := static_onsite_deriv P₀ _ (fun _ _ => rfl) R h (fun _ => 0) E₀ (diagonalized _ _ _) u v
      have hv' : HasDerivAt (fun β => (thermalMoments P₀ β E₀).static 0 u v) (D.static 0 u v) 0 := by
        unfold D thermalMoments measured avg m₀
        apply HasDerivAt.div_const
        repeat' (apply HasDerivAt.fun_sum; intro _ _)
        apply HasDerivAt.mul_const
        simpa [w,dim,div_eq_mul_inv,mul_comm] using gibbs_slope E₀ (traceEnergy R h _) _
      exact hv'.unique hv
    rcases axCases k with rfl|rfl|rfl <;> simp [Data.mag,flip,axisAdd,axisTable] <;> field_simp <;> ring
  rw [← onsite_zero, coeff₂_zero,measured_onsite _ _ _ _ _ _ (diagonalized R h _) a a]
  change (fieldMap D.mag (fun k => (h k : ℂ)) a a + background _ R (fun _ _ _ => (0:ℂ)) a a).re = _
  simp only [background,zero_mul,Finset.sum_const_zero,add_zero,fieldMap,mag]
  rcases axCases a with rfl|rfl|rfl <;> norm_num [axisAdd,axisTable,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im] <;> ring

end DSFTomography.HT.Diagonal
