import DSFTomography.SFPolarization
import Mathlib.LinearAlgebra.Matrix.Gershgorin

noncomputable section
namespace DSFTomography.SF
open DSFTomography HT HT.Pauli
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def driven (V : Volume S) (B : ℝ) (i : Axis) : Volume S :=
  { V with h := fun a => V.h a - if a=i then B else 0 }

theorem driven_matrix (V : Volume S) (B : ℝ) (i : Axis) :
    let W := driven V B i
    qubitH W.R W.h W.J = zeeman B i + qubitH V.R V.h V.J := by
  simp only [driven,qubitH,realH,H,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  have loc (r : S) : (∑ a, ((if a=i then B else 0 : ℝ) : ℂ) • (qubitSpins 1).σ r a) =
      (B:ℂ) • spinAt r i := by
    rw [Finset.sum_eq_single i]
    · simp [qubitSpins,spinAt,string,inBasis]
    · intro a _ ne; simp [ne]
    · simp
  simp_rw [loc]
  rw [zeeman,neg_smul,Finset.smul_sum]
  abel

def lowest (V : Volume S) : Config S :=
  (Finset.exists_min_image Finset.univ (energies V.R V.h V.J) Finset.univ_nonempty).choose
theorem lowest_le (V : Volume S) (x : Config S) : energies V.R V.h V.J (lowest V) ≤ energies V.R V.h V.J x :=
  (Finset.exists_min_image Finset.univ (energies V.R V.h V.J) Finset.univ_nonempty).choose_spec.2 x (Finset.mem_univ _)

private abbrev basis (V : Volume S) := energyBasis V.R V.h V.J
private theorem star_basis (V : Volume S) (A : Op (Config S)) :
    inBasis (basis V) A.conjTranspose = (inBasis (basis V) A).conjTranspose := by
  let U := (qubitH_hermitian V.R V.h V.J).eigenvectorUnitary
  change (U : Op (Config S)).conjTranspose * A.conjTranspose * (U : Op (Config S)) =
    ((U : Op (Config S)).conjTranspose * A * (U : Op (Config S))).conjTranspose
  simp [Matrix.mul_assoc]

def eigenState (V : Volume S) (m : Config S) : State (Config S) where
  ev := { toFun A := inBasis (basis V) A m m
          map_add' A C := by simp [inBasis,Matrix.mul_add,Matrix.add_mul]
          map_smul' c A := by simp [inBasis] }
  normed := by simp [inBasis]
  cs A C := by
    have hh := (indexState m).cs (inBasis (basis V) A) (inBasis (basis V) C)
    simpa only [indexState,LinearMap.coe_mk,AddHom.coe_mk,← star_basis, inBasis_mul] using hh

theorem eigenState_ground (V : Volume S) (m : Config S)
    (low : ∀ x, energies V.R V.h V.J m ≤ energies V.R V.h V.J x) : (eigenState V m).Ground (qubitH V.R V.h V.J) := by
  intro A
  have hh := indexGround m _ low (inBasis (basis V) A)
  have diag := (rotate_H V.R V.h V.J (basis V)).symm.trans (diagonalized V.R V.h V.J)
  rw [← diag] at hh
  change (((inBasis (basis V) A).conjTranspose * (inBasis (basis V) A * inBasis (basis V) (qubitH V.R V.h V.J) -
    inBasis (basis V) (qubitH V.R V.h V.J) * inBasis (basis V) A)) m m).re ≤ 0 at hh
  rw [← star_basis,inBasis_mul,inBasis_mul,← show ∀ X Y, inBasis (basis V) (X-Y) = inBasis (basis V) X-inBasis (basis V) Y by
    intros; simp [inBasis,Matrix.mul_sub,Matrix.sub_mul],inBasis_mul] at hh
  exact hh

def pureWeight (m : Config S) (j : Config S) : ℂ := if j=m then 1 else 0

/-- The two harmonics of the ground-state Lehmann spectrum, in the normalization
m/(2π). Elastic intensity is included in the static data. -/
def groundDSF (V : Volume S) (m : Config S) : Data (Momentum S) :=
  let A := measured (qubitSpins (basis V)) (pureWeight m) (fun j => (energies V.R V.h V.J j : ℂ))
  { static := fun q a b => toMomentum (fun d => A.static d a b) q
    first := fun q a b => toMomentum (fun d => A.first d a b) q }

theorem harmonics_ground (V : Volume S) (m : Config S) :
    (groundDSF V m).harmonics = measured (qubitSpins (basis V)) (pureWeight m) (fun j => (energies V.R V.h V.J j : ℂ)) := by
  simp [groundDSF,Data.harmonics,harmonic_toMomentum]

omit [AddCommGroup S] in
private theorem mean_pure (m : Config S) (A : Op (Config S)) : mean (pureWeight m) A = A m m := by
  simp [mean,pureWeight,ite_mul]

theorem static_ground (V : Volume S) (m : Config S) (d : S) (a b : Axis) :
    (groundDSF V m).harmonics.static d a b =
    avg (fun t => (eigenState V m).ev (spinAt t a * spinAt (t+d) b)) := by
  rw [harmonics_ground]
  unfold measured
  simp only [zeroMoment,qubitSpins,string,inBasis_mul,mean_pure]
  rfl

theorem mag_ground (V : Volume S) (m : Config S) (a : Axis) :
    (groundDSF V m).harmonics.mag a = avg (fun t => (eigenState V m).ev (spinAt t a)) := by
  rw [harmonics_ground]
  let P := qubitSpins (basis V)
  let w := pureWeight m
  let E := fun j => (energies V.R V.h V.J j : ℂ)
  change ((measured P w E).static 0 (a+1) (a+2)-(measured P w E).static 0 (a+2) (a+1))/(2*Complex.I) = _
  change (avg _ - avg _)/(2*Complex.I) = _
  rw [show ∀ f g : S → ℂ, (avg f - avg g)/(2*Complex.I) = avg (fun t => (f t - g t)/(2*Complex.I)) by
    intros; simp only [avg,← Finset.sum_div,Finset.sum_sub_distrib]; ring]
  apply congrArg avg
  funext t
  simp only [add_zero]
  change magnet P w t a = _
  rw [magnet_eq,mean_pure]
  rfl

omit [DecidableEq S] in
theorem avg_close {f : S → ℂ} {c : ℂ} {δ : ℝ} (bound : ∀ t, ‖f t-c‖ ≤ δ) :
    ‖avg f-c‖ ≤ δ := by
  have eq : avg f-c = (∑ t, (f t-c))/(Fintype.card S : ℂ) := by
    simp [avg,Finset.sum_sub_distrib,sub_div,Fintype.card_ne_zero]
  rw [eq,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0:ℝ)<Fintype.card S)).mpr
  calc
    _ ≤ ∑ t, ‖f t - c‖ := norm_sum_le .. 
    _ ≤ ∑ _t : S, δ := Finset.sum_le_sum (fun t _ => bound t)
    _ = _ := by simp [mul_comm]

/-- Entrywise proximity to the three coordinate projectors certifies the pooled
inverse by strict diagonal dominance. -/
theorem pooled_det (C : Axis → Tensor)
    (near : ∀ i a b, ‖C i a b - polarizedCorrelation i a b‖ ≤ 1/16) : (∑ i, C i).det ≠ 0 := by
  let M := ∑ i, C i
  have close (a b : Axis) : ‖M a b - (1 : Tensor) a b‖ ≤ 3/16 := by
    rw [← sum_polarized]
    simp only [M,Matrix.sum_apply,← Finset.sum_sub_distrib]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _ : Axis, (1/16:ℝ) := Finset.sum_le_sum (fun i _ => near i a b)
      _ = _ := by norm_num [Fin.sum_univ_three]
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have diag := close k k
  simp only [Matrix.one_apply_eq] at diag
  have diaglo := norm_sub_norm_le (1:ℂ) (M k k)
  rw [norm_sub_rev] at diaglo
  have off (j) (hj : j∈Finset.univ.erase k) : ‖M k j‖ ≤ 3/16 := by
    simpa [Matrix.one_apply_ne (Ne.symm (Finset.ne_of_mem_erase hj))] using close k j
  have total := Finset.sum_le_sum off
  change ∑ j ∈ Finset.univ.erase k, ‖M k j‖ < ‖M k k‖
  have card : (Finset.univ.erase k).card = 2 := by simp [Finset.card_erase_of_mem]
  simp only [Finset.sum_const,card,nsmul_eq_mul,Nat.cast_ofNat] at total
  norm_num at diaglo
  linarith

end DSFTomography.SF
