import DSFTomography.HTSpectrum
import Mathlib.Topology.Instances.Matrix

/-! An exact full-channel strong-field inverse from the sum of the three
stationary moment equations. Only the sum of the bond correlations needs to
be nonsingular. A single polarized acquisition has rank one in the limit. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography Filter
open scoped Topology

variable {S ι : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]

def polarizedCorrelation (i : Axis) : Tensor := fun a b => if a=i ∧ b=i then 1 else 0

theorem sum_polarized : ∑ i, polarizedCorrelation i = 1 := by
  ext a b
  simp only [Matrix.sum_apply,polarizedCorrelation, Matrix.one_apply]
  by_cases hab : a=b
  · subst b; simp
  · have ne (i : Axis) : ¬(a=i ∧ b=i) := fun h => hab (h.1.trans h.2.symm)
    simp [ne,hab]

theorem pooled_nonsingular_near_polarization :
    ∀ᶠ C : Axis → Tensor in 𝓝 polarizedCorrelation, (∑ i, C i).det ≠ 0 := by
  have tend : Continuous (fun C : Axis → Tensor => (∑ i, C i).det) := by fun_prop
  have nz : (∑ i, polarizedCorrelation i).det ≠ 0 := by rw [sum_polarized, Matrix.det_one]; exact one_ne_zero
  exact tend.continuousAt.eventually_ne nz

def pooledExchange (A : Axis → Data S) (d : S) :=
  recoverBond (∑ i, (A i).static d) (∑ i, (A i).force d)

def pooledField (A : Axis → Data S) (R : Bonds S) (i : Axis) (B : ℂ) : Axis → ℂ :=
  fun a => recoverField (A i).mag ((A i).force 0 -
    background (fun s t => (A i).static (t-s)) R (pooledExchange A)) i a + (if a=i then B else 0)

theorem bondMap_sum (C : Axis → Tensor) (J : Tensor) :
    ∑ i, bondMap (C i) J = bondMap (∑ i, C i) J := by
  ext a b
  simp only [Matrix.sum_apply,bondMap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.sum_comm

def fieldMoments (P : Axis → Spins S ι) (w E : Axis → ι → ℂ) (i : Axis) := measured (P i) (w i) (E i)

theorem threeField_recovery (P : Axis → Spins S ι) (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)
    (B : ℂ) (w E : Axis → ι → ℂ)
    (stationary : ∀ i, H (P i) R (fun a => h a - if a=i then B else 0) J = Matrix.diagonal (E i))
    (nonsing : ∀ d ∈ R.dirs, (∑ i, (fieldMoments P w E i).static d).det ≠ 0)
    (i : Axis) (mag : (fieldMoments P w E i).mag i ≠ 0) :
    (∀ d ∈ R.dirs, pooledExchange (fieldMoments P w E) d = J d) ∧
    pooledField (fieldMoments P w E) R i B = h := by
  let A := fieldMoments P w E
  have forces (j d) (hd : d ∈ R.dirs) : (A j).force d = bondMap ((A j).static d) (J d) :=
    measured_bond _ R _ _ _ _ (stationary j) hd
  have ex (d) (hd : d ∈ R.dirs) : pooledExchange A d = J d := by
    unfold pooledExchange
    simp_rw [fun j => forces j d hd]
    rw [bondMap_sum,recoverBond_exact _ _ (nonsing _ hd)]
  refine ⟨ex,?_⟩
  have bg : background (fun s t => (A i).static (t-s)) R (pooledExchange A) =
      background (fun s t => (A i).static (t-s)) R J := by
    ext a b; unfold background
    apply Finset.sum_congr rfl
    intro e he; rw [ex _ he]
  have field : (A i).force 0 - background (fun s t => (A i).static (t-s)) R J =
      fieldMap (A i).mag (fun a => h a - if a=i then B else 0) := by
    ext a b
    exact sub_eq_of_eq_add (measured_onsite _ R _ _ _ _ (stationary i) a b)
  funext a
  change recoverField _ (_ - _) i a + _ = _
  rw [bg,field,recoverField_exact _ _ _ mag,sub_add_cancel]

end DSFTomography.SF
