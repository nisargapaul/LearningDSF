import DSFTomography.SFClusterThermodynamic
import DSFTomography.SFClusterEvaluation
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! Uniform analytic functions of the sources with values in the convergent
sequences of box measurements. The point at infinity is the bulk value. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology ContDiff
variable {ν : ℕ} (R : Bonds (Site ν))

abbrev Trace := C(OnePoint ℕ, ℂ)
def sample : Local R →L[ℂ] Trace :=
  LinearMap.mkContinuous {
    toFun := fun v => OnePoint.continuousMapMkNat (fun n => vacuumAt R n v.val) (vacuumLimit R v) (tendsto_vacuum R v)
    map_add' := by
      intro x y; ext t; induction t using OnePoint.rec with
      | infty => exact map_add (vacuumLimit R) x y
      | coe n => exact map_add (vacuumAt R n) x.val y.val
    map_smul' := by
      intro c x; ext t; induction t using OnePoint.rec with
      | infty => exact map_smul (vacuumLimit R) c x
      | coe n => exact map_smul (vacuumAt R n) c x.val }
    1 (by
      intro x; rw [one_mul]; apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr; intro t
      induction t using OnePoint.rec with
      | infty => exact le_of_tendsto (tendsto_vacuum R x).norm (Eventually.of_forall fun n => vacuumAt_le R n x.val)
      | coe n => exact vacuumAt_le R n x.val)

structure Branch where
  a : Sources R → Local R
  analytic : AnalyticAt ℂ a 0
  zero : a 0=0
  solves : ∀ᶠ p in 𝓝 0, (a p).val = freeResidual R (a p).val -
    ∑ j, p j • localFlip R (flipSites R j) (expAmplitude R (localResponse R (signSites R j) (a p).val))

theorem branch_exists : Nonempty (Branch R) := by
  obtain ⟨a,h,z,s⟩ := local_branch R
  exact ⟨a,h,z,s⟩

namespace Branch
variable {R} (b : Branch R)
def wordColumn (A D : Pattern ν) (p : Sources R) : Local R :=
  XOp R A (localExp R (DOp R D (b.a p)))
def rel (p : Sources R) : Local R →L[ℂ] Local R :=
  let ex (D) := restrictBilin R (localExcitation R D) (excitation_preserves R D);
  -ex [0] (localExp R (DOp R [0] (b.a p)) - localVac R) +
    ∑ j, p j • ex (signSites R j) (b.wordColumn (flipSites R j) (signSites R j) p)

theorem val_rel (p : Sources R) (x : Local R) :
    (b.rel p x).val = errorOperator R p (b.a p).val x.val := by
  have ex (D) (u x : Local R) : ((restrictBilin R (localExcitation R D) (excitation_preserves R D) u) x).val =
      localExcitation R D u.val x.val := rfl
  have col (A D) : (b.wordColumn A D p).val = localFlip R A (expAmplitude R (localResponse R D (b.a p).val)) :=
    congrArg (localFlip R A) (val_localExp R _)
  simp only [rel,errorOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,Submodule.coe_add,Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul_of_tower,ex,col,
    Submodule.coe_sub,val_localExp]; rfl

theorem analytic_col (A D) : AnalyticAt ℂ (b.wordColumn A D) 0 :=
  ((XOp R A).analyticAt _).comp ((localExp_analytic R _).comp (((DOp R D).analyticAt _).comp b.analytic))
theorem analytic_rel : AnalyticAt ℂ b.rel 0 := by
  have ea (D) : AnalyticAt ℂ (fun p => localExp R (DOp R D (b.a p))) 0 :=
    (localExp_analytic R _).comp (((DOp R D).analyticAt _).comp b.analytic)
  apply AnalyticAt.add
  · exact (((restrictBilin R _ (excitation_preserves R [0])).analyticAt _).comp ((ea [0]).sub analyticAt_const)).neg
  · apply Finset.analyticAt_fun_sum; intro j _
    exact ((ContinuousLinearMap.proj j : Sources R →L[ℂ] ℂ).analyticAt 0).smul
      (((restrictBilin R _ (excitation_preserves R _)).analyticAt _).comp (b.analytic_col _ _))

@[simp] theorem rel_zero : b.rel 0=0 := by
  ext z : 1
  simp [rel,b.zero,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
def inverse (p : Sources R) := Ring.inverse (1+b.rel p)
theorem analytic_inverse : AnalyticAt ℂ b.inverse 0 := by
  have h : AnalyticAt ℂ Ring.inverse (1+b.rel 0) := by
    rw [rel_zero,add_zero]; exact analyticAt_inverse (𝕜 := ℂ) (1 : (Local R →L[ℂ] Local R)ˣ)
  exact h.comp (g := Ring.inverse) (f := fun p => 1+b.rel p) (analyticAt_const.add b.analytic_rel)
theorem inverse_ok : ∀ᶠ p in 𝓝 0, (1+b.rel p)*b.inverse p=1 := by
  have sm := b.analytic_rel.continuousAt.norm.eventually_lt_const (show ‖b.rel 0‖<1 by simp)
  exact sm.mono fun p hp => Ring.mul_inverse_cancel _ (by simpa using isUnit_one_sub_of_norm_lt_one (x := -b.rel p) (by simpa using hp))

def obs (A D : Pattern ν) (p : Sources R) : Trace := sample R (b.inverse p (b.wordColumn A D p))
def singleFlip (s : Site ν) : Local R := XOp R [s] (localVac R)
def cen (r s : Site ν) (p : Sources R) : Trace :=
  (2:ℂ) • sample R (b.inverse p (XOp R [r] (b.rel p (singleFlip (R:=R) s))))

private theorem app {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : Sources R → E →L[ℂ] E} {g : Sources R → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (fun p => f p (g p)) 0 := by
  exact (hf.contDiffAt.clm_apply (n := ω) hg.contDiffAt).analyticAt

theorem analytic_obs (A D) : AnalyticAt ℂ (b.obs A D) 0 :=
  ((sample R).analyticAt _).comp (app b.analytic_inverse (b.analytic_col A D))
theorem analytic_cen (r s) : AnalyticAt ℂ (b.cen r s) 0 := by
  unfold cen
  apply AnalyticAt.smul (𝕜 := ℂ) (f := fun _ : Sources R => (2:ℂ)) analyticAt_const
  apply ((sample R).analyticAt _).comp
  apply app b.analytic_inverse
  apply ((XOp R [r]).analyticAt _).comp
  exact ((ContinuousLinearMap.apply ℂ (Local R) (singleFlip (R:=R) s)).analyticAt _).comp b.analytic_rel

end Branch
end DSFTomography.SF.Cluster
