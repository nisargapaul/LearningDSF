import DSFTomography.SFClusterAlgebra
import DSFTomography.SFPaperLimit
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Bounded spin-flip families on all periodic boxes. The supremum norm
keeps one radius for every box. -/
noncomputable section
set_option maxHeartbeats 700000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology ContDiff ENNReal
variable {E F : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℂ (F n)]

private def bounded (v : ∀ n, E n) (c : ℝ) (h : ∀ n, ‖v n‖ ≤ c) : lp E ∞ :=
  ⟨v,memℓp_infty ⟨c,by rintro _ ⟨n,rfl⟩; exact h n⟩⟩

def familyMap (L : ∀ n, E n →L[ℂ] F n) (c : ℝ) (h : ∀ n, ‖L n‖ ≤ c) :
    lp E ∞ →L[ℂ] lp F ∞ :=
  let b (x : lp E ∞) (n : ℕ) : ‖L n (x n)‖ ≤ c*‖x‖ :=
    ((L n).le_opNorm _).trans (mul_le_mul (h n) (lp.norm_apply_le_norm ENNReal.top_ne_zero x n)
      (norm_nonneg _) ((norm_nonneg _).trans (h n)))
  LinearMap.mkContinuous {
    toFun := fun x => bounded _ _ (b x)
    map_add' := fun _ _ => Subtype.ext (funext fun n => (L n).map_add _ _)
    map_smul' := fun _ _ => Subtype.ext (funext fun n => (L n).map_smul _ _) }
    c (fun x => lp.norm_le_of_forall_le' _ (b x))

variable {ν : ℕ} (R : Bonds (Site ν))
abbrev Amplitudes : Type := lp (fun n : ℕ => Amp (Box R n)) ∞
abbrev Operators := Amplitudes R →L[ℂ] Amplitudes R

def vacuumFamily : Amplitudes R := bounded (fun _ => basis 0) 1 (by simp)
def vacuumColumn : Operators R →L[ℂ] Amplitudes R :=
  ContinuousLinearMap.apply ℂ _ (vacuumFamily R)

def convolutionFamily : Amplitudes R →L[ℂ] Operators R :=
  let C (x : Amplitudes R) := familyMap (fun n => convolute (x n)) ‖x‖
    (fun n => (convolution_bound (x n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero x n))
  LinearMap.mkContinuous {
    toFun := C
    map_add' := by intro x y; ext w : 1; exact Subtype.ext (funext fun n =>
      congrArg (fun L : Amp (Box R n) →L[ℂ] Amp (Box R n) => L (w n)) (map_add convolute (x n) (y n)))
    map_smul' := by intro k x; ext w : 1; exact Subtype.ext (funext fun n =>
      congrArg (fun L : Amp (Box R n) →L[ℂ] Amp (Box R n) => L (w n)) (map_smul convolute k (x n))) }
    1 (fun x => by
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro y
      exact lp.norm_le_of_forall_le' _ fun n => ((convolute (x n)).le_opNorm _).trans
        (mul_le_mul ((convolution_bound (x n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero x n))
          (lp.norm_apply_le_norm ENNReal.top_ne_zero y n) (norm_nonneg _) (norm_nonneg _)))

theorem convolute_vac (S : Type*) [Fintype S] [DecidableEq S] (x : Amp S) :
    convolute x (basis 0) = x := by
  change (∑ y, x y • flip y) (basis 0) = _
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,flip,columns_basis,add_zero]
  exact sum_basis x

theorem column_convolution (x : Amplitudes R) : vacuumColumn R (convolutionFamily R x) = x :=
  Subtype.ext (funext fun n => convolute_vac _ (x n))

def expAmplitude (x : Amplitudes R) : Amplitudes R :=
  vacuumColumn R (exp ℂ (convolutionFamily R x))

@[simp] theorem expAmplitude_zero : expAmplitude R 0 = vacuumFamily R := by
  simp only [expAmplitude,map_zero,exp_zero]; rfl

theorem expAmplitude_analytic (x : Amplitudes R) : AnalyticAt ℂ (expAmplitude R) x :=
  ((vacuumColumn R).analyticAt _).comp ((exp_analytic (𝕂 := ℂ) _).comp ((convolutionFamily R).analyticAt x))

def localResponse (D : List (Site ν)) : Amplitudes R →L[ℂ] Amplitudes R :=
  familyMap (fun n => response (D.map (periodicSite R n))) D.length
    (fun n => by simpa using response_bound (D.map (periodicSite R n)))

/-- X flips the spin, Z changes its sign, and Y = i X Z. -/
def xSites (r : Site ν) (a : Axis) := if a=2 then [] else [r]
def zSites (r : Site ν) (a : Axis) := if a=0 then [] else [r]
def flipSites : Shape R → List (Site ν)
  | .inl a => xSites 0 a
  | .inr (d,a,b) => xSites 0 a ++ xSites d.val b
def signSites : Shape R → List (Site ν)
  | .inl a => zSites 0 a
  | .inr (d,a,b) => zSites 0 a ++ zSites d.val b

def bitSum {S : Type*} [DecidableEq S] (A : List S) : Config S :=
  (A.map fun s => fun t => if t=s then (1 : Fin 2) else 0).sum

def localFlip (A : List (Site ν)) : Amplitudes R →L[ℂ] Amplitudes R :=
  familyMap (fun n => flip (bitSum (A.map (periodicSite R n)))) 1 (fun _ => flip_bound _)

abbrev Sources := Shape R → ℂ
def freeResidual (x : Amplitudes R) :=
  expAmplitude R (localResponse R [0] x) - vacuumFamily R - localResponse R [0] x

end DSFTomography.SF.Cluster
