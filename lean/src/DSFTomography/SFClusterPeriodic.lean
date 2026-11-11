import DSFTomography.SFClusterFamily
import DSFTomography.SFClusterEigen

/-! Evaluation of the common analytic branch in each physical box. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν))

def atBox (n : ℕ) : Amplitudes R →L[ℂ] Amp (Box R n) :=
  LinearMap.mkContinuous {
    toFun := fun x => x n
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
    1 (fun x => by simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero x n)

theorem atBox_bound (n : ℕ) : ‖atBox R n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero x n

theorem atBox_exp (n : ℕ) (x : Amplitudes R) :
    atBox R n (expAmplitude R x) = ampExp (x n) := by
  let C := convolutionFamily R x
  let c : Operator (Box R n) := convolute (x n)
  have power (k : ℕ) (v : Amplitudes R) : atBox R n ((C^k) v) = (c^k) (v n) := by
    induction k generalizing v with
    | zero => rfl
    | succ k ih => rw [pow_succ,pow_succ]; exact ih (C v)
  let vac := vacuumFamily R
  let l := (atBox R n).comp (ContinuousLinearMap.apply ℂ (Amplitudes R) vac)
  let r := ContinuousLinearMap.apply ℂ (Amp (Box R n)) (basis (0 : Config (Box R n)))
  have h := l.hasSum (exp_series_hasSum_exp' (𝕂 := ℂ) C)
  have g := r.hasSum (exp_series_hasSum_exp' (𝕂 := ℂ) c)
  apply (h.congr_fun _).unique g
  intro k
  simp only [map_smul]
  exact congrArg (_ • ·) (power k vac).symm

def boxFlips (n : ℕ) (j : Shape R) := bitSum ((flipSites R j).map (periodicSite R n))
def boxSigns (n : ℕ) (j : Shape R) := (signSites R j).map (periodicSite R n)

theorem equation_in_boxes (p : Sources R) (v : Amplitudes R)
    (eqn : v = freeResidual R v -
      ∑ j, p j • localFlip R (flipSites R j) (expAmplitude R (localResponse R (signSites R j) v))) :
    ∀ n, FiniteEquation (boxFlips R n) (boxSigns R n) p (v n) := by
  intro n
  have vp (x : Amplitudes R) : x n = atBox R n x := rfl
  have flipAt (A) (x : Amplitudes R) : atBox R n (localFlip R A x) =
      flip (bitSum (A.map (periodicSite R n))) (atBox R n x) := rfl
  have respAt (D) (x : Amplitudes R) : atBox R n (localResponse R D x) =
      response (D.map (periodicSite R n)) (atBox R n x) := rfl
  have h := congrArg (atBox R n) eqn
  simp only [freeResidual,map_sub,map_sum,map_smul,flipAt,atBox_exp] at h
  simp only [vp (localResponse R _ v),respAt,List.map_cons,List.map_nil] at h
  exact h

end DSFTomography.SF.Cluster
