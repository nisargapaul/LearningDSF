import DSFTomography.SFClusterGap

/-! The branch isolated in the sup norm over periodic boxes is the physical
simple ground state throughout one neighborhood of the polarized model. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology ENNReal
variable {ν : ℕ} (R : Bonds (Site ν))

def localExcitation (D : List (Site ν)) : Amplitudes R →L[ℂ] Operators R :=
  let b (x : Amplitudes R) (n : ℕ) : ‖excitation (D.map (periodicSite R n)) (x n)‖ ≤ D.length*‖x‖ :=
    ((excitation _).le_opNorm _).trans (mul_le_mul (by simpa using excitation_bound (D.map (periodicSite R n)))
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x n) (norm_nonneg _) (by positivity))
  let C (x : Amplitudes R) := familyMap (fun n => excitation (D.map (periodicSite R n)) (x n)) _ (b x)
  LinearMap.mkContinuous {
    toFun := C
    map_add' := by intro x y; ext w : 1; exact Subtype.ext (funext fun n =>
      congrArg (fun L : Operator (Box R n) => L (w n)) (map_add (excitation _) (x n) (y n)))
    map_smul' := by intro c x; ext w : 1; exact Subtype.ext (funext fun n =>
      congrArg (fun L : Operator (Box R n) => L (w n)) (map_smul (excitation _) c (x n))) }
    D.length (fun x => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro y
      exact lp.norm_le_of_forall_le' _ fun n => ((excitation _ (x n)).le_opNorm _).trans
        (mul_le_mul (b x n) (lp.norm_apply_le_norm ENNReal.top_ne_zero y n) (norm_nonneg _) (by positivity)))

def errorOperator (p : Sources R) (v : Amplitudes R) : Operators R :=
  -localExcitation R [0] (expAmplitude R (localResponse R [0] v) - vacuumFamily R) +
  ∑ j, p j • localExcitation R (signSites R j)
    (localFlip R (flipSites R j) (expAmplitude R (localResponse R (signSites R j) v)))

theorem error_analytic {a : Sources R → Amplitudes R} (h : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (fun p => errorOperator R p (a p)) 0 := by
  have ea (D) : AnalyticAt ℂ (fun p => expAmplitude R (localResponse R D (a p))) 0 :=
    (expAmplitude_analytic R _).comp (((localResponse R D).analyticAt _).comp h)
  apply AnalyticAt.add
  · exact (((localExcitation R [0]).analyticAt _).comp ((ea [0]).sub analyticAt_const)).neg
  · apply Finset.analyticAt_fun_sum; intro j _
    exact ((ContinuousLinearMap.proj j : Sources R →L[ℂ] ℂ).analyticAt 0).smul
      (((localExcitation R _).analyticAt _).comp (((localFlip R _).analyticAt _).comp (ea _)))

theorem error_atBox (p : Sources R) (v x : Amplitudes R) (n : ℕ) :
    atBox R n (errorOperator R p v x) =
      correction (boxFlips R n) (boxSigns R n) p (v n) (x n) := by
  have act (D u) : atBox R n (localExcitation R D u x) = excitation (D.map (periodicSite R n)) (atBox R n u) (x n) := rfl
  have flipAt (A u) : atBox R n (localFlip R A u) =
      flip (bitSum (A.map (periodicSite R n))) (atBox R n u) := rfl
  simp only [errorOperator,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,map_add,map_neg,map_sum,map_smul,act,flipAt,ContinuousLinearMap.sub_apply,map_sub,atBox_exp,correction,boxFlips,boxSigns]
  rfl

theorem correction_le (p : Sources R) (v : Amplitudes R) (n : ℕ) :
    ‖correction (boxFlips R n) (boxSigns R n) p (v n)‖ ≤ ‖errorOperator R p v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro u
  let x : Amplitudes R := lp.single ∞ n u
  have self : x n = u := lp.single_apply_self ..
  have normx : ‖x‖ = ‖u‖ := lp.norm_single (by simp) _ _
  rw [← self,← error_atBox]
  calc
    _ ≤ ‖errorOperator R p v x‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ _
    _ ≤ ‖errorOperator R p v‖*‖x‖ := (errorOperator R p v).le_opNorm _
    _ = _ := by rw [normx,self]

def GroundNeighborhood (a : Sources R → Amplitudes R) : Prop :=
  ∀ᶠ p in 𝓝 0, ∀ n,
      let H := clusterH (boxFlips R n) (boxSigns R n) p
      let ψ := eigenKet (a p n)
      let E := -(Fintype.card (Box R n):ℂ)*(a p n) 0
      ψ ≠ 0 ∧ H ψ = E • ψ ∧
        ∀ μ (ξ : Amp (Box R n)), ξ ≠ 0 → H ξ = μ • ξ → μ.re ≤ E.re + 1 →
          μ = E ∧ ∃ c : ℂ, ξ = c • ψ

theorem ground_of_branch (a : Sources R → Amplitudes R) (ha : AnalyticAt ℂ a 0) (z : a 0=0)
    (eqn : ∀ᶠ p in 𝓝 0, a p = freeResidual R (a p) -
      ∑ j, p j • localFlip R (flipSites R j) (expAmplitude R (localResponse R (signSites R j) (a p)))) :
    GroundNeighborhood R a := by
  have small := (error_analytic R ha).continuousAt.norm.eventually_lt_const
    (show ‖errorOperator R 0 (a 0)‖ < 1/2 by simp [z,errorOperator])
  filter_upwards [eqn,small] with p hp size
  intro n H ψ E
  let v := a p n
  let U := exp ℂ (convolute (generator v))
  have bij : Function.Bijective U := ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_exp ..)
  have h := equation_in_boxes R p _ hp n
  obtain ⟨nz,eig⟩ := exact_eigenpair _ _ _ _ h
  refine ⟨nz,eig,?_⟩
  intro μ ξ hξ hx bound
  obtain ⟨y,hy⟩ := bij.surjective ξ
  have conj := congrArg (fun L : Operator (Box R n) => L y) (dressed_H _ _ _ _ h)
  let T := correction (boxFlips R n) (boxSigns R n) p v
  change H (U y) = U (E • y + (1+T) (gapOp y)) at conj
  rw [hy,hx,← hy,← map_smul U] at conj
  have diff : (1+T) (gapOp y) = (μ-E) • y := by
    rw [sub_smul,eq_sub_iff_add_eq']; exact (bij.injective conj).symm
  have limit : (μ-E).re ≤ 1 := by simp only [Complex.sub_re]; linarith
  have yray := low_line T ((correction_le R p _ n).trans_lt size) y _ limit diff
  have ray : ξ = y 0 • ψ := hy.symm.trans ((congrArg U yray).trans (map_smul U _ _))
  refine ⟨?_,y 0,ray⟩
  have same : E • ξ = μ • ξ := by
    rw [← hx]; conv_rhs => rw [ray,map_smul,eig,smul_comm (y 0) E,← ray]
  exact (smul_left_injective ℂ hξ) same.symm

end DSFTomography.SF.Cluster
