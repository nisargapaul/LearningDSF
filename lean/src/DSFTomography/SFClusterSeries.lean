import DSFTomography.SFPaperLimit
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! A series valued in continuous functions on the convergent sequence
of boxes gives coefficient convergence in multilinear operator norm.
The compactness used here is only that of the unit ball of the parameter space. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter
open scoped Topology NNReal ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
abbrev Boxes := OnePoint ℕ
def ev (t : Boxes) : C(Boxes,F) →L[ℝ] F := ContinuousMap.evalCLM ℝ t

theorem coefficient_limit {k : ℕ} (P : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) C(Boxes,F)) :
    Tendsto (fun n : ℕ => (ev (n : Boxes)).compContinuousMultilinearMap P) atTop
      (𝓝 ((ev OnePoint.infty).compContinuousMultilinearMap P)) := by
  let K := Fin k → Metric.closedBall (0:E) 1
  let m : K → Fin k → E := fun v j => (v j).val
  have cm : Continuous m := continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)
  let f : C(Boxes × K,F) := ⟨fun z => P (m z.2) z.1,
    (P.cont.comp (cm.comp continuous_snd)).eval continuous_fst⟩
  let M := fun t : Boxes => (ev (F:=F) t).compContinuousMultilinearMap P
  have bound (s t : Boxes) : dist (M s) (M t) ≤ dist (f.curry s) (f.curry t) := by
    rw [dist_eq_norm]; apply ContinuousMultilinearMap.opNorm_le_bound dist_nonneg
    intro z
    let u : K := fun j => ⟨_,inv_norm_smul_mem_unitClosedBall (z j)⟩
    have scale : (fun j => ‖z j‖ • (m u j)) = z := by
      funext j; change ‖z j‖ • (‖z j‖⁻¹ • z j) = z j
      by_cases hz : z j = 0 <;> simp [smul_smul,hz]
    have scaled := (M s-M t).map_smul_univ (fun j => ‖z j‖) (m u)
    rw [scale] at scaled
    rw [scaled,norm_smul_of_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)),mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    rw [dist_eq_norm]; exact (f.curry s - f.curry t).norm_coe_le_norm u
  have cv := (OnePoint.continuous_iff_from_nat _).mp f.curry.continuous
  apply Metric.tendsto_atTop.mpr; intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp cv ε hε
  exact ⟨N,fun n hn => (bound _ _).trans_lt (hN n hn)⟩

variable {ν : ℕ} (R : Bonds (Site ν))
/-- Package a common analytic box readout, including its physical limit,
as the exact expansion consumed by the original strong-field theorem. -/
theorem expansion_of_continuous_family (G : BoxCharts R) (Y : Params R.dirs → C(Boxes,Harmonics R.dirs))
    (h : AnalyticAt ℝ Y 0)
    (agree : ∀ᶠ p in 𝓝 0, ∀ n : ℕ, Y p (n : Boxes) = boxReadout R G n p)
    (physical : ∀ᶠ p in 𝓝 (0 : Params R.dirs), ∀ n i, let x := boxParams R n p
      IsGroundPair (periodicBonds R n) i x ((G n i).ψ x) ((G n i).E x)) :
    Nonempty (LocalGroundExpansion R G) := by
  obtain ⟨P,r,hP⟩ := h
  obtain ⟨d,hd,ball⟩ := Metric.mem_nhds_iff.mp (agree.and physical)
  let d' : ℝ≥0 := ⟨d,hd.le⟩
  have pos : 0 < min r (d':ℝ≥0∞) := lt_min hP.r_pos (ENNReal.coe_pos.mpr hd)
  obtain ⟨r',pr,small⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp pos
  have hr := small.trans_le (min_le_left ..)
  have hd' : (r' : ℝ)<d := ENNReal.coe_lt_coe.mp (small.trans_le (min_le_right ..))
  have both (p : Params R.dirs) (hp : ‖p‖<(r':ℝ)) := ball (by simpa [Metric.mem_ball] using hp.trans hd')
  let cf := fun t : Boxes => (ev (F:=Harmonics R.dirs) t).compFormalMultilinearSeries P
  refine ⟨⟨r',ENNReal.coe_pos.mp pr,fun n => cf (n : Boxes),cf OnePoint.infty,
    fun n p hp i => (both p hp).2 n i,?_,fun k => coefficient_limit (P k),?_⟩⟩
  · intro n; apply ((ev (F:=Harmonics R.dirs) (n:Boxes)).comp_hasFPowerSeriesOnBall (hP.mono pr hr.le)).congr
    intro p hp
    have s : ‖p‖<(r':ℝ) := by
      rw [EMetric.mem_ball,edist_zero_right] at hp; exact ENNReal.coe_lt_coe.mp hp
    exact (both p s).1 n
  · obtain ⟨K,_,bound⟩ := P.norm_mul_pow_le_of_lt_radius (hr.trans_le hP.r_le)
    refine ⟨K,fun n k => le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) (bound k)⟩
    have e : ‖ev (F:=Harmonics R.dirs) (n:Boxes)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using x.norm_coe_le_norm (n:Boxes)
    exact ((ev (F:=Harmonics R.dirs) (n:Boxes)).norm_compContinuousMultilinearMap_le (P k)).trans
      (mul_le_of_le_one_left (norm_nonneg _) e)

end DSFTomography.SF.Cluster
