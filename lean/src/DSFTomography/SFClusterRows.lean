import DSFTomography.SFClusterCharts
import DSFTomography.SFClusterObservables
import DSFTomography.SFClusterSeries

/-! The manuscript's constant term and four ordered bond harmonics as a
single analytic function taking its values in convergent box measurements. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter
open scoped Topology ContDiff
variable {ν : ℕ} (R : Bonds (Site ν))
abbrev RealTrace := C(Boxes,ℝ)
abbrev Rows := (Axis → RealTrace) × (R.dirs → Axis → Fin 4 → RealTrace)
def collect : Rows R →L[ℝ] C(Boxes,Harmonics R.dirs) :=
  LinearMap.mkContinuous {
    toFun := fun x => ⟨fun t => (fun i => x.1 i t,fun d i k => x.2 d i k t),
      (continuous_pi fun i => (x.1 i).continuous).prodMk (continuous_pi fun d =>
        continuous_pi fun i => continuous_pi fun k => (x.2 d i k).continuous)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
    1 (by
      intro x; rw [one_mul]; apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr; intro t
      apply max_le
      · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i
        exact ((x.1 i).norm_coe_le_norm t).trans ((norm_le_pi_norm x.1 i).trans (norm_fst_le x))
      · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro d
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro k
        exact ((x.2 d i k).norm_coe_le_norm t).trans ((norm_le_pi_norm _ k).trans
          ((norm_le_pi_norm _ i).trans ((norm_le_pi_norm _ d).trans (norm_snd_le x)))))

def realPart : Trace →L[ℝ] RealTrace := Complex.reCLM.compLeftContinuous ℝ Boxes
def imagPart : Trace →L[ℝ] RealTrace := Complex.imCLM.compLeftContinuous ℝ Boxes

namespace Branch
variable {R} (b : Branch R)
def mean (a : Axis) (q : Sources R) : Trace :=
  axisPhase a • b.obs (xSites 0 a) (zSites 0 a) q
def pair (d : R.dirs) (a e : Axis) (q : Sources R) : Trace :=
  (axisPhase a*axisPhase e) • b.obs (xSites 0 a ++ xSites d.val e) (zSites 0 a ++ zSites d.val e) q -
    b.mean a q * b.mean e q
def centered (r s : Site ν) (q : Sources R) : Trace :=
  b.cen r s q + (2:ℂ) • (b.mean 0 q * b.mean 0 q)
def rows (p : Params R.dirs) : Rows R :=
  (fun i => realPart (b.centered 0 0 (sourceMap R i p)), fun d i =>
    let q := sourceMap R i p
    let plus := b.centered 0 d.val q
    let minus := b.centered d.val 0 q
    ![realPart (plus+minus),imagPart (minus-plus),realPart (b.pair d 0 0 q - b.pair d 1 1 q),
      realPart (b.pair d 0 1 q + b.pair d 1 0 q)])
def harmonics (p : Params R.dirs) := collect R (b.rows p)

theorem analytic_harmonics : AnalyticAt ℝ b.harmonics 0 := by
  have mn (a) : AnalyticAt ℂ (b.mean a) 0 :=
    AnalyticAt.smul (f:=fun _ : Sources R => axisPhase a) analyticAt_const (b.analytic_obs _ _)
  have pr (d a e) : AnalyticAt ℂ (b.pair d a e) 0 := by
    exact (AnalyticAt.smul (f:=fun _ : Sources R => axisPhase a*axisPhase e) analyticAt_const
      (b.analytic_obs _ _)).sub ((mn a).mul (mn e))
  have ct (r s) : AnalyticAt ℂ (b.centered r s) 0 :=
    (b.analytic_cen r s).add (AnalyticAt.smul (f:=fun _ : Sources R => (2:ℂ)) analyticAt_const ((mn 0).mul (mn 0)))
  have frame (f : Sources R → Trace) (hf : AnalyticAt ℂ f 0) (i : Axis) :
      AnalyticAt ℝ (fun p => f (sourceMap R i p)) 0 := by
    have atS : ContDiffAt ℝ ω f (sourceMap R i 0) := by simpa using hf.contDiffAt.restrict_scalars ℝ
    exact (atS.comp 0 (sourceMap R i).contDiff.contDiffAt).analyticAt
  apply ((collect R).analyticAt _).comp
  apply AnalyticAt.prod
  · apply AnalyticAt.pi; intro i
    exact (realPart.analyticAt _).comp (frame _ (ct 0 0) i)
  · apply AnalyticAt.pi; intro d; apply AnalyticAt.pi; intro i; apply AnalyticAt.pi; intro k
    fin_cases k
    · exact (realPart.analyticAt _).comp ((frame _ (ct 0 d.val) i).add (frame _ (ct d.val 0) i))
    · exact (imagPart.analyticAt _).comp ((frame _ (ct d.val 0) i).sub (frame _ (ct 0 d.val) i))
    · exact (realPart.analyticAt _).comp ((frame _ (pr d 0 0) i).sub (frame _ (pr d 1 1) i))
    · exact (realPart.analyticAt _).comp ((frame _ (pr d 0 1) i).add (frame _ (pr d 1 0) i))
end Branch
end DSFTomography.SF.Cluster
