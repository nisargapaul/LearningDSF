import DSFTomography.DSFInfiniteRecovery
import Mathlib.Analysis.Normed.Group.Tannery

/-! Spatial Fourier construction, in Fourier-coefficient test coordinates.
The sign convention is S(q,ω)=Σ_d exp(i q·d) S_d(ω), so the input `f d`
is the coefficient paired with exp(i q·d). No pointwise momentum density or
summability of the physical correlations is assumed. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord Filter MeasureTheory
open scoped Topology
namespace BulkDSF
variable {ν : ℕ} {R : Bonds (Site ν)} {h : Axis → ℝ} {J : Site ν → Matrix Axis Axis ℝ}
  {p : ∀ n, Config (Box R n) → ℝ} {volumes : ℕ → ℕ}
variable (D : BulkDSF R h J p volumes)
  (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)

theorem spectrum_bound (c : LocalChannel ν) (f : SchwartzMap ℝ ℂ) :
    ‖D.spectrum positive normed c f‖ ≤ (2*Real.pi)*SchwartzMap.seminorm ℂ 0 0 f := by
  simpa using timeTransform_bound (fun n => channelLines R h J p (volumes (D.select n)) c) (D.time c) 1
    (fun n => by simpa [momentBound] using box_absMoment_bound R h J p positive normed (volumes (D.select n)) c.1 c.2.1 c.2.2 0) (D.pointwise_time c) f

/-- Pair the momentum DSF with a test specified by its spatial Fourier coefficients. -/
def momentumPairing (a b : Axis) (f : Site ν → SchwartzMap ℝ ℂ) : ℂ :=
  ∑' d, D.spectrum positive normed (d,a,b) (f d)

theorem momentum_summable (a b : Axis) (f : Site ν → SchwartzMap ℝ ℂ)
    (decay : Summable fun d => SchwartzMap.seminorm ℂ 0 0 (f d)) :
    Summable fun d => D.spectrum positive normed (d,a,b) (f d) :=
  (decay.mul_left (2*Real.pi)).of_norm_bounded fun d => D.spectrum_bound positive normed _ _

theorem momentum_bound (a b : Axis) (f : Site ν → SchwartzMap ℝ ℂ)
    (decay : Summable fun d => SchwartzMap.seminorm ℂ 0 0 (f d)) :
    ‖D.momentumPairing positive normed a b f‖ ≤
      (2*Real.pi)*∑' d, SchwartzMap.seminorm ℂ 0 0 (f d) := by
  have sn := (D.momentum_summable positive normed a b f decay).norm
  apply (norm_tsum_le_tsum_norm sn).trans
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun d => D.spectrum_bound positive normed _ _) sn (decay.mul_left _)

theorem momentum_limit (a b : Axis) (f : Site ν → SchwartzMap ℝ ℂ)
    (decay : Summable fun d => SchwartzMap.seminorm ℂ 0 0 (f d)) :
    Tendsto (fun n => ∑' d, (channelLines R h J p (volumes (D.select n)) (d,a,b)).distribution (f d))
      atTop (𝓝 (D.momentumPairing positive normed a b f)) := by
  apply tendsto_tsum_of_dominated_convergence (decay.mul_left (2*Real.pi))
    (fun d => D.spectrum_limit positive normed (d,a,b) (f d))
  exact Eventually.of_forall fun n d => by
    apply ((channelLines R h J p (volumes (D.select n)) (d,a,b)).distribution_bound _).trans
    have bound : (channelLines R h J p (volumes (D.select n)) (d,a,b)).absMoment 0 ≤ 1 := by
      simpa [momentBound] using box_absMoment_bound R h J p positive normed (volumes (D.select n)) d a b 0
    simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (show 0 ≤ 2*Real.pi by positivity)) (apply_nonneg (SchwartzMap.seminorm ℂ 0 0) (f d))

/-- A single spatial Fourier test extracts the corresponding local spectrum. -/
theorem momentum_single (a b : Axis) (d : Site ν) (f : SchwartzMap ℝ ℂ) :
    D.momentumPairing positive normed a b (Pi.single d f) =
      D.spectrum positive normed (d,a,b) f := by
  classical
  unfold momentumPairing
  rw [tsum_eq_single d]
  · simp
  · intro e he; simp [Pi.single_eq_of_ne he]

theorem momentum_time (a b : Axis) (f : Site ν → SchwartzMap ℝ ℂ) :
    D.momentumPairing positive normed a b f =
      ∑' d, ∫ t, D.time (d,a,b) t*angularTest (f d) t := rfl

end BulkDSF
end DSFTomography.Spectral
