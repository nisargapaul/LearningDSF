import DSFTomography.DSFInfiniteRecovery

/-! The volume-first HT curves are moments of the constructed time-Fourier DSF.
Choosing a different thermodynamic subsequence at each temperature does not
change these curves in the certified high-temperature neighborhood. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord Filter Set MeasureTheory Metric
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def gibbsDSF (β : ℝ) : BulkDSF R h J (gibbsPop R h J β) id :=
  Classical.choice (gibbsDSF_exists R h J β)

def gibbsMoment (d : Site ν) (a b : Axis) (k : ℕ) (β : ℝ) : ℂ :=
  (gibbsDSF R h J β).moment (d,a,b) k/(2*Real.pi)

theorem gibbsMoment_spectral (d : Site ν) (a b : Axis) (k : ℕ) (β : ℝ) :
    HasSpectralMoment ((gibbsDSF R h J β).spectrum
      (gibbsPop_positive R h J β) (gibbsPop_normalized R h J β) (d,a,b)) k
      ((2*Real.pi:ℂ)*gibbsMoment R h J d a b k β) := by
  simpa only [gibbsMoment,mul_div_cancel₀ _ two_pi_ne_zero] using (gibbsDSF R h J β).spectral_moments
    (gibbsPop_positive R h J β) (gibbsPop_normalized R h J β) (d,a,b) k

theorem infinite_DSF_static (β : ℝ) (small : |β| < diskRadius R h J)
    (D : BulkDSF R h J (gibbsPop R h J β) id) (c : Channel (Site ν))
    (valid : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True) :
    D.moment (channelIndex c) 0 = (2*Real.pi:ℂ)*bulkHarmonic R h J c β := by
  apply D.agrees_with_certified_limit
  simpa only [channelLines,box_static_channel,id_eq] using
    ((bulk_static_derivative R h J c valid).1 β small).const_mul (2*Real.pi:ℂ)

theorem infinite_DSF_static_slope (c : Channel (Site ν))
    (valid : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True) :
    HasDerivAt (fun β => gibbsMoment R h J (channelIndex c).1
      (channelIndex c).2.1 (channelIndex c).2.2 0 β) (channelTarget h J c) 0 := by
  apply (bulk_static_derivative R h J c valid).2.congr_of_eventuallyEq
  have near : ∀ᶠ β in 𝓝 (0:ℝ), β ∈ ball 0 (diskRadius R h J) := ball_mem_nhds _ (diskRadius_pos ..)
  filter_upwards [near] with β hb
  have eq := infinite_DSF_static R h J β (by simpa [mem_ball,Real.dist_eq] using hb) (gibbsDSF R h J β) c valid
  change (gibbsDSF R h J β).moment (channelIndex c) 0/(2*Real.pi) = _
  rw [eq,mul_div_cancel_left₀ _ two_pi_ne_zero]

/-- These are the static slopes in the paper, after constructing the real-time
DSF in infinite volume. No derivative/volume-limit interchange is assumed. -/
theorem fullAccessHT_infinite_DSF :
    (∀ d ∈ R.dirs, ∀ a b, HasDerivAt (gibbsMoment R h J d a b 0) (-(J d a b:ℂ)) 0) ∧
    (∀ k, HasDerivAt (gibbsMoment R h J 0 (k+1) (k+2) 0) (-(Complex.I*h k)) 0) :=
  ⟨fun d hd a b => infinite_DSF_static_slope R h J (.bond d a b) hd,
    fun k => infinite_DSF_static_slope R h J (.onsite k) trivial⟩

namespace Diagonal
open HT.Diagonal HT.Diagonal.Bulk
variable (R : Bonds (Site ν))

def curves (p : Params R) (i : Index R) : ℝ → ℂ :=
  let s := setting R i
  gibbsMoment R (fields R p) (exch R p) s.d s.a s.a s.k

theorem observed (p : Params R) : Observed R p (curves R p) := by
  intro i
  let s := setting R i
  let h := fields R p
  let J := exch R p
  have near : ∀ᶠ β in 𝓝[>] (0:ℝ), β ∈ ball 0 (diskRadius R h J) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (diskRadius_pos ..))
  filter_upwards [near] with β hb
  have small : |β| < diskRadius R h J := by simpa [mem_ball,Real.dist_eq] using hb
  have eq := infinite_DSF_HT_moments R h J β small (gibbsDSF R h J β) s.d s.a s.k
  change Tendsto _ atTop (𝓝 ((gibbsDSF R h J β).moment (s.d,s.a,s.a) s.k/(2*Real.pi)))
  rw [eq,mul_div_cancel_left₀ _ two_pi_ne_zero]
  exact (volume_first R h J s.k s.d s.a).1 β small

/-- The exact same polynomial feature map and Jacobian witness apply. -/
theorem features_eq : (fun p => positiveReadout R (curves R p)) = features R :=
  funext fun p => readout_eq R (observed R p)

theorem generic_local_solvability :
    ∀ᵐ p ∂volume.restrict {p : Params R | ∀ i, p i ∈ Icc (-1:ℝ) 1},
      LocallySolvable (fun q => positiveReadout R (curves R q)) p := by
  rw [features_eq]
  exact diagonalHT_thermodynamic R
end Diagonal
end DSFTomography.Spectral
