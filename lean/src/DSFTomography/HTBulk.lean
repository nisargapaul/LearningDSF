import DSFTomography.HTLocalGibbs
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Differentiate the volume limit of the measured static harmonic. The
high-temperature cluster bound is stated on the finite Gibbs traces, before
taking any derivatives. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter Metric
open scoped Topology

/-- Volume limit at each fixed real β. The theorem below proves convergence
on the disk where the high-temperature estimates hold. -/
def bulkHarmonic {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
    (c : Channel (Site ν)) (β : ℝ) : ℂ :=
  limUnder atTop (fun n => (periodicVolume R h J n).observable (periodicChannel R c n) β)

/-- On any smaller high-temperature disk, the periodic cluster expansion
gives a zero-free partition function and a uniform Cauchy bound for the
expectation of a fixed local probe (Nguyen–Fernández, Cor. 6.6 and §7.2.3).
This abstract implication accepts those estimates. HTThermodynamic proves
both directly and instantiates this result for the lattice family. -/
theorem periodic_limit_then_derivative {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ)
    (J : Site ν → Matrix Axis Axis ℝ) (c : Channel (Site ν))
    (valid : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True)
    {r : ℝ} (hr : 0 < r)
    (regular : ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) r, (periodicVolume R h J n).partition z ≠ 0)
    (cluster : UniformCauchySeqOn
      (fun n => (periodicVolume R h J n).localGibbs (periodicChannel R c n)) atTop (ball 0 r)) :
    (∀ β : ℝ, |β| < r → Tendsto
      (fun n => (periodicVolume R h J n).observable (periodicChannel R c n) β)
      atTop (𝓝 (bulkHarmonic R h J c β))) ∧
    HasDerivAt (bulkHarmonic R h J c)
      (channelTarget h J c) 0 := by
  let F := fun n => (periodicVolume R h J n).localGibbs (periodicChannel R c n)
  let f := fun z : ℂ => limUnder atTop (fun n => F n z)
  let D := ball (0 : ℂ) r
  have atZero : (0 : ℂ) ∈ D := mem_ball_self hr
  have conv (z : ℂ) (hz : z ∈ D) : Tendsto (fun n => F n z) atTop (𝓝 (f z)) :=
    (cluster.cauchySeq hz).tendsto_limUnder
  have uniform : TendstoLocallyUniformlyOn F f atTop D :=
    (cluster.tendstoUniformlyOn_of_tendsto conv).tendstoLocallyUniformlyOn
  have hol : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D :=
    regular.mono fun n hn => (periodicVolume R h J n).localGibbs_differentiableOn _ hn
  have realData (n : ℕ) (β : ℝ) :
      (periodicVolume R h J n).observable (periodicChannel R c n) β = F n β :=
    Volume.observable_eq_localGibbs ..
  have bulk_eq (β : ℝ) : bulkHarmonic R h J c β = f β := by
    unfold bulkHarmonic f
    simp only [realData]
  constructor
  · intro β hβ
    rw [bulk_eq]
    simpa only [realData] using conv β (by simpa [D, mem_ball, Real.norm_eq_abs] using hβ)
  · let v := channelTarget h J c
    have slope : ∀ᶠ n in atTop, deriv (F n) 0 = v := by
      filter_upwards [hol] with n hn
      obtain ⟨hc, target⟩ := periodic_channel_target R h J c valid n
      have fd := (periodicVolume R h J n).derivative _ hc
      simp only [show (periodicVolume R h J n).observable (periodicChannel R c n) =
        (fun β : ℝ => F n β) from funext (realData n)] at fd
      have hd := (hn.differentiableAt (isOpen_ball.mem_nhds atZero)).hasDerivAt
      have realHd : HasDerivAt (fun β : ℝ => F n β) (deriv (F n) 0) 0 := by
        simpa using (show HasDerivAt (F n) (deriv (F n) 0) ((0 : ℝ) : ℂ) by simpa using hd).comp_ofReal
      exact (realHd.unique fd).trans target
    have convDeriv := (uniform.deriv hol isOpen_ball).tendsto_at atZero
    have eqv : deriv f 0 = v := tendsto_nhds_unique convDeriv (tendsto_const_nhds.congr' (slope.mono fun _ hn => hn.symm))
    have hd := ((uniform.differentiableOn hol isOpen_ball).differentiableAt
      (isOpen_ball.mem_nhds atZero)).hasDerivAt
    rw [show bulkHarmonic R h J c = (fun β : ℝ => f β) from funext bulk_eq]
    exact (show HasDerivAt f v ((0 : ℝ) : ℂ) by simpa [eqv] using hd).comp_ofReal

/-- The positive-temperature quotient uses only the measured limiting scan.
At valid bonds and cyclic on-site pairs its intercept vanishes. -/
def positiveSlope (f : ℝ → ℂ) : ℂ := limUnder (𝓝[>] (0 : ℝ)) (fun β => β⁻¹ • f β)

/-- Full readout from positive-temperature data after the periodic volume
limit. The cluster estimates concern only the Gibbs state, and can be shared
by every channel. D may be supplied independently of the Hamiltonian. -/
theorem fullAccessHT_bulk {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ)
    (J : Site ν → Matrix Axis Axis ℝ) {r : ℝ} (hr : 0 < r)
    (regular : ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) r, (periodicVolume R h J n).partition z ≠ 0)
    (cluster : ∀ c, (match c with | Channel.bond d _ _ => d ∈ R.dirs | .onsite _ => True) →
      UniformCauchySeqOn
        (fun n => (periodicVolume R h J n).localGibbs (periodicChannel R c n)) atTop (ball 0 r))
    (D : Channel (Site ν) → ℝ → ℂ)
    (data : ∀ c, (match c with | Channel.bond d _ _ => d ∈ R.dirs | .onsite _ => True) →
      ∀ᶠ β in 𝓝[>] (0 : ℝ), Tendsto
        (fun n => (periodicVolume R h J n).observable (periodicChannel R c n) β) atTop (𝓝 (D c β))) :
    (∀ d ∈ R.dirs, ∀ a b, -positiveSlope (D (.bond d a b)) = (J d a b : ℂ)) ∧
    (∀ k, Complex.I * positiveSlope (D (.onsite k)) = (h k : ℂ)) := by
  have slope (c : Channel (Site ν))
      (hc : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True) :
      positiveSlope (D c) = channelTarget h J c := by
    obtain ⟨hlim, hd⟩ := periodic_limit_then_derivative R h J c hc hr regular (cluster c hc)
    have hzero : bulkHarmonic R h J c 0 = 0 := by
      apply tendsto_nhds_unique (hlim 0 (by simpa using hr))
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun n =>
        ((periodicVolume R h J n).observable_zero _ (periodic_channel_target R h J c hc n).1).symm
    have agree : D c =ᶠ[𝓝[>] (0 : ℝ)] bulkHarmonic R h J c := by
      have near : ∀ᶠ β in 𝓝[>] (0 : ℝ), β ∈ ball (0 : ℝ) r :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hr)
      filter_upwards [data c hc, near] with β observed hβ
      exact tendsto_nhds_unique observed (hlim β (by simpa [mem_ball, Real.dist_eq] using hβ))
    have quotient := hd.tendsto_slope_zero_right
    simp only [zero_add, hzero, sub_zero] at quotient
    exact (quotient.congr' (agree.mono fun β eq => congrArg (β⁻¹ • ·) eq.symm)).limUnder_eq
  constructor
  · intro d hd a b
    rw [slope (.bond d a b) hd]
    exact neg_neg _
  · intro k
    rw [slope (.onsite k) trivial]
    simp [channelTarget, ← mul_assoc, Complex.I_mul_I]


end DSFTomography.HT
