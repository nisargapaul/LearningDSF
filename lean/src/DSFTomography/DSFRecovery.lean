import DSFTomography.DSFPhysical
import DSFTomography.FDStationary
import DSFTomography.HTDiagonalThermodynamic
import DSFTomography.SFClusterBulk

/-! Public recovery endpoints using moments of the time-Fourier DSF.
DSFMomentum supplies the bridge to the existing certified moment protocol.
It preserves the elastic weight for FD/HT; the SF readout performs its
already-certified connected-static subtraction. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT SF Filter MeasureTheory
open scoped Topology
/-- The common normalization of raw spectral moments is nonzero. -/
theorem two_pi_ne_zero : (2*Real.pi:ℂ) ≠ 0 := by
  exact_mod_cast (show (2*Real.pi:ℝ) ≠ 0 by positivity)

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def physicalData (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ) (β : ℝ) :=
  rawData (qubitSpins (energyBasis R h J)) β (energies R h J)

/-- Exact FD recovery from the zeroth and first integrals of the DSF defined
by Heisenberg evolution and the positive-sign time Fourier transform. -/
theorem fd_from_time_DSF (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ) (β : ℝ)
    (nonsingular : ∀ d ∈ R.dirs, ((physicalData R h J β).harmonics.static d).det ≠ 0)
    (k : Axis) (mag : (physicalData R h J β).harmonics.mag k ≠ 0) :
    (∀ d ∈ R.dirs, (physicalData R h J β).harmonics.exchange d = fun a b => (J d a b:ℂ)) ∧
      (physicalData R h J β).harmonics.field R k = fun a => (h a:ℂ) := by
  exact fdFromDSF _ R β _ h J (diagonalized R h J) _ (rawData_eq ..) nonsingular k mag

open scoped Matrix.Norms.Frobenius in
/-- The manuscript accuracy constant for moments integrated from the physical
DSF. Both noisy inputs may be complex matrices. -/
theorem fd_accuracy_from_time_DSF (V : Volume S) (β : ℝ) {d : S} (hd : d ∈ V.R.dirs)
    (small : ∀ a b, |V.J d a b| ≤ 1) (Chat Fhat : Tensor) (ε γ : ℝ)
    (noise : max ‖Chat-(physicalData V.R V.h V.J β).harmonics.static d‖
      ‖Fhat-(physicalData V.R V.h V.J β).harmonics.force d‖ ≤ ε)
    (pos : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(V.J d a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
  apply FD.fd_accuracy_stationary V (FD.Accuracy.population V β)
    (FD.Accuracy.population_pos V β) (FD.Accuracy.population_sum V β) hd small Chat Fhat ε γ _ pos det
  simpa only [← FD.thermal_mixture,FD.Accuracy.thermalData,physicalData,rawData_eq] using noise

def staticTimeScan (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ) : StaticScan S :=
  fun β => (physicalData R h J β).static
theorem staticTimeScan_eq (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ) :
    staticTimeScan R h J = gibbsStaticDSF R h J := by
  funext β; exact congrArg Data.static (rawData_eq ..)

theorem fullAccessHT_from_time_DSF (R : Bonds S) (h : Axis → ℝ) (J : S → Matrix Axis Axis ℝ) :
    (∀ d ∈ R.dirs, HT.exchange (staticTimeScan R h J) d = fun a b => (J d a b:ℂ)) ∧
      HT.field (staticTimeScan R h J) = fun a => (h a:ℂ) := by
  rw [staticTimeScan_eq]; exact fullAccessHT R h J

def diagonalTimeData (R : Bonds S) (p : HT.Diagonal.Params R) : HT.Diagonal.DiagonalData S where
  static β q a := (physicalData R (HT.Diagonal.fields R p) (HT.Diagonal.exch R p) β).static q a a
  second β q a := (momentumLines (qubitSpins (energyBasis R (HT.Diagonal.fields R p) (HT.Diagonal.exch R p)))
    (gibbs β (energies R (HT.Diagonal.fields R p) (HT.Diagonal.exch R p)))
    (energies R (HT.Diagonal.fields R p) (HT.Diagonal.exch R p)) q a a).moment 2/(2*Real.pi)

theorem diagonalTimeData_eq (R : Bonds S) (p : HT.Diagonal.Params R) :
    diagonalTimeData R p = HT.Diagonal.gibbsData R p := by
  apply congrArg₂ HT.Diagonal.DiagonalData.mk
  · funext β q a; exact congrFun (congrFun (congrFun (congrArg Data.static (rawData_eq ..)) q) a) a
  · funext β q a; simp only [diagonalTimeData,HT.Diagonal.gibbsData,momentum_second,mul_div_cancel_left₀ _ two_pi_ne_zero]

theorem diagonalHT_from_time_DSF (R : Bonds S) :
    ∀ᵐ p ∂volume.restrict {p : HT.Diagonal.Params R | ∀ i, p i ∈ Set.Icc (-1:ℝ) 1},
      HT.Diagonal.LocallySolvable (fun q => HT.Diagonal.readout R (diagonalTimeData R q)) p := by
  simp only [diagonalTimeData_eq]
  exact HT.Diagonal.diagonalHT_cube R

def stationaryData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Spins S ι) (w : ι → ℂ) (E : ι → ℝ) : Data (Momentum S) where
  static q a b := (momentumLines P w E q a b).moment 0/(2*Real.pi)
  first q a b := (momentumLines P w E q a b).moment 1/(2*Real.pi)

theorem ground_time_data (V : Volume S) (m : Config S) :
    stationaryData (qubitSpins (energyBasis V.R V.h V.J)) (pureWeight m) (energies V.R V.h V.J) = groundDSF V m := by
  apply congrArg₂ Data.mk <;> funext q a b
  · simp only [stationaryData,momentum_zeroth,mul_div_cancel_left₀ _ two_pi_ne_zero,groundDSF]
  · simp only [stationaryData,momentum_first,mul_div_cancel_left₀ _ two_pi_ne_zero,groundDSF]

def groundTimeReadout (V : Volume S) (B : ℝ) : Harmonics V.R.dirs :=
  paperFromDSF Subtype.val B fun i => let W := driven V B i
    stationaryData (qubitSpins (energyBasis W.R W.h W.J)) (pureWeight (lowest W)) (energies W.R W.h W.J)

theorem groundTimeReadout_eq (V : Volume S) (B : ℝ) :
    groundTimeReadout V B = groundPaperReadout V B Subtype.val := by
  unfold groundTimeReadout groundPaperReadout
  simp only [ground_time_data]

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def periodicTimePacket (β : ℝ) (n : ℕ) : FD.Packet R.dirs :=
  let V := periodicVolume R h J n
  let A := (physicalData V.R V.h V.J β).harmonics
  (fun d => A.static (periodicSite R n d),fun d => A.force (periodicSite R n d),A.mag,A.force 0)
theorem periodicTimePacket_eq (β : ℝ) (n : ℕ) :
    periodicTimePacket R h J β n = FD.periodicPacket R h J β n := by
  simp only [periodicTimePacket,physicalData,rawData_eq,FD.periodicPacket]

theorem fd_bulk_from_time_DSF (β : ℝ) (A : FD.Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicTimePacket R h J β (seq n)) atTop (𝓝 A))
    (nonsingular : ∀ d, (A.1 d).det ≠ 0) (k : Axis) (mag : A.2.2.1 k ≠ 0) :
    FD.Packet.exchange A = (fun (d : R.dirs) a b => (J d a b:ℂ)) ∧
      FD.Packet.field A k = fun a => (h a:ℂ) := by
  simp only [periodicTimePacket_eq] at data
  exact FD.fd_thermodynamic R h J β A seq data nonsingular k mag

theorem fd_bulk_time_data_exist (β : ℝ) :
    ∃ A : FD.Packet R.dirs, ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Tendsto (fun n => periodicTimePacket R h J β (seq n)) atTop (𝓝 A) := by
  simp only [periodicTimePacket_eq]
  exact FD.fd_gibbs_bulk_data_exist R h J β

open scoped Matrix.Norms.Frobenius in
theorem fd_accuracy_bulk_from_time_DSF (β : ℝ) (A : FD.Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicTimePacket R h J β (seq n)) atTop (𝓝 A))
    (d : R.dirs) (small : ∀ a b, |J d a b| ≤ 1) (Chat Fhat : Tensor) (ε γ : ℝ)
    (noise : max ‖Chat-A.1 d‖ ‖Fhat-A.2.1 d‖ ≤ ε) (pos : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(J d a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
  simp only [periodicTimePacket_eq] at data
  exact FD.fd_accuracy_bulk R h J β A seq data d small Chat Fhat ε γ noise pos det

/-- The bulk SF theorem expressed using the time-Fourier spectral integrals
and exactly the manuscript's connected sine/cosine readout. -/
theorem fullAccessSF_bulk_from_time_DSF :
    let measured := fun B n p => originalLabels R n (groundTimeReadout
      (withParams (periodicBonds R n) (boxParams R n p)) B)
    ∃ M : ℝ → SF.Params R.dirs → Harmonics R.dirs, ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (M B) (couplingCube R.dirs) ∧ ∀ p ∈ couplingCube R.dirs,
        Tendsto (fun n => measured B n p) atTop (𝓝 (M B p)) ∧ DifferentiableAt ℝ (M B) p ∧
        ‖fderiv ℝ (fun q => M B q-leading q) p‖ ≤ C/B ∧ ‖M B p-leading p‖ ≤ (C/B)*‖p‖ := by
  simp only [groundTimeReadout_eq]
  exact fullAccessSF_lab_thermodynamic R

end DSFTomography.Spectral
