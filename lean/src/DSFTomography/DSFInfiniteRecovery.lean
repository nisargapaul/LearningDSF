import DSFTomography.DSFThermodynamic

/-! The infinite DSF's spectral moments reproduce the previously certified
thermodynamic data and feed the same FD inverse and accuracy bound. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord Filter
open scoped Topology

namespace BulkDSF
variable {ν : ℕ} {R : Bonds (Site ν)} {h : Axis → ℝ} {J : Site ν → Matrix Axis Axis ℝ}
  {p : ∀ n, Config (Box R n) → ℝ} {volumes : ℕ → ℕ}
variable (D : BulkDSF R h J p volumes)

def data : Data (Site ν) where
  static d a b := D.moment (d,a,b) 0/(2*Real.pi)
  first d a b := D.moment (d,a,b) 1/(2*Real.pi)

def packet : FD.Packet R.dirs :=
  (fun d => D.data.static d,fun d => D.data.force d,D.data.mag,D.data.force 0)

theorem static_limit (d : Site ν) (a b : Axis) :
    Tendsto (fun n => (FD.mixtureData (periodicVolume R h J (volumes (D.select n)))
      (p (volumes (D.select n)))).static (place R (volumes (D.select n)) d) a b)
      atTop (𝓝 (D.data.static d a b)) := by
  simpa only [channelLines,box_zeroth,mul_div_cancel_left₀ _ two_pi_ne_zero] using
    (D.moment_limit (d,a,b) 0).div_const (2*Real.pi:ℂ)

theorem first_limit (d : Site ν) (a b : Axis) :
    Tendsto (fun n => (FD.mixtureData (periodicVolume R h J (volumes (D.select n)))
      (p (volumes (D.select n)))).first (place R (volumes (D.select n)) d) a b)
      atTop (𝓝 (D.data.first d a b)) := by
  simpa only [channelLines,box_first,mul_div_cancel_left₀ _ two_pi_ne_zero] using
    (D.moment_limit (d,a,b) 1).div_const (2*Real.pi:ℂ)

theorem force_limit (d : Site ν) (a b : Axis) :
    Tendsto (fun n => (FD.mixtureData (periodicVolume R h J (volumes (D.select n)))
      (p (volumes (D.select n)))).force (place R (volumes (D.select n)) d) a b)
      atTop (𝓝 (D.data.force d a b)) := by
  have neg (n : ℕ) : place R n (-d) = -place R n d := by ext i; simp [place,periodicSite,reduceBond]
  simpa only [Data.force,neg] using (D.first_limit d a b).add (D.first_limit (-d) b a)

theorem magnetization_limit (a : Axis) :
    Tendsto (fun n => (FD.mixtureData (periodicVolume R h J (volumes (D.select n)))
      (p (volumes (D.select n)))).mag a) atTop (𝓝 (D.data.mag a)) := by
  have zero (n : ℕ) : place R n 0 = 0 := by ext i; simp [place,periodicSite,reduceBond]
  simpa only [Data.mag,zero] using ((D.static_limit 0 (a+1) (a+2)).sub
    (D.static_limit 0 (a+2) (a+1))).div_const (2*Complex.I)

theorem packet_limit :
    Tendsto (fun n => FD.probabilityPacket R h J p (volumes (D.select n))) atTop (𝓝 D.packet) := by
  have stat := tendsto_pi_nhds.mpr fun d : R.dirs => tendsto_pi_nhds.mpr fun a =>
    tendsto_pi_nhds.mpr fun b => D.static_limit d a b
  have force := tendsto_pi_nhds.mpr fun d : R.dirs => tendsto_pi_nhds.mpr fun a =>
    tendsto_pi_nhds.mpr fun b => D.force_limit d a b
  have mag := tendsto_pi_nhds.mpr D.magnetization_limit
  have zero (n : ℕ) : place R n 0 = 0 := by ext i; simp [place,periodicSite,reduceBond]
  have onsite := tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => D.force_limit 0 a b
  simpa only [← nhds_prod_eq,zero] using stat.prodMk (force.prodMk (mag.prodMk onsite))

/-- The full frequency distribution retains the original certified FD data. -/
theorem agrees_with_FD_packet (A : FD.Packet R.dirs)
    (certified : Tendsto (fun n => FD.probabilityPacket R h J p (volumes n)) atTop (𝓝 A)) :
    D.packet = A := tendsto_nhds_unique D.packet_limit (certified.comp D.increasing.tendsto_atTop)

/-- Exchange and field recovery from genuine infinite-volume DSF moments. -/
theorem fd_from_infinite_DSF (nonsingular : ∀ d : R.dirs, (D.data.static d).det ≠ 0)
    (k : Axis) (mag : D.data.mag k ≠ 0) :
    FD.Packet.exchange D.packet = (fun (d : R.dirs) a b => (J d a b:ℂ)) ∧
      FD.Packet.field D.packet k = fun a => (h a:ℂ) :=
  FD.fd_stationary_thermodynamic R h J (fun n i => (p n i:ℂ)) D.packet
    (volumes ∘ D.select) D.packet_limit nonsingular k mag

open scoped Matrix.Norms.Frobenius in
theorem fd_accuracy_infinite_DSF (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (d : R.dirs) (small : ∀ a b, |J d a b| ≤ 1) (Chat Fhat : Tensor) (ε γ : ℝ)
    (noise : max ‖Chat-D.data.static d‖ ‖Fhat-D.data.force d‖ ≤ ε)
    (pos : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(J d a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε :=
  FD.fd_accuracy_stationary_thermodynamic R h J p positive normed D.packet
    (volumes ∘ D.select) D.packet_limit d small Chat Fhat ε γ noise pos det

end BulkDSF

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

/-- At fixed high temperature, the spectral moment of the constructed real-time
DSF equals the bulk moment used before differentiating in diagonal HT. -/
theorem infinite_DSF_HT_moments (β : ℝ) (small : |β| < diskRadius R h J)
    (D : BulkDSF R h J (gibbsPop R h J β) id) (d : Site ν) (a : Axis) (k : ℕ) :
    D.moment (d,a,a) k = (2*Real.pi:ℂ)*HT.Diagonal.Bulk.bulkMoment R h J k d a β := by
  apply D.agrees_with_certified_limit
  simpa only [channelLines,box_diagonal_moment,id_eq] using
    ((HT.Diagonal.Bulk.volume_first R h J k d a).1 β small).const_mul (2*Real.pi:ℂ)

end DSFTomography.Spectral
