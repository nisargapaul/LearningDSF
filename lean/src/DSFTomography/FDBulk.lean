import DSFTomography.SFBulk

/-! FD recovery for thermodynamic limits of the measured local moments.
The limit can be taken along any growing sequence of periodic boxes. No
uniqueness of a thermodynamic Gibbs state or nonsingularity in finite boxes
is assumed. The determinant and magnetization conditions concern the data
in the limit, exactly as in the manuscript. -/
noncomputable section
namespace DSFTomography.FD
open DSFTomography HT SF Filter
open scoped Topology

/-- Bond statics, symmetrized first moments, magnetization, on-site force.
All moments are divided by 2π; elastic static weight is retained. -/
abbrev Packet (D : Type*) := (D → Tensor) × (D → Tensor) × (Axis → ℂ) × Tensor
abbrev Base (D : Type*) := (D → Tensor) × (Axis → ℂ)
namespace Packet
variable {D : Type*} [Fintype D]
def base (A : Packet D) : Base D := (A.1,A.2.2.1)
def forward (A : Base D) (h : Axis → ℂ) (J : D → Tensor) : Packet D :=
  (A.1,fun d => bondMap (A.1 d) (J d),A.2,
    fun a b => fieldMap A.2 h a b + ∑ d, atEnds (A.1 d) (J d) a b)
def exchange (A : Packet D) (d : D) := recoverBond (A.1 d) (A.2.1 d)
def field (A : Packet D) (k : Axis) := recoverField A.2.2.1
  (fun a b => A.2.2.2 a b - ∑ d, atEnds (A.1 d) (exchange A d) a b) k
theorem continuous_base : Continuous (base (D := D)) := by unfold base; fun_prop
theorem continuous_forward (h : Axis → ℂ) (J : D → Tensor) :
    Continuous (fun A => forward A h J) := by
  unfold forward bondMap fieldMap atEnds; fun_prop

theorem recover_exchange (A : Packet D) (h : Axis → ℂ) (J : D → Tensor)
    (eq : A = forward (base A) h J) (d : D) (nonsingular : (A.1 d).det ≠ 0) :
    exchange A d = J d := by
  have force := congrArg (fun K : Packet D => K.2.1 d) eq
  change A.2.1 d = bondMap (A.1 d) (J d) at force
  rw [exchange,force,recoverBond_exact _ _ nonsingular]

theorem recover (A : Packet D) (h : Axis → ℂ) (J : D → Tensor)
    (eq : A = forward (base A) h J)
    (nonsingular : ∀ d, (A.1 d).det ≠ 0) (k : Axis) (mag : A.2.2.1 k ≠ 0) :
    exchange A = J ∧ field A k = h := by
  have ex (d : D) : exchange A d = J d :=
    recover_exchange A h J eq d (nonsingular d)
  refine ⟨funext ex,?_⟩
  have onsite := congrArg (fun K : Packet D => K.2.2.2) eq
  unfold field; simp_rw [ex]
  have residual : (fun a b => A.2.2.2 a b - ∑ d, atEnds (A.1 d) (J d) a b) =
      fieldMap A.2.2.1 h := by
    ext a b; exact sub_eq_of_eq_add (congrFun (congrFun onsite a) b)
  rw [residual,recoverField_exact _ _ k mag]
end Packet

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

/-- Exact fixed-temperature measurements of the physical periodic Hamiltonian. -/
def periodicPacket (β : ℝ) (n : ℕ) : Packet R.dirs :=
  let V := periodicVolume R h J n
  let A := (momentumMoments (qubitSpins (energyBasis V.R V.h V.J)) β
    (energies V.R V.h V.J)).harmonics
  (fun d => A.static (periodicSite R n d),fun d => A.force (periodicSite R n d),A.mag,A.force 0)

theorem periodic_equations (β : ℝ) (n : ℕ) :
    periodicPacket R h J β n = Packet.forward (Packet.base (periodicPacket R h J β n))
      (fun a => (h a:ℂ)) (fun d a b => (J d a b:ℂ)) := by
  let V := periodicVolume R h J n
  let P := qubitSpins (energyBasis V.R V.h V.J)
  let E := energies V.R V.h V.J
  let A := measured P (gibbs β E) (fun j => (E j:ℂ))
  have station := diagonalized V.R V.h V.J
  have img (d : R.dirs) : periodicSite R n d ∈ V.R.dirs := Finset.mem_image_of_mem _ d.property
  simp only [periodicPacket,harmonics_momentumMoments,thermalMoments,Packet.forward,Packet.base]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
  · funext d
    change A.force (periodicSite R n d) = bondMap (A.static (periodicSite R n d)) (fun a b => (J d a b:ℂ))
    rw [measured_bond P V.R _ _ _ _ station (img d)]
    congr 1; ext a b
    simp only [V,periodicSite,image_coupling R h J n d.property]
  · ext a b
    change A.force 0 a b = fieldMap A.mag _ a b + _
    rw [measured_onsite P V.R _ _ _ _ station,background_local]
    apply congrArg₂ (·+·) rfl
    rw [show V.R.dirs = R.dirs.image (periodicSite R n) from rfl,
      Finset.sum_image (injects_dirs R n),← Finset.sum_attach R.dirs]
    apply Finset.sum_congr rfl; intro d _
    simp only [V,periodicSite,image_coupling R h J n d.property]
    rfl

/-- Stationary spectral populations, allowing Gibbs states or ground states. -/
def stationaryPacket (weights : ∀ n, Config (Box R n) → ℂ) (n : ℕ) : Packet R.dirs :=
  let V := periodicVolume R h J n
  let A := measured (qubitSpins (energyBasis V.R V.h V.J)) (weights n) (fun i => (energies V.R V.h V.J i:ℂ))
  (fun d => A.static (periodicSite R n d),fun d => A.force (periodicSite R n d),A.mag,A.force 0)

theorem stationary_equations (weights : ∀ n, Config (Box R n) → ℂ) (n : ℕ) :
    stationaryPacket R h J weights n = Packet.forward (Packet.base (stationaryPacket R h J weights n))
      (fun a => (h a:ℂ)) (fun d a b => (J d a b:ℂ)) := by
  let V := periodicVolume R h J n
  let P := qubitSpins (energyBasis V.R V.h V.J)
  let E := energies V.R V.h V.J
  let A := measured P (weights n) (fun j => (E j:ℂ))
  have station := diagonalized V.R V.h V.J
  have img (d : R.dirs) : periodicSite R n d ∈ V.R.dirs := Finset.mem_image_of_mem _ d.property
  simp only [stationaryPacket,Packet.forward,Packet.base]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
  · funext d
    change A.force (periodicSite R n d) = bondMap (A.static (periodicSite R n d)) (fun a b => (J d a b:ℂ))
    rw [measured_bond P V.R _ _ _ _ station (img d)]
    congr 1; ext a b
    simp only [V,periodicSite,image_coupling R h J n d.property]
  · ext a b
    change A.force 0 a b = fieldMap A.mag _ a b + _
    rw [measured_onsite P V.R _ _ _ _ station,background_local]
    apply congrArg₂ (·+·) rfl
    rw [show V.R.dirs = R.dirs.image (periodicSite R n) from rfl,
      Finset.sum_image (injects_dirs R n),← Finset.sum_attach R.dirs]
    apply Finset.sum_congr rfl; intro d _
    simp only [V,periodicSite,image_coupling R h J n d.property]
    rfl

/-- The local FD equations pass to every thermodynamic limiting data set. -/
theorem thermodynamic_equations (β : ℝ) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A)) :
    A = Packet.forward (Packet.base A) (fun a => (h a:ℂ)) (fun d a b => (J d a b:ℂ)) := by
  apply tendsto_nhds_unique data
  apply ((Packet.continuous_forward _ _).continuousAt.tendsto.comp
    (Packet.continuous_base.continuousAt.tendsto.comp data)).congr'
  exact Eventually.of_forall fun n => (periodic_equations R h J β (seq n)).symm

/-- Exact recovery applies to any stationary thermodynamic data, including
zero-temperature limits selected from finite-volume ground states. -/
theorem fd_stationary_thermodynamic (weights : ∀ n, Config (Box R n) → ℂ)
    (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => stationaryPacket R h J weights (seq n)) atTop (𝓝 A))
    (nonsingular : ∀ d, (A.1 d).det ≠ 0) (k : Axis) (mag : A.2.2.1 k ≠ 0) :
    Packet.exchange A = (fun (d : R.dirs) a b => (J d a b:ℂ)) ∧
      Packet.field A k = (fun a => (h a:ℂ)) := by
  apply Packet.recover A _ _ _ nonsingular k mag
  apply tendsto_nhds_unique data
  apply ((Packet.continuous_forward _ _).continuousAt.tendsto.comp
    (Packet.continuous_base.continuousAt.tendsto.comp data)).congr'
  exact Eventually.of_forall fun n => (stationary_equations R h J weights (seq n)).symm

/-- The manuscript FD theorem in the periodic thermodynamic limit at any
fixed inverse temperature. The estimator depends only on the limiting data. -/
theorem fd_thermodynamic (β : ℝ) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A))
    (nonsingular : ∀ d, (A.1 d).det ≠ 0) (k : Axis) (mag : A.2.2.1 k ≠ 0) :
    Packet.exchange A = (fun (d : R.dirs) a b => (J d a b:ℂ)) ∧
      Packet.field A k = (fun a => (h a:ℂ)) :=
  Packet.recover A _ _ (thermodynamic_equations R h J β A seq data) nonsingular k mag

/-- Each bond is recovered on its own determinant condition, without any
magnetization hypothesis and without conditions on the other bonds. -/
theorem fd_exchange_thermodynamic (β : ℝ) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A))
    (d : R.dirs) (nonsingular : (A.1 d).det ≠ 0) :
    Packet.exchange A d = (fun a b => (J d a b:ℂ)) :=
  Packet.recover_exchange A _ _ (thermodynamic_equations R h J β A seq data) d nonsingular

/-- Identical thermodynamic data determine identical physical couplings. -/
theorem fd_thermodynamic_identifiable (h' : Axis → ℝ) (J' : Site ν → Matrix Axis Axis ℝ)
    (β : ℝ) (A : Packet R.dirs) (seq seq' : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A))
    (data' : Tendsto (fun n => periodicPacket R h' J' β (seq' n)) atTop (𝓝 A))
    (nonsingular : ∀ d, (A.1 d).det ≠ 0) (k : Axis) (mag : A.2.2.1 k ≠ 0) :
    (∀ d ∈ R.dirs, J d = J' d) ∧ h = h' := by
  obtain ⟨ex,fields⟩ := fd_thermodynamic R h J β A seq data nonsingular k mag
  obtain ⟨ex',fields'⟩ := fd_thermodynamic R h' J' β A seq' data' nonsingular k mag
  constructor
  · intro d hd; ext a b
    exact Complex.ofReal_injective (congrFun (congrFun (congrFun (ex.symm.trans ex') ⟨d,hd⟩) a) b)
  · funext a; exact Complex.ofReal_injective (congrFun (fields.symm.trans fields') a)

end DSFTomography.FD
