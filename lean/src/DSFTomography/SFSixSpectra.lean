import DSFTomography.SFSixLaboratory
import DSFTomography.SFSixElastic
import DSFTomography.SFSixInfinite

/-! End-to-end measurement interface: the six physical diagonal Lehmann
spectra, their measured elastic lines, spectral integration and inversion. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Spectral Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

abbrev DiagonalSpectra (S : Type*) [AddCommGroup S] :=
  Momentum S → Axis → Lines (S × S × Config S × Config S)

def coordinateSpectra (V : Volume S) : DiagonalSpectra S :=
  fun q a => momentumLines (qubitSpins (energyBasis V.R V.h V.J))
    (pureWeight (lowest V)) (energies V.R V.h V.J) q a a

/-- Probes and field are the literal rotated laboratory vectors. The
transported basis is certified to diagonalize this Hamiltonian. -/
def laboratorySpectra (V : Volume S) (t : Pair) (B : ℝ) : DiagonalSpectra S := fun q a =>
  let W := driven (rotatedVolume V t) B 2
  let E := energies W.R W.h W.J
  let U := tiltedBasis V t B
  {frequency k := E k.2.2.2-E k.2.2.1
   weight k := q k.1/(Fintype.card S:ℂ)*pureWeight (lowest W) k.2.2.1*
     inBasis U (laboratoryProbe t k.2.1 a) k.2.2.1 k.2.2.2*
     inBasis U (laboratoryProbe t (k.2.1+k.1) a) k.2.2.2 k.2.2.1}

theorem laboratorySpectra_eq (V : Volume S) (t : Pair) (B : ℝ) :
    laboratorySpectra V t B=coordinateSpectra (driven (rotatedVolume V t) B 2) := by
  funext q a
  simp only [laboratorySpectra,tilted_probe_in_basis,coordinateSpectra,momentumLines]

/-- Heisenberg correlation of a diagonal laboratory polarization channel,
in the certified energy basis of the tilted Hamiltonian. -/
def laboratoryTime (V : Volume S) (t : Pair) (B : ℝ) (q : Momentum S) (a : Axis) (τ : ℝ) : ℂ :=
  let W := driven (rotatedVolume V t) B 2
  let U := tiltedBasis V t B
  (∑ r, ∑ s, q (s-r)*timeCorrelation (pureWeight (lowest W)) (energies W.R W.h W.J)
    (inBasis U (laboratoryProbe t r a)) (inBasis U (laboratoryProbe t s a)) τ)/(Fintype.card S:ℂ)

/-- The actual time-Fourier definition precedes spectral integration. -/
theorem laboratory_dsf_definition (V : Volume S) (t : Pair) (B : ℝ)
    (q : Momentum S) (a : Axis) (f : SchwartzMap ℝ ℂ) :
    (∫ τ : ℝ, laboratoryTime V t B q a τ*angularTest f τ)=
      (laboratorySpectra V t B q a).distribution f := by
  have eq : laboratoryTime V t B q a =
      let W := driven (rotatedVolume V t) B 2
      momentumTime (qubitSpins (energyBasis W.R W.h W.J)) (pureWeight (lowest W))
        (energies W.R W.h W.J) q a a := by
    funext τ
    simp only [laboratoryTime,tilted_probe_in_basis,momentumTime]
  rw [eq,laboratorySpectra_eq]
  exact momentum_dsf_definition _ _ _ _ _ _ _

/-- Only integrals of diagonal spectra and the frequency-zero intensity
enter the estimator. The elastic line is removed from the static moment. -/
def momentsFromSpectra (L : DiagonalSpectra S) : DiagonalData S where
  static d a := harmonic (fun q => (L q a).moment 0/(2*Real.pi:ℂ)) d-
    (∑ k, if (L 1 a).frequency k=0 then (L 1 a).weight k else 0)/(Fintype.card S:ℂ)
  first d a := harmonic (fun q => (L q a).moment 1/(2*Real.pi:ℂ)) d

theorem spectral_moments (V : Volume S)
    (simple : ∀ j, energies V.R V.h V.J j=energies V.R V.h V.J (lowest V) → j=lowest V) :
    momentsFromSpectra (coordinateSpectra V)=observedDiagonal V (lowest V) := by
  have elastic (a : Axis) :
      (∑ k, if (coordinateSpectra V 1 a).frequency k=0 then (coordinateSpectra V 1 a).weight k else 0)/
        (Fintype.card S:ℂ)=coherentZero V (lowest V) a := by
    rw [← elasticZero_eq V (lowest V) simple a]
    simp only [coordinateSpectra,elasticZero,momentumLines,Fintype.sum_prod_type]
  have nz : (2*Real.pi:ℂ)≠0 := two_pi_ne_zero
  simp only [momentsFromSpectra,elastic]
  simp only [coordinateSpectra,momentum_zeroth,momentum_first,
    mul_div_cancel_left₀ _ nz,harmonic_toMomentum,observedDiagonal,harmonics_ground]

/-- The complete finite-volume acquisition uses exactly six field directions. -/
def physicalReadout (R : Bonds S) (B : ℝ) (p : Params R.dirs) : Harmonics R.dirs :=
  fromDiagonal Subtype.val B
    (fun i => momentsFromSpectra (coordinateSpectra (driven (withParams R p) B i)))
    (fun t => momentsFromSpectra (laboratorySpectra (withParams R p) t B))

theorem physicalReadout_eq (R : Bonds S) (B : ℝ) (p : Params R.dirs)
    (simple : ∀ i j, let W := driven (withParams R p) B i
      energies W.R W.h W.J j=energies W.R W.h W.J (lowest W) → j=lowest W)
    (tilted : ∀ t j, let W := driven (withParams R (rotate t p)) B 2
      energies W.R W.h W.J j=energies W.R W.h W.J (lowest W) → j=lowest W) :
    physicalReadout R B p=finiteReadout R B p := by
  simp only [physicalReadout,laboratorySpectra_eq,rotate_withParams]
  simp_rw [fun i => spectral_moments _ (simple i),fun t => spectral_moments _ (tilted t)]
  exact finite_diagonal_access R B p

/-- Raw diagonal DSF spectra determine every field and exchange at large B.
No ground-state simplicity or expansion assumption is supplied by the user. -/
theorem diagonalSF_from_spectra (R : Bonds S) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (physicalReadout R B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        ‖physicalReadout R B p-leading p‖ ≤ (C/B)*‖p‖ := by
  let G := fun i => (groundChart_exists R i).some
  let U : Set (Params R.dirs) := {p | ∀ i, IsGroundPair R i p ((G i).ψ p) ((G i).E p)}
  have near : U ∈ 𝓝 0 := eventually_all.mpr fun i => (G i).physical
  have rotated : {p | p∈U ∧ ∀ t, rotate t p∈U} ∈ 𝓝 (0:Params R.dirs) := by
    apply Filter.Eventually.and near
    apply eventually_all.mpr; intro t
    have tend : Tendsto (rotate (D := R.dirs) t) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (rotate (D := R.dirs) t).continuous.continuousAt (x := 0) |>.tendsto
    exact tend.eventually near
  obtain ⟨a,ha,physical⟩ := scaled_neighborhood rotated
  obtain ⟨C,hC,b,hb,result⟩ := diagonalSF_finite R
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  have la := (le_max_left ..).trans large
  have lb := (le_max_right ..).trans large
  have pos := ha.trans_le la
  have eq (p : Params R.dirs) (hp : p∈couplingCube R.dirs) : physicalReadout R B p=finiteReadout R B p := by
    have ground := (physical B la p hp).self_of_nhds
    apply physicalReadout_eq
    · intro i; exact ground_energy_simple (G i) pos p (ground.1 i)
    · intro t; exact ground_energy_simple (G 2) pos (rotate t p) (by simpa only [map_smul] using ground.2 t 2)
  constructor
  · intro p hp q hq same
    exact (result B lb).1 hp hq ((eq p hp).symm.trans (same.trans (eq q hq)))
  · intro p hp; rw [eq p hp]; exact ((result B lb).2 p hp).2.2

/-- Mathematical exact inversion of the raw six-setting diagonal spectra. -/
theorem exact_recovery_from_spectra (R : Bonds S) :
    ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube R.dirs,
      Function.invFunOn (physicalReadout R B) (couplingCube R.dirs) (physicalReadout R B p)=p := by
  obtain ⟨C,hC,b,hb,result⟩ := diagonalSF_from_spectra R
  exact ⟨b,hb,fun B large p hp => (result B large).1.leftInvOn_invFunOn hp⟩

/-- Explicit linear inversion with additive errors in the extracted harmonics. -/
theorem recovery_error_from_spectra (R : Bonds S) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube R.dirs,
      ∀ η : Harmonics R.dirs,
        ‖decoder (physicalReadout R B p+η)-p‖ ≤
          ‖(decoder (D := R.dirs))‖*((C/B)*‖p‖+‖η‖) := by
  obtain ⟨C,hC,b,hb,result⟩ := diagonalSF_from_spectra R
  refine ⟨C,hC,b,hb,?_⟩
  intro B large p hp η
  have eq : decoder (physicalReadout R B p+η)-p =
      decoder ((physicalReadout R B p-leading p)+η) := by
    rw [map_add,map_add,map_sub,show decoder (leading p)=p from readout_leading p]
    abel
  rw [eq]
  exact (decoder.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add_right ((result B large).2 p hp) _)) (norm_nonneg _))

variable {ν : ℕ}

/-- The raw six-setting acquisitions converge to the certified infinite-volume
real-time DSF readout, including their elastic subtraction. -/
theorem physical_bulk_limit (R : Bonds (Site ν)) {G : BoxCharts R}
    (A : LocalGroundExpansion R G) {B : ℝ} (pos : 0<B) (p : Params R.dirs)
    (small : ‖B⁻¹ • p‖ < A.radius)
    (tiltedSmall : ∀ t, ‖rotate t (B⁻¹ • p)‖ < A.radius) :
    Tendsto (fun n => originalLabels R n
      (physicalReadout (periodicBonds R n) B (boxParams R n p))) atTop (𝓝 (infiniteReadout R B p)) := by
  have target : infiniteReadout R B p=atField (sixFunction A.limitSeries.sum) B p := by
    rw [six_field]
    unfold infiniteReadout sixFunction
    apply congrArg combine
    refine Prod.ext (infinite_eq_series R A pos p small) ?_
    funext t
    exact infinite_eq_series R A pos (rotate t p) (by simpa only [map_smul] using tiltedSmall t)
  rw [target]
  have convergence : Tendsto (fun n => sixFunction (boxReadout R G n) (B⁻¹ • p)) atTop
      (𝓝 (sixFunction A.limitSeries.sum (B⁻¹ • p))) := by
    apply combine.continuous.continuousAt.tendsto.comp
    exact (A.bulk_readout small).prodMk_nhds
      (tendsto_pi_nhds.mpr fun t => A.bulk_readout (tiltedSmall t))
  apply (convergence.const_smul B).congr'
  apply Eventually.of_forall; intro n
  have base := A.physical n (B⁻¹ • p) small
  have tilted (t : Pair) := A.physical n (rotate t (B⁻¹ • p)) (tiltedSmall t)
  have base' : ∀ i, IsGroundPair (periodicBonds R n) i (B⁻¹ • boxParams R n p)
      ((G n i).ψ (B⁻¹ • boxParams R n p)) ((G n i).E (B⁻¹ • boxParams R n p)) := by
    simpa only [map_smul] using base
  have tilted' : ∀ t i, IsGroundPair (periodicBonds R n) i (B⁻¹ • rotate t (boxParams R n p))
      ((G n i).ψ (B⁻¹ • rotate t (boxParams R n p))) ((G n i).E (B⁻¹ • rotate t (boxParams R n p))) := by
    intro t; simpa only [map_smul,rotate_box] using tilted t
  change B • sixFunction (boxReadout R G n) (B⁻¹ • p) = originalLabels R n _
  rw [physicalReadout_eq (periodicBonds R n) B (boxParams R n p)
    (fun i => ground_energy_simple (G n i) pos _ (base' i))
    (fun t => ground_energy_simple (G n 2) pos _ (tilted' t 2))]
  rw [finite_eq_chart (periodicBonds R n) (G n) pos _ base' tilted']
  simp only [atField,sixFunction,← map_smul,combine_labels,map_smul,rotate_box,boxReadout]

/-- Complete volume-first result. Inputs are the six physical diagonal
spectra. Their limit determines all couplings, with a controlled linear
reconstruction error at finite applied field. -/
theorem six_direction_protocol (R : Bonds (Site ν)) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (infiniteReadout R B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        Tendsto (fun n => originalLabels R n
          (physicalReadout (periodicBonds R n) B (boxParams R n p))) atTop (𝓝 (infiniteReadout R B p)) ∧
        exactRecover R B (infiniteReadout R B p)=p ∧
        ∀ η : Harmonics R.dirs, ‖decoder (infiniteReadout R B p+η)-p‖ ≤
          ‖(decoder (D := R.dirs))‖*((C/B)*‖p‖+‖η‖) := by
  obtain ⟨G,⟨A⟩⟩ := periodic_ground_expansion R
  have ball : {p : Params R.dirs | ‖p‖ < A.radius} ∈ 𝓝 0 := by
    simpa [Metric.ball,dist_zero_right] using Metric.ball_mem_nhds (0:Params R.dirs) (show 0<(A.radius:ℝ) from A.positive)
  have near : {p : Params R.dirs | ‖p‖ < A.radius ∧ ∀ t, ‖rotate t p‖ < A.radius} ∈ 𝓝 0 := by
    apply Filter.Eventually.and ball
    apply eventually_all.mpr; intro t
    have tend : Tendsto (rotate (D := R.dirs) t) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (rotate (D := R.dirs) t).continuous.continuousAt (x := 0) |>.tendsto
    exact tend.eventually ball
  obtain ⟨a,ha,inside⟩ := scaled_neighborhood near
  obtain ⟨C,hC,b,hb,estimate⟩ := diagonalSF_reconstruction R
  obtain ⟨_,_,c,_,unique⟩ := diagonalSF_infinite_DSF R
  refine ⟨C,hC,max a (max b c),ha.trans_le (le_max_left ..),?_⟩
  intro B large
  have la := (le_max_left ..).trans large
  have lb := (le_max_left ..).trans ((le_max_right ..).trans large)
  have lc := (le_max_right ..).trans ((le_max_right ..).trans large)
  refine ⟨(unique B lc).1,?_⟩
  intro p hp
  have small := (inside B la p hp).self_of_nhds
  exact ⟨physical_bulk_limit R A (ha.trans_le la) p small.1 small.2,
    (unique B lc).1.leftInvOn_invFunOn hp,estimate B lb p hp⟩

end DSFTomography.SF.DiagonalSix
