import DSFTomography.SFFinite
import Mathlib.Topology.Sequences

/-! The same finite-dimensional equations hold on every thermodynamic
accumulation point of the measured local harmonics. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
/-- Contributions of the two ends of one oriented bond to the on-site force. -/
def atEnds (C J : Tensor) (a b : Axis) := ∑ u, ∑ v, J u v *
  (phase a u * phase (third a u) b * C (third (third a u) b) v +
   phase a v * phase (third a v) b * C u (third (third a v) b))

theorem background_local (C J : S → Tensor) (R : Bonds S) (a b : Axis) :
    background (fun s t => C (t-s)) R J a b = ∑ d ∈ R.dirs, atEnds (C d) (J d) a b := by
  unfold background
  apply Finset.sum_congr rfl
  intro d hd
  have nz := R.nonzero d hd
  have loc (t : S) (u v : Axis) :
      pair (fun s e => C (e-s)) 0 0 t (t+d) a b u v =
      (if t=0 then phase a u * phase (third a u) b * C d (third (third a u) b) v else 0) +
      (if t= -d then phase a v * phase (third a v) b * C d u (third (third a v) b) else 0) := by
    by_cases ht : t=0
    · subst t; simp [pair,coeff,nz,Ne.symm nz,mul_assoc]
    · by_cases he : t= -d
      · subst t; simp [pair,coeff,nz,mul_assoc]
      · have ne : t+d ≠ 0 := fun e => he (eq_neg_of_add_eq_zero_left e)
        simp [pair,coeff,ht,Ne.symm ht,ne,Ne.symm ne,he]
  simp_rw [loc]
  rw [Finset.sum_comm]
  unfold atEnds
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp [mul_add,Finset.sum_add_distrib,mul_ite]

/-- Data for each field: bond statics, bond forces, magnetization and on-site force. -/
abbrev Packet (D : Type*) := Axis → (D → Tensor) × (D → Tensor) × (Axis → ℂ) × Tensor
abbrev BaseData (D : Type*) := Axis → (Axis ⊕ (D × Axis × Axis)) → ℂ

namespace Packet
variable {D : Type*} [Fintype D]
def base (A : Packet D) : BaseData D := fun i t => match t with
  | .inl a => (A i).2.2.1 a
  | .inr (d,a,b) => (A i).1 d a b

def forward (p : BaseData D) (b : Axis → ℂ) (J : D → Tensor) (B : ℝ) : Packet D := fun i =>
  let C : D → Tensor := fun d a v => p i (.inr (d,a,v))
  let m := fun a => p i (.inl a)
  (C, fun d => bondMap (C d) (J d), m, fun a v => fieldMap m (fun x => b x - if x=i then (B:ℂ) else 0) a v +
    ∑ d, atEnds (C d) (J d) a v)

omit [Fintype D] in
theorem continuous_base : Continuous (base (D := D)) := by
  apply continuous_pi
  intro i; apply continuous_pi
  rintro (a|⟨d,a,b⟩) <;> unfold base <;> fun_prop

theorem continuous_forward (b : Axis → ℂ) (J : D → Tensor) (B : ℝ) : Continuous (fun p => forward p b J B) := by
  unfold forward bondMap fieldMap atEnds; fun_prop

def exchange (A : Packet D) (d : D) := recoverBond (∑ i, (A i).1 d) (∑ i, (A i).2.1 d)
def field (A : Packet D) (B : ℝ) : Axis → ℂ := fun a =>
  recoverField (A 0).2.2.1 (fun s t => (A 0).2.2.2 s t - ∑ d, atEnds ((A 0).1 d) (exchange A d) s t) 0 a +
    (if a=0 then (B:ℂ) else 0)

theorem recover (A : Packet D) (b : Axis → ℂ) (J : D → Tensor) (B : ℝ)
    (eq : A = forward (base A) b J B)
    (near : ∀ d i a v, ‖(A i).1 d a v-polarizedCorrelation i a v‖ ≤ 1/16)
    (mag : (A 0).2.2.1 0 ≠ 0) : exchange A = J ∧ field A B = b := by
  have ex (d : D) : exchange A d = J d := by
    have forces (i : Axis) : (A i).2.1 d = bondMap ((A i).1 d) (J d) := congrArg (fun K : Packet D => (K i).2.1 d) eq
    unfold exchange
    simp_rw [forces]
    rw [bondMap_sum,recoverBond_exact _ _ (pooled_det _ (near d))]
  refine ⟨funext ex,?_⟩
  have onsite := congrArg (fun K : Packet D => (K 0).2.2.2) eq
  unfold field
  simp_rw [ex]
  have sub : (fun s t => (A 0).2.2.2 s t - ∑ d, atEnds ((A 0).1 d) (J d) s t) =
      fieldMap (A 0).2.2.1 (fun x => b x - if x=0 then (B:ℂ) else 0) := by
    ext s t; exact sub_eq_of_eq_add (congrFun (congrFun onsite s) t)
  rw [sub,recoverField_exact _ _ _ mag]
  simp

end Packet

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
def periodicPacket (B : ℝ) (n : ℕ) : Packet R.dirs := fun i =>
  let A := restore (scan (periodicVolume R h J n) B i)
  (fun d => A.static (periodicSite R n d), fun d => A.force (periodicSite R n d), A.mag,A.force 0)

private theorem packet_equations (B : ℝ) (n : ℕ) :
    periodicPacket R h J B n = Packet.forward (Packet.base (periodicPacket R h J B n))
      (fun a => (h a:ℂ)) (fun d a b => (J d a b:ℂ)) B := by
  let V := periodicVolume R h J n
  funext i
  let W := driven V B i
  let A := (groundDSF W (lowest W)).harmonics
  let P := qubitSpins (energyBasis W.R W.h W.J)
  let w := pureWeight (lowest W)
  let E := fun j => (energies W.R W.h W.J j:ℂ)
  have same : A = measured P w E := harmonics_ground ..
  have station := diagonalized W.R W.h W.J
  have img (d : R.dirs) : periodicSite R n d ∈ W.R.dirs := Finset.mem_image_of_mem _ d.property
  simp only [periodicPacket,scan,restore_connected,Packet.forward,Packet.base]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
  · funext d
    change A.force (periodicSite R n d) = bondMap (A.static (periodicSite R n d)) (fun a b => (J d.val a b : ℂ))
    rw [same,measured_bond P W.R _ _ w E station (img d)]
    congr 1
    ext a b; simp only [W,V,driven,periodicSite,image_coupling R h J n d.property]
  · ext a b
    change A.force 0 a b = fieldMap A.mag (fun x => (h x:ℂ) - if x=i then (B:ℂ) else 0) a b + ∑ d : R.dirs, atEnds (A.static (periodicSite R n d)) (fun u v => (J d u v:ℂ)) a b
    rw [same,measured_onsite P W.R _ _ w E station,background_local]
    apply congrArg₂ (·+·)
    · congr 1; funext k; simp [W,driven,V,periodicVolume,apply_ite Complex.ofReal]
    · rw [show W.R.dirs = R.dirs.image (periodicSite R n) from rfl,
        Finset.sum_image (injects_dirs R n),← Finset.sum_attach R.dirs]
      apply Finset.sum_congr rfl
      intro d _
      simp only [W,V,driven,periodicSite,image_coupling R h J n d.property]

private theorem packet_bounds (bounded : ∀ s, ‖strength R h J s‖ ≤ 1) (B : ℝ)
    (large : sufficientField R ≤ B) (n : ℕ) :
    (∀ d : R.dirs, ∀ i a b, ‖(periodicPacket R h J B n i).1 d a b-polarizedCorrelation i a b‖ ≤ 1/16) ∧
    1/2 ≤ ((periodicPacket R h J B n 0).2.2.1 0).re := by
  have pos : 0 < sufficientField R := by unfold sufficientField; positivity
  have bounds := scan_bounds (periodicVolume R h J n) (boxInteraction R h J n) (boxInteraction_matrix ..)
    (pos.trans_le large) (incidentBound_pos R h J).le (boxInteraction_incident R h J n)
    ((cube_bound R h J bounded).trans large)
  exact ⟨fun d i => (bounds i).1 _ (Finset.mem_image_of_mem _ d.property),(bounds 0).2⟩

/-- Every thermodynamic subsequential limit of the observed harmonics has the
same measured-data inverse. In particular different couplings cannot share a
thermodynamic data set, even if the limiting state is allowed to vary. -/
theorem fullAccessSF_bulk (bounded : ∀ s, ‖strength R h J s‖ ≤ 1) (B : ℝ)
    (large : sufficientField R ≤ B) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun k => periodicPacket R h J B (seq k)) atTop (𝓝 A)) :
    Packet.exchange A = (fun (d : R.dirs) a b => (J d a b:ℂ)) ∧ Packet.field A B = (fun a => (h a:ℂ)) := by
  apply Packet.recover
  · apply tendsto_nhds_unique data
    apply ((Packet.continuous_forward _ _ B).continuousAt.tendsto.comp
      (Packet.continuous_base.continuousAt.tendsto.comp data)).congr'
    exact Eventually.of_forall fun k => (packet_equations R h J B (seq k)).symm
  · intro d i a b
    have cont : Continuous (fun K : Packet R.dirs => ‖(K i).1 d a b-polarizedCorrelation i a b‖) := by fun_prop
    exact le_of_tendsto (cont.continuousAt.tendsto.comp data) (Eventually.of_forall fun k =>
      (packet_bounds R h J bounded B large (seq k)).1 d i a b)
  · have cont : Continuous (fun K : Packet R.dirs => ((K 0).2.2.1 0).re) := by fun_prop
    have lower : 1/2 ≤ ((A 0).2.2.1 0).re := ge_of_tendsto (cont.continuousAt.tendsto.comp data)
      (Eventually.of_forall fun k => (packet_bounds R h J bounded B large (seq k)).2)
    intro zero; rw [zero,Complex.zero_re] at lower; norm_num at lower

/-- Two models with the same observed thermodynamic data agree, even when
their data were obtained along different growing sequences of boxes. -/
theorem fullAccessSF_identifiable (h' : Axis → ℝ) (J' : Site ν → Matrix Axis Axis ℝ)
    (bounded : ∀ s, ‖strength R h J s‖ ≤ 1) (bounded' : ∀ s, ‖strength R h' J' s‖ ≤ 1)
    (B : ℝ) (large : sufficientField R ≤ B) (A : Packet R.dirs) (seq seq' : ℕ → ℕ)
    (data : Tendsto (fun k => periodicPacket R h J B (seq k)) atTop (𝓝 A))
    (data' : Tendsto (fun k => periodicPacket R h' J' B (seq' k)) atTop (𝓝 A)) :
    (∀ d ∈ R.dirs, J d = J' d) ∧ h = h' := by
  obtain ⟨ex,field⟩ := fullAccessSF_bulk R h J bounded B large A seq data
  obtain ⟨ex',field'⟩ := fullAccessSF_bulk R h' J' bounded' B large A seq' data'
  constructor
  · intro d hd; ext a b
    exact Complex.ofReal_injective (congrFun (congrFun (congrFun (ex.symm.trans ex') ⟨d,hd⟩) a) b)
  · funext a; exact Complex.ofReal_injective (congrFun (field.symm.trans field') a)

/-- Thermodynamic data exist along growing subsequences. Compactness is needed
only for the static correlations and magnetizations. The moment equations then
supply the corresponding limiting first-moment combinations. -/
theorem bulk_data_exist (B : ℝ) : ∃ A : Packet R.dirs, ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Tendsto (fun k => periodicPacket R h J B (seq k)) atTop (𝓝 A) := by
  let V := periodicVolume R h J
  let f := fun n => Packet.base (periodicPacket R h J B n)
  let ball := Metric.closedBall (0:ℂ) 1
  let K : Set (BaseData R.dirs) := Set.univ.pi fun _ => Set.univ.pi fun _ => ball
  have compact : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have mem (n : ℕ) : f n ∈ K := by
    intro i _ t _
    let W := driven (V n) B i
    let m := lowest W
    let ρ := eigenState W m
    have cap (w : Pauli.Label (Box R n)) := ρ.unit_bound (word_unit w)
    rcases t with a | ⟨d,a,b⟩
    · change (restore (scan (V n) B i)).mag a ∈ ball
      rw [scan,restore_connected,mag_ground]
      have le := avg_close (c := 0) (δ := 1) (fun t : Box R n => by simpa only [sub_zero] using cap (oneLabel t a))
      simpa [ball,Metric.mem_closedBall,ρ,W,m,V,spinAt] using le
    · change (restore (scan (V n) B i)).static (periodicSite R n d) a b ∈ ball
      rw [scan,restore_connected,static_ground]
      have each (t : Box R n) : ‖ρ.ev (spinAt t a * spinAt (t+periodicSite R n d) b) - 0‖ ≤ 1 := by
        rw [sub_zero,spinAt,spinAt,Pauli.product,map_smul,norm_smul,Pauli.phase_norm,one_mul]
        exact cap _
      simpa [ball,Metric.mem_closedBall,ρ,W,m,V] using avg_close each
  obtain ⟨base,_,seq,inc,lim⟩ := compact.tendsto_subseq mem
  refine ⟨Packet.forward base (fun a => (h a:ℂ)) (fun d a b => (J d a b:ℂ)) B,seq,inc,?_⟩
  apply ((Packet.continuous_forward _ _ B).continuousAt.tendsto.comp lim).congr'
  exact Eventually.of_forall fun k => (packet_equations R h J B (seq k)).symm

end DSFTomography.SF
