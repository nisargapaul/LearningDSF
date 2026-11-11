import DSFTomography.SFLabGround
import DSFTomography.SFPaperLimit

/-! Endpoints using the same laboratory-basis ground-state DSF as the rest of
the package. The analytic field-frame chart disappears from the observables. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Matrix Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {R : Bonds S}

private theorem lab_first (W : Volume S) (m : Config S) (d : S) (a b : Axis) :
    (groundDSF W m).harmonics.first d a b = avg (fun r => (eigenState W m).ev
      (spinAt r a*(qubitH W.R W.h W.J - (energies W.R W.h W.J m:ℂ) • 1)*spinAt (r+d) b)) := by
  let U := energyBasis W.R W.h W.J
  let e := fun j => (energies W.R W.h W.J j:ℂ)
  let L := qubitH W.R W.h W.J
  have D : inBasis U L = Matrix.diagonal e :=
    (rotate_H W.R W.h W.J U).symm.trans (diagonalized W.R W.h W.J)
  have mid : inBasis U (L - e m • 1) = Matrix.diagonal (fun j => e j-e m) := by
    have first : inBasis U (L-e m • 1) = inBasis U L - e m • 1 := by
      simp [inBasis,Matrix.mul_sub,Matrix.sub_mul]
    rw [first,D]
    ext j k; by_cases eq : j=k <;> simp [eq]
  rw [harmonics_ground]
  apply congrArg avg; funext r
  change m₁ (pureWeight m) e (inBasis U (spinAt r a)) (inBasis U (spinAt (r+d) b)) =
    inBasis U (spinAt r a*(L-e m • 1)*spinAt (r+d) b) m m
  rw [← inBasis_mul,← inBasis_mul,mid]
  simp only [m₁,pureWeight,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro j _
  simp [Matrix.diagonal_apply,mul_ite,mul_comm]

private theorem sandwich_scalar {ι : Type*} [Fintype ι] (v : ι → ℂ) (A : Op ι) (c : ℂ) :
    sandwich v (c • A) v = c*sandwich v A v := by
  simp only [sandwich,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

set_option maxHeartbeats 600000 in
/-- Equality of the actual ordered measured moments, including crossed spin
channels, before projecting them to the manuscript features. -/
theorem laboratory_moments {i : Axis} (g : GroundChart R i) {B : ℝ} (hB : 0 < B)
    (p : Params R.dirs) (physical : IsGroundPair R i (B⁻¹ • p) (g.ψ (B⁻¹ • p)) (g.E (B⁻¹ • p))) :
    let W := driven (withParams R p) B i
    (groundDSF W (lowest W)).harmonics = energyScale B (g.linesData (B⁻¹ • p)) := by
  let x := B⁻¹ • p
  let W := driven (withParams R p) B i
  let m := lowest W
  let T := toLab (S := S) i
  let H := unitHamiltonian R i x
  let L := qubitH W.R W.h W.J
  let e := (energies W.R W.h W.J m:ℂ)
  let E := g.E x
  let rot := fun A : Op (Config S) => T*A*T.conjTranspose
  obtain ⟨en,ev⟩ := laboratory_ground g hB p physical
  have probe (r : S) (a : Axis) : rot (spinAt r (inChart i a)) = spinAt r a := by
    rw [show rot (spinAt r (inChart i a)) = spinAt r (axisInLab i (inChart i a)) from toLab_probe ..]
    congr 1; fin_cases i <;> fin_cases a <;> decide
  have mul (A C : Op (Config S)) : rot (A*C) = rot A * rot C := by
    change T*(A*C)*T.conjTranspose = (T*A*T.conjTranspose)*(T*C*T.conjTranspose)
    have unit : T.conjTranspose*T=1 := (toLab_unit i).1
    calc
      _ = T*A*(T.conjTranspose*T)*C*T.conjTranspose := by rw [unit,Matrix.mul_one,Matrix.mul_assoc T A C]
      _ = _ := by simp only [Matrix.mul_assoc]
  have shift : rot ((B:ℂ) • (H - E • 1)) = L-e • 1 := by
    have drive := toLab_driven R i hB p
    change T*((B:ℂ) • H)*T.conjTranspose = ((B:ℂ)*Fintype.card S) • 1 + L at drive
    change (e:ℂ) = (B:ℂ)*(E-Fintype.card S) at en
    dsimp only [rot]; rw [smul_sub,smul_smul,Matrix.mul_sub,Matrix.sub_mul,drive,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,(toLab_unit i).2,en,mul_sub,sub_smul]
    abel
  dsimp only
  apply congrArg₂ Data.mk
  · funext d a b
    change (groundDSF W m).harmonics.static d a b = (g.linesData x).static d a b
    rw [static_ground,g.static_lines]
    apply congrArg avg; funext r
    rw [← ev,show T*(spinAt r (inChart i a)*spinAt (r+d) (inChart i b))*T.conjTranspose =
      spinAt r a*spinAt (r+d) b by rw [← probe r a,← probe (r+d) b,← mul]]
  · funext d a b
    change (groundDSF W m).harmonics.first d a b = (B:ℂ) * (g.linesData x).first d a b
    rw [lab_first,g.first_lines]
    have loc (r : S) : (eigenState W m).ev (spinAt r a*(L-e • 1)*spinAt (r+d) b) =
        (B:ℂ)*sandwich (g.ψ x) (spinAt r (inChart i a)*(H-E • 1)*spinAt (r+d) (inChart i b)) (g.ψ x) := by
      rw [← probe r a,← probe (r+d) b,← shift,← mul,← mul]
      change (eigenState W m).ev (T*_ *T.conjTranspose) = _
      rw [ev,Matrix.mul_smul,Matrix.smul_mul]
      exact sandwich_scalar ..
    change avg (fun r => (eigenState W m).ev (spinAt r a*(L-e • 1)*spinAt (r+d) b)) = _
    simp only [loc,avg,← Finset.mul_sum,mul_div_assoc,H,E]

/-- A directly supplied ground-state scan and the chart yield identical
harmonics in a physical neighborhood. -/
theorem laboratory_readout (G : ∀ i, GroundChart R i) {B : ℝ} (hB : 0 < B) (p : Params R.dirs)
    (physical : ∀ i, IsGroundPair R i (B⁻¹ • p) ((G i).ψ (B⁻¹ • p)) ((G i).E (B⁻¹ • p))) :
    groundPaperReadout (withParams R p) B Subtype.val = atField (unitReadout G) B p := by
  rw [← exact_spectral_readout G]
  unfold groundPaperReadout paperFromDSF
  apply congrArg (paperHarmonics Subtype.val B)
  funext i
  rw [laboratory_moments (G i) hB p (physical i)]
  simp [Data.harmonics,paperSpectra,harmonic_toMomentum]

/-- Fixed finite lattice. The only input is its oriented bond set. Measurements
come from diagonalizing the literal driven laboratory Pauli Hamiltonian. -/
theorem fullAccessSF_lab_finite (R : Bonds S) :
    let M := fun B (p : Params R.dirs) => groundPaperReadout (withParams R p) B Subtype.val
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b, Set.InjOn (M B) (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs, DifferentiableAt ℝ (M B) p ∧
        ‖fderiv ℝ (fun q => M B q - leading q) p‖ ≤ C/B ∧
        ‖M B p - leading p‖ ≤ (C/B)*‖p‖ := by
  dsimp only
  let G := fun i => (groundChart_exists R i).some
  obtain ⟨C,hC,a,ha,result⟩ := paper_finite G
  obtain ⟨b,hb,physical⟩ := groundChart_cube_neighborhood G
  refine ⟨C,hC,max a b,ha.trans_le (le_max_left ..),?_⟩
  intro B large
  have la := (le_max_left ..).trans large
  have lb := (le_max_right ..).trans large
  have hB := ha.trans_le la
  let M : Params R.dirs → Harmonics R.dirs := fun p => groundPaperReadout (withParams R p) B Subtype.val
  have near (p : Params R.dirs) (hp : p ∈ couplingCube R.dirs) : M =ᶠ[𝓝 p] atField (unitReadout G) B := by
    have sc : Continuous (fun q : Params R.dirs => B⁻¹ • q) := continuous_const.smul continuous_id
    filter_upwards [sc.continuousAt.tendsto.eventually (physical B lb p hp)] with q ground
    exact laboratory_readout G hB q ground
  obtain ⟨inj,est⟩ := result B la
  refine ⟨fun p hp q hq same => inj hp hq ((near p hp).self_of_nhds.symm.trans (same.trans (near q hq).self_of_nhds)),?_⟩
  intro p hp
  have eq : (fun q => M q-leading q) =ᶠ[𝓝 p] (fun q => atField (unitReadout G) B q-leading q) :=
    (near p hp).sub EventuallyEq.rfl
  refine ⟨(est p hp).1.congr_of_eventuallyEq (near p hp),?_⟩
  change ‖fderiv ℝ (fun q => M q-leading q) p‖ ≤ _ ∧ ‖M p-leading p‖ ≤ _
  rw [eq.fderiv_eq,(near p hp).self_of_nhds]
  exact (est p hp).2

/-- Volume-first theorem in laboratory coordinates. The finite measurements
in the limit below are functions solely of the lattice, the couplings and B. -/
theorem fullAccessSF_lab_limit {ν : ℕ} (R : Bonds (Site ν))
    {G : BoxCharts R} (A : LocalGroundExpansion R G) :
    let boxMap := fun B n p => originalLabels R n (groundPaperReadout
      (withParams (periodicBonds R n) (boxParams R n p)) B Subtype.val)
    ∃ M : ℝ → Params R.dirs → Harmonics R.dirs, ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (M B) (couplingCube R.dirs) ∧ ∀ p ∈ couplingCube R.dirs,
        Tendsto (fun n => boxMap B n p) atTop (𝓝 (M B p)) ∧ DifferentiableAt ℝ (M B) p ∧
        ‖fderiv ℝ (fun q => M B q-leading q) p‖ ≤ C/B ∧ ‖M B p-leading p‖ ≤ (C/B)*‖p‖ := by
  dsimp only
  obtain ⟨C,hC,b,hb,bulk⟩ := fullAccessSF_paper_limit R A
  refine ⟨atField A.limitSeries.sum,C,hC,b,hb,?_⟩
  intro B large
  obtain ⟨inj,data⟩ := bulk B large
  refine ⟨inj,?_⟩
  intro p hp
  obtain ⟨physical,lim,estimate⟩ := data p hp
  refine ⟨lim.congr' (Eventually.of_forall (fun n => ?_)),estimate⟩
  apply congrArg (originalLabels R n)
  rw [exact_spectral_readout,laboratory_readout (G n) (hb.trans_le large)]
  intro i
  simpa only [map_smul] using physical n i

end DSFTomography.SF
