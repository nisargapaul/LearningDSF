import DSFTomography.DSFJointLimit

/-! The manuscript's connected sine/cosine SF readout, now formed from the
moments of the infinite-volume real-time spectra. -/
noncomputable section
set_option maxHeartbeats 300000
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord SF Filter
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def drivenFields (B : ℝ) (i a : Axis) : ℝ := h a-if a=i then B else 0

def groundPop (B : ℝ) (i : Axis) (n : ℕ) (j : Config (Box R n)) : ℝ :=
  if j=lowest (periodicVolume R (drivenFields h B i) J n) then 1 else 0

theorem groundPop_positive (B : ℝ) : ∀ i n j, 0 ≤ groundPop R h J B i n j := by
  intros; unfold groundPop; split <;> norm_num

theorem groundPop_normalized (B : ℝ) : ∀ i n, ∑ j, groundPop R h J B i n j=1 := by
  intros; simp [groundPop]

/-- All three orientations share one growing volume subsequence. -/
theorem SF_spectra_exist (B : ℝ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i, ∃ D : BulkDSF R (drivenFields h B i) J (groundPop R h J B i) id,
      D.select=s :=
  joint_bulkDSF_exists R (drivenFields h B) (fun _ => J) (groundPop R h J B)
    (groundPop_positive R h J B) (groundPop_normalized R h J B)

def momentData (f : LocalChannel ν → ℕ → ℂ) : Data (Site ν) where
  static d a b := f (d,a,b) 0/(2*Real.pi)
  first d a b := f (d,a,b) 1/(2*Real.pi)

def SF_momentReadout (B : ℝ) (f : Axis → LocalChannel ν → ℕ → ℂ) : Harmonics R.dirs :=
  paperHarmonics Subtype.val B (fun i => connected (momentData (f i)))

theorem SF_momentReadout_continuous (B : ℝ) : Continuous (SF_momentReadout R B) := by
  apply Continuous.prodMk
  · apply continuous_pi; intro i
    dsimp [SF_momentReadout,paperHarmonics,connected,momentData,Data.mag]
    fun_prop
  · apply continuous_pi; intro d
    apply continuous_pi; intro i
    apply continuous_pi; intro k
    fin_cases k <;>
      dsimp [SF_momentReadout,paperHarmonics,cosAmp,sinAmp,connected,momentData,Data.mag] <;> fun_prop

/-- Continuous processing preserves the certified limit, including connected
subtraction, centering at 2B, and the oriented sine and cosine coefficients. -/
theorem SF_readout_limit (B : ℝ) (s : ℕ → ℕ)
    (D : ∀ i, BulkDSF R (drivenFields h B i) J (groundPop R h J B i) id)
    (shared : ∀ i, (D i).select=s) :
    Tendsto (fun n => SF_momentReadout R B (fun i c k =>
      (channelLines R (drivenFields h B i) J (groundPop R h J B i) (s n) c).moment k))
      atTop (𝓝 (SF_momentReadout R B (fun i => (D i).moment))) := by
  apply (SF_momentReadout_continuous R B).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr; intro i
  apply tendsto_pi_nhds.mpr; intro c
  apply tendsto_pi_nhds.mpr; intro k
  have lim := (D i).moment_limit c k
  rw [shared i] at lim
  exact lim

/-- Agreement with any already-certified full-sequence SF harmonic limit. -/
theorem SF_agrees_with_certified_limit (B : ℝ) (s : ℕ → ℕ) (inc : StrictMono s)
    (D : ∀ i, BulkDSF R (drivenFields h B i) J (groundPop R h J B i) id)
    (shared : ∀ i, (D i).select=s) (M : Harmonics R.dirs)
    (certified : Tendsto (fun n => SF_momentReadout R B (fun i c k =>
      (channelLines R (drivenFields h B i) J (groundPop R h J B i) n c).moment k)) atTop (𝓝 M)) :
    SF_momentReadout R B (fun i => (D i).moment) = M :=
  tendsto_nhds_unique (SF_readout_limit R h J B s D shared) (certified.comp inc.tendsto_atTop)

/-- The finite input of this limit is exactly the manuscript's laboratory
readout of its ground-state DSF, with the original bond labels. -/
theorem SF_finite_readout (B : ℝ) (n : ℕ) :
    SF_momentReadout R B (fun i c k =>
      (channelLines R (drivenFields h B i) J (groundPop R h J B i) n c).moment k) =
      groundPaperReadout (periodicVolume R h J n) B (fun d : R.dirs => place R n d) := by
  have zero : place R n 0 = 0 := by ext i; simp [place,periodicSite,reduceBond]
  have neg (d : Site ν) : place R n (-d) = -place R n d := by ext i; simp [place,periodicSite,reduceBond]
  have weights (i : Axis) : (fun j => (groundPop R h J B i n j:ℂ)) =
      pureWeight (lowest (driven (periodicVolume R h J n) B i)) := by
    funext j; simp only [groundPop,pureWeight,apply_ite Complex.ofReal,Complex.ofReal_one,Complex.ofReal_zero]; rfl
  unfold SF_momentReadout groundPaperReadout paperFromDSF
  simp only [harmonics_ground]
  apply Prod.ext
  · funext i
    simp only [paperHarmonics,connected,momentData,channelLines,box_zeroth,box_first,
      mul_div_cancel_left₀ _ two_pi_ne_zero,Data.mag,zero,FD.mixtureData,weights]
    rfl
  · funext d i k
    fin_cases k <;>
      simp only [paperHarmonics,connected,momentData,channelLines,box_zeroth,box_first,
        mul_div_cancel_left₀ _ two_pi_ne_zero,Data.mag,zero,neg,FD.mixtureData,weights] <;> rfl

structure SFRealTimeDSF (B : ℝ) where
  select : ℕ → ℕ
  increasing : StrictMono select
  dsf : ∀ i, BulkDSF R (drivenFields h B i) J (groundPop R h J B i) id
  shared : ∀ i, (dsf i).select=select

noncomputable def groundDSFs (B : ℝ) : SFRealTimeDSF R h J B := Classical.choice (by
  obtain ⟨s,inc,existsD⟩ := SF_spectra_exist R h J B
  choose D same using existsD
  exact ⟨⟨s,inc,D,same⟩⟩)

def infiniteSFReadout (B : ℝ) : Harmonics R.dirs :=
  SF_momentReadout R B (fun i => ((groundDSFs R h J B).dsf i).moment)

theorem infiniteSFReadout_eq_limit (B : ℝ) (M : Harmonics R.dirs)
    (certified : Tendsto (fun n => groundPaperReadout (periodicVolume R h J n) B
      (fun d : R.dirs => place R n d)) atTop (𝓝 M)) :
    infiniteSFReadout R h J B = M := by
  let D := groundDSFs R h J B
  apply SF_agrees_with_certified_limit R h J B D.select D.increasing D.dsf D.shared M
  simpa only [SF_finite_readout] using certified

def parameterExchanges (p : Params R.dirs) (d : Site ν) : Matrix Axis Axis ℝ :=
  if hd : d ∈ R.dirs then p.2 ⟨d,hd⟩ else 0

theorem periodicVolume_parameters (p : Params R.dirs) (n : ℕ) :
    periodicVolume R p.1 (parameterExchanges R p) n =
      withParams (periodicBonds R n) (boxParams R n p) := by
  apply congrArg (fun f : Box R n → Matrix Axis Axis ℝ =>
    ({R:=periodicBonds R n,h:=p.1,J:=f}:Volume (Box R n)))
  funext x
  change (periodicVolume R p.1 (parameterExchanges R p) n).J x =
    if hx : x ∈ (periodicBonds R n).dirs then p.2 ((bondInBox R n).symm ⟨x,hx⟩) else 0
  by_cases hx : x ∈ (periodicBonds R n).dirs
  · rw [dif_pos hx]
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hx
    subst x
    rw [image_coupling R p.1 (parameterExchanges R p) n hd]
    simp only [parameterExchanges,dif_pos hd]
    exact congrArg p.2 ((bondInBox R n).symm_apply_apply ⟨d,hd⟩).symm
  · rw [dif_neg hx]
    apply Finset.sum_eq_zero
    intro d hd
    have ne : reduceBond (periodIndex R n) d ≠ x := by
      intro eq
      exact hx (Finset.mem_image.mpr ⟨d,hd,eq⟩)
    simp [ne]

/-- The strong-field bulk inverse is unchanged when its inputs are moments
of the infinite-volume time-Fourier distributions. -/
theorem fullAccessSF_infinite_DSF :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (fun p : Params R.dirs => infiniteSFReadout R p.1 (parameterExchanges R p) B)
        (couplingCube R.dirs) ∧
      ∀ p ∈ couplingCube R.dirs,
        ‖infiniteSFReadout R p.1 (parameterExchanges R p) B-leading p‖ ≤ (C/B)*‖p‖ := by
  obtain ⟨M,C,hC,b,hb,cert⟩ := fullAccessSF_lab_thermodynamic R
  refine ⟨C,hC,b,hb,fun B hB => ?_⟩
  have eq (p : Params R.dirs) (hp : p ∈ couplingCube R.dirs) :
      infiniteSFReadout R p.1 (parameterExchanges R p) B = M B p := by
    apply infiniteSFReadout_eq_limit
    have lim := ((cert B hB).2 p hp).1
    have point (n : ℕ) : groundPaperReadout (periodicVolume R p.1 (parameterExchanges R p) n) B
        (fun d : R.dirs => place R n d) =
        originalLabels R n (groundPaperReadout (withParams (periodicBonds R n) (boxParams R n p)) B Subtype.val) := by
      rw [periodicVolume_parameters]
      rfl
    simpa only [point] using lim
  constructor
  · intro p hp q hq same
    apply (cert B hB).1 hp hq
    exact (eq p hp).symm.trans (same.trans (eq q hq))
  · intro p hp
    rw [eq p hp]
    exact ((cert B hB).2 p hp).2.2.2

end DSFTomography.Spectral
