import DSFTomography.SFMeasurement

/-! A uniform sufficient field for exact full-channel tomography on the coupling
cube. The data are the ground-state Lehmann spectra at three probe fields. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

/-- Connected statics of the translation-averaged state. The product of its
two magnetizations is symmetric in the two channels, including on site. -/
def connected (D : Data S) : Data S where
  static d a b := D.static d a b - D.mag a * D.mag b
  first := D.first

def restore (D : Data S) : Data S where
  static d a b := D.static d a b + D.mag a * D.mag b
  first := D.first

omit [Fintype S] [DecidableEq S] in
theorem restore_connected (D : Data S) : restore (connected D) = D := by
  have mag : (connected D).mag = D.mag := by
    funext k
    unfold Data.mag connected
    congr 1; ring
  have stat : (restore (connected D)).static = D.static := by
    funext d a b
    change D.static d a b - D.mag a * D.mag b + (connected D).mag a * (connected D).mag b = _
    rw [mag,sub_add_cancel]
  exact congrArg₂ Data.mk stat rfl

/-- Connected, normalized spatial harmonics of the full momentum-resolved
zeroth and first moments at the specified pure ground state. -/
def scan (V : Volume S) (B : ℝ) (i : Axis) : Data S :=
  let W := driven V B i
  connected (groundDSF W (lowest W)).harmonics

def scannedExchange (V : Volume S) (B : ℝ) := pooledExchange fun i => restore (scan V B i)
def scannedField (V : Volume S) (B : ℝ) := pooledField (fun i => restore (scan V B i)) V.R 0 B

theorem scan_bounds (V : Volume S) {T : Type*} [Fintype T] (I : PauliInteraction S T)
    (model : I.matrix = qubitH V.R V.h V.J) {g B : ℝ} (hB : 0<B) (hg : 0≤g) (incident : I.SiteBound g)
    (large : 4096*g ≤ B) (i : Axis) :
    (∀ d ∈ V.R.dirs, ∀ a b, ‖(restore (scan V B i)).static d a b - polarizedCorrelation i a b‖ ≤ 1/16) ∧
    1/2 ≤ ((restore (scan V B i)).mag i).re := by
  let W := driven V B i
  let m := lowest W
  let ρ := eigenState W m
  have gr : ρ.Ground (zeeman B i + I.matrix) := by
    rw [model,← driven_matrix]
    exact eigenState_ground W m (lowest_le W)
  simp only [scan,restore_connected]
  constructor
  · intro d hd a b
    rw [static_ground]
    apply avg_close
    intro t
    exact ground_correlation ρ I hB hg incident large i gr
      (show t≠t+d from Ne.symm (by simpa using V.R.nonzero d hd)) a b
  · rw [mag_ground]
    have each (t : S) : 1/2 ≤ (ρ.ev (spinAt t i)).re := by
      have bound := ground_polarization ρ I hB hg incident i gr t
      have small : 2*g/B ≤ 1/2 := (div_le_iff₀ hB).mpr (by linarith)
      linarith
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => each t)
    change 1/2 ≤ (avg (fun t => ρ.ev (spinAt t i))).re
    change 1/2 ≤ ((∑ t, ρ.ev (spinAt t i))/((Fintype.card S : ℝ):ℂ)).re
    rw [Complex.div_ofReal_re,Complex.re_sum]
    apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0:ℝ)<Fintype.card S)).mpr
    simpa [mul_comm] using sum

theorem fullAccessSF_finite (V : Volume S) {T : Type*} [Fintype T] (I : PauliInteraction S T)
    (model : I.matrix = qubitH V.R V.h V.J) {g B : ℝ} (hB : 0<B) (hg : 0≤g) (incident : I.SiteBound g)
    (large : 4096*g ≤ B) :
    (∀ d ∈ V.R.dirs, scannedExchange V B d = fun a b => (V.J d a b : ℂ)) ∧
    scannedField V B = fun a => (V.h a : ℂ) := by
  let W := driven V B
  let P := fun i => qubitSpins (energyBasis (W i).R (W i).h (W i).J)
  let w := fun i => pureWeight (lowest (W i))
  let E := fun i j => (energies (W i).R (W i).h (W i).J j : ℂ)
  have eq (i : Axis) : restore (scan V B i) = fieldMoments P w E i := by
    rw [scan,restore_connected,harmonics_ground]; rfl
  have bounds := scan_bounds V I model hB hg incident large
  have station (i : Axis) : H (P i) V.R (fun a => (V.h a:ℂ) - if a=i then (B:ℂ) else 0)
      (fun d a b => (V.J d a b:ℂ)) = Matrix.diagonal (E i) := by
    simpa only [P,W,driven,realH,Complex.ofReal_sub,apply_ite Complex.ofReal,Complex.ofReal_zero] using
      diagonalized (W i).R (W i).h (W i).J
  have det (d : S) (hd : d∈V.R.dirs) : (∑ i, (fieldMoments P w E i).static d).det ≠ 0 :=
    pooled_det _ fun i a b => by rw [← eq]; exact (bounds i).1 d hd a b
  have mag : (fieldMoments P w E 0).mag 0 ≠ 0 := by
    rw [← eq]; intro zero
    have pos := (bounds 0).2; rw [zero,Complex.zero_re] at pos; norm_num at pos
  simpa only [scannedExchange,scannedField,eq] using
    threeField_recovery P V.R (fun a => (V.h a:ℂ)) (fun d a b => (V.J d a b:ℂ)) B w E station det 0 mag

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
def sufficientField := 4096*(1+2*(Fintype.card (Shape R) : ℝ))

theorem cube_bound (bounded : ∀ s, ‖strength R h J s‖ ≤ 1) : 4096*incidentBound R h J ≤ sufficientField R := by
  have le := Finset.sum_le_sum (s := Finset.univ)
    (fun (s : Shape R) _ => mul_le_mul_of_nonneg_left (bounded s) (by norm_num : (0:ℝ)≤2))
  simp only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at le
  unfold sufficientField incidentBound; linarith

theorem fullAccessSF_periodic (bounded : ∀ s, ‖strength R h J s‖ ≤ 1) (B : ℝ)
    (large : sufficientField R ≤ B) (n : ℕ) :
    (∀ d ∈ R.dirs, scannedExchange (periodicVolume R h J n) B (periodicSite R n d) =
      fun a b => (J d a b : ℂ)) ∧
    scannedField (periodicVolume R h J n) B = fun a => (h a : ℂ) := by
  have pos : 0 < sufficientField R := by unfold sufficientField; positivity
  obtain ⟨ex,field⟩ := fullAccessSF_finite (periodicVolume R h J n) (boxInteraction R h J n)
    (boxInteraction_matrix ..) (pos.trans_le large) (incidentBound_pos R h J).le (boxInteraction_incident R h J n)
    ((cube_bound R h J bounded).trans large)
  refine ⟨fun d hd => ?_,field⟩
  simpa only [periodicSite,image_coupling R h J n hd] using ex (periodicSite R n d) (Finset.mem_image_of_mem _ hd)

end DSFTomography.SF
