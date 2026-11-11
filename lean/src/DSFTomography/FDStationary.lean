import DSFTomography.FDComplexAccuracy

/-! Physical stationary mixtures, including Gibbs and ground states.
The compactness argument constructs thermodynamic moment data without a
uniqueness assumption on the equilibrium state. -/
noncomputable section
namespace DSFTomography.FD
open DSFTomography HT SF Matrix Filter
open scoped Topology Matrix.Norms.Frobenius
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def mixtureData (V : Volume S) (p : Config S → ℝ) : Data S :=
  measured (qubitSpins (energyBasis V.R V.h V.J)) (fun m => (p m:ℂ))
    (fun m => (energies V.R V.h V.J m:ℂ))

theorem mixture_static (V : Volume S) (p : Config S → ℝ) (d : S) (a b : Axis) :
    (mixtureData V p).static d a b = avg (fun r => ∑ m, (p m:ℂ)*(eigenState V m).ev (spinAt r a*spinAt (r+d) b)) := by
  simp only [mixtureData,measured,zeroMoment,qubitSpins,string,inBasis_mul,mean]
  rfl

theorem mixture_mag (V : Volume S) (p : Config S → ℝ) (a : Axis) :
    (mixtureData V p).mag a = avg (fun r => ∑ m, (p m:ℂ)*(eigenState V m).ev (spinAt r a)) := by
  let P := qubitSpins (energyBasis V.R V.h V.J)
  change (avg _-avg _)/(2*Complex.I) = _
  rw [show ∀ f g : S → ℂ, (avg f-avg g)/(2*Complex.I) = avg (fun r => (f r-g r)/(2*Complex.I)) by
    intros; simp only [avg,← Finset.sum_div,Finset.sum_sub_distrib]; ring]
  apply congrArg avg; funext r
  simp only [add_zero]
  change magnet P (fun m => (p m:ℂ)) r a = _
  rw [magnet_eq]
  rfl

theorem mixture_bilinear (V : Volume S) (p : Config S → ℝ)
    (positive : ∀ m, 0 ≤ p m) (normed : ∑ m, p m = 1) (d : S) :
    Accuracy.BilinearBound ((mixtureData V p).static d |>.map Complex.re) := by
  have eq : ((mixtureData V p).static d).map Complex.re =
      ∑ r : S, (1/(Fintype.card S:ℝ)) • (∑ m, p m • Accuracy.correlation (eigenState V m) r (r+d)) := by
    ext a b
    simp only [Matrix.map_apply,mixture_static,avg,← Complex.ofReal_natCast,Complex.div_ofReal_re,
      Complex.re_sum,Complex.re_ofReal_mul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Accuracy.correlation]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro r _; ring
  rw [eq]
  apply Accuracy.bilinear_mixture _ (fun _ : S => 1/(Fintype.card S:ℝ)) (fun _ => by positivity)
  · simp [Fintype.card_ne_zero]
  · intro r
    exact Accuracy.bilinear_mixture _ p positive normed
      (fun m => Accuracy.correlation_bound (eigenState V m) r (r+d))

theorem eigen_word_real (V : Volume S) (m : Config S) (w : S → Letter) :
    ((eigenState V m).ev (word w)).im = 0 := by
  have herm : (inBasis (energyBasis V.R V.h V.J) (word w)).IsHermitian := by
    let U := (qubitH_hermitian V.R V.h V.J).eigenvectorUnitary
    change ((U:Op (Config S)).conjTranspose*word w*(U:Op (Config S))).IsHermitian
    simp [Matrix.IsHermitian,Matrix.mul_assoc,word_hermitian]
  have diag := congrArg (fun A : Op (Config S) => (A m m).im) herm
  simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_im] at diag
  change (inBasis (energyBasis V.R V.h V.J) (word w) m m).im = 0
  linarith

theorem mixture_static_real (V : Volume S) (p : Config S → ℝ) {d : S} (nonzero : d ≠ 0) :
    ComplexAccuracy.lift (((mixtureData V p).static d).map Complex.re) = (mixtureData V p).static d := by
  ext a b
  apply Complex.ext
  · rfl
  · change 0 = ((mixtureData V p).static d a b).im
    rw [mixture_static]
    have pair (r : S) : spinAt r a*spinAt (r+d) b = word (twoLabel r (r+d) a b) := by
      have ne : r ≠ r+d := by intro eq; apply nonzero; exact add_left_cancel (show r+d = r+0 by simpa using eq.symm)
      simpa [spinAt,string,inBasis] using string_pair (1:(Op (Config S))ˣ) ne a b
    simp only [pair,avg,← Complex.ofReal_natCast,Complex.div_ofReal_im,Complex.im_sum,
      Complex.im_ofReal_mul,eigen_word_real,mul_zero,Finset.sum_const_zero,zero_div]

theorem mixture_force (V : Volume S) (p : Config S → ℝ) {d : S} (hd : d ∈ V.R.dirs) :
    (mixtureData V p).force d = bondMap ((mixtureData V p).static d) ((V.J d).map Complex.ofReal) :=
  measured_bond _ _ _ _ _ _ (diagonalized V.R V.h V.J) hd

/-- The paper's bound for physical spectral populations, with arbitrary complex
measurement errors. It applies to Gibbs mixtures and selected ground states. -/
theorem fd_accuracy_stationary (V : Volume S) (p : Config S → ℝ)
    (positive : ∀ m, 0 ≤ p m) (normed : ∑ m, p m = 1) {d : S} (hd : d ∈ V.R.dirs)
    (small : ∀ a b, |V.J d a b| ≤ 1) (Chat Fhat : Tensor) (ε γ : ℝ)
    (noise : max ‖Chat-(mixtureData V p).static d‖ ‖Fhat-(mixtureData V p).force d‖ ≤ ε)
    (pos : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(V.J d a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
  let C := ((mixtureData V p).static d).map Complex.re
  let F := Accuracy.bond C (V.J d)
  have cr : ComplexAccuracy.lift C = (mixtureData V p).static d := mixture_static_real V p (V.R.nonzero d hd)
  have fr : ComplexAccuracy.lift F = (mixtureData V p).force d := by
    rw [mixture_force V p hd,← cr]
    exact (Accuracy.bond_complex C (V.J d)).symm
  have bound := mixture_bilinear V p positive normed d
  apply ComplexAccuracy.accuracy C F (V.J d) Chat Fhat ε γ rfl small
    (Accuracy.bilinear_contracts C bound) (Accuracy.bilinear_contracts _ (Accuracy.bilinear_transpose C bound))
    _ pos det
  simpa only [cr,fr] using noise

theorem mixture_unit_bound (V : Volume S) (p : Config S → ℝ)
    (positive : ∀ m, 0 ≤ p m) (normed : ∑ m, p m = 1)
    (O : Op (Config S)) (unit : O.conjTranspose*O = 1) :
    ‖∑ m, (p m:ℂ)*(eigenState V m).ev O‖ ≤ 1 := by
  calc
    _ ≤ ∑ m, ‖(p m:ℂ)*(eigenState V m).ev O‖ := norm_sum_le _ _
    _ ≤ ∑ m, p m := Finset.sum_le_sum fun m _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive m)]
      exact mul_le_of_le_one_right (positive m) ((eigenState V m).unit_bound unit)
    _ = 1 := normed

theorem mixture_bounds (V : Volume S) (p : Config S → ℝ)
    (positive : ∀ m, 0 ≤ p m) (normed : ∑ m, p m = 1) :
    (∀ d a b, ‖(mixtureData V p).static d a b‖ ≤ 1) ∧
      (∀ a, ‖(mixtureData V p).mag a‖ ≤ 1) := by
  constructor
  · intro d a b
    rw [mixture_static]
    have each (r : S) : ‖∑ m, (p m:ℂ)*(eigenState V m).ev (spinAt r a*spinAt (r+d) b)-0‖ ≤ 1 := by
      rw [sub_zero]
      apply mixture_unit_bound V p positive normed
      have ua := word_unit (oneLabel r a)
      have ub := word_unit (oneLabel (r+d) b)
      change (spinAt r a).conjTranspose*spinAt r a=1 at ua
      change (spinAt (r+d) b).conjTranspose*spinAt (r+d) b=1 at ub
      rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (spinAt r a).conjTranspose,
        ua,Matrix.one_mul,ub]
    simpa using avg_close each
  · intro a
    rw [mixture_mag]
    have each (r : S) : ‖∑ m, (p m:ℂ)*(eigenState V m).ev (spinAt r a)-0‖ ≤ 1 := by
      rw [sub_zero]
      exact mixture_unit_bound V p positive normed _ (word_unit _)
    simpa using avg_close each

theorem thermal_mixture (V : Volume S) (β : ℝ) :
    Accuracy.thermalData V β = mixtureData V (Accuracy.population V β) := by
  simp only [Accuracy.thermalData,harmonics_momentumMoments,thermalMoments,mixtureData]
  rfl

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def probabilityPacket (p : ∀ n, Config (Box R n) → ℝ) (n : ℕ) : Packet R.dirs :=
  stationaryPacket R h J (fun n m => (p n m:ℂ)) n

/-- Every sequence of normalized stationary mixtures has a growing subsequence
on which all FD input quantities converge. No temperature or gap assumption. -/
theorem fd_bulk_data_exist (p : ∀ n, Config (Box R n) → ℝ)
    (positive : ∀ n m, 0 ≤ p n m) (normed : ∀ n, ∑ m, p n m = 1) :
    ∃ A : Packet R.dirs, ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Tendsto (fun n => probabilityPacket R h J p (seq n)) atTop (𝓝 A) := by
  let f := fun n => Packet.base (probabilityPacket R h J p n)
  let ball := Metric.closedBall (0:ℂ) 1
  let K : Set (Base R.dirs) := (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => ball) ×ˢ
    (Set.univ.pi fun _ => ball)
  have compact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).prod
      (isCompact_univ_pi fun _ => isCompact_closedBall 0 1)
  have mem (n : ℕ) : f n ∈ K := by
    have bounds := mixture_bounds (periodicVolume R h J n) (p n) (positive n) (normed n)
    constructor
    · intro d _ a _ b _
      simpa only [ball,Metric.mem_closedBall,dist_zero_right] using bounds.1 (periodicSite R n d) a b
    · intro a _
      simpa only [ball,Metric.mem_closedBall,dist_zero_right] using bounds.2 a
  obtain ⟨base,_,seq,inc,lim⟩ := compact.tendsto_subseq mem
  refine ⟨Packet.forward base (fun a => (h a:ℂ)) (fun d a b => (J d a b:ℂ)),seq,inc,?_⟩
  apply ((Packet.continuous_forward _ _).continuousAt.tendsto.comp lim).congr'
  exact Eventually.of_forall fun n => (stationary_equations R h J (fun n m => (p n m:ℂ)) (seq n)).symm

/-- The manuscript accuracy bound for thermodynamic stationary data, including
zero-temperature data. Complex perturbations of the measured matrices are allowed. -/
theorem fd_accuracy_stationary_thermodynamic (p : ∀ n, Config (Box R n) → ℝ)
    (positive : ∀ n m, 0 ≤ p n m) (normed : ∀ n, ∑ m, p n m = 1)
    (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => probabilityPacket R h J p (seq n)) atTop (𝓝 A))
    (d : R.dirs) (small : ∀ a b, |J d a b| ≤ 1) (Chat Fhat : Tensor) (ε γ : ℝ)
    (noise : max ‖Chat-A.1 d‖ ‖Fhat-A.2.1 d‖ ≤ ε) (pos : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(J d a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
  let error (P : Packet R.dirs) := max ‖Chat-P.1 d‖ ‖Fhat-P.2.1 d‖
  let bound (t : ℝ) := 25*(1+t)^2/(4*γ)*t
  have continuous_bound : Continuous (fun P => bound (error P)) := by
    dsimp [bound, error]; fun_prop
  have error_nonneg : 0 ≤ error A := le_max_of_le_left (norm_nonneg _)
  have bound_mono : bound (error A) ≤ bound ε := by
    dsimp [bound]
    gcongr
  intro a b
  apply le_trans (b := bound (error A)) _ bound_mono
  apply ge_of_tendsto (continuous_bound.continuousAt.tendsto.comp data)
  apply Eventually.of_forall
  intro n
  have image := image_coupling R h J (seq n) d.property
  have finite := fd_accuracy_stationary (periodicVolume R h J (seq n)) (p (seq n))
    (positive (seq n)) (normed (seq n)) (Finset.mem_image_of_mem _ d.property)
    (by simpa only [image] using small) Chat Fhat
    (error (probabilityPacket R h J p (seq n))) γ le_rfl pos det a b
  simpa only [image] using finite

/-- Gibbs packets are a specialization of the normalized stationary construction. -/
theorem probability_gibbs_eq (β : ℝ) (n : ℕ) :
    probabilityPacket R h J (fun n => Accuracy.population (periodicVolume R h J n) β) n =
      periodicPacket R h J β n := by
  simp only [probabilityPacket,stationaryPacket,periodicPacket,harmonics_momentumMoments,thermalMoments]
  rfl

theorem fd_gibbs_bulk_data_exist (β : ℝ) :
    ∃ A : Packet R.dirs, ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A) := by
  simpa only [probability_gibbs_eq] using fd_bulk_data_exist R h J
    (fun n => Accuracy.population (periodicVolume R h J n) β)
    (fun n => Accuracy.population_pos _ _) (fun n => Accuracy.population_sum _ _)

/-- Exact manuscript corollary for complex noisy thermodynamic Gibbs moments. -/
theorem fd_accuracy_bulk (β : ℝ) (A : Packet R.dirs) (seq : ℕ → ℕ)
    (data : Tendsto (fun n => periodicPacket R h J β (seq n)) atTop (𝓝 A))
    (d : R.dirs) (small : ∀ a b, |J d a b| ≤ 1) (Chat Fhat : Tensor) (ε γ : ℝ)
    (noise : max ‖Chat-A.1 d‖ ‖Fhat-A.2.1 d‖ ≤ ε) (pos : 0 < γ) (det : γ ≤ ‖Chat.det‖) :
    ∀ a b, ‖recoverBond Chat Fhat a b-(J d a b:ℂ)‖ ≤ 25*(1+ε)^2/(4*γ)*ε := by
  apply fd_accuracy_stationary_thermodynamic R h J
    (fun n => Accuracy.population (periodicVolume R h J n) β)
    (fun n => Accuracy.population_pos _ _) (fun n => Accuracy.population_sum _ _)
    A seq _ d small Chat Fhat ε γ noise pos det
  simpa only [probability_gibbs_eq] using data

end DSFTomography.FD
