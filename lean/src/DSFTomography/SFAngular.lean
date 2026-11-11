import DSFTomography.SFPaperDSF
import DSFTomography.DSFLehmann
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Angular tomography at fixed finite volume. The interaction is an arbitrary
Hermitian matrix, so the result includes higher-body Pauli interactions. The
spin frame has its third axis along the applied field. -/
noncomputable section
namespace DSFTomography.SF.Angular
open DSFTomography HT Perturbation Filter Matrix
open scoped Topology
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The polarized energy is shifted to zero; t = 1/B. -/
def unitH (V : Op (Config S)) (t : ℝ) : Op (Config S) :=
  Matrix.diagonal flipGap + (t:ℂ) • V

omit [DecidableEq S] in
theorem unitH_self {V : Op (Config S)} (hV : V.IsHermitian) (t : ℝ) :
    (unitH V t).IsHermitian := by
  apply Matrix.IsHermitian.add
  · unfold Matrix.IsHermitian
    ext x y
    by_cases h : x=y
    · subst y; simp [Matrix.conjTranspose_apply,flipGap]
    · simp [Matrix.conjTranspose_apply,h,Ne.symm h]
  · unfold Matrix.IsHermitian at *
    simpa using congrArg (fun M => (t:ℂ) • M) hV

/-- A normalized smooth ground eigenline; existence is proved below. -/
structure GroundRay (V : Op (Config S)) where
  ψ : ℝ → Config S → ℂ
  E : ℝ → ℂ
  smoothψ : ContDiffAt ℝ 2 ψ 0
  smoothE : ContDiffAt ℝ 2 E 0
  vac : ψ 0 = ket (vacuum S)
  E0 : E 0 = 0
  normed : ∀ t, ∑ k, Complex.normSq (ψ t k) = 1
  physical : ∀ᶠ t in 𝓝 0,
    (unitH V t *ᵥ ψ t = E t • ψ t) ∧
    (∀ (μ : ℂ) (ξ : Config S → ℂ), ξ ≠ 0 →
      unitH V t *ᵥ ξ = μ • ξ → μ.re ≤ (E t).re →
      μ = E t ∧ ∃ c : ℂ, ξ = c • ψ t)

/-- Finite-dimensional perturbation theory constructs the ground state.
No restriction on the body order of V is used. -/
theorem groundRay_exists (V : Op (Config S)) : Nonempty (GroundRay V) := by
  let o := vacuum S
  have gap0 : flipGap o = 0 := by simp [o,vacuum,flipGap_bits]
  have nz (k : Config S) (hk : k≠o) : flipGap k ≠ 0 := by
    intro bad; have pos := gap_nonvac k hk; rw [bad,Complex.zero_re] at pos; linarith
  obtain ⟨v,hv,v0,eig⟩ := finite_branch o flipGap gap0 nz
  let L : ℝ → Entries (Config S) := fun t => (t:ℂ) • V
  have sL : ContDiff ℝ 2 L := by unfold L; fun_prop
  have L0 : L 0 = 0 := by simp [L]
  let b := fun t : ℝ => v (L t)
  have b0 : b 0 = 0 := by simp [b,L0,v0]
  have sb : ContDiffAt ℝ 2 b 0 :=
    (show ContDiffAt ℝ 2 v (L 0) by simpa [L0] using hv.restrict_scalars ℝ).comp _ sL.contDiffAt
  let w := fun t k => vector o (b t) k
  have wo (t) : w t o = 1 := by simp [w,vector,ket,mask]
  have w0 (k) : w 0 k = ket o k := by simp [w,vector,b0,mask]
  have bk (k) : ContDiffAt ℝ 2 (fun t => b t k) 0 :=
    (ContinuousLinearMap.proj k : (Config S → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt.comp 0 sb
  have sw (k) : ContDiffAt ℝ 2 (fun t => w t k) 0 := by
    by_cases h : k=o <;> simp [w,vector,mask,h] <;> fun_prop
  let n2 := fun t => ∑ k, Complex.normSq (w t k)
  let n := fun t => (Real.sqrt (n2 t) : ℂ)
  have n2pos (t) : 0 < n2 t := by
    have le := Finset.single_le_sum (s := Finset.univ) (f := fun k => Complex.normSq (w t k))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ o)
    change Complex.normSq (w t o) ≤ n2 t at le
    rw [wo,Complex.normSq_one] at le
    exact zero_lt_one.trans_le le
  have nn (t) : n t ≠ 0 := by simpa [n] using (Real.sqrt_pos.mpr (n2pos t)).ne'
  have n0 : n 0 = 1 := by simp [n,n2,w0,ket,apply_ite]
  have sn2 : ContDiffAt ℝ 2 n2 0 := by
    unfold n2
    apply ContDiffAt.sum; intro k _
    simp only [Complex.normSq_apply]
    have a := Complex.reCLM.contDiff.contDiffAt.comp 0 (sw k)
    have b := Complex.imCLM.contDiff.contDiffAt.comp 0 (sw k)
    exact (a.mul a).add (b.mul b)
  have sn : ContDiffAt ℝ 2 n 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (sn2.sqrt (n2pos 0).ne')
  let ψ := fun t k => w t k / n t
  refine ⟨{ ψ := ψ
            E := fun t => b t o
            smoothψ := contDiffAt_pi.mpr (fun k => by
              simp only [ψ,div_eq_mul_inv]; exact (sw k).mul ((contDiffAt_inv ℝ (nn 0)).comp 0 sn))
            smoothE := bk o
            vac := by funext k; simp [ψ,n0,w0,o]
            E0 := by simp [b0]
            normed := ?_
            physical := ?_ }⟩
  · intro t
    simp only [ψ,map_div₀,← Finset.sum_div]
    change n2 t / Complex.normSq (n t) = 1
    rw [show Complex.normSq (n t) = n2 t by
      simp only [n,Complex.normSq_ofReal,← sq,Real.sq_sqrt (n2pos t).le]]
    exact div_self (n2pos t).ne'
  · have nearL : Tendsto L (𝓝 (0:ℝ)) (𝓝 0) := by
      simpa [L0] using (sL.continuous.continuousAt (x := 0)).tendsto
    have small := ((continuous_const.mul sL.continuous.norm :
      Continuous (fun t => (2*(Fintype.card (Config S):ℝ))*‖L t‖)).continuousAt (x := 0)).eventually_lt_const
      (show (2*(Fintype.card (Config S):ℝ))*‖L 0‖ < 1 by simp [L0])
    have close := sb.continuousAt.norm.eventually_lt_const (by simp [b0] : ‖b 0‖ < 1)
    filter_upwards [nearL.eventually eig,small,close] with t eigen sm cl
    change ∀ k, flipGap k * w t k + ∑ j, L t k j*w t j = b t o*w t k at eigen
    have row (ξ : Config S → ℂ) (k) : (unitH V t *ᵥ ξ) k =
        flipGap k*ξ k + ∑ j, L t k j*ξ j := by
      simp only [unitH,Matrix.add_mulVec,Pi.add_apply,Matrix.mulVec_diagonal]; rfl
    refine ⟨?_,?_⟩
    · funext k; rw [row]
      simpa only [ψ,Pi.smul_apply,smul_eq_mul,← mul_div_assoc,← Finset.sum_div,← add_div]
        using congrArg (· / n t) (eigen k)
    · intro μ ξ hξ test lower
      have μlow : μ.re ≤ 1 := lower.trans
        (((Complex.re_le_norm _).trans (norm_le_pi_norm (b t) o)).trans cl.le)
      have align := low_eigenline o flipGap (L t) (w t) ξ (wo t) gap_nonvac eigen
        (fun k => (row ξ k).symm.trans (congrFun test k)) sm
        (fun k hk => by simpa [w,vector,ket,mask,hk] using (norm_le_pi_norm (b t) k).trans cl.le) μlow
      have overlap : ξ o ≠ 0 := by
        intro no; apply hξ; funext k; simp [align k,no]
      have erow := (row ξ o).symm.trans (congrFun test o)
      simp only [gap0,zero_mul,zero_add] at erow
      have base := eigen o; simp only [gap0,wo,zero_add,mul_one] at base
      have alt (j) : L t o j*ξ j = ξ o*(L t o j*w t j) := by rw [align j]; ring
      simp_rw [alt,← Finset.mul_sum,base] at erow
      refine ⟨mul_right_cancel₀ overlap ((mul_comm _ _).trans erow).symm,ξ o*n t,?_⟩
      funext k
      change ξ k = (ξ o*n t)*(w t k/n t)
      rw [align k]; field_simp [nn t]

/-- Laboratory Pauli a in a frame whose third axis is the field direction. -/
def probe (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) : Op (Config S) :=
  ∑ b, (R a b:ℂ) • spinAt r b

theorem probe_self (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) :
    (probe R r a).IsHermitian := by
  unfold Matrix.IsHermitian probe
  simp [Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,spinAt,word_hermitian]

private theorem spin_vacuum (r : S) (a : Axis) (x : Config S) :
    spinAt r a x (vacuum S) =
      pauli (some a) 0 0 * ket (vacuum S) x + pauli (some a) 1 0 * ket (flip r) x := by
  rw [spinAt,word_one]
  by_cases hv : x=vacuum S
  · subst x
    have ne : vacuum S ≠ flip r := by
      intro h; have := congrFun h r; simp [vacuum,flip,bitConfig] at this
    simp [ket,ne,vacuum,bitConfig]
  · by_cases hf : x=flip r
    · subst x
      simp [ket,hv,flip,vacuum,bitConfig]
    · simp only [ket,if_neg hv,if_neg hf,mul_zero,add_zero]
      split_ifs with outside
      · exfalso
        have bit : x r=0 ∨ x r=1 := by have := (x r).isLt; omega
        rcases bit with bit|bit
        · apply hv; funext s; by_cases h : s=r
          · subst s; simpa [vacuum,bitConfig] using bit
          · exact outside s h
        · apply hf; funext s; by_cases h : s=r
          · subst s; simpa [flip,bitConfig] using bit
          · simpa [flip,vacuum,bitConfig,h] using outside s h
      · rfl

/-- Pauli transition amplitude from the polarized spin to its opposite. -/
def amplitude (R : Matrix Axis Axis ℝ) (a : Axis) : ℂ := R a 0 + Complex.I*R a 1

private theorem probe_vacuum (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) (x : Config S) :
    probe R r a x (vacuum S) =
      (R a 2:ℂ)*ket (vacuum S) x + amplitude R a*ket (flip r) x := by
  simp only [probe,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,spin_vacuum,
    Fin.sum_univ_three,pauliValues,amplitude]
  simp; ring

/-- The one-flip weights add to two, for every orthonormal spin frame. -/
theorem spin_trace (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1) :
    (1/2:ℂ) * ∑ a, star (amplitude R a)*amplitude R a = 1 := by
  have col (b : Axis) : ∑ a, R a b*R a b = 1 := by
    simpa [Matrix.mul_apply,Matrix.transpose_apply] using congrFun (congrFun orth b) b
  have one (a) : star (amplitude R a)*amplitude R a = ((R a 0*R a 0+R a 1*R a 1:ℝ):ℂ) := by
    apply Complex.ext <;> simp [amplitude,Complex.mul_re,Complex.mul_im]
    ring
  simp_rw [one]
  rw [← Complex.ofReal_sum,Finset.sum_add_distrib,col,col]
  norm_num

/-- n_a = R_{a,z}. The applied field is exactly the chart's Z field. -/
theorem field_direction (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1) (r : S) :
    (∑ a, (R a 2:ℂ) • probe R r a) = spinAt r 2 := by
  have col (b : Axis) : ∑ a, R a 2*R a b = if b=2 then 1 else 0 := by
    have h := congrFun (congrFun orth 2) b
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,eq_comm] using h
  simp only [probe,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul,← Complex.ofReal_mul,← Complex.ofReal_sum,col]
  simp

/-- B times the unit-field matrix differs from H_B only by the vacuum
Zeeman energy, which cancels in every excitation frequency. -/
theorem driven_frame (V : Op (Config S)) (R : Matrix Axis Axis ℝ)
    (orth : R.transpose*R=1) (B : ℝ) (nz : B≠0) :
    (B:ℂ) • unitH V B⁻¹ = ((B:ℂ)*Fintype.card S) • 1 +
      (-(B:ℂ) • ∑ r : S, ∑ a, (R a 2:ℂ) • probe R r a) + V := by
  simp_rw [field_direction R orth]
  rw [unitH,smul_add,field_gap_matrix,smul_add,smul_smul,smul_smul]
  simp [zeeman,nz]

namespace GroundRay
variable {V : Op (Config S)} (g : GroundRay V)

def centeredProbe (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) (t : ℝ) : Op (Config S) :=
  probe R r a - sandwich (g.ψ t) (probe R r a) (g.ψ t) • 1

def applied (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) (t : ℝ) :=
  g.centeredProbe R r a t *ᵥ g.ψ t

theorem applied_zero (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) :
    g.applied R r a 0 = amplitude R a • ket (flip r) := by
  have ne : vacuum S ≠ flip r := by
    intro h; have := congrFun h r; simp [vacuum,flip,bitConfig] at this
  have mean0 : sandwich (g.ψ 0) (probe R r a) (g.ψ 0) = R a 2 := by
    rw [g.vac]
    simp only [sandwich,ket,apply_ite,star_one,star_zero,ite_mul,one_mul,zero_mul,
      mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [probe_vacuum]
    simp [ket,ne]
  funext x
  simp only [applied,centeredProbe]
  rw [mean0,g.vac,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,ket,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [probe_vacuum]
  simp only [ket,mul_ite,mul_one,mul_zero]
  abel

theorem applied_smooth (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) (x : Config S) :
    ContDiffAt ℝ 2 (fun t => g.applied R r a t x) 0 := by
  have each (y) := (contDiffAt_pi.mp g.smoothψ) y
  have starred (y) : ContDiffAt ℝ 2 (fun t => star (g.ψ t y)) 0 :=
    Complex.conjCLE.contDiff.contDiffAt.comp 0 (each y)
  have mean : ContDiffAt ℝ 2 (fun t => sandwich (g.ψ t) (probe R r a) (g.ψ t)) 0 := by
    unfold sandwich; fun_prop
  simp only [applied,centeredProbe,Matrix.mulVec,dotProduct,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul]
  fun_prop

/-- The connected centered moment, in unit-field energy units. -/
def centeredPair (R : Matrix Axis Axis ℝ) (r s : S) (a : Axis) (t : ℝ) : ℂ :=
  sandwich (g.applied R r a t)
    (unitH V t - (g.E t+2) • 1) (g.applied R s a t)

/-- Both one-flip kets are annihilated by the unperturbed centered operator.
Consequently their first-order corrections do not contribute. -/
theorem centered_slope (R : Matrix Axis Axis ℝ) {r s : S} (ne : r≠s) (a : Axis) :
    HasDerivAt (g.centeredPair R r s a)
      (star (amplitude R a)*amplitude R a * V (flip r) (flip s)) 0 := by
  let T := fun t : ℝ => unitH V t - (g.E t+2) • 1
  let dT := V - deriv g.E 0 • (1 : Op (Config S))
  have dE := (g.smoothE.differentiableAt (by norm_num)).hasDerivAt
  have dt := (hasDerivAt_id (0:ℝ)).ofReal_comp
  have hT (x y) : HasDerivAt (fun t => T t x y) (dT x y) 0 := by
    by_cases h : x=y
    · subst y
      simpa [T,dT,unitH] using
        ((hasDerivAt_const (0:ℝ) (flipGap x)).add (dt.mul_const (V x x))).sub (dE.add_const 2)
    · simpa [T,dT,unitH,h,Matrix.diagonal_apply_ne _ h] using dt.mul_const (V x y)
  have hv (t : S) (x) := ((g.applied_smooth R t a x).differentiableAt (by norm_num)).hasDerivAt
  have response := sandwich_deriv (hv r) (hv s) hT
  have zeroRow (x) : T 0 (flip r) x = 0 := by
    by_cases h : flip r=x
    · subst x; simp [T,unitH,g.E0,flip,flipGap_bits]
    · simp [T,unitH,g.E0,h]
  have zeroCol (x) : T 0 x (flip s) = 0 := by
    by_cases h : x=flip s
    · subst x; simp [T,unitH,g.E0,flip,flipGap_bits]
    · simp [T,unitH,g.E0,h]
  have distinct : flip r ≠ flip s := by simpa [flip,bitConfig_injective.eq_iff] using ne
  have bra (c : ℂ) (l : Config S) (A : Op (Config S)) (w : Config S → ℂ) :
      sandwich (c • ket l) A w = star c * ∑ y, A l y*w y := by
    simp [sandwich,ket,Pi.smul_apply,smul_eq_mul,apply_ite,ite_mul,
      Finset.sum_ite_irrel,Finset.mul_sum,mul_assoc]
  have endKet (v : Config S → ℂ) (A : Op (Config S)) (c : ℂ) (l : Config S) :
      sandwich v A (c • ket l) = (∑ y, star (v y)*A y l)*c := by
    simp [sandwich,ket,Pi.smul_apply,smul_eq_mul,mul_ite,Finset.sum_mul,mul_assoc]
  rw [g.applied_zero,g.applied_zero,endKet,endKet,bra] at response
  simpa [centeredPair,T,zeroCol,zeroRow,ket,Pi.smul_apply,smul_eq_mul,star_mul',
    apply_ite,ite_mul,dT,distinct,mul_assoc,mul_comm,mul_left_comm] using response

def angularMoment (R : Matrix Axis Axis ℝ) (r s : S) (t : ℝ) : ℂ :=
  (1/2:ℂ)*∑ a, g.centeredPair R r s a t

theorem angular_slope (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1)
    {r s : S} (ne : r≠s) :
    HasDerivAt (g.angularMoment R r s) (V (flip r) (flip s)) 0 := by
  have all := (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => g.centered_slope R ne a)).const_mul (1/2:ℂ)
  simpa only [angularMoment,← Finset.sum_mul,← mul_assoc,spin_trace R orth,one_mul] using all

theorem angular_zero (R : Matrix Axis Axis ℝ) (r s : S) : g.angularMoment R r s 0 = 0 := by
  have one (a) : g.centeredPair R r s a 0 = 0 := by
    have zeroCol (x) : (unitH V 0 - (g.E 0+2) • 1) x (flip s) = 0 := by
      by_cases h : x=flip s
      · subst x; simp [unitH,g.E0,flip,flipGap_bits]
      · simp [unitH,g.E0,h]
    simp only [centeredPair,g.applied_zero,sandwich,ket,Pi.smul_apply,smul_eq_mul,
      mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,zeroCol,
      mul_zero,zero_mul,Finset.sum_const_zero]
  simp [angularMoment,one]

theorem angular_smooth (R : Matrix Axis Axis ℝ) (r s : S) :
    ContDiffAt ℝ 2 (g.angularMoment R r s) 0 := by
  have applied (r : S) (a x) := g.applied_smooth R r a x
  have starred (a x) : ContDiffAt ℝ 2 (fun t => star (g.applied R r a t x)) 0 :=
    Complex.conjCLE.contDiff.contDiffAt.comp 0 (applied r a x)
  have energy := g.smoothE
  have time : ContDiffAt ℝ 2 (fun t : ℝ => (t:ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt
  change ContDiffAt ℝ 2 (fun t => (1/2:ℂ)*∑ a,
    ∑ x, ∑ y, star (g.applied R r a t x) *
      ((Matrix.diagonal flipGap) x y + (t:ℂ)*V x y - (g.E t+2)*(1:Op (Config S)) x y) *
      g.applied R s a t y) 0
  fun_prop

/-- The large-field limit of the connected centered matrix element. -/
theorem angular_limit (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1)
    {r s : S} (ne : r≠s) :
    Tendsto (fun B : ℝ => (B:ℂ)*g.angularMoment R r s B⁻¹) atTop
      (𝓝 (V (flip r) (flip s))) := by
  have invNear : Tendsto (fun B : ℝ => B⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero,
      (eventually_gt_atTop 0).mono (fun B hB => by simp [hB.ne'])⟩
  simpa [g.angular_zero,Complex.real_smul,Function.comp_def] using
    (g.angular_slope R orth ne).tendsto_slope_zero.comp invNear

end GroundRay

/-- C² regularity turns the vanishing unperturbed response into an O(1/B)
error. The constants may depend on the finite system and interaction. -/
private theorem rescaled_error {f : ℝ → ℂ} {L : ℂ} (smooth : ContDiffAt ℝ 2 f 0)
    (zero : f 0=0) (jet : HasDerivAt f L 0) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b, ‖(B:ℂ)*f B⁻¹-L‖ ≤ C/B := by
  have dsD : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := smooth.fderiv_right (by norm_num)
  have ds : ContDiffAt ℝ 1 (deriv f) 0 := dsD.clm_apply contDiffAt_const
  obtain ⟨K,U,hU,lip⟩ := ds.exists_lipschitzOnWith
  have regular := smooth.eventually (by simp)
  obtain ⟨r,hr,inside⟩ := Metric.mem_nhds_iff.mp (inter_mem hU regular)
  refine ⟨K,K.coe_nonneg,2/r,by positivity,?_⟩
  intro B large
  have hB : 0 < B := (by positivity : 0 < 2/r).trans_le large
  have small : B⁻¹ < r := by
    rw [inv_eq_one_div,div_lt_iff₀ hB]
    have := (div_le_iff₀ hr).mp large
    linarith [mul_comm B r]
  let t := B⁻¹
  have ht : 0 ≤ t := inv_nonneg.mpr hB.le
  have atx (x : ℝ) (hx : x ∈ Set.Icc 0 t) : x ∈ U ∧ ContDiffAt ℝ 2 f x := by
    apply inside
    simpa [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx.1]
      using hx.2.trans_lt small
  have at0 := atx 0 ⟨le_rfl,ht⟩
  have derivBound (x : ℝ) (hx : x ∈ Set.Icc 0 t) : ‖deriv f x-L‖ ≤ K*t := by
    have bound := lip.dist_le_mul x (atx x hx).1 0 at0.1
    rw [dist_eq_norm,dist_zero_right,jet.deriv,Real.norm_eq_abs,abs_of_nonneg hx.1] at bound
    exact bound.trans (mul_le_mul_of_nonneg_left hx.2 K.coe_nonneg)
  have df (x : ℝ) (hx : x ∈ Set.Icc 0 t) :
      HasDerivWithinAt (fun y : ℝ => f y-(y:ℂ)*L) (deriv f x-L) (Set.Icc 0 t) x := by
    have dh := ((atx x hx).2.differentiableAt (by norm_num)).hasDerivAt
    simpa using (dh.sub (((hasDerivAt_id x).ofReal_comp).mul_const L)).hasDerivWithinAt
  have est := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le df derivBound
    (convex_Icc 0 t) (show (0:ℝ) ∈ Set.Icc 0 t from ⟨le_rfl,ht⟩)
    (show t ∈ Set.Icc 0 t from ⟨ht,le_rfl⟩)
  have numerator : ‖f t-(t:ℂ)*L‖ ≤ K*t*t := by
    simpa [zero,Real.norm_eq_abs,abs_of_nonneg ht] using est
  have cancel : (B:ℂ)*f t-L = (B:ℂ)*(f t-(t:ℂ)*L) := by
    simp [t,mul_sub,hB.ne']
  rw [cancel,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
  exact (mul_le_mul_of_nonneg_left numerator hB.le).trans_eq (by dsimp [t]; field_simp)

private theorem sandwich_star (v : Config S → ℂ) (A : Op (Config S)) :
    star (sandwich v A v) = sandwich v A.conjTranspose v := by
  simp only [sandwich,star_sum,star_mul',star_star,Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  ring

private theorem sandwich_real (v : Config S → ℂ) {A : Op (Config S)} (hA : A.IsHermitian) :
    ((sandwich v A v).re:ℂ) = sandwich v A v := by
  have h := sandwich_star v A
  rw [hA.eq] at h
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im h
    simp only [Complex.star_def,Complex.conj_im] at hi
    simp only [Complex.ofReal_im]; linarith

/-- Spectral projectors give the actual matrix exponential. -/
private theorem propagator_lines {H : Op (Config S)} (h : H.IsHermitian) (z E : ℂ) :
    (∑ j, Complex.exp (z*((h.eigenvalues j:ℂ)-E)) • spectralLine h j) =
      NormedSpace.exp ℂ (z • (H-E • 1)) := by
  let U := unitary.toUnits h.eigenvectorUnitary
  have diag : (↑U⁻¹ : Op (Config S))*H*(↑U : Op (Config S)) = Matrix.diagonal (fun j => (h.eigenvalues j:ℂ)) :=
    h.star_mul_self_mul_eq_diagonal
  have shifted : (↑U⁻¹ : Op (Config S))*(z • (H-E • 1))*(↑U : Op (Config S)) =
      Matrix.diagonal (fun j => z*((h.eigenvalues j:ℂ)-E)) := by
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_one,Units.inv_mul,diag]
    ext x y
    by_cases hxy : x=y <;> simp [hxy]
  have conjugate : z • (H-E • 1) =
      (↑U : Op (Config S))*Matrix.diagonal (fun j => z*((h.eigenvalues j:ℂ)-E))*(↑U⁻¹ : Op (Config S)) := by
    rw [← shifted]; simp [Matrix.mul_assoc]
  rw [conjugate,Matrix.exp_units_conj,Matrix.exp_diagonal,weighted_lines]
  simp only [Pi.exp_def,← Complex.exp_eq_exp_ℂ]
  rfl

namespace GroundRay
variable {V : Op (Config S)} (g : GroundRay V)

theorem centeredProbe_self (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) (t : ℝ) :
    (g.centeredProbe R r a t).IsHermitian := by
  have real := sandwich_real (g.ψ t) (probe_self R r a)
  rw [centeredProbe,← real]
  apply Matrix.IsHermitian.sub (probe_self R r a)
  unfold Matrix.IsHermitian
  simp

/-- Centering removes the ground-to-ground transition exactly. -/
theorem centered_mean_zero (R : Matrix Axis Axis ℝ) (r : S) (a : Axis) (t : ℝ) :
    sandwich (g.ψ t) (g.centeredProbe R r a t) (g.ψ t) = 0 := by
  have unit : sandwich (g.ψ t) 1 (g.ψ t) = 1 := by
    simp [sandwich,Matrix.one_apply,mul_ite,ite_mul,
      ← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_sum,g.normed]
  have split : sandwich (g.ψ t) (g.centeredProbe R r a t) (g.ψ t) =
      sandwich (g.ψ t) (probe R r a) (g.ψ t) -
      sandwich (g.ψ t) (probe R r a) (g.ψ t)*sandwich (g.ψ t) 1 (g.ψ t) := by
    simp [centeredProbe,sandwich,mul_sub,sub_mul,Finset.sum_sub_distrib,
      Finset.mul_sum,mul_assoc,mul_left_comm]
  rw [split,unit,mul_one,sub_self]

theorem energy_real (hV : V.IsHermitian) : ∀ᶠ t in 𝓝 (0:ℝ), ((g.E t).re:ℂ) = g.E t := by
  filter_upwards [g.physical] with t ht
  have ev : sandwich (g.ψ t) (unitH V t) (g.ψ t) = g.E t := by
    have eq : sandwich (g.ψ t) (unitH V t) (g.ψ t) =
        ∑ k, star (g.ψ t k)*(unitH V t *ᵥ g.ψ t) k := by
      simp [sandwich,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
    rw [eq,ht.1]
    simp only [Pi.smul_apply,smul_eq_mul]
    have term (k) : star (g.ψ t k)*(g.E t*g.ψ t k) =
        g.E t*(Complex.normSq (g.ψ t k):ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; simp only [Complex.star_def]; ring
    simp_rw [term,← Finset.mul_sum,← Complex.ofReal_sum,g.normed,Complex.ofReal_one,mul_one]
  rw [← ev]
  exact sandwich_real _ (unitH_self hV t)

/-- Exact connected DSF lines at physical field B. Scalar ground-energy
shifts cancel in the transition frequencies. -/
def lines (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (r s : S) (a : Axis) (B : ℝ) :
    Spectral.Lines (Config S) where
  frequency j := B*((unitH_self hV B⁻¹).eigenvalues j - (g.E B⁻¹).re)
  weight j := intensity (unitH_self hV B⁻¹) (g.ψ B⁻¹)
    (g.centeredProbe R r a B⁻¹) (g.centeredProbe R s a B⁻¹) j

/-- The stationary ground-state correlation, with its ground energy removed. -/
def timeCorrelation (R : Matrix Axis Axis ℝ) (r s : S) (a : Axis) (B τ : ℝ) : ℂ :=
  sandwich (g.ψ B⁻¹) (g.centeredProbe R r a B⁻¹ *
    NormedSpace.exp ℂ ((-Complex.I*(B:ℂ)*τ) • (unitH V B⁻¹-g.E B⁻¹ • 1)) *
    g.centeredProbe R s a B⁻¹) (g.ψ B⁻¹)

theorem timeCorrelation_eq (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (r s : S)
    (a : Axis) (B τ : ℝ) (real : ((g.E B⁻¹).re:ℂ) = g.E B⁻¹) :
    g.timeCorrelation R r s a B τ = (g.lines hV R r s a B).correlation τ := by
  rw [timeCorrelation,← propagator_lines (unitH_self hV B⁻¹),← spectral_sum]
  simp only [Spectral.Lines.correlation,lines,Complex.ofReal_mul,Complex.ofReal_sub,real]
  apply Finset.sum_congr rfl; intro j _
  rw [mul_comm]
  congr 2
  ring

/-- Positive-sign time Fourier transform, including the raw 2π intensity. -/
theorem dsf_definition (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (r s : S)
    (a : Axis) (B : ℝ) (real : ((g.E B⁻¹).re:ℂ) = g.E B⁻¹) (f : SchwartzMap ℝ ℂ) :
    (∫ τ : ℝ, g.timeCorrelation R r s a B τ * Spectral.angularTest f τ) =
      (g.lines hV R r s a B).distribution f := by
  simp only [g.timeCorrelation_eq hV R r s a B _ real]
  exact Spectral.time_fourier_eq_lines _ _

/-- The calibrated angular readout, using raw 2π-normalized DSF moments. -/
def fromDSF (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (r s : S) (B : ℝ) : ℂ :=
  (1/2:ℂ)*∑ a, ((g.lines hV R r s a B).moment 1 -
    2*(B:ℂ)*(g.lines hV R r s a B).moment 0)/(2*Real.pi:ℂ)

theorem centered_lines (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (r s : S)
    (a : Axis) (B : ℝ) (real : ((g.E B⁻¹).re:ℂ) = g.E B⁻¹) :
    ((g.lines hV R r s a B).moment 1 - 2*(B:ℂ)*(g.lines hV R r s a B).moment 0)/
      (2*Real.pi:ℂ) = (B:ℂ)*g.centeredPair R r s a B⁻¹ := by
  have pi : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (show (2*Real.pi:ℝ) ≠ 0 by positivity)
  let h := unitH_self hV B⁻¹
  let A := g.centeredProbe R r a B⁻¹
  let C := g.centeredProbe R s a B⁻¹
  have scalar : ((g.lines hV R r s a B).moment 1 -
      2*(B:ℂ)*(g.lines hV R r s a B).moment 0)/(2*Real.pi:ℂ) =
      (B:ℂ)*∑ j, ((h.eigenvalues j:ℂ)-(g.E B⁻¹+2))*intensity h (g.ψ B⁻¹) A C j := by
    simp only [Spectral.Lines.moment,lines,pow_one,pow_zero,mul_one,Complex.ofReal_mul,
      Complex.ofReal_sub,real]
    dsimp only [h,A,C]
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,
      Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    field_simp [pi]; ring
  rw [scalar,lehmann_first,sandwich_probes _ _ _ _ (g.centeredProbe_self R r a B⁻¹)]
  rfl

theorem dsf_eq_centered (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (r s : S) :
    ∀ᶠ B : ℝ in atTop, g.fromDSF hV R r s B = (B:ℂ)*g.angularMoment R r s B⁻¹ := by
  filter_upwards [tendsto_inv_atTop_zero.eventually (g.energy_real hV)] with B hB
  simp only [fromDSF,g.centered_lines hV R r s _ B hB,angularMoment,← Finset.mul_sum]
  ring

/-- The angular tomography identity follows from exact connected DSF moments. -/
theorem dsf_limit (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1)
    {r s : S} (ne : r≠s) :
    Tendsto (g.fromDSF hV R r s) atTop (𝓝 (V (flip r) (flip s))) :=
  (g.angular_limit R orth ne).congr' ((g.dsf_eq_centered hV R r s).mono (fun _ h => h.symm))

theorem dsf_error (hV : V.IsHermitian) (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1)
    {r s : S} (ne : r≠s) :
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      ‖g.fromDSF hV R r s B - V (flip r) (flip s)‖ ≤ C/B := by
  obtain ⟨C,hC,b,hb,estimate⟩ := rescaled_error (g.angular_smooth R r s)
    (g.angular_zero R r s) (g.angular_slope R orth ne)
  obtain ⟨a,exactMoment⟩ := eventually_atTop.mp (g.dsf_eq_centered hV R r s)
  refine ⟨C,hC,max a b,hb.trans_le (le_max_right ..),?_⟩
  intro B large
  rw [exactMoment B ((le_max_left ..).trans large)]
  exact estimate B ((le_max_right ..).trans large)

end GroundRay

/-- For any fixed finite spin system and arbitrary Hermitian interaction,
the connected angular DSF readout tends to the one-spin-flip matrix element. -/
theorem angular_tomography_finite (V : Op (Config S)) (hV : V.IsHermitian)
    (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1) (r s : S) (ne : r≠s) :
    let g := (groundRay_exists V).some
    Tendsto (g.fromDSF hV R r s) atTop (𝓝 (V (flip r) (flip s))) := by
  exact GroundRay.dsf_limit _ hV R orth ne

/-- The same physical DSF readout has a finite-volume O(1/B) remainder. -/
theorem angular_error_finite (V : Op (Config S)) (hV : V.IsHermitian)
    (R : Matrix Axis Axis ℝ) (orth : R.transpose*R=1) (r s : S) (ne : r≠s) :
    let g := (groundRay_exists V).some
    ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      ‖g.fromDSF hV R r s B - V (flip r) (flip s)‖ ≤ C/B := by
  exact GroundRay.dsf_error _ hV R orth ne

end DSFTomography.SF.Angular
