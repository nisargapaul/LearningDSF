import DSFTomography.SFEigenbranch
import DSFTomography.SFPaper
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The exact normalized eigenket in each sufficiently weakly perturbed
finite-volume unit-field Hamiltonian. Regularity is obtained by an inverse
function theorem at the polarized configuration, not by selecting phases of
numerically ordered eigenvectors. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Perturbation Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def withParams (R : Bonds S) (p : Params R.dirs) : Volume S where
  R := R
  h := p.1
  J d := if hd : d ∈ R.dirs then p.2 ⟨d,hd⟩ else 0

@[simp] theorem parameters_withParams (R : Bonds S) (p : Params R.dirs) : parameters (withParams R p) = p := by
  apply Prod.ext
  · rfl
  · funext d; simp [parameters,withParams]

theorem frame_linear (R : Bonds S) (i : Axis) :
    ∃ L : Params R.dirs →L[ℝ] Entries (Config S), ∀ p, L p = fieldFrame (withParams R p) i := by
  let σ := (qubitSpins (1 : (Op (Config S))ˣ)).σ
  let K := fun (p : Params R.dirs) (x y : Config S) =>
    (∑ r, ∑ a, (p.1 (axisInLab i a) : ℂ) * σ r a x y) +
    ∑ d : R.dirs, ∑ r, ∑ a, ∑ b, (p.2 d (axisInLab i a) (axisInLab i b) : ℂ) *
      (σ r a * σ (r+d.val) b) x y
  refine ⟨LinearMap.toContinuousLinearMap {toFun := K, map_add' := ?_, map_smul' := ?_}, ?_⟩
  · intro p q; funext x y
    simp only [K,Prod.fst_add,Prod.snd_add,Pi.add_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]; abel
  · intro t p; funext x y
    simp only [K,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.real_smul,mul_assoc,← Finset.mul_sum,← mul_add,RingHom.id_apply]
  · intro p; funext x y
    change K p x y = _
    simp only [K,fieldFrame,qubitH,realH,H,withParams,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,
      smul_eq_mul,σ]
    congr 1
    rw [← Finset.sum_attach R.dirs]
    apply Finset.sum_congr rfl; intro d _
    simp only [dif_pos d.property]

omit [AddCommGroup S] in
/-- The vacuum energy has been subtracted and the field is one. Every
nonvacuum product configuration has energy at least two. -/
theorem gap_nonvac (x : Config S) (hx : x ≠ vacuum S) : 2 ≤ (flipGap x).re := by
  have existsOne : ∃ s, x s = 1 := by
    by_contra! h
    apply hx; funext s
    have ne := h s
    have zero : x s = 0 := by have := (x s).isLt; omega
    simp [vacuum,bitConfig,zero]
  obtain ⟨s,hs⟩ := existsOne
  have hc := Finset.card_pos.mpr (show (Finset.univ.filter fun s => x s=1).Nonempty from
    ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩)
  simp [flipGap]
  exact Finset.card_pos.mp hc

/-- A normalized eigenstate spanning the lowest eigenspace in the unit-field frame. -/
def IsGroundPair (R : Bonds S) (i : Axis) (p : Params R.dirs) (ψ : Config S → ℂ) (E : ℂ) : Prop :=
    (∑ k, Complex.normSq (ψ k)) = 1 ∧
    (∀ k, flipGap k * ψ k + (∑ j, fieldFrame (withParams R p) i k j * ψ j) = E * ψ k) ∧
    (∀ (μ : ℂ) (ξ : Config S → ℂ), ξ ≠ 0 →
      (∀ k, flipGap k * ξ k + (∑ j, fieldFrame (withParams R p) i k j * ξ j) = μ * ξ k) →
      μ.re ≤ E.re → μ = E ∧ ∃ c : ℂ, ξ = c • ψ)

/-- Unit-field chart as a function of all couplings, before selecting a ray. -/
structure GroundChart (R : Bonds S) (i : Axis) where
  ψ : Params R.dirs → Config S → ℂ
  E : Params R.dirs → ℂ
  smoothψ : ContDiffAt ℝ 2 ψ 0
  smoothE : ContDiffAt ℝ 2 E 0
  vac : ψ 0 = ket (vacuum S)
  E0 : E 0 = 0
  physical : ∀ᶠ p in 𝓝 0, IsGroundPair R i p (ψ p) (E p)

/-- A single threshold makes all three charts physical for every coupling in the cube. -/
theorem groundChart_cube_neighborhood {R : Bonds S} (G : ∀ i, GroundChart R i) :
    ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube R.dirs, ∀ᶠ x in 𝓝 (B⁻¹ • p),
      ∀ i : Axis, IsGroundPair R i x ((G i).ψ x) ((G i).E x) := by
  have allCharts := eventually_all.mpr (fun i : Axis => (G i).physical)
  obtain ⟨r,hr,within⟩ := Metric.mem_nhds_iff.mp (eventually_eventually_nhds.mpr allCharts)
  refine ⟨2/r,by positivity,?_⟩
  intro B large p hp
  have hB : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2/r) large
  have hp' : ‖p‖ ≤ 1 := by simpa [couplingCube] using hp
  have small : B⁻¹ < r := by
    rw [inv_eq_one_div,div_lt_iff₀ hB]
    have := (div_le_iff₀ hr).mp large
    linarith [mul_comm B r]
  apply within
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hB)]
  exact lt_of_le_of_lt (by simpa using mul_le_mul_of_nonneg_left hp' (inv_nonneg.mpr hB.le)) small

theorem groundChart_cube {R : Bonds S} (G : ∀ i, GroundChart R i) :
    ∃ b > (0:ℝ), ∀ B ≥ b, ∀ p ∈ couplingCube R.dirs, ∀ i : Axis,
      IsGroundPair R i (B⁻¹ • p) ((G i).ψ (B⁻¹ • p)) ((G i).E (B⁻¹ • p)) := by
  obtain ⟨b,hb,near⟩ := groundChart_cube_neighborhood G
  exact ⟨b,hb,fun B hB p hp => (near B hB p hp).self_of_nhds⟩

/-- Every finite periodic lattice has a regular ground-state chart on a
neighborhood of the polarized point. Its radius can depend on the volume. -/
theorem groundChart_exists (R : Bonds S) (i : Axis) : Nonempty (GroundChart R i) := by
  let o := vacuum S
  have gap0 : flipGap o = 0 := by simp [o,vacuum,flipGap_bits]
  have nz (k : Config S) (hk : k≠o) : flipGap k ≠ 0 := by
    intro bad; have pos := gap_nonvac k hk; rw [bad,Complex.zero_re] at pos; linarith
  obtain ⟨L,hL⟩ := frame_linear R i
  obtain ⟨v,hv,v0,eig⟩ := finite_branch o flipGap gap0 nz
  let b := fun p : Params R.dirs => v (L p)
  have b0 : b 0 = 0 := by simp [b,v0]
  have sb : ContDiffAt ℝ 2 b 0 := (show ContDiffAt ℝ 2 v (L 0) by simpa using hv.restrict_scalars ℝ).comp _ L.contDiff.contDiffAt
  let w := fun p k => vector o (b p) k
  have wo (p) : w p o = 1 := by simp [w,vector,ket,mask]
  have w0 (k) : w 0 k = ket o k := by simp [w,vector,b0,mask]
  have bk (k) : ContDiffAt ℝ 2 (fun p => b p k) 0 :=
    (ContinuousLinearMap.proj k : (Config S → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt.comp 0 sb
  have sw (k) : ContDiffAt ℝ 2 (fun p => w p k) 0 := by
    by_cases h : k=o <;> simp [w,vector,mask,h] <;> fun_prop
  let n2 := fun p => ∑ k, Complex.normSq (w p k)
  let n := fun p => (Real.sqrt (n2 p) : ℂ)
  have n2pos (p) : 0 < n2 p := by
    have le := Finset.single_le_sum (s := Finset.univ) (f := fun k => Complex.normSq (w p k))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ o)
    change Complex.normSq (w p o) ≤ n2 p at le
    rw [wo,Complex.normSq_one] at le
    exact zero_lt_one.trans_le le
  have nn (p) : n p ≠ 0 := by simpa [n] using (Real.sqrt_pos.mpr (n2pos p)).ne'
  have n0 : n 0 = 1 := by simp [n,n2,w0,ket,apply_ite]
  have sn2 : ContDiffAt ℝ 2 n2 0 := by
    unfold n2
    apply ContDiffAt.sum; intro k _
    simp only [Complex.normSq_apply]
    have a := Complex.reCLM.contDiff.contDiffAt.comp 0 (sw k)
    have b := Complex.imCLM.contDiff.contDiffAt.comp 0 (sw k)
    exact (a.mul a).add (b.mul b)
  have sn : ContDiffAt ℝ 2 n 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (sn2.sqrt (n2pos 0).ne')
  let ψ := fun p k => w p k / n p
  refine ⟨{ ψ := ψ, E := fun p => b p o, smoothψ := contDiffAt_pi.mpr (fun k => by
              simp only [ψ,div_eq_mul_inv]; exact (sw k).mul ((contDiffAt_inv ℝ (nn 0)).comp 0 sn)),
            smoothE := bk o, vac := by funext k; simp [ψ,n0,w0,o], E0 := by simp [b0], physical := ?_ }⟩
  have nearL : Tendsto L (𝓝 (0:Params R.dirs)) (𝓝 0) := by simpa using (L.continuous.continuousAt (x := 0)).tendsto
  have small := ((continuous_const.mul L.continuous.norm : Continuous (fun x => (2*(Fintype.card (Config S):ℝ))*‖L x‖)).continuousAt (x := 0)).eventually_lt_const
    (show (2*(Fintype.card (Config S):ℝ))*‖L 0‖ < 1 by simp)
  have close := sb.continuousAt.norm.eventually_lt_const (by simp [b0] : ‖b 0‖ < 1)
  filter_upwards [nearL.eventually eig, small, close] with p eigen sm cl
  change ∀ k, flipGap k * w p k + ∑ j, L p k j * w p j = b p o * w p k at eigen
  unfold IsGroundPair
  rw [← hL]
  refine ⟨?_,?_,?_⟩
  · simp only [ψ,map_div₀,← Finset.sum_div]
    change n2 p / Complex.normSq (n p) = 1
    rw [show Complex.normSq (n p) = n2 p by simp only [n,Complex.normSq_ofReal,← sq,Real.sq_sqrt (n2pos p).le]]
    exact div_self (n2pos p).ne'
  · intro k
    simpa only [ψ,← mul_div_assoc,← Finset.sum_div,← add_div] using congrArg (· / n p) (eigen k)
  · intro μ ξ hξ test lower
    have μlow : μ.re ≤ 1 := lower.trans (((Complex.re_le_norm _).trans (norm_le_pi_norm (b p) o)).trans cl.le)
    have align := low_eigenline o flipGap (L p) (w p) ξ (wo p) gap_nonvac eigen test sm
      (fun k hk => by simpa [w,vector,ket,mask,hk] using (norm_le_pi_norm (b p) k).trans cl.le) μlow
    have overlap : ξ o ≠ 0 := by
      intro no; apply hξ; funext k; simp [align k,no]
    have erow := test o
    simp only [gap0,zero_mul,zero_add] at erow
    have base := eigen o; simp only [gap0,wo,zero_add,mul_one] at base
    have alt (j) : L p o j*ξ j = ξ o*(L p o j*w p j) := by calc
      _ = L p o j*(ξ o*w p j) := congrArg _ (align j)
      _ = _ := by ring
    simp_rw [alt,← Finset.mul_sum,base] at erow
    refine ⟨mul_right_cancel₀ overlap ((mul_comm _ _).trans erow).symm, ξ o*n p,?_⟩
    funext k
    change ξ k = (ξ o*n p)*(w p k/n p)
    rw [align k]; field_simp [nn p]

end DSFTomography.SF
