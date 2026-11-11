import DSFTomography.HTBulkMomentJets

/-! Uniform convergence of the local complex-temperature extensions, followed
by Cauchy differentiation. The public bulk moment is defined by the limit of
the finite Lehmann harmonics at fixed real β. -/
noncomputable section
namespace DSFTomography.HT.Diagonal.Bulk
open DSFTomography HT LocalWord Filter Metric
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
local notation "rβ" => diskRadius R h J
local notation "Vₙ" => periodicVolume R h J

private theorem form_uniform (u : Form (Site ν)) :
    ∃ F : ℂ → ℂ, TendstoUniformlyOn
      (fun n z => Form.apply u (fun w => value R h J w n z)) F atTop (closedBall 0 rβ) := by
  induction u with
  | nil => exact ⟨0,tendsto_const_nhds.tendstoUniformlyOn_const _⟩
  | cons p u ih =>
    obtain ⟨F,hF⟩ := ih
    have hc := uniform R h J p.2
    have hw := hc.tendstoUniformlyOn_of_tendsto (f := fun z => limUnder atTop (fun n => value R h J p.2 n z)) (fun z hz => (hc.cauchySeq hz).tendsto_limUnder)
    have hs := (uniformContinuous_const_smul (X := ℂ) p.1).comp_tendstoUniformlyOn hw
    exact ⟨_,hs.add hF⟩

theorem finite_intercept (k d a n) :
    moment (Vₙ n) k (place R n d) a 0 = intercept R h J k d a n := by
  rw [moment_eq_test,← extension_eq,extension,intercept]
  apply congrArg (Form.apply _); funext w
  exact (state_apply R h J n 0 _).trans (test_zero (Vₙ n) (eval (place R n) w))

theorem finite_deriv (k d a n) :
    HasDerivAt (moment (Vₙ n) k (place R n d) a) (slope R h J k d a n) 0 := by
  simp only [funext (moment_eq_test (Vₙ n) k (place R n d) a),← extension_eq,extension,slope]
  induction form R h J k d a with
  | nil => simpa using hasDerivAt_const (0:ℝ) (0:ℂ)
  | cons p u ih =>
    have term := test_slope (Vₙ n) (eval (place R n) p.2)
    have realVal (t : ℝ) : value R h J p.2 n t = test (Vₙ n) (eval (place R n) p.2) t := state_apply ..
    simpa only [Form.apply_cons,realVal,smul_eq_mul,wordSlope,Pi.add_apply] using (term.const_mul p.1).add ih

/-- Real space displacement harmonic of the diagonal DSF in the thermodynamic
limit. The frequency moment is taken at each fixed inverse temperature. -/
def bulkMoment (k : ℕ) (d : Site ν) (a : Axis) (β : ℝ) : ℂ :=
  limUnder atTop (fun n => moment (Vₙ n) k (place R n d) a β)

theorem volume_first (k d a) :
    (∀ β : ℝ, |β| < rβ → Tendsto (fun n => moment (Vₙ n) k (place R n d) a β)
      atTop (𝓝 (bulkMoment R h J k d a β))) ∧
    (∃ v : ℂ, HasDerivAt (bulkMoment R h J k d a) v 0 ∧
      Tendsto (slope R h J k d a) atTop (𝓝 v)) := by
  let F := extension R h J k d a
  obtain ⟨f,uniform⟩ := form_uniform R h J (form R h J k d a)
  have loc : TendstoLocallyUniformlyOn F f atTop (ball 0 rβ) :=
    (uniform.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  have reg (n z) (hz : z ∈ ball (0:ℂ) rβ) : (Vₙ n).partition z ≠ 0 := by
    apply (periodic_zeroFree_bounded R h J n z _).1
    have small : ‖z‖ < rβ := by simpa [mem_ball] using hz
    have pos := bulkRadius_pos R h J
    unfold diskRadius at small; linarith
  have hol : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball 0 rβ) := by
    apply Eventually.of_forall; intro n
    change DifferentiableOn ℂ (extension R h J k d a n) _
    rw [funext (extension_eq R h J k d a n)]
    exact holTest _ _ (reg n)
  have data (n : ℕ) (β : ℝ) : moment (Vₙ n) k (place R n d) a β = F n β :=
    (moment_eq_test ..).trans (extension_eq R h J k d a n β).symm
  have inside (β : ℝ) (hβ : |β| < rβ) : (β : ℂ) ∈ ball (0:ℂ) rβ := by simpa [mem_ball,Real.norm_eq_abs] using hβ
  have conv (β : ℝ) (hβ : |β| < rβ) : Tendsto (fun n => moment (Vₙ n) k (place R n d) a β) atTop (𝓝 (f β)) := by
    simp only [data]; exact loc.tendsto_at (inside β hβ)
  have eq (β : ℝ) (hβ : |β| < rβ) : bulkMoment R h J k d a β = f β := (conv β hβ).limUnder_eq
  have z0 : (0:ℂ) ∈ ball 0 rβ := mem_ball_self (diskRadius_pos ..)
  refine ⟨fun β hb => eq β hb ▸ conv β hb,deriv f 0,?_,?_⟩
  · have der := ((loc.differentiableOn hol isOpen_ball).differentiableAt (isOpen_ball.mem_nhds z0)).hasDerivAt
    have hd : HasDerivAt (fun β : ℝ => f β) (deriv f 0) 0 :=
      (show HasDerivAt f (deriv f 0) ((0:ℝ):ℂ) from der).comp_ofReal
    apply hd.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0:ℝ) (diskRadius_pos R h J)] with β hb
    exact eq β (by simpa [mem_ball,Real.dist_eq] using hb)
  · apply ((loc.deriv hol isOpen_ball).tendsto_at z0).congr'
    filter_upwards [hol] with n hn
    have hd := (hn.differentiableAt (isOpen_ball.mem_nhds z0)).hasDerivAt
    have realD : HasDerivAt (fun β : ℝ => F n β) (deriv (F n) 0) 0 :=
      (show HasDerivAt (F n) (deriv (F n) 0) ((0:ℝ):ℂ) from hd).comp_ofReal
    exact realD.unique (by simpa only [funext (data n)] using finite_deriv R h J k d a n)

end DSFTomography.HT.Diagonal.Bulk
