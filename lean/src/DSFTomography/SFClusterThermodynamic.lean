import DSFTomography.SFClusterLocal

/-! The cluster equation in the closure of finite spatial patterns. Solving
in this closed space gives Taylor coefficients with thermodynamic limits. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 120000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology ContDiff ENNReal
variable {ν : ℕ} (R : Bonds (Site ν))
abbrev Local := ↥(localSpace R)
instance : NormedSpace ℂ (Local R) := Submodule.normedSpace (localSpace R)
instance : CompleteSpace (Local R) := (raw R).isClosed_topologicalClosure.completeSpace_coe
def restrictOp (L : Operators R) (h : ∀ x ∈ localSpace R, L x ∈ localSpace R) :
    Local R →L[ℂ] Local R :=
  (L.comp (localSpace R).subtypeL).codRestrict _ (fun x => h _ x.property)

theorem restrict_bound (L : Operators R) (h) : ‖restrictOp R L h‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => L.le_opNorm x.val

def restrictBilin (L : Amplitudes R →L[ℂ] Operators R)
    (h : ∀ x ∈ localSpace R, ∀ y ∈ localSpace R, L x y ∈ localSpace R) :
    Local R →L[ℂ] (Local R →L[ℂ] Local R) :=
  LinearMap.mkContinuous (𝕜 := ℂ) (E := Local R) (F := Local R →L[ℂ] Local R) {
    toFun := fun x => restrictOp R (L x.val) (h _ x.property)
    map_add' := by intro x y; ext z : 1; exact Subtype.ext (congrArg (fun T : Operators R => T z.val) (map_add L x.val y.val))
    map_smul' := by intro c x; ext z : 1; exact Subtype.ext (congrArg (fun T : Operators R => T z.val) (map_smul L c x.val)) }
    ‖L‖ (fun x => (restrict_bound R (L x.val) (h _ x.property)).trans (L.le_opNorm x.val))

def localVac : Local R := ⟨_,vacuum_local R⟩
def localConv := restrictBilin R (convolutionFamily R) (convolution_preserves R)
def localExp (v : Local R) : Local R := exp ℂ (localConv R v) (localVac R)
def DOp (D : Pattern ν) := restrictOp R (localResponse R D) (response_preserves R D)
def XOp (A : Pattern ν) := restrictOp R (localFlip R A) (flip_preserves R A)

theorem val_localExp (x : Local R) : (localExp R x).val = expAmplitude R x.val := by
  let i := (localSpace R).subtypeL
  let col := ContinuousLinearMap.apply ℂ (Local R) (localVac R)
  have pw (k : ℕ) (v : Local R) : i (((localConv R x)^k) v) = ((convolutionFamily R x.val)^k) v.val := by
    induction k generalizing v with
    | zero => rfl
    | succ k ih => rw [pow_succ,pow_succ]; exact ih (localConv R x v)
  have lhs := (i.comp col).hasSum (exp_series_hasSum_exp' (𝕂 := ℂ) (localConv R x))
  have rhs := (vacuumColumn R).hasSum (exp_series_hasSum_exp' (𝕂 := ℂ) (convolutionFamily R x.val))
  apply (lhs.congr_fun _).unique rhs
  intro k; simp only [map_smul]; exact congrArg (_ • ·) (pw k (localVac R)).symm

@[simp] theorem localExp_zero : localExp R 0 = localVac R := by simp [localExp]
theorem localExp_analytic (x : Local R) : AnalyticAt ℂ (localExp R) x :=
  ((ContinuousLinearMap.apply ℂ (Local R) (localVac R)).analyticAt _).comp
    ((exp_analytic (𝕂 := ℂ) _).comp ((localConv R).analyticAt x))
theorem localExp_deriv : HasFDerivAt (localExp R) (ContinuousLinearMap.id ℂ (Local R)) 0 := by
  have e : HasFDerivAt (exp ℂ) (1 : (Local R →L[ℂ] Local R) →L[ℂ] (Local R →L[ℂ] Local R)) (localConv R 0) := by
    rw [map_zero]; exact hasFDerivAt_exp_zero ..
  let col := ContinuousLinearMap.apply ℂ (Local R) (localVac R)
  convert col.hasFDerivAt.comp 0 (e.comp 0 (localConv R).hasFDerivAt) using 1
  exact ContinuousLinearMap.ext (fun x => Subtype.ext (column_convolution R x.val).symm)

private abbrev Z := Sources R × Local R
private def localResid (z : Z R) := localExp R (DOp R [0] z.2) - localVac R - DOp R [0] z.2 -
  ∑ j, z.1 j • XOp R (flipSites R j) (localExp R (DOp R (signSites R j) z.2) - localVac R)
private def localBare : Sources R →L[ℂ] Local R :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (XOp R (flipSites R j) (localVac R))
private theorem resid_analytic : ContDiffAt ℂ ω (localResid R) 0 := by
  have ea (D) : ContDiffAt ℂ ω (fun z : Z R => localExp R (DOp R D z.2)) 0 :=
    (localExp_analytic R _).contDiffAt.comp 0 ((DOp R _).contDiff.contDiffAt.comp 0 contDiffAt_snd)
  apply ContDiffAt.sub
  · exact ((ea _).sub contDiffAt_const).sub ((DOp R [0]).contDiff.contDiffAt.comp 0 contDiffAt_snd)
  · apply ContDiffAt.sum; intro j _
    exact ((ContinuousLinearMap.proj j : Sources R →L[ℂ] ℂ).contDiff.contDiffAt.comp 0 contDiffAt_fst).smul
      ((XOp R _).contDiff.contDiffAt.comp 0 ((ea _).sub contDiffAt_const))

private theorem resid_flat : HasFDerivAt (𝕜 := ℂ) (localResid R) 0 0 := by
  let L (D : Pattern ν) := (DOp R D).comp (ContinuousLinearMap.snd ℂ (Sources R) (Local R))
  have de (D) : HasFDerivAt (fun z : Z R => localExp R (L D z)) (L D) 0 := by
    have e := localExp_deriv R
    rw [← map_zero (L D)] at e
    simpa using e.comp 0 (L D).hasFDerivAt
  have df := ((de [0]).sub_const (localVac R)).sub (L [0]).hasFDerivAt
  have di (j : Shape R) : HasFDerivAt (𝕜 := ℂ)
      (fun z : Z R => z.1 j • XOp R (flipSites R j) (localExp R (DOp R (signSites R j) z.2) - localVac R)) 0 0 := by
    have h := (XOp R (flipSites R j)).hasFDerivAt.comp 0 ((de (signSites R j)).sub_const (localVac R))
    let π := (ContinuousLinearMap.proj j : Sources R →L[ℂ] ℂ).comp (ContinuousLinearMap.fst ℂ (Sources R) (Local R))
    convert π.hasFDerivAt.smul h using 1
    apply ContinuousLinearMap.ext; intro w; simp [π,L]
  simpa only [sub_self,Finset.sum_const_zero,sub_zero] using df.sub (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => di j)

/-- A common holomorphic solution, now valued in the closure of finite
spatial patterns. In particular this is a single series for all boxes. -/
theorem local_branch :
    ∃ a : Sources R → Local R, AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧ ∀ᶠ p in 𝓝 0,
      (a p).val = freeResidual R (a p).val -
        ∑ j, p j • localFlip R (flipSites R j) (expAmplitude R (localResponse R (signSites R j) (a p).val)) := by
  let F := fun z : Z R => (z.1,z.2-localResid R z)
  have sm : ContDiffAt ℂ ω F 0 := contDiffAt_fst.prodMk (contDiffAt_snd.sub (resid_analytic R))
  have der : HasFDerivAt F (ContinuousLinearEquiv.refl ℂ (Z R)).toContinuousLinearMap 0 := by
    simpa using (hasFDerivAt_fst (𝕜 := ℂ) (p := (0 : Z R))).prodMk
      ((hasFDerivAt_snd (𝕜 := ℂ) (p := (0 : Z R))).sub (resid_flat R))
  have one : (1:WithTop ℕ∞) ≤ ω := by simp
  let inv := sm.localInverse der one
  have z : F 0=0 := by simp [F,localResid]
  let src := (ContinuousLinearMap.id ℂ (Sources R)).prod (-(localBare R))
  have hi : ContDiffAt ℂ ω inv 0 := by simpa only [z] using sm.to_localInverse der one
  have iz : inv 0=0 := by simpa only [z] using sm.localInverse_apply_image der one
  refine ⟨fun p => (inv (src p)).2,?_,by simp [iz],?_⟩
  · have h : ContDiffAt ℂ ω inv (src 0) := by simpa using hi
    exact (contDiffAt_snd.comp 0 (h.comp 0 src.contDiff.contDiffAt)).analyticAt
  · have h := (sm.hasStrictFDerivAt' der one).eventually_right_inverse
    rw [z] at h
    have cv : Tendsto src (𝓝 0) (𝓝 0) := by simpa using src.continuous.continuousAt (x := 0) |>.tendsto
    filter_upwards [cv.eventually h] with p hp
    let v := (inv (src p)).2
    have f : (inv (src p)).1=p := congrArg Prod.fst hp
    have s : v-localResid R (inv (src p)) = - localBare R p := congrArg Prod.snd hp
    simp only [localResid,f,map_sub,smul_sub,Finset.sum_sub_distrib,localBare,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply] at s
    have eq : v = localExp R (DOp R [0] v) - localVac R - DOp R [0] v -
        ∑ j, p j • XOp R (flipSites R j) (localExp R (DOp R (signSites R j) v)) :=
      (sub_eq_iff_eq_add.mp s).trans (by abel)
    have e := congrArg (localSpace R).subtypeL eq
    simp only [map_sub,map_sum,map_smul,Submodule.subtypeL_apply] at e
    simpa only [DOp,XOp,restrictOp,ContinuousLinearMap.coe_codRestrict_apply,ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply,val_localExp] using e

/-- Simple dressed eigenstate with a volume-independent excitation gap for
real physical sources. The stronger statement orders all complex eigenvalues
by real part in a neighborhood of zero. -/
theorem uniform_ground_branch :
    ∃ a : Sources R → Amplitudes R, AnalyticAt ℂ a 0 ∧ a 0=0 ∧ GroundNeighborhood R a := by
  obtain ⟨v,hv,hz,sol⟩ := local_branch R
  let a := fun p => (v p).val
  have ha : AnalyticAt ℂ a 0 := ((localSpace R).subtypeL.analyticAt _).comp hv
  have zero : a 0=0 := by simp [a,hz]
  exact ⟨a,ha,zero,ground_of_branch R a ha zero sol⟩

end DSFTomography.SF.Cluster
