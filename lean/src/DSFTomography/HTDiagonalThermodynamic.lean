import DSFTomography.HTBulkMomentLimit
import DSFTomography.HTBulkDiagonalBoxes

/-! Volume-first diagonal HT on ℤ^ν. Each input curve is the limit at fixed
β of the corresponding finite-volume Lehmann harmonic. Only after forming
this curve do we extract the thermal slope. -/
noncomputable section
namespace DSFTomography.HT.Diagonal.Bulk
open DSFTomography HT LocalWord Filter Set MeasureTheory Metric
open scoped Topology ContDiff
variable {ν : ℕ} (R : Bonds (Site ν))
def curve (p : Params R) (i : Index R) : ℝ → ℂ :=
  let s := setting R i
  bulkMoment R (fields R p) (exch R p) s.k s.d s.a

def features (p : Params R) : Params R := fun i => extract (setting R i) (curve R p i)

/-- One box threshold suffices for the entire feature map, simultaneously for
all fields and exchanges. This is equality of the Taylor coefficients; the
unexpanded finite-temperature curves still depend on the box. -/
theorem features_stabilize : ∀ᶠ n : ℕ in atTop, features R = finiteFeatures R n := by
  choose N hN using fun i : Index R => moment_jet_stable R (setting R i).k (setting R i).d (setting R i).a
  filter_upwards [eventually_ge_atTop (Finset.univ.sup N)] with n hn
  funext p i
  let s := setting R i
  let h := fields R p
  let J := exch R p
  have large : N i ≤ n := (Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ i)).trans hn
  have stable := fun m hm => hN i m hm n large h J
  obtain ⟨conv,v,der,lim⟩ := volume_first R h J s.k s.d s.a
  have constant₀ : ∀ᶠ m in atTop, intercept R h J s.k s.d s.a m = intercept R h J s.k s.d s.a n :=
    (eventually_ge_atTop (N i)).mono fun m hm => (stable m hm).1
  have constant₁ : ∀ᶠ m in atTop, slope R h J s.k s.d s.a m = slope R h J s.k s.d s.a n :=
    (eventually_ge_atTop (N i)).mono fun m hm => (stable m hm).2
  have zero := conv 0 (by simpa using diskRadius_pos R h J)
  simp only [finite_intercept] at zero
  change extract s (bulkMoment R h J s.k s.d s.a) = extract s (moment _ s.k (place R n s.d) s.a)
  unfold extract; split
  · have hv := tendsto_nhds_unique lim (tendsto_const_nhds.congr' (constant₁.mono fun _ hm => hm.symm))
    rw [der.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0),
      (finite_deriv R h J s.k s.d s.a n).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0),hv]
  · rw [finite_intercept,tendsto_nhds_unique zero (tendsto_const_nhds.congr' (constant₀.mono fun _ hm => hm.symm))]

private theorem reference :
    ∃ n, features R = (coordinates R n).symm ∘ paperFeatures (periodicBonds R n) ∘ coordinates R n := by
  obtain ⟨n,hn⟩ := (features_stabilize R).exists
  exact ⟨n,hn.trans (box_features R n)⟩

private theorem feature_smooth : ContDiff ℝ ω (features R) := by
  obtain ⟨n,eq⟩ := reference R
  rw [eq,paper_eq]
  exact (coordinates R n).symm.contDiff.comp ((rows_smooth _ false).comp (coordinates R n).contDiff)

/-- The same field and antisymmetric-exchange witness works for the limiting
features for every sufficiently small positive ε. -/
theorem bulk_witness : ∀ᶠ e in 𝓝[>] (0:ℝ),
    Function.Injective (fderiv ℝ (features R) (witness R e)) := by
  obtain ⟨n,eq⟩ := reference R
  let T := coordinates R n
  let B := periodicBonds R n
  have ws (e : ℝ) : T (witness R e) = witness B e := by
    funext j; obtain ⟨i,rfl⟩ := (indexEquiv R n).surjective j
    rw [show T (witness R e) (indexEquiv R n i) = _ from coord_apply R n _ i]
    cases i with
    | inl a => rfl
    | inr i => obtain ⟨d,a,k⟩ := i; rfl
  have smooth : ContDiff ℝ ω (paperFeatures B) := paper_eq B ▸ rows_smooth B false
  filter_upwards [regular_witness B] with e he
  let x := witness R e
  have hd := (smooth.differentiable (by simp)).differentiableAt (x := T x)
  have comp := T.symm.hasFDerivAt.comp x (hd.hasFDerivAt.comp x T.hasFDerivAt)
  rw [eq,comp.fderiv]
  exact T.symm.injective.comp ((ws e ▸ he : Function.Injective (fderiv ℝ (paperFeatures B) (T x))).comp T.injective)

/-- The limiting feature rows retain their respective total-degree bounds. -/
theorem bulk_degree (i : Index R) :
    DegreeLE (match i with | .inl _ => 2 | .inr (_,_,k) => k.val+1) (fun p => features R p i) := by
  obtain ⟨n,eq⟩ := reference R
  let idx := indexEquiv R n
  obtain ⟨P,deg,data⟩ := featureDegree (periodicBonds R n) (idx i)
  refine ⟨MvPolynomial.rename idx.symm P,(MvPolynomial.totalDegree_rename_le _ _).trans ?_,?_⟩
  · cases i with
    | inl a => exact deg
    | inr i => obtain ⟨d,a,k⟩ := i; exact deg
  · intro p
    rw [MvPolynomial.eval_rename,eq]
    change MvPolynomial.eval (coordinates R n p) P = _
    rw [data]
    simpa only [idx,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply] using
      (coord_apply R n ((coordinates R n).symm (paperFeatures (periodicBonds R n) (coordinates R n p))) i)

/-- The limiting Jacobian loses rank on the zero set of a nonzero polynomial. -/
theorem diagonalHT_bulk_algebraic :
    ∃ D : MvPolynomial (Index R) ℝ, D ≠ 0 ∧
      (∀ p, MvPolynomial.eval p D = LinearMap.det (fderiv ℝ (features R) p).toLinearMap) ∧
      (∀ p, MvPolynomial.eval p D ≠ 0 → LocallySolvable (features R) p) := by
  choose P _ hP using bulk_degree R
  obtain ⟨e,he⟩ := (bulk_witness R).exists
  exact algebraic_of_witness (feature_smooth R) P hP he

/-- Generic local solvability on the physical cube, after taking the periodic
thermodynamic limit of the DSF harmonics before differentiation. -/
theorem diagonalHT_thermodynamic :
    ∀ᵐ p ∂volume.restrict {p : Params R | ∀ i, p i ∈ Icc (-1:ℝ) 1},
      LocallySolvable (features R) p := by
  obtain ⟨e,he⟩ := (bulk_witness R).exists
  exact ae_restrict_of_ae (generic_of_witness (feature_smooth R) he)

/-- Complete an observed positive-temperature harmonic with its right limit
at zero. This supplies the intercept for both the intercept and slope rows. -/
def positiveReadout (D : Index R → ℝ → ℂ) : Params R := fun i =>
  extract (setting R i) (fun β => if β=0 then limUnder (𝓝[>] (0:ℝ)) (D i) else D i β)

def Observed (p : Params R) (D : Index R → ℝ → ℂ) : Prop :=
  ∀ i, ∀ᶠ β in 𝓝[>] (0:ℝ), Tendsto (fun n => finiteCurve R n p i β) atTop (𝓝 (D i β))

theorem readout_eq {p : Params R} {D : Index R → ℝ → ℂ} (cal : Observed R p D) :
    positiveReadout R D = features R p := by
  funext i
  let s := setting R i
  let r := diskRadius R (fields R p) (exch R p)
  obtain ⟨conv,v,der,_⟩ := volume_first R (fields R p) (exch R p) s.k s.d s.a
  have near : ∀ᶠ β in 𝓝[>] (0:ℝ), β ∈ ball (0:ℝ) r :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (diskRadius_pos ..))
  have eq : D i =ᶠ[𝓝[>] (0:ℝ)] curve R p i := by
    filter_upwards [near,cal i] with β hb obs
    exact tendsto_nhds_unique obs (conv β (by simpa [mem_ball,Real.dist_eq] using hb))
  have cont : ContinuousAt (curve R p i) 0 := der.continuousAt
  have intercept : limUnder (𝓝[>] (0:ℝ)) (D i) = curve R p i 0 :=
    ((cont.tendsto.mono_left nhdsWithin_le_nhds).congr' eq.symm).limUnder_eq
  let f := fun β => if β=0 then limUnder (𝓝[>] (0:ℝ)) (D i) else D i β
  have eq₀ : f =ᶠ[𝓝[Set.Ici 0] (0:ℝ)] curve R p i := by
    rw [← Ioi_union_left,nhdsWithin_union,Filter.EventuallyEq,eventually_sup]
    constructor
    · filter_upwards [eq,self_mem_nhdsWithin] with β h hβ
      simpa [f,ne_of_gt (show 0 < β from hβ)] using h
    · simpa [f] using intercept
  change extract s f = extract s (curve R p i)
  unfold extract; split
  · rw [eq₀.derivWithin_eq_of_mem Set.left_mem_Ici]
  · simp [f,intercept]

theorem diagonalHT_from_bulk_DSF :
    ∀ᵐ p ∂volume.restrict {p : Params R | ∀ i, p i ∈ Icc (-1:ℝ) 1},
      ∃ G : Params R → Params R, ContinuousAt G (features R p) ∧
        ∀ᶠ y in 𝓝 p, ∀ D, Observed R y D → G (positiveReadout R D) = y := by
  filter_upwards [diagonalHT_thermodynamic R] with p hp
  obtain ⟨G,cont,left,_⟩ := hp
  refine ⟨G,cont,?_⟩
  filter_upwards [left] with y hy
  intro D hD; rw [readout_eq R hD,hy]
end DSFTomography.HT.Diagonal.Bulk
