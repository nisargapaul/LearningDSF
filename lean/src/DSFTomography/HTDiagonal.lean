import DSFTomography.HTDiagonalDegree
import DSFTomography.HTDiagonalWitness
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Public diagonal HT theorem and its real algebraic exceptional set. -/
noncomputable section
namespace DSFTomography.HT.Diagonal
open DSFTomography HT MeasureTheory Filter Set
open scoped Topology ContDiff
variable {I : Type*} [Fintype I] [DecidableEq I]

private def coordStep (j : I) (i : I) : ℝ := if i=j then 1 else 0

omit [Fintype I] in
private theorem partialAlong (P : MvPolynomial I ℝ) (x : V I) (j : I) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (x + t • coordStep j) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv j P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa using hasDerivAt_const (0:ℝ) r
  | add P Q h k => simpa [Pi.add_apply] using h.add k
  | mul_X P i h =>
    have l : HasDerivAt (fun t : ℝ => (x + t • coordStep j) i) (coordStep j i) 0 := by
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,zero_add,one_mul,id_eq] using
        (hasDerivAt_const (0:ℝ) (x i)).add ((hasDerivAt_id (0:ℝ)).mul_const (coordStep j i))
    by_cases he : i=j
    · subst i
      simpa [MvPolynomial.pderiv_mul,coordStep,add_comm,mul_comm,Pi.mul_apply] using h.mul l
    · simpa [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X_of_ne he,coordStep,he,mul_comm,Pi.mul_apply] using h.mul l

private theorem detPolynomial {F : V I → V I} (smooth : ContDiff ℝ ω F)
    (P : I → MvPolynomial I ℝ) (hp : ∀ i x, MvPolynomial.eval x (P i) = F x i) :
    ∃ D : MvPolynomial I ℝ, ∀ x, MvPolynomial.eval x D = LinearMap.det (fderiv ℝ F x).toLinearMap := by
  let M : Matrix I I (MvPolynomial I ℝ) := fun i j => MvPolynomial.pderiv j (P i)
  refine ⟨M.det,fun x => ?_⟩
  rw [RingHom.map_det,← LinearMap.det_toMatrix']
  congr 1
  ext i j
  change MvPolynomial.eval x (MvPolynomial.pderiv j (P i)) = (LinearMap.toMatrix' _ ) i j
  rw [LinearMap.toMatrix'_apply]
  have dl := (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const (coordStep j))
  have line : HasDerivAt (fun t : ℝ => x + t • coordStep j) (coordStep j) 0 := by simpa only [Pi.add_apply,id_eq,zero_add,one_smul] using dl
  have df := (smooth.differentiable (by simp)).differentiableAt (x := x + (0:ℝ) • coordStep j)
  have h := df.hasFDerivAt.comp_hasDerivAt 0 line
  simp only [zero_smul,add_zero] at h
  have proj := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt _ h
  have dp := partialAlong (P i) x j
  simp only [hp] at dp
  exact dp.unique proj

/-- A full-rank witness makes the Jacobian determinant a nonzero polynomial.
Every point outside its zero set admits a local inverse. -/
theorem algebraic_of_witness {F : V I → V I} {x : V I} (smooth : ContDiff ℝ ω F)
    (P : I → MvPolynomial I ℝ) (hp : ∀ i y, MvPolynomial.eval y (P i) = F y i)
    (regular : Function.Injective (fderiv ℝ F x)) :
    ∃ D : MvPolynomial I ℝ, D ≠ 0 ∧
      (∀ y, MvPolynomial.eval y D = LinearMap.det (fderiv ℝ F y).toLinearMap) ∧
      (∀ y, MvPolynomial.eval y D ≠ 0 → LocallySolvable F y) := by
  obtain ⟨D,hd⟩ := detPolynomial smooth P hp
  refine ⟨D,?_,hd,fun y h => local_of_regular smooth ((det_iff _).mp ((hd y) ▸ h))⟩
  intro zero
  have hw := (hd x).trans_ne ((det_iff _).2 regular)
  simp [zero] at hw

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] (R : Bonds S)

/-- The singular locus is precisely the zero set of a nonzero real polynomial.
Outside it the measured diagonal features have a continuous local inverse. -/
theorem diagonalHT_algebraic :
    ∃ D : MvPolynomial (Index R) ℝ, D ≠ 0 ∧
      (∀ p, MvPolynomial.eval p D = LinearMap.det (fderiv ℝ (paperFeatures R) p).toLinearMap) ∧
      (∀ p, MvPolynomial.eval p D ≠ 0 → LocallySolvable (paperFeatures R) p) := by
  have smooth : ContDiff ℝ ω (paperFeatures R) := paper_eq R ▸ rows_smooth R false
  choose P _ hP using featureDegree R
  obtain ⟨e,he⟩ := (regular_witness R).exists
  exact algebraic_of_witness smooth P hP he

/-- This conclusion uses Lebesgue measure restricted to the physical cube. -/
theorem diagonalHT_cube :
    ∀ᵐ p ∂volume.restrict {p : Params R | ∀ i, p i ∈ Icc (-1:ℝ) 1},
      LocallySolvable (paperFeatures R) p :=
  ae_restrict_of_ae (diagonalHT R)

/-- A supplied diagonal scan can differ away from the measured temperature
window. Agreement near zero on the physical side gives the same four rows. -/
theorem calibrated_readout {p : Params R} (D : DiagonalData S)
    (cal : ∀ᶠ β in 𝓝[Set.Ici 0] (0:ℝ), D.static β = (gibbsData R p).static β ∧
      D.second β = (gibbsData R p).second β) :
    readout R D = paperFeatures R p := by
  have at0 := cal.self_of_nhdsWithin (Set.left_mem_Ici : (0:ℝ) ∈ Set.Ici 0)
  have eq₂ (d : S) (a : Axis) :
      (fun β => harmonic (fun q => D.second β q a) d) =ᶠ[𝓝[Set.Ici 0] (0:ℝ)]
      (fun β => harmonic (fun q => (gibbsData R p).second β q a) d) := by
    filter_upwards [cal] with β hb; rw [hb.2]
  have eq₀ (d : S) (a : Axis) :
      (fun β => harmonic (fun q => D.static β q a) d) =ᶠ[𝓝[Set.Ici 0] (0:ℝ)]
      (fun β => harmonic (fun q => (gibbsData R p).static β q a) d) := by
    filter_upwards [cal] with β hb; rw [hb.1]
  funext i
  cases i with
  | inl a => simp only [paperFeatures,readout,at0.2]
  | inr i =>
    obtain ⟨d,a,k⟩ := i
    have s := (eq₀ d a).derivWithin_eq_of_mem Set.left_mem_Ici
    have t := (eq₂ d a).derivWithin_eq_of_mem Set.left_mem_Ici
    simp only [paperFeatures,readout,s,t,at0.2]

/-- For almost every physical point a single local inverse recovers all nearby
couplings from any calibrated diagonal scan of their Gibbs DSF. -/
theorem diagonalHT_fromDSF :
    ∀ᵐ p ∂volume.restrict {p : Params R | ∀ i, p i ∈ Icc (-1:ℝ) 1},
      ∃ G : Params R → Params R, ContinuousAt G (paperFeatures R p) ∧
        ∀ᶠ y in 𝓝 p, ∀ D : DiagonalData S,
          (∀ᶠ β in 𝓝[Set.Ici 0] (0:ℝ), D.static β = (gibbsData R y).static β ∧
            D.second β = (gibbsData R y).second β) → G (readout R D) = y := by
  filter_upwards [diagonalHT_cube R] with p hp
  obtain ⟨G,continuous,left,_⟩ := hp
  refine ⟨G,continuous,?_⟩
  filter_upwards [left] with y hy
  intro D cal
  rw [calibrated_readout R D cal,hy]
end DSFTomography.HT.Diagonal
