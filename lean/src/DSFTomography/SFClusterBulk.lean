import DSFTomography.SFClusterMatching
import DSFTomography.SFLaboratory

/-! The volume-first laboratory theorem with the ground-state expansion
constructed from the one- and two-body interactions. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace DSFTomography.SF
open DSFTomography HT Filter Cluster
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν))

namespace Cluster
private theorem avg_eq {S : Type*} [Fintype S] [Nonempty S] (f : S → ℂ) (k : ℂ) (h : ∀ r, f r=k) : avg f=k := by
  simp [avg,h,Fintype.card_ne_zero]

private theorem box_matches (b : Branch R) (G : BoxCharts R) (n : ℕ) (p : Params R.dirs)
    (states : ∀ i, BoxState b n i p)
    (ψ : ∀ i, (G n i).ψ (boxParams R n p) = WithLp.ofLp (states i).u)
    (energy : ∀ i, (G n i).E (boxParams R n p) = Ebox R n (b.a (sourceMap R i p)).val) :
    (b.harmonics p) (n:Boxes) = boxReadout R G n p := by
  let q := fun i => sourceMap R i p
  let x := boxParams R n p
  have origin : periodicSite R n 0=0 := by funext j; simp [periodicSite,reduceBond]
  have c (i : Axis) (r s : Site ν) : (avg fun t => (G n i).centeredAt x (periodicSite R n r+t) (periodicSite R n s+t)) =
      b.centered r s (q i) (n:Boxes) := avg_eq _ _ fun t => (states i).centered_matches _ (ψ i) (energy i) t r s
  have c₀ (i : Axis) : (avg fun t => (G n i).centeredAt x t t) = b.centered 0 0 (q i) (n:Boxes) := by simpa [origin] using c i 0 0
  have plus (i : Axis) (d : R.dirs) : (avg fun t => (G n i).centeredAt x t (t+periodicSite R n d)) =
      b.centered 0 d.val (q i) (n:Boxes) := by simpa [origin,add_comm (periodicSite R n d)] using c i 0 d.val
  have minus (i : Axis) (d : R.dirs) : (avg fun t => (G n i).centeredAt x (t+periodicSite R n d) t) =
      b.centered d.val 0 (q i) (n:Boxes) := by simpa [origin,add_comm (periodicSite R n d)] using c i d.val 0
  have st (i : Axis) (d : R.dirs) (a e : Axis) : (avg fun t => (G n i).staticAt x t (t+periodicSite R n d) a e) =
      b.pair d a e (q i) (n:Boxes) := avg_eq _ _ fun t => (states i).static_matches _ (ψ i) d t a e
  apply Prod.ext
  · funext i; exact (congrArg Complex.re (c₀ i)).symm
  · funext d i k; let v := periodicSite R n d
    change _ = ![cosAmp (avg fun t => (G n i).centeredAt x t (t+v)) (avg fun t => (G n i).centeredAt x (t+v) t),
      sinAmp (avg fun t => (G n i).centeredAt x t (t+v)) (avg fun t => (G n i).centeredAt x (t+v) t),
      ((avg fun t => (G n i).staticAt x t (t+v) 0 0)-(avg fun t => (G n i).staticAt x t (t+v) 1 1)).re,
      ((avg fun t => (G n i).staticAt x t (t+v) 0 1)+(avg fun t => (G n i).staticAt x t (t+v) 1 0)).re] k
    dsimp only [v]; rw [plus,minus,st,st,st,st]; fin_cases k <;> rfl

end Cluster

/-- The physical family itself supplies the common radius, the coefficient
envelope and convergence of each coefficient in multilinear operator norm. -/
theorem periodic_ground_expansion : ∃ G : BoxCharts R, Nonempty (LocalGroundExpansion R G) := by
  obtain ⟨b⟩ := branch_exists R
  let a := fun q => (b.a q).val
  have ha : AnalyticAt ℂ a 0 := ((localSpace R).subtypeL.analyticAt _).comp b.analytic
  have hz : a 0=0 := by simp [a,b.zero]
  obtain ⟨G,chart,phy⟩ := charts_of_branch R a ha hz (ground_of_branch R a ha hz b.solves)
  refine ⟨G,expansion_of_continuous_family R G b.harmonics b.analytic_harmonics ?_ phy⟩
  have good : ∀ᶠ p in 𝓝 (0:Params R.dirs), ∀ i, b.good (sourceMap R i p) := by
    apply eventually_all.mpr; intro i
    exact ((sourceMap R i).continuous.continuousAt.tendsto.eventually (by simpa using b.eventually_good))
  filter_upwards [good] with p hp
  intro n
  let w := fun i => eigenKet ((b.a (sourceMap R i p)).val n)
  let u := fun i => WithLp.toLp 1 (normalize (w i))
  have ok (i) := normalized (w i) (ket_nonzero _)
  choose c _ amp normed using ok
  let states (i) : BoxState b n i p := {
    good := hp i, u := u i, c := c i,
    ket := by apply WithLp.ofLp_injective; funext k; exact amp i k,
    normed := by
      rw [bra_apply]
      change (∑ k, star (normalize (w i) k) * normalize (w i) k) = 1
      calc
        _ = ∑ k, (Complex.normSq (normalize (w i) k) : ℂ) :=
          Finset.sum_congr rfl fun k _ => (Complex.normSq_eq_conj_mul_self (z := normalize (w i) k)).symm
        _ = 1 := by rw [← Complex.ofReal_sum,normed,Complex.ofReal_one] }
  exact box_matches R b G n p states (fun i => (chart n i p).1) (fun i => (chart n i p).2)

/-- For a fixed finite oriented bond set in any dimension the thermodynamic
laboratory sine/cosine readout exists, has a uniform O(1/B) derivative and
value remainder, and identifies the entire physical coupling cube. -/
theorem fullAccessSF_lab_thermodynamic :
    let measured := fun B n p => originalLabels R n (groundPaperReadout
      (withParams (periodicBonds R n) (boxParams R n p)) B Subtype.val)
    ∃ M : ℝ → Params R.dirs → Harmonics R.dirs, ∃ C ≥ (0:ℝ), ∃ b > (0:ℝ), ∀ B ≥ b,
      Set.InjOn (M B) (couplingCube R.dirs) ∧ ∀ p ∈ couplingCube R.dirs,
        Tendsto (fun n => measured B n p) atTop (𝓝 (M B p)) ∧ DifferentiableAt ℝ (M B) p ∧
        ‖fderiv ℝ (fun q => M B q-leading q) p‖ ≤ C/B ∧ ‖M B p-leading p‖ ≤ (C/B)*‖p‖ := by
  obtain ⟨_,⟨expansion⟩⟩ := periodic_ground_expansion R
  exact fullAccessSF_lab_limit R expansion

end DSFTomography.SF
