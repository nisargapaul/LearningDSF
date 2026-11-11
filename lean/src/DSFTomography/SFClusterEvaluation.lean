import DSFTomography.SFClusterLocal

/-! Evaluation of a local cluster family at the vacuum has a thermodynamic
limit. Both the box evaluations and their limit have operator norm at most one. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter
open scoped Topology ENNReal
variable {ν : ℕ} (R : Bonds (Site ν))

def vacuumAt (n : ℕ) : Amplitudes R →L[ℂ] ℂ :=
  (PiLp.proj 1 (fun _ : Config (Box R n) => ℂ) 0).comp (atBox R n)

theorem vacuumAt_le (n : ℕ) (v : Amplitudes R) : ‖vacuumAt R n v‖ ≤ ‖v‖ :=
  (PiLp.norm_apply_le (p := 1) (v n) 0).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero v n)

theorem count_zero {S : Type*} [Fintype S] [DecidableEq S] (x : Config S) : flipCount x=0 ↔ x=0 := by
  simp [flipCount,Finset.filter_eq_empty_iff,funext_iff]

private theorem raw_converges (v : Amplitudes R) (hv : v ∈ raw R) :
    ∃ c : ℂ, ∀ᶠ n in atTop, vacuumAt R n v=c := by
  apply Submodule.span_induction (p := fun x _ => ∃ c : ℂ, ∀ᶠ n in atTop, vacuumAt R n x=c) _ _ _ _ hv
  · rintro x (⟨A,rfl⟩|h)
    · refine ⟨if weight A=0 then 1 else 0,(placed_count R A).mono fun n e => ?_⟩
      change atBox R n (localKet R A) 0 = _
      rw [localKet_at,basis_at]
      by_cases h : weight A=0
      · simp [h,(count_zero _).mp (e.trans h)]
      · simp [h,Ne.symm (fun z => h (e.symm.trans ((count_zero _).mpr z)))]
    · exact ⟨0,h.mono fun n e => by change atBox R n x 0=0; rw [e]; rfl⟩
  · exact ⟨0,Eventually.of_forall fun n => map_zero _⟩
  · rintro x y _ _ ⟨c,hc⟩ ⟨d,hd⟩
    exact ⟨c+d,(hc.and hd).mono fun n h => by simp [h.1,h.2]⟩
  · rintro c x _ ⟨d,hd⟩; exact ⟨c • d,hd.mono fun n h => by simp [h]⟩

theorem local_converges (v : ↥(localSpace R)) :
    ∃ c : ℂ, Tendsto (fun n => vacuumAt R n v.val) atTop (𝓝 c) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff'.mpr; intro ε pos
  obtain ⟨x,hx,near⟩ := Metric.mem_closure_iff.mp v.property (ε/2) (by positivity)
  obtain ⟨c,hc⟩ := raw_converges R x hx
  obtain ⟨N,hN⟩ := eventually_atTop.mp hc
  refine ⟨N,fun n hn => ?_⟩
  have err (k) : dist (vacuumAt R k v.val) (vacuumAt R k x) < ε/2 := by
    rw [dist_eq_norm,← map_sub]; exact (vacuumAt_le R _ _).trans_lt near
  calc
    _ ≤ dist (vacuumAt R n v.val) c + dist c (vacuumAt R N v.val) := dist_triangle _ _ _
    _ < ε := by
      have e₁ := err n; have e₂ := err N
      rw [hN n hn] at e₁; rw [hN N le_rfl,dist_comm] at e₂; linarith

def vacuumLimit : ↥(localSpace R) →L[ℂ] ℂ :=
  LinearMap.mkContinuous {
    toFun := fun v => (local_converges R v).choose
    map_add' := fun v w => tendsto_nhds_unique (local_converges R (v+w)).choose_spec
      ((local_converges R v).choose_spec.add (local_converges R w).choose_spec)
    map_smul' := fun c v => tendsto_nhds_unique (local_converges R (c • v)).choose_spec
      ((local_converges R v).choose_spec.const_smul c) }
    1 (by
      intro v; rw [one_mul]
      exact le_of_tendsto (local_converges R v).choose_spec.norm (Eventually.of_forall fun n => vacuumAt_le R n v.val))

theorem tendsto_vacuum (v : ↥(localSpace R)) :
    Tendsto (fun n => vacuumAt R n v.val) atTop (𝓝 (vacuumLimit R v)) := (local_converges R v).choose_spec

end DSFTomography.SF.Cluster
