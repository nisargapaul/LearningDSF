import DSFTomography.HTUniform

/-! Full-access HT reconstruction after the periodic volume limit. No cluster
expansion, limiting state, or estimate on a partition function is an input. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter Metric LocalWord
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

private def probeWord : Channel (Site ν) → Script (Site ν)
  | .bond d a b => [(0,a),(d,b)]
  | .onsite k => [(0,k+1),(0,k+2)]

private theorem value_probe (c : Channel (Site ν)) (n : ℕ) (z : ℂ) :
    value R h J (probeWord c) n z = (periodicVolume R h J n).localGibbs (periodicChannel R c n) z := by
  rw [value,state_apply,Volume.localGibbs]
  have zero : place R n 0 = 0 := by funext i; simp [place,periodicSite,reduceBond]
  have spin (s : Box R n) (a : Axis) : (qubitSpins (1 : (Op (Config (Box R n)))ˣ)).σ s a = word (oneLabel s a) := by
    simp [qubitSpins,string,inBasis]
  have eq : eval (place R n) (probeWord c) = Volume.probe (periodicChannel R c n) 0 := by
    cases c with
    | bond d a b => change eval (place R n) [(0,a),(d,b)] = (qubitSpins 1).σ 0 a * (qubitSpins 1).σ (0+place R n d) b; simp [spin,zero]
    | onsite k => change eval (place R n) [(0,k+1),(0,k+2)] = (qubitSpins 1).σ 0 (k+1) * (qubitSpins 1).σ 0 (k+2); simp [spin,zero]
  rw [eq]

/-- The periodic local Gibbs traces are uniformly Cauchy on a common closed disk. -/
theorem periodic_uniformCauchy (c : Channel (Site ν)) :
    UniformCauchySeqOn (fun n => (periodicVolume R h J n).localGibbs (periodicChannel R c n))
      atTop (closedBall 0 (diskRadius R h J)) := by
  rw [← show value R h J (probeWord c) = _ from funext fun n => funext (value_probe R h J c n)]
  exact uniform R h J (probeWord c)

/-- Uniform convergence at fixed complex inverse temperature on the closed disk.
The limit function is constructed from the periodic traces themselves. -/
theorem periodic_uniformLimit (c : Channel (Site ν)) :
    let F := fun n => (periodicVolume R h J n).localGibbs (periodicChannel R c n)
    TendstoUniformlyOn F (fun z => limUnder atTop (fun n => F n z))
      atTop (closedBall 0 (diskRadius R h J)) := by
  intro F
  have hc := periodic_uniformCauchy R h J c
  exact hc.tendstoUniformlyOn_of_tendsto (fun _ hz => (hc.cauchySeq hz).tendsto_limUnder)

private theorem regular_disk : ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) (diskRadius R h J),
    (periodicVolume R h J n).partition z ≠ 0 := by
  refine Eventually.of_forall fun n z hz => (periodic_zeroFree_bounded R h J n z ?_).1
  have hh : ‖z‖ < diskRadius R h J := by simpa [mem_ball] using hz
  have pos := bulkRadius_pos R h J
  unfold diskRadius at hh; linarith

theorem bulk_static_derivative (c : Channel (Site ν))
    (valid : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True) :
    (∀ β : ℝ, |β| < diskRadius R h J → Tendsto
       (fun n => (periodicVolume R h J n).observable (periodicChannel R c n) β)
       atTop (𝓝 (bulkHarmonic R h J c β))) ∧
    HasDerivAt (bulkHarmonic R h J c) (channelTarget h J c) 0 :=
  periodic_limit_then_derivative R h J c valid (diskRadius_pos ..) (regular_disk ..)
    ((periodic_uniformCauchy R h J c).mono Metric.ball_subset_closedBall)

/-- An independently supplied positive-temperature measurement has the same
inverse when it is the limit of the finite-volume calibrated DSF harmonics. -/
theorem fullAccessHT_from_bulk_data (D : Channel (Site ν) → ℝ → ℂ)
    (observed : ∀ c, (match c with | Channel.bond d _ _ => d ∈ R.dirs | .onsite _ => True) →
      ∀ᶠ β in 𝓝[>] (0 : ℝ), Tendsto
        (fun n => (periodicVolume R h J n).observable (periodicChannel R c n) β) atTop (𝓝 (D c β))) :
    (∀ d ∈ R.dirs, ∀ a b, -positiveSlope (D (.bond d a b)) = (J d a b : ℂ)) ∧
    (∀ k, Complex.I * positiveSlope (D (.onsite k)) = (h k : ℂ)) :=
  fullAccessHT_bulk R h J (diskRadius_pos R h J) (regular_disk R h J)
    (fun c _ => (periodic_uniformCauchy R h J c).mono Metric.ball_subset_closedBall) D observed

/-- Recover the Hamiltonian from the positive-temperature limiting DSF. -/
theorem fullAccessHT_thermodynamic :
    (∀ d ∈ R.dirs, ∀ a b, -positiveSlope (bulkHarmonic R h J (.bond d a b)) = (J d a b : ℂ)) ∧
    (∀ k, Complex.I * positiveSlope (bulkHarmonic R h J (.onsite k)) = (h k : ℂ)) := by
  apply fullAccessHT_from_bulk_data R h J
  intro c hc
  have near : ∀ᶠ β in 𝓝[>] (0 : ℝ), β ∈ ball (0 : ℝ) (diskRadius R h J) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (diskRadius_pos ..))
  exact near.mono fun β hb => (bulk_static_derivative R h J c hc).1 β (by simpa [mem_ball,Real.dist_eq] using hb)
end DSFTomography.HT
