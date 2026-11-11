import DSFTomography.DSFBoxSpectra
import DSFTomography.DSFCutoffMoments

/-! Infinite-volume real-time correlations, their Fourier distributions, and
all spectral moments. Any growing sequence can be refined; limits already
certified on the original sequence are preserved. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord Filter Set MeasureTheory
open scoped Topology

abbrev LocalChannel (ν : ℕ) := Site ν × Axis × Axis
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def channelLines (p : ∀ n, Config (Box R n) → ℝ) (n : ℕ) (c : LocalChannel ν) :=
  boxLines R h J p n c.1 c.2.1 c.2.2

structure BulkDSF (p : ∀ n, Config (Box R n) → ℝ) (volumes : ℕ → ℕ) where
  select : ℕ → ℕ
  increasing : StrictMono select
  time : LocalChannel ν → C(ℝ,ℂ)
  moment : LocalChannel ν → ℕ → ℂ
  time_limit : ∀ c, Tendsto (fun n => (channelLines R h J p (volumes (select n)) c).timeMap) atTop (𝓝 (time c))
  moment_limit : ∀ c k, Tendsto (fun n => (channelLines R h J p (volumes (select n)) c).moment k) atTop (𝓝 (moment c k))

/-- A countable family of experiments shares one subsequence for its real-time
correlations and all moments. Compactness is applied to both data sets at once. -/
theorem family_bulkDSF_exists {I : Type*} [Countable I]
    (h : I → Axis → ℝ) (J : I → Site ν → Matrix Axis Axis ℝ)
    (p : I → ∀ n, Config (Box R n) → ℝ)
    (positive : ∀ i n j, 0 ≤ p i n j) (normed : ∀ i n, ∑ j, p i n j = 1)
    (volumes : ℕ → ℕ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ i, ∃ D : BulkDSF R (h i) (J i) (p i) volumes, D.select = s := by
  let lipschitz : I → NNReal := fun i => ⟨momentBound R (h i) (J i) 1,by
    have := incidentBound_pos R (h i) (J i); unfold momentBound; positivity⟩
  let lines := fun n (c : I × LocalChannel ν) => channelLines R (h c.1) (J c.1) (p c.1) (volumes n) c.2
  let timeData := fun n c => (lines n c).timeMap
  let momentData := fun n (c : (I × LocalChannel ν) × ℕ) => (lines n c.1).moment c.2
  have timeCompact : IsCompact (Set.univ.pi fun c : I × LocalChannel ν => controlled 1 (lipschitz c.1)) :=
    isCompact_univ_pi fun c => controlled_compact 1 (lipschitz c.1)
  have momentCompact : IsCompact (Set.univ.pi fun c : (I × LocalChannel ν) × ℕ =>
      Metric.closedBall (0:ℂ) ((2*Real.pi)*momentBound R (h c.1.1) (J c.1.1) c.2)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have bounds (n : ℕ) (c : I × LocalChannel ν) (k : ℕ) :
      (lines n c).absMoment k ≤ momentBound R (h c.1) (J c.1) k :=
    box_absMoment_bound R (h c.1) (J c.1) (p c.1) (positive c.1) (normed c.1) (volumes n) _ _ _ k
  have timeMem (n : ℕ) : timeData n ∈ Set.univ.pi (fun c => controlled 1 (lipschitz c.1)) := by
    intro c _
    apply Lines.timeMap_controlled
    · simpa [momentBound] using bounds n c 0
    · exact bounds n c 1
  have momentMem (n : ℕ) : momentData n ∈ Set.univ.pi (fun c : (I × LocalChannel ν) × ℕ =>
      Metric.closedBall (0:ℂ) ((2*Real.pi)*momentBound R (h c.1.1) (J c.1.1) c.2)) := by
    intro c _
    simpa only [Metric.mem_closedBall,dist_zero_right] using ((lines n c.1).moment_bound c.2).trans
      (mul_le_mul_of_nonneg_left (bounds n c.1 c.2) (by positivity))
  obtain ⟨limit, _, subseq, increasing, convergence⟩ :=
    (timeCompact.prod momentCompact).tendsto_subseq
      (x := fun n => (timeData n, momentData n)) (fun n => ⟨timeMem n, momentMem n⟩)
  refine ⟨subseq,increasing,fun i => ⟨⟨subseq,increasing,fun c => limit.1 (i,c),fun c k => limit.2 ((i,c),k),?_,?_⟩,rfl⟩⟩
  · intro c
    exact ((continuous_apply (i,c)).tendsto limit.1).comp (continuous_fst.tendsto limit |>.comp convergence)
  · intro c k
    exact ((continuous_apply ((i,c),k)).tendsto limit.2).comp (continuous_snd.tendsto limit |>.comp convergence)

theorem bulkDSF_exists (p : ∀ n, Config (Box R n) → ℝ)
    (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1) (volumes : ℕ → ℕ) :
    Nonempty (BulkDSF R h J p volumes) := by
  obtain ⟨_, _, limits⟩ := family_bulkDSF_exists R
    (fun _ : Unit => h) (fun _ => J) (fun _ => p)
    (fun _ => positive) (fun _ => normed) volumes
  exact ⟨(limits ()).choose⟩

/-- Fixed-temperature Gibbs DSFs exist on a growing subsequence, with no
high-temperature or nondegeneracy hypothesis. -/
theorem gibbsDSF_exists (β : ℝ) : Nonempty (BulkDSF R h J (gibbsPop R h J β) id) :=
  bulkDSF_exists R h J _ (gibbsPop_positive R h J β) (gibbsPop_normalized R h J β) id

namespace BulkDSF
variable {R h J} {p : ∀ n, Config (Box R n) → ℝ} {volumes : ℕ → ℕ}
variable (D : BulkDSF R h J p volumes)

theorem volumes_grow (growing : Tendsto volumes atTop atTop) :
    Tendsto (volumes ∘ D.select) atTop atTop := growing.comp D.increasing.tendsto_atTop

theorem pointwise_time (c : LocalChannel ν) (t : ℝ) :
    Tendsto (fun n => (channelLines R h J p (volumes (D.select n)) c).correlation t) atTop (𝓝 (D.time c t)) := by
  have cont : Continuous (fun f : C(ℝ,ℂ) => f t) := by fun_prop
  exact (cont.tendsto (D.time c)).comp (D.time_limit c)

def spectrum (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (c : LocalChannel ν) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  limitDistribution (fun n => channelLines R h J p (volumes (D.select n)) c) (D.time c) 1 (by norm_num)
    (fun n => by simpa [momentBound] using box_absMoment_bound R h J p positive normed (volumes (D.select n)) c.1 c.2.1 c.2.2 0)
    (D.pointwise_time c)

theorem spectrum_time (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (c : LocalChannel ν) (f : SchwartzMap ℝ ℂ) :
    D.spectrum positive normed c f = ∫ t, D.time c t*angularTest f t := rfl

theorem spectrum_limit (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (c : LocalChannel ν) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (channelLines R h J p (volumes (D.select n)) c).distribution f) atTop
      (𝓝 (D.spectrum positive normed c f)) :=
  distribution_tendsto _ _ 1
    (fun n => by simpa [momentBound] using box_absMoment_bound R h J p positive normed (volumes (D.select n)) c.1 c.2.1 c.2.2 0)
    (D.pointwise_time c) f

theorem spectral_moments (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (c : LocalChannel ν) (k : ℕ) : HasSpectralMoment (D.spectrum positive normed c) k (D.moment c k) :=
  limit_spectral_moment _ _ (D.spectrum_limit positive normed c) k _ (D.moment_limit c k)
    (momentBound R h J (k+1))
    (fun n => box_absMoment_bound R h J p positive normed (volumes (D.select n)) c.1 c.2.1 c.2.2 (k+1))

/-- Every previously established thermodynamic moment remains unchanged upon
constructing the full time-dependent spectrum. -/
theorem agrees_with_certified_limit (c : LocalChannel ν) (k : ℕ) (m : ℂ)
    (certified : Tendsto (fun n => (channelLines R h J p (volumes n) c).moment k) atTop (𝓝 m)) :
    D.moment c k = m :=
  tendsto_nhds_unique (D.moment_limit c k) (certified.comp D.increasing.tendsto_atTop)

end BulkDSF
/-- The limit is of the actual normalized Heisenberg Gibbs trace, not merely
an abstract family having specified moments. -/
theorem gibbs_real_time_limit (β : ℝ) (D : BulkDSF R h J (gibbsPop R h J β) id)
    (d : Site ν) (a b : Axis) (t : ℝ) :
    Tendsto (fun n => avg (fun r : Box R (D.select n) =>
      physicalCorrelation (periodicVolume R h J (D.select n)) β t
        (word (oneLabel r a)) (word (oneLabel (r+place R (D.select n) d) b))))
      atTop (𝓝 (D.time (d,a,b) t)) := by
  simpa only [channelLines,id_eq,box_time_gibbs] using D.pointwise_time (d,a,b) t

end DSFTomography.Spectral
