import DSFTomography.HTLimit
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter
open scoped Topology

/-- The local cluster-expansion input in a smaller closed temperature interval.
Entry k in the tail is the coefficient of β^(k+2). Each fixed-order coefficient
stabilizes on sufficiently large boxes. A single summable envelope bounds the
series there. The first derivative in the expansion is the actual finite-volume
DSF derivative, whose value is computed by the HT theorem. -/
structure LocalExpansion (f : ℕ → ℝ → ℂ) where
  radius : ℝ
  positive : 0 < radius
  constant : ℂ
  tail : ℕ → ℕ → ℂ
  bulkTail : ℕ → ℂ
  localizes : ∀ k, ∀ᶠ L in atTop, tail L k = bulkTail k
  envelope : ℕ → ℝ
  summable : Summable envelope
  bound : ∀ L k, radius^k * ‖tail L k‖ ≤ envelope k
  expansion : ∀ L β, β ∈ Set.Icc 0 radius →
    f L β = constant + β • derivWithin (f L) (Set.Ici 0) 0 +
      β^2 • ∑' k : ℕ, β^k • tail L k

variable {S : ℕ → Type*} [∀ L, AddCommGroup (S L)] [∀ L, Fintype (S L)] [∀ L, DecidableEq (S L)]
  (V : ∀ L, Volume (S L)) (c : ∀ L, Channel (S L)) (v : ℂ)

/-- From the local expansion, construct the thermodynamic observable itself
on the common interval and compute its derivative. Existence of the
positive-temperature thermodynamic limit is a conclusion here. -/
theorem bulkFromLocalExpansion
    (fixed : ∀ᶠ L in atTop, (V L).valid (c L) ∧ (V L).target (c L) = v)
    (A : LocalExpansion (fun L => (V L).observable (c L))) :
    ∃ f : ℝ → ℂ, (∀ β ∈ Set.Icc 0 A.radius,
      Tendsto (fun L => (V L).observable (c L) β) atTop (𝓝 (f β))) ∧
      HasDerivWithinAt f v (Set.Ici 0) 0 := by
  let f := fun β : ℝ => A.constant + β • v + β^2 • ∑' k : ℕ, β^k • A.bulkTail k
  have major (L : ℕ) (β : ℝ) (hb : β ∈ Set.Icc 0 A.radius) (k : ℕ) :
      ‖β^k • A.tail L k‖ ≤ A.envelope k := by
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.1 hb.2 k) (norm_nonneg _)).trans
      (A.bound L k)
  have lim (β : ℝ) (hb : β ∈ Set.Icc 0 A.radius) :
      Tendsto (fun L => (V L).observable (c L) β) atTop (𝓝 (f β)) := by
    have ht := tendsto_tsum_of_dominated_convergence (f := fun L k => β^k • A.tail L k)
      (g := fun k => β^k • A.bulkTail k) A.summable
      (fun k => tendsto_const_nhds.congr' ((A.localizes k).mono (fun _ h => congrArg (fun z : ℂ => β^k • z) h.symm)))
      (Eventually.of_forall (fun L k => major L β hb k))
    apply (tendsto_const_nhds.add (ht.const_smul (β^2))).congr'
    filter_upwards [slope_stabilizes V c v fixed] with L hs
    rw [A.expansion L β hb, hs]
  have small : ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ici 0), β ∈ Set.Icc 0 A.radius :=
    Icc_mem_nhdsGE A.positive
  refine ⟨f,lim,thermodynamic_slope V c v f fixed (small.mono (fun β hb => lim β hb)) ?_⟩
  refine ⟨∑' k, A.envelope k, small.mono (fun β hb => Eventually.of_forall (fun L => ?_))⟩
  have sums : Summable (fun k : ℕ => ‖β^k • A.tail L k‖) :=
    A.summable.of_nonneg_of_le (fun _ => norm_nonneg _) (major L β hb)
  have sz := (norm_tsum_le_tsum_norm sums).trans (sums.tsum_le_tsum (major L β hb) A.summable)
  have origin := A.expansion L 0 (show 0 ∈ Set.Icc (0 : ℝ) A.radius from ⟨le_rfl,A.positive.le⟩)
  simp at origin
  rw [A.expansion L β hb, origin]
  have cancel (x y z : ℂ) : x+y+z-x-y=z := by abel
  simp only [cancel, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hb.1, mul_comm _ (β^2)]
  exact mul_le_mul_of_nonneg_left sz (sq_nonneg β)

end DSFTomography.HT
