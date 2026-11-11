import DSFTomography.DSFInfiniteRecovery

/-! Simultaneous thermodynamic spectra for multiple measurement Hamiltonians.
One common volume subsequence is used; in particular, the three SF field
orientations are not allowed independent volume selections. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord Filter Set
open scoped Topology

variable {ν : ℕ} (R : Bonds (Site ν)) {I : Type*} [Countable I]
  (h : I → Axis → ℝ) (J : I → Site ν → Matrix Axis Axis ℝ)
  (p : I → ∀ n, Config (Box R n) → ℝ)

/-- Any countable family of stationary experiments admits a common subsequence
for its real-time correlations and all spectral moments. -/
theorem joint_bulkDSF_exists
    (positive : ∀ i n j, 0 ≤ p i n j) (normed : ∀ i n, ∑ j, p i n j=1) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i, ∃ D : BulkDSF R (h i) (J i) (p i) id, D.select = s :=
  family_bulkDSF_exists R h J p positive normed id

end DSFTomography.Spectral
