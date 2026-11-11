import DSFTomography.HTSeries

/-! The standard growing periodic boxes for a fixed interaction on ℤ^ν. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter
variable {ν : ℕ}
abbrev Site (ν : ℕ) := Fin ν → ℤ

/-- Finite set that must embed to retain all directed bond information. -/
private def labels (R : Bonds (Site ν)) :=
  insert 0 (R.dirs ∪ R.dirs.image Neg.neg)

private theorem threshold_exists (R : Bonds (Site ν)) :
    ∃ n : ℕ, ∀ L ≥ n, Set.InjOn (reduceBond L) (labels R : Set (Site ν)) :=
  eventually_atTop.mp (eventually_resolves (labels R))

/-- Skip the finite initial set of possibly aliased periodic volumes. -/
def periodIndex (R : Bonds (Site ν)) (n : ℕ) := (threshold_exists R).choose + n

private theorem injects (R : Bonds (Site ν)) (n : ℕ) :
    Set.InjOn (reduceBond (periodIndex R n)) (labels R : Set (Site ν)) :=
  (threshold_exists R).choose_spec _ (Nat.le_add_right _ _)

theorem injects_dirs (R : Bonds (Site ν)) (n : ℕ) :
    Set.InjOn (reduceBond (periodIndex R n)) (R.dirs : Set (Site ν)) :=
  (injects R n).mono (fun _ hx => by simp [labels,hx])

abbrev Box (R : Bonds (Site ν)) (n : ℕ) := Fin ν → ZMod (periodIndex R n + 1)

def periodicBonds (R : Bonds (Site ν)) (n : ℕ) : Bonds (Box R n) where
  dirs := R.dirs.image (reduceBond (periodIndex R n))
  nonzero := by
    intro x hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    intro hz
    apply R.nonzero d hd
    apply injects R n (by simp [labels, hd]) (by simp [labels])
    simpa [reduceBond] using hz
  oriented := by
    intro x hx y hy
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hy
    intro hz
    have hde : d = -e := by
      apply injects R n (by simp [labels, hd]) (by simp [labels, he])
      have same := eq_neg_of_add_eq_zero_left hz
      funext i
      simpa [reduceBond] using congrFun same i
    exact R.oriented d hd e he (by simp [hde])

/-- Periodize the same physical coefficients in each box. -/
def periodicVolume (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
    (n : ℕ) : Volume (Box R n) where
  R := periodicBonds R n
  h := h
  J x := ∑ d ∈ R.dirs, if reduceBond (periodIndex R n) d = x then J d else 0

theorem image_coupling (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
    (n : ℕ) {d : Site ν} (hd : d ∈ R.dirs) :
    (periodicVolume R h J n).J (reduceBond (periodIndex R n) d) = J d := by
  simp only [periodicVolume]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hne
    have ne : reduceBond (periodIndex R n) e ≠ reduceBond (periodIndex R n) d :=
      fun eq => hne (injects R n (by simp [labels,he]) (by simp [labels,hd]) eq)
    simp [ne]
  · simp [hd]

def periodicChannel (R : Bonds (Site ν)) (c : Channel (Site ν)) (n : ℕ) : Channel (Box R n) :=
  match c with
  | .bond d a b => .bond (reduceBond (periodIndex R n) d) a b
  | .onsite k => .onsite k

/-- On every sufficiently large periodic box, all inferred exchanges and fields
are exactly their original infinite-lattice coefficients. -/
theorem periodic_recovery (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
    (n : ℕ) :
    let V := periodicVolume R h J n
    let D := gibbsStaticDSF V.R V.h V.J
    (∀ d ∈ R.dirs, exchange D (reduceBond (periodIndex R n) d) = fun a b => (J d a b : ℂ)) ∧
      field D = fun k => (h k : ℂ) := by
  intro V D
  obtain ⟨bonds, fields⟩ := fullAccessHT V.R V.h V.J
  refine ⟨?_, fields⟩
  intro d hd
  have mem : reduceBond (periodIndex R n) d ∈ V.R.dirs := Finset.mem_image_of_mem _ hd
  simpa only [V, image_coupling R h J n hd] using bonds _ mem

/-- Slope read out by the chosen channel of the infinite-lattice model. -/
def channelTarget (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ) : Channel (Site ν) → ℂ
  | .bond d a b => -(J d a b : ℂ)
  | .onsite k => -(Complex.I * h k)

/-- The target of a valid channel is independent of the period. -/
theorem periodic_channel_target (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
    (c : Channel (Site ν)) (valid : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True)
    (n : ℕ) :
    (periodicVolume R h J n).valid (periodicChannel R c n) ∧
    (periodicVolume R h J n).target (periodicChannel R c n) =
      channelTarget h J c := by
  cases c with
  | bond d a b =>
    exact ⟨Finset.mem_image_of_mem _ valid, by
      simp only [periodicChannel, channelTarget, Volume.target, image_coupling R h J n valid]⟩
  | onsite k => exact ⟨trivial,rfl⟩

/-- The slope of the bulk moment for a fixed channel of an actual lattice
Hamiltonian, conditional on its local high-temperature expansion. -/
theorem periodic_bulk (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
    (c : Channel (Site ν)) (valid : match c with | .bond d _ _ => d ∈ R.dirs | .onsite _ => True)
    (A : LocalExpansion (fun n => (periodicVolume R h J n).observable (periodicChannel R c n))) :
    ∃ f : ℝ → ℂ, (∀ β ∈ Set.Icc 0 A.radius, Tendsto
      (fun n => (periodicVolume R h J n).observable (periodicChannel R c n) β) atTop (nhds (f β))) ∧
      HasDerivWithinAt f (channelTarget h J c) (Set.Ici 0) 0 := by
  apply bulkFromLocalExpansion (periodicVolume R h J) (periodicChannel R c) _ _ A
  exact Eventually.of_forall (periodic_channel_target R h J c valid)

end DSFTomography.HT
