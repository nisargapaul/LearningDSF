import DSFTomography.HTSpectrum
import Mathlib.Data.ZMod.Basic

/-! Finite-size stabilization and the derivative of a thermodynamic observable. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter Asymptotics
open scoped Topology

/-- Side length L+1 guarantees a nonempty finite period for every sequence index. -/
def reduceBond {ν : ℕ} (L : ℕ) (d : Fin ν → ℤ) : Fin ν → ZMod (L+1) :=
  fun i => d i

/-- Take K to include zero, all displacements in R, and their negatives.
Eventually the torus distinguishes every one of these labels. -/
theorem eventually_resolves {ν : ℕ} (K : Finset (Fin ν → ℤ)) :
    ∀ᶠ L : ℕ in atTop, Set.InjOn (reduceBond L) (K : Set (Fin ν → ℤ)) := by
  have sep (x y : Fin ν → ℤ) : ∀ᶠ L : ℕ in atTop, reduceBond L x = reduceBond L y → x=y := by
    by_cases eq : x=y
    · exact Eventually.of_forall (fun _ _ => eq)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp eq
    filter_upwards [eventually_gt_atTop (y i - x i).natAbs] with L hL
    intro same
    have dvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (y i) (L+1)).mp (congrFun same i)
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs dvd (by simpa using hL.trans (Nat.lt_succ_self L))
    exact (hi (sub_eq_zero.mp hz).symm).elim
  exact (K.eventually_all.mpr (fun x _ =>
    K.eventually_all.mpr (fun y _ => sep x y))).mono (fun _ h x hx y hy => h x hx y hy)

/-- The physical input for one periodic volume. Its eigenbasis is constructed by the spectral theorem. -/
structure Volume (S : Type*) [AddCommGroup S] [Fintype S] [DecidableEq S] where
  R : Bonds S
  h : Axis → ℝ
  J : S → Matrix Axis Axis ℝ

/-- The channels required by the full-access inverse. -/
inductive Channel (S : Type*)
  | bond (d : S) (a b : Axis)
  | onsite (k : Axis)

namespace Volume
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def valid (V : Volume S) : Channel S → Prop
  | .bond d _ _ => d ∈ V.R.dirs
  | .onsite _ => True

def target (V : Volume S) : Channel S → ℂ
  | .bond d a b => -(V.J d a b : ℂ)
  | .onsite k => -(Complex.I * V.h k)

def observable (V : Volume S) (c : Channel S) : ℝ → ℂ := match c with
  | .bond d a b => staticHarmonic (gibbsStaticDSF V.R V.h V.J) d a b
  | .onsite k => staticHarmonic (gibbsStaticDSF V.R V.h V.J) 0 (k+1) (k+2)

private theorem scan_harmonic (V : Volume S) (d : S) (a b : Axis) :
    staticHarmonic (gibbsStaticDSF V.R V.h V.J) d a b =
      fun β => (thermalMoments (qubitSpins (energyBasis V.R V.h V.J)) β (energies V.R V.h V.J)).static d a b := by
  funext β
  exact harmonic_toMomentum _ _

theorem derivative (V : Volume S) (c : Channel S) (valid : V.valid c) :
    HasDerivAt (V.observable c) (V.target c) 0 := by
  cases c with
  | bond d a b =>
    simpa only [observable, target, scan_harmonic] using
      static_bond_deriv (qubitSpins (energyBasis V.R V.h V.J)) (energyBasis V.R V.h V.J)
        (fun _ _ => rfl) V.R V.h V.J (energies V.R V.h V.J) (diagonalized V.R V.h V.J) valid a b
  | onsite k =>
    simpa only [observable, target, scan_harmonic] using
      static_field_deriv (qubitSpins (energyBasis V.R V.h V.J)) (energyBasis V.R V.h V.J)
        (fun _ _ => rfl) V.R V.h V.J (energies V.R V.h V.J) (diagonalized V.R V.h V.J) k
end Volume

variable {S : ℕ → Type*} [∀ L, AddCommGroup (S L)] [∀ L, Fintype (S L)] [∀ L, DecidableEq (S L)]
  (V : ∀ L, Volume (S L)) (c : ∀ L, Channel (S L)) (v : ℂ)

/-- Fix one physical coupling and follow its channel through the boxes.
The first Taylor coefficient is eventually exactly equal to its bulk value. -/
theorem slope_stabilizes
    (fixed : ∀ᶠ L in atTop, (V L).valid (c L) ∧ (V L).target (c L) = v) :
    ∀ᶠ L in atTop, derivWithin ((V L).observable (c L)) (Set.Ici 0) 0 = v := by
  filter_upwards [fixed] with L hL
  exact ((V L).derivative (c L) hL.1).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici 0) |>.trans hL.2

/-- If the local static moments have a pointwise bulk limit and a volume-uniform
quadratic Taylor remainder, the measured bulk moment has the same physical
right derivative. Both analytic inputs are explicit and local to this channel. -/
theorem thermodynamic_slope (f : ℝ → ℂ)
    (fixed : ∀ᶠ L in atTop, (V L).valid (c L) ∧ (V L).target (c L) = v)
    (hlim : ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ici 0),
      Tendsto (fun L => (V L).observable (c L) β) atTop (𝓝 (f β)))
    (uniform : ∃ C : ℝ, ∀ᶠ β in nhdsWithin (0 : ℝ) (Set.Ici 0), ∀ᶠ L in atTop,
      ‖(V L).observable (c L) β - (V L).observable (c L) 0 -
        β • derivWithin ((V L).observable (c L)) (Set.Ici 0) 0‖ ≤ C * β^2) :
    HasDerivWithinAt f v (Set.Ici 0) 0 := by
  obtain ⟨C, hC⟩ := uniform
  have h0 := hlim.self_of_nhdsWithin (by simp)
  rw [hasDerivWithinAt_iff_isLittleO]
  simp only [sub_zero]
  refine (IsBigO.of_bound C ?_).trans_isLittleO
    ((isLittleO_pow_id (𝕜 := ℝ) (show 1 < 2 by decide)).mono nhdsWithin_le_nhds)
  filter_upwards [hlim, hC] with β hβ bound
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg β)]
  apply le_of_tendsto (((hβ.sub h0).sub_const (β • v)).norm)
  filter_upwards [bound, slope_stabilizes V c v fixed] with L hL hs
  simpa only [hs] using hL

end DSFTomography.HT
