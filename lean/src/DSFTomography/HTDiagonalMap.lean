import DSFTomography.HTDiagonalField
import DSFTomography.HTGeneric
import Mathlib.Analysis.Complex.RealDeriv

/-! Parameterization by the three laboratory fields and nine ordered exchanges
per bond. The feature index uses the same finite type: the last index selects
static slope, second moment, or real slope of the second moment. -/
noncomputable section
namespace DSFTomography.HT.Diagonal
open DSFTomography HT
open scoped ContDiff
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
variable (R : Bonds S)
abbrev Index := Axis ⊕ (R.dirs × Axis × Axis)
abbrev Params := V (Index R)
def fields (p : Params R) (a : Axis) := p (.inl a)
def exch (p : Params R) (d : S) (a b : Axis) : ℝ :=
  if hd : d ∈ R.dirs then p (.inr (⟨d,hd⟩,a,b)) else 0
abbrev ham (p : Params R) := qubitH R (fields R p) (exch R p)
def qt (p : Params R) (d : R.dirs) (u v : Axis) := (quadraticCorrelation (ham R p) d.val u v).re

def minorRow (J : Axis → Axis → ℝ) (a : Axis) :=
  -8*(J (a+1) (a+1)*J (a+2) (a+2) - J (a+1) (a+2)*J (a+2) (a+1))

/-- At aux=false this is exactly the polynomial map. The alternative row
is used only in the proof to remove a vanishing scalar from the Jacobian. -/
def polynomialRows (aux : Bool) (p : Params R) : Params R
  | .inl a => onsiteRow (ham R p) a
  | .inr (d,a,k) =>
    let J := exch R p d
    ![-J a a, if aux then J (a+1) (a+2)-J (a+2) (a+1) else minorRow J a,
      contract (qt R p d) J a] k

/-- Only the three diagonal spin components are present in either scan.
Both momentum moments are normalized by 2π. -/
structure DiagonalData (S : Type*) [AddCommGroup S] where
  static : ℝ → Momentum S → Axis → ℂ
  second : ℝ → Momentum S → Axis → ℂ

def readout (D : DiagonalData S) : Params R
  | .inl a => (harmonic (fun q => D.second 0 q a) 0).re
  | .inr (d,a,k) =>
    let c := fun β => harmonic (fun q => D.second β q a) d.val
    let s := fun β => harmonic (fun q => D.static β q a) d.val
    ![(derivWithin s (Set.Ici 0) 0).re,(c 0).re,(derivWithin c (Set.Ici 0) 0).re] k

def gibbsData (p : Params R) : DiagonalData S where
  static β q a := gibbsStaticDSF R (fields R p) (exch R p) β q a a
  second := scan (qubitSpins (energyBasis R (fields R p) (exch R p)))
    (energies R (fields R p) (exch R p))

/-- Eq. (FdiagI), divided by 2π, evaluated on the physical Gibbs DSF. -/
def paperFeatures (p : Params R) := readout R (gibbsData R p)

theorem paper_eq : paperFeatures R = polynomialRows R false := by
  funext p i
  cases i with
  | inl a => exact onsite_zero _ _ _ _
  | inr i =>
    obtain ⟨d,a,k⟩ := i
    have static := congrFun (congrFun ((fullAccessHT R (fields R p) (exch R p)).1 d.val d.property) a) a
    change -staticSlope _ _ _ _ = _ at static
    have hs := congrArg Complex.re (neg_eq_iff_eq_neg.mp static)
    rcases (show k=0 ∨ k=1 ∨ k=2 by fin_cases k <;> decide) with rfl|rfl|rfl
    · exact hs
    · exact bond_zero _ _ _ d.property _
    · exact bond_slope _ _ _ d.property _

omit [Fintype S] in
@[local fun_prop] theorem exch_smooth (d : S) (a b : Axis) : ContDiff ℝ ω (fun p => exch R p d a b) := by
  unfold exch
  split <;> fun_prop

@[local fun_prop] private theorem ham_smooth (i j : Config S) : ContDiff ℝ ω (fun p => ham R p i j) := by
  simp only [ham,qubitH,realH,H,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  unfold fields
  have ofR : ContDiff ℝ ω Complex.ofReal := Complex.ofRealCLM.contDiff
  fun_prop

@[local fun_prop] theorem qt_smooth (d : R.dirs) (u v : Axis) : ContDiff ℝ ω (fun p => qt R p d u v) := by
  simp only [qt,quadraticCorrelation,avg,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  have reS : ContDiff ℝ ω Complex.re := Complex.reCLM.contDiff
  simp only [div_eq_mul_inv]
  fun_prop

theorem onsite_smooth (a : Axis) : ContDiff ℝ ω (fun p => onsiteRow (ham R p) a) := by
  simp only [onsiteRow,avg,Matrix.trace,Matrix.diag,bracket,Matrix.sub_apply,Matrix.mul_apply]
  have reS : ContDiff ℝ ω Complex.re := Complex.reCLM.contDiff
  simp only [div_eq_mul_inv]
  fun_prop

theorem rows_smooth (aux : Bool) : ContDiff ℝ ω (polynomialRows R aux) := by
  apply contDiff_pi.mpr; intro i
  cases i with
  | inl a => exact onsite_smooth R a
  | inr i =>
    obtain ⟨d,a,k⟩ := i
    rcases (show k=0 ∨ k=1 ∨ k=2 by fin_cases k <;> decide) with rfl|rfl|rfl
    · change ContDiff ℝ ω (fun p => -exch R p d a a); fun_prop
    · cases aux <;> simp [polynomialRows,minorRow] <;> fun_prop
    · simp [polynomialRows,contract]; fun_prop

end DSFTomography.HT.Diagonal
