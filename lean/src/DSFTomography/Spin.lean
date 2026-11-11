import DSFTomography.Moments
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

noncomputable section
namespace DSFTomography
abbrev Axis := Fin 3
abbrev Tensor := Matrix Axis Axis ℂ
def third (a u : Axis) : Axis := ![![0,2,1], ![2,1,0], ![1,0,2]] a u
def sign (a u : Axis) : ℂ := ![![0,1,-1], ![-1,0,1], ![1,-1,0]] a u
/-- The complete one-site structure constants in the laboratory frame. -/
theorem axisTable :
    sign 0 0 = 0 ∧
    third 0 0 = 0 ∧
    sign 0 1 = 1 ∧
    third 0 1 = 2 ∧
    sign 0 2 = -1 ∧
    third 0 2 = 1 ∧
    sign 1 0 = -1 ∧
    third 1 0 = 2 ∧
    sign 1 1 = 0 ∧
    third 1 1 = 1 ∧
    sign 1 2 = 1 ∧
    third 1 2 = 0 ∧
    sign 2 0 = 1 ∧
    third 2 0 = 1 ∧
    sign 2 1 = -1 ∧
    third 2 1 = 0 ∧
    sign 2 2 = 0 ∧
    third 2 2 = 2 := by repeat' constructor

def phase (a u : Axis) : ℂ := (2 * Complex.I) * sign a u

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq S]

/-- Local Pauli observables expressed in the chosen energy eigenbasis.
Only their Lie algebra is needed. This formulation applies in every representation. -/
structure Spins (S ι : Type*) [Fintype ι] [DecidableEq ι] [DecidableEq S] where
  σ : S → Axis → Op ι
  pauli : ∀ r a i u, bracket (σ r a) (σ i u) =
    (if r = i then phase a u else 0) • σ i (third a u)

def coeff (r i : S) (a u : Axis) : ℂ := if r = i then phase a u else 0

def corr (P : Spins S ι) (w : ι → ℂ) (i j : S) : Tensor :=
  fun u v => m₀ w (P.σ i u) (P.σ j v)

/-- Extract magnetization from two ordered on-site static moments. -/
def magnet (P : Spins S ι) (w : ι → ℂ) (i : S) (a : Axis) : ℂ :=
  (corr P w i i (a+1) (a+2) - corr P w i i (a+2) (a+1)) / (2 * Complex.I)

theorem magnet_eq (P : Spins S ι) (w : ι → ℂ) (i : S) (a : Axis) :
    magnet P w i a = mean w (P.σ i a) := by
  unfold magnet corr
  rw [zeroMoment, zeroMoment, ← mean_sub]
  change mean w (bracket _ _) / _ = _
  rw [P.pauli, if_pos rfl, mean_smul]
  have hs : sign (a+1) (a+2) = 1 := by fin_cases a <;> rfl
  have ht : third (a+1) (a+2) = a := by fin_cases a <;> rfl
  simp [phase, hs, ht, mul_div_cancel_left₀, Complex.I_ne_zero]

def response (w : ι → ℂ) (A B X : Op ι) := mean w (bracket (bracket A X) B)

omit [DecidableEq ι] in
theorem bracket_mul (A X Y : Op ι) :
    bracket A (X * Y) = bracket A X * Y + X * bracket A Y := by
  unfold bracket
  noncomm_ring

omit [DecidableEq ι] in
theorem mul_bracket (X Y B : Op ι) :
    bracket (X * Y) B = bracket X B * Y + X * bracket Y B := by
  unfold bracket
  noncomm_ring

@[simp] theorem bracket_smul (k : ℂ) (A X : Op ι) :
    bracket A (k • X) = k • bracket A X := by simp [bracket, smul_sub]
@[simp] theorem smul_bracket (k : ℂ) (A X : Op ι) :
    bracket (k • X) A = k • bracket X A := by simp [bracket, smul_sub]
omit [DecidableEq ι] in
@[simp] theorem bracket_add (A X Y : Op ι) :
    bracket A (X+Y) = bracket A X + bracket A Y := by unfold bracket; noncomm_ring
omit [DecidableEq ι] in
@[simp] theorem add_bracket (X Y B : Op ι) :
    bracket (X+Y) B = bracket X B + bracket Y B := by unfold bracket; noncomm_ring

omit [DecidableEq ι] in
@[simp] theorem response_add (w : ι → ℂ) (A B X Y : Op ι) :
    response w A B (X+Y) = response w A B X + response w A B Y := by simp [response]
@[simp] theorem response_smul (w : ι → ℂ) (A B X : Op ι) (k : ℂ) :
    response w A B (k • X) = k * response w A B X := by simp [response]
omit [DecidableEq ι] in
@[simp] theorem response_sum {α : Type*} (w : ι → ℂ) (A B : Op ι) (s : Finset α)
    (f : α → Op ι) : response w A B (∑ i ∈ s, f i) = ∑ i ∈ s, response w A B (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [response, bracket, mean]
  | insert i s hi ih => simp [hi, ih]

/-- The double commutator of a single-site term, expressed in measured data. -/
def single (M : S → Axis → ℂ) (r s i : S) (a b u : Axis) :=
  coeff r i a u * coeff i s (third a u) b * M i (third (third a u) b)

/-- The four Leibniz terms for a two-site interaction. All four statics are measured. -/
def pair (C : S → S → Tensor) (r s i j : S) (a b u v : Axis) :=
  coeff r i a u * (coeff i s (third a u) b * C i j (third (third a u) b) v +
                   coeff j s v b * C i j (third a u) (third v b)) +
  coeff r j a v * (coeff i s u b * C i j (third u b) (third a v) +
                   coeff j s (third a v) b * C i j u (third (third a v) b))

omit [DecidableEq ι] in
@[simp] theorem bracket_zero_left (A : Op ι) : bracket 0 A = 0 := by simp [bracket]

theorem response_single (P : Spins S ι) (w : ι → ℂ) (r s i : S) (a b u : Axis) :
    response w (P.σ r a) (P.σ s b) (P.σ i u) =
      single (magnet P w) r s i a b u := by
  by_cases hi : i = s <;> by_cases hr : r = i <;> subst_vars <;>
    simp [response, single, P.pauli, coeff, magnet_eq, *, mul_assoc, bracket_zero_left]

theorem response_pair (P : Spins S ι) (w : ι → ℂ) (r s i j : S) (a b u v : Axis) :
    response w (P.σ r a) (P.σ s b) (P.σ i u * P.σ j v) =
      pair (corr P w) r s i j a b u v := by
  classical
  by_cases hi : i = s <;> by_cases hj : j = s <;> by_cases hr : r = i <;> by_cases ht : r = j <;> subst_vars <;>
    simp [response, pair, bracket_mul, mul_bracket, P.pauli, coeff, corr, zeroMoment,
      mul_add, *, mean_zero]

end DSFTomography
