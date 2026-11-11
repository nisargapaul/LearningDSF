import DSFTomography.Fourier

/-! Pauli strings as literal tensor-product matrices. The basis change below
expresses the same operators in the energy basis used by the Lehmann sums. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography
abbrev Config (S : Type*) := S → Fin 2
abbrev Letter := Option Axis
abbrev Qubit := Op (Fin 2)

def pauli : Letter → Qubit
  | none => 1
  | some a => ![ (!![0, 1; 1, 0] : Qubit), !![0, -Complex.I; Complex.I, 0],
      !![1, 0; 0, -1] ] a

theorem pauliValues : pauli none = 1 ∧ pauli (some 0) = !![0, 1; 1, 0] ∧
    pauli (some 1) = !![0, -Complex.I; Complex.I, 0] ∧ pauli (some 2) = !![1, 0; 0, -1] := by
  repeat' constructor

private theorem axes (a : Axis) : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide

private theorem letters (a : Letter) :
    a = none ∨ a = some 0 ∨ a = some 1 ∨ a = some 2 := by
  cases a with
  | none => simp
  | some a => simpa using axes a

theorem trace_pauli_pair (a b : Letter) :
    (pauli a * pauli b).trace = if a = b then 2 else 0 := by
  rcases letters a with rfl|rfl|rfl|rfl <;> rcases letters b with rfl|rfl|rfl|rfl <;>
    norm_num (config := {decide := true}) [pauliValues, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Complex.I_mul_I]

variable {S : Type*} [Fintype S] [DecidableEq S]
def tensor (A : S → Qubit) : Op (Config S) := fun x y => ∏ r, A r (x r) (y r)

theorem tensor_mul (A B : S → Qubit) :
    tensor A * tensor B = tensor (fun r => A r * B r) := by
  ext x y
  simp only [tensor, Matrix.mul_apply, Finset.prod_mul_distrib, Fintype.prod_sum]

theorem trace_tensor (A : S → Qubit) :
    (tensor A).trace = ∏ r, (A r).trace := by
  simp only [tensor, Matrix.trace, Matrix.diag, Fintype.prod_sum]

def word (l : S → Letter) : Op (Config S) := tensor (fun r => pauli (l r))

theorem word_overlap (l m : S → Letter) : (word l * word m).trace =
    if l = m then (Fintype.card (Config S) : ℂ) else 0 := by
  simp only [word, tensor_mul, trace_tensor, trace_pauli_pair, Fintype.prod_ite_zero]
  simp [funext_iff, Config, Fintype.card_pi]

def oneLabel (i : S) (a : Axis) (r : S) : Letter := if r = i then some a else none
def twoLabel (i j : S) (a b : Axis) (r : S) : Letter :=
  if r = i then some a else if r = j then some b else none

def inBasis (U : (Op (Config S))ˣ) (A : Op (Config S)) : Op (Config S) :=
  U.val * A * (↑U⁻¹ : Op (Config S))

theorem inBasis_mul (U : (Op (Config S))ˣ) (A B : Op (Config S)) :
    inBasis U A * inBasis U B = inBasis U (A * B) := by
  simp [inBasis, Matrix.mul_assoc]

def string (U : (Op (Config S))ˣ) (l : S → Letter) := inBasis U (word l)

theorem string_overlap (U : (Op (Config S))ˣ) (l m : S → Letter) :
    (string U l * string U m).trace = if l = m then (Fintype.card (Config S) : ℂ) else 0 := by
  rw [string, string, inBasis_mul, inBasis, Matrix.trace_units_conj, word_overlap]

theorem string_pair (U : (Op (Config S))ˣ) {i j : S} (hij : i ≠ j) (a b : Axis) :
    string U (oneLabel i a) * string U (oneLabel j b) = string U (twoLabel i j a b) := by
  simp only [string, inBasis_mul, word, tensor_mul]
  congr 2
  funext r
  by_cases hi : r = i <;> by_cases hj : r = j <;> simp_all [oneLabel, twoLabel, pauli]

private theorem string_local_mul (U : (Op (Config S))ˣ) (i : S) (a b k : Axis) (z : ℂ)
    (prod : pauli (some a) * pauli (some b) = z • pauli (some k)) :
    string U (oneLabel i a) * string U (oneLabel i b) = z • string U (oneLabel i k) := by
  have hloc (r : S) : pauli (oneLabel i a r) * pauli (oneLabel i b r) =
      (if r = i then z else 1) • pauli (oneLabel i k r) := by
    by_cases hr : r = i <;> simp [oneLabel, hr, prod, show pauli none = 1 from rfl]
  have ht : word (oneLabel i a) * word (oneLabel i b) = z • word (oneLabel i k) := by
    simp only [word, tensor_mul, hloc]
    ext x y
    simp only [tensor, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    simp
  simp only [string, inBasis_mul, ht]
  simp [inBasis]

omit [DecidableEq S] in
theorem word_hermitian (l : S → Letter) : (word l).conjTranspose = word l := by
  have site (a : Letter) : (pauli a).conjTranspose = pauli a := by
    rcases letters a with rfl|rfl|rfl|rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [pauliValues, Matrix.conjTranspose_apply, Matrix.one_apply]
  ext x y
  change star (∏ r, pauli (l r) (y r) (x r)) = ∏ r, pauli (l r) (x r) (y r)
  rw [star_prod]
  exact Finset.prod_congr rfl (fun r _ => congrFun (congrFun (site (l r)) (x r)) (y r))

private theorem different_axes (a b : Axis) (h : a ≠ b) :
    pauli (some a) * pauli (some b) = (Complex.I * sign a b) • pauli (some (third a b)) := by
  rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;> try contradiction
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [axisTable, pauliValues, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem string_same_site (U : (Op (Config S))ˣ) (i : S) (a b : Axis) (hab : a ≠ b) :
    string U (oneLabel i a) * string U (oneLabel i b) =
      (Complex.I * sign a b) • string U (oneLabel i (third a b)) :=
  string_local_mul U i _ _ _ _ (different_axes a b hab)

theorem string_square (U : (Op (Config S))ˣ) (i : S) (a : Axis) :
    string U (oneLabel i a) * string U (oneLabel i a) = 1 := by
  have square (l : Letter) : pauli l * pauli l = 1 := by
    rcases letters l with rfl|rfl|rfl|rfl <;> ext m n <;> fin_cases m <;> fin_cases n <;>
      norm_num [pauliValues, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.I_mul_I]
  have id : tensor (fun _ : S => (1 : Qubit)) = 1 := by
    ext x y
    simp [tensor, Matrix.one_apply, Fintype.prod_ite_zero, funext_iff]
  simp only [string, inBasis_mul, word, tensor_mul, square, id]
  simp [inBasis]

/-- The canonical tensor-product spin system, expressed in basis U. -/
def qubitSpins (U : (Op (Config S))ˣ) : Spins S (Config S) where
  σ i a := string U (oneLabel i a)
  pauli r a i b := by
    by_cases hri : r=i
    · subst r
      rw [if_pos rfl]
      by_cases hab : a=b
      · subst b
        have hs : sign a a = 0 := by rcases axes a with rfl|rfl|rfl <;> rfl
        simp [bracket, phase, hs]
      · have ht : third b a = third a b := by
          rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;> rfl
        have hs : sign b a = -sign a b := by
          rcases axes a with rfl|rfl|rfl <;> rcases axes b with rfl|rfl|rfl <;> simp [axisTable]
        rw [bracket, string_same_site U i a b hab,
          string_same_site U i b a (Ne.symm hab), ht, hs, ← sub_smul]
        congr 1
        unfold phase
        ring
    · have swap : twoLabel r i a b = twoLabel i r b a := by
        funext t
        by_cases hr : t=r <;> by_cases hi : t=i <;> simp_all [twoLabel]
      simp [bracket, hri, string_pair U hri, string_pair U (Ne.symm hri), swap]

/-- Every local observable is the usual qubit Pauli in the same energy basis. -/
def IsQubitFrame (P : Spins S (Config S)) (U : (Op (Config S))ˣ) :=
  ∀ r a, P.σ r a = string U (oneLabel r a)

end DSFTomography.HT
