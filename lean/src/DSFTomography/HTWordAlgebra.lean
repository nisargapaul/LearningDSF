import DSFTomography.HTLocalGibbs

/-! Multiplication, support and separation of Pauli words for the local Gibbs recursion. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography

namespace Pauli
def join : Letter → Letter → Letter
  | none, b => b
  | some a, none => some a
  | some a, some b => if a = b then none else some (third a b)

def factor : Letter → Letter → ℂ
  | some a, some b => if a = b then 1 else Complex.I * sign a b
  | _, _ => 1

private theorem allLetters (a : Letter) :
    a = none ∨ a = some 0 ∨ a = some 1 ∨ a = some 2 := by
  cases a with
  | none => simp
  | some a => fin_cases a <;> decide

theorem join_comm (a b : Letter) : join a b = join b a := by
  rcases allLetters a with rfl|rfl|rfl|rfl <;> rcases allLetters b with rfl|rfl|rfl|rfl <;> decide

theorem norm_factor (a b : Letter) : ‖factor a b‖ = 1 := by
  rcases allLetters a with rfl|rfl|rfl|rfl <;> rcases allLetters b with rfl|rfl|rfl|rfl <;>
    norm_num (config := {decide := true}) [factor, axisTable]

theorem mul_letter (a b : Letter) : pauli a * pauli b = factor a b • pauli (join a b) := by
  rcases allLetters a with rfl|rfl|rfl|rfl <;> rcases allLetters b with rfl|rfl|rfl|rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num (config := {decide := true}) [pauliValues, factor, join, axisTable, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Complex.I_mul_I]

variable {S : Type*}
abbrev Label (S : Type*) := S → Letter
def combine (w v : Label S) : Label S := fun i => join (w i) (v i)

variable [Fintype S] [DecidableEq S]
def unitPhase (w v : Label S) := ∏ i, factor (w i) (v i)
def supp (w : Label S) := Finset.univ.filter (fun i => w i ≠ none)

theorem product (w v : Label S) : word w * word v = unitPhase w v • word (combine w v) := by
  simp only [word, tensor_mul, mul_letter]
  ext x y
  simp [tensor, combine, unitPhase, Finset.prod_mul_distrib]

omit [DecidableEq S] in
theorem phase_norm (w v : Label S) : ‖unitPhase w v‖ = 1 := by simp [unitPhase, norm_prod, norm_factor]

theorem commutator (w v : Label S) : bracket (word w) (word v) =
    (unitPhase w v - unitPhase v w) • word (combine w v) := by
  have swap : combine v w = combine w v := funext fun i => join_comm _ _
  rw [bracket, product, product, swap, sub_smul]

omit [DecidableEq S] in
theorem phase_eq_of_disjoint {w v : Label S} (hs : Disjoint (supp w) (supp v)) :
    unitPhase w v = unitPhase v w := by
  apply Finset.prod_congr rfl
  intro i _
  have hn : w i = none ∨ v i = none := by
    by_contra! ne
    exact (Finset.disjoint_left.mp hs) (by simpa [supp] using ne.1) (by simpa [supp] using ne.2)
  rcases hn with h|h <;> simp only [h] <;> cases w i <;> cases v i <;> rfl

theorem supp_combine (w v : Label S) : supp (combine w v) ⊆ supp w ∪ supp v := by
  intro i hi
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, combine] at hi ⊢
  by_contra! h
  simp_all [Finset.mem_union, join]

theorem card_step {w v : Label S} (overlap : ¬Disjoint (supp w) (supp v))
    (two : (supp v).card ≤ 2) : (supp (combine w v)).card ≤ (supp w).card + 1 := by
  have h := Finset.card_union_add_card_inter (supp w) (supp v)
  have pos : 0 < ((supp w) ∩ (supp v)).card :=
    Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp overlap)
  have sub := Finset.card_le_card (supp_combine w v)
  omega

omit [DecidableEq S] in
theorem word_empty : word (fun _ : S => none) = 1 := by
  ext x y
  simp [word, tensor, pauli, Matrix.one_apply, Finset.prod_ite_zero, funext_iff]

theorem phase_site (i : S) (a : Axis) (v : Label S) :
    unitPhase (oneLabel i a) v = factor (some a) (v i) ∧
    unitPhase v (oneLabel i a) = factor (v i) (some a) := by
  have hn (l : Letter) : factor none l = 1 ∧ factor l none = 1 := by cases l <;> exact ⟨rfl,rfl⟩
  constructor <;> unfold unitPhase <;> rw [Finset.prod_eq_single i] <;> simp_all [oneLabel]

theorem flip_at {w : Label S} {i : S} {b : Axis} (hw : w i = some b) :
    word (oneLabel i (b+1)) * word w = -(word w * word (oneLabel i (b+1))) := by
  have pf := phase_site i (b+1) w
  have ph : factor (some (b+1)) (some b) = -factor (some b) (some (b+1)) := by
    fin_cases b
    · change Complex.I * (-1) = -(Complex.I * 1); ring
    · change Complex.I * (-1) = -(Complex.I * 1); ring
    · change Complex.I * (-1) = -(Complex.I * 1); ring
  have same : combine (oneLabel i (b+1)) w = combine w (oneLabel i (b+1)) :=
    funext fun _ => join_comm _ _
  rw [product, product, same, pf.1, pf.2, hw, ph, neg_smul]

theorem flip {w : Label S} (nontriv : w ≠ fun _ => none) :
    ∃ i a, word (oneLabel i a) * word w = -(word w * word (oneLabel i a)) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp nontriv
  cases hw : w i with
  | none => exact (hi hw).elim
  | some b => exact ⟨i,b+1,flip_at hw⟩

/-- The normalized trace pairing with all Pauli words separates matrices. -/
theorem span_words : Submodule.span ℂ (Set.range (word (S := S))) = ⊤ := by
  have li : LinearIndependent ℂ (word (S := S)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro f hf i
    have h := congrArg (fun A : Op (Config S) => (A * word i).trace) hf
    simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul,
      word_overlap, smul_eq_mul, mul_ite] at h
    exact h
  apply li.span_eq_top_of_card_eq_finrank
  simp [Config, Letter, Axis, Module.finrank_matrix, ← mul_pow]

theorem trace_separates (A : Op (Config S)) (h : ∀ w : Label S, (A * word w).trace = 0) :
    ∀ B, (A * B).trace = 0 := by
  intro B
  have mem : B ∈ Submodule.span ℂ (Set.range (word (S := S))) := by rw [span_words]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx => obtain ⟨w,rfl⟩ := hx; exact h w
  | zero => simp
  | add x y _ _ hx hy => simp [Matrix.mul_add, hx, hy]
  | smul c x _ hx => simp [hx]

end Pauli
end DSFTomography.HT
