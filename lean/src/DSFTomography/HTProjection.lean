import DSFTomography.PauliWords

noncomputable section
namespace DSFTomography.HT
open DSFTomography
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

omit [AddCommGroup S] [Fintype S] in
private theorem one_eq (i j : S) (a u : Axis) :
    oneLabel i a = oneLabel j u ↔ i = j ∧ a = u := by
  constructor
  · intro h
    have hx := congrFun h i
    by_cases hij : i = j <;> simp_all [oneLabel]
  · rintro ⟨rfl,rfl⟩; rfl

omit [AddCommGroup S] [Fintype S] in
private theorem one_ne_two (i j k : S) (hjk : j ≠ k) (a u v : Axis) :
    oneLabel i a ≠ twoLabel j k u v := by
  intro h
  have hj := congrFun h j
  have hk := congrFun h k
  by_cases hji : j = i <;> by_cases hki : k = i <;> simp_all [oneLabel, twoLabel]

omit [Fintype S] in
private theorem bond_eq (R : Bonds S) {d e : S} (hd : d ∈ R.dirs) (he : e ∈ R.dirs)
    (i j : S) (a b u v : Axis) :
    twoLabel i (i+d) a b = twoLabel j (j+e) u v ↔ d=e ∧ i=j ∧ a=u ∧ b=v := by
  constructor
  · intro h
    have h1 := congrFun h i
    have h2 := congrFun h (i+d)
    have hid : i+d ≠ i := by simpa using R.nonzero d hd
    have hje : j+e ≠ j := by simpa using R.nonzero e he
    by_cases hij : i = j
    · subst j
      by_cases hde : d = e <;> simp_all [twoLabel]
    · by_cases hrev : i = j+e
      · have hnj : i+d ≠ j := by
          intro hj
          apply R.oriented d hd e he
          have hx : j+(e+d) = j := by rw [← add_assoc, ← hrev, hj]
          simpa [add_comm] using hx
        simp [twoLabel, hid, hnj, ← hrev] at h2
      · simp [twoLabel, hij, hrev] at h1
  · rintro ⟨rfl,rfl,rfl,rfl⟩; rfl

variable (P : Spins S (Config S)) (U : (Op (Config S))ˣ) (frame : IsQubitFrame P U)
  (R : Bonds S) (h : Axis → ℂ) (J : S → Tensor)

include frame in
theorem H_words : H P R h J =
    (∑ i, ∑ a, h a • string U (oneLabel i a)) +
    ∑ d ∈ R.dirs, ∑ i, ∑ a, ∑ b, J d a b • string U (twoLabel i (i+d) a b) := by
  have single (r : S) (a : Axis) := frame r a
  simp only [H, single]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro d hd
  have dist (i : S) : i ≠ i+d := Ne.symm (by simpa using R.nonzero d hd)
  simp_rw [string_pair U (dist _) ]

omit [AddCommGroup S] in
private theorem trace_string (l : S → Letter) : (string U l).trace =
    if l = fun _ => none then (Fintype.card (Config S) : ℂ) else 0 := by
  have letter (a : Letter) : (pauli a).trace = if a = none then 2 else 0 := by
    simpa only [show pauli none = 1 from rfl, Matrix.mul_one] using trace_pauli_pair a none
  simp only [string, inBasis, Matrix.trace_units_conj, word, trace_tensor, letter,
    Fintype.prod_ite_zero]
  simp [funext_iff, Config, Fintype.card_pi]

include frame in
theorem H_traceless : (H P R h J).trace = 0 := by
  have one (i : S) (a : Axis) : oneLabel i a ≠ fun _ => none := by
    intro eq; simpa [oneLabel] using congrFun eq i
  have two (i j : S) (a b : Axis) : twoLabel i j a b ≠ fun _ => none := by
    intro eq; simpa [twoLabel] using congrFun eq i
  simp [H_words P U frame R h J, Matrix.trace_sum, trace_string, one, two]

include frame in
private theorem project (l : S → Letter) :
    (H P R h J * string U l).trace =
    (∑ i, ∑ u, h u * (if l = oneLabel i u then (Fintype.card (Config S) : ℂ) else 0)) +
    ∑ e ∈ R.dirs, ∑ i, ∑ u, ∑ v, J e u v *
      (if l = twoLabel i (i+e) u v then (Fintype.card (Config S) : ℂ) else 0) := by
  rw [Matrix.trace_mul_comm, H_words P U frame R h J]
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sum, Matrix.trace_smul, string_overlap, smul_eq_mul]

include frame in
theorem project_field (i : S) (a : Axis) :
    (H P R h J * string U (oneLabel i a)).trace = h a * Fintype.card (Config S) := by
  rw [project P U frame R h J]
  have noBonds (e : S) (he : e ∈ R.dirs) (j : S) (u v : Axis) :
      oneLabel i a ≠ twoLabel j (j+e) u v :=
    one_ne_two _ _ _ (Ne.symm (by simpa using R.nonzero e he)) _ _ _
  apply Eq.trans (congrArg₂ (· + ·) rfl (Finset.sum_eq_zero (fun e he => by simp [noBonds e he])))
  simp [one_eq, ite_and, mul_ite, Finset.sum_ite_irrel]

include frame in
theorem project_bond {d : S} (hd : d ∈ R.dirs) (i : S) (a b : Axis) :
    (H P R h J * string U (twoLabel i (i+d) a b)).trace =
      J d a b * Fintype.card (Config S) := by
  rw [project P U frame R h J]
  have dist : i ≠ i+d := Ne.symm (by simpa using R.nonzero d hd)
  have noFields (j : S) (u : Axis) := Ne.symm (one_ne_two j i (i+d) dist u a b)
  simp only [noFields, if_false, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single d]
  · simp [bond_eq R hd hd, ite_and, mul_ite, Finset.sum_ite_irrel]
  · intro e he hne
    simp [bond_eq R hd he, Ne.symm hne]
  · simp [hd]

end DSFTomography.HT
