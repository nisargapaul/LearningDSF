import DSFTomography.HTPeriodicBounds

/-! A local string is an ordered product with fixed lattice addresses. Its
phase and its nonidentity letters stabilize as soon as the addresses separate. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter Pauli

namespace LocalWord
abbrev Atom (S : Type*) := S × Axis
abbrev Script (S : Type*) := List (Atom S)
variable {S B : Type*} [DecidableEq S] [DecidableEq B]

def letters : Script S → Label S
  | [] => fun _ => none
  | (i,a)::xs => Function.update (letters xs) i (join (some a) (letters xs i))

def scalar : Script S → ℂ
  | [] => 1
  | (i,a)::xs => factor (some a) (letters xs i) * scalar xs

def move (f : S → B) (xs : Script S) : Script B := xs.map (Prod.map f id)

theorem scalar_norm (xs : Script S) : ‖scalar xs‖ = 1 := by
  induction xs with
  | nil => simp [scalar]
  | cons x xs ih => simp [scalar,norm_factor,ih]

variable [Fintype B]
def eval (f : S → B) (xs : Script S) : Op (Config B) :=
  (xs.map fun x => word (oneLabel (f x.1) x.2)).prod
omit [DecidableEq S] in
@[simp] theorem eval_nil (f : S → B) : eval f [] = 1 := rfl
omit [DecidableEq S] in
@[simp] theorem eval_cons (f : S → B) (x : Atom S) (xs : Script S) :
    eval f (x::xs) = word (oneLabel (f x.1) x.2) * eval f xs := rfl
omit [DecidableEq S] in
@[simp] theorem eval_append (f : S → B) (xs ys : Script S) :
    eval f (xs++ys) = eval f xs * eval f ys := by simp [eval,List.prod_append]

omit [DecidableEq S] in
theorem normal (f : S → B) (xs : Script S) :
    eval f xs = scalar (move f xs) • word (letters (move f xs)) := by
  induction xs with
  | nil => simp [scalar,move,letters,word_empty]
  | cons x xs ih =>
    obtain ⟨i,a⟩ := x
    let v := letters (move f xs)
    have lab : combine (oneLabel (f i) a) v = Function.update v (f i) (join (some a) (v (f i))) := by
      funext j
      by_cases hj : j=f i
      · subst j; simp [combine,oneLabel]
      · simp [combine,oneLabel,hj,Function.update_of_ne,Pauli.join]
    rw [eval_cons,ih,Matrix.mul_smul,product,(phase_site ..).1,smul_smul,mul_comm]
    simp only [move,List.map_cons,Prod.map_apply,id_eq,scalar,letters]
    exact congrArg (_ • ·) (congrArg word lab)

omit [Fintype B] in
theorem off (xs : Script B) {j : B} (hj : j ∉ xs.map Prod.fst) : letters xs j = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at hj
    simp [letters,Function.update_of_ne hj.1,ih hj.2]

variable {ν : ℕ} (R : Bonds (Site ν))
abbrev place (n : ℕ) := periodicSite R n

theorem eventual_eq_test (i j : Site ν) :
    ∀ᶠ n in atTop, place R n i = place R n j ↔ i=j := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_resolves ({i,j} : Finset (Site ν)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hs := hN (periodIndex R n) (hn.trans (Nat.le_add_left n _))
  exact ⟨hs (by simp) (by simp), congrArg _⟩

theorem letters_place (xs : Script (Site ν)) (j : Site ν) :
    ∀ᶠ n in atTop, letters (move (place R n) xs) (place R n j) = letters xs j := by
  induction xs with
  | nil => exact Eventually.of_forall fun _ => rfl
  | cons x xs ih =>
    obtain ⟨i,a⟩ := x
    filter_upwards [ih,eventual_eq_test R j i] with n hn he
    by_cases eq : j=i
    · subst j; simpa [move,letters] using congrArg (join (some a)) hn
    · simpa [move,letters,Function.update_of_ne eq, Function.update_of_ne (he.not.mpr eq)] using hn

theorem scalar_place (xs : Script (Site ν)) :
    ∀ᶠ n in atTop, scalar (move (place R n) xs) = scalar xs := by
  induction xs with
  | nil => exact Eventually.of_forall fun _ => rfl
  | cons x xs ih =>
    filter_upwards [ih,letters_place R xs x.1] with n hn hl
    exact congrArg₂ (· * ·) (congrArg (factor (some x.2)) hl) hn

theorem classify (xs : Script (Site ν)) :
    (∃ t : ℂ, ∀ᶠ n in atTop, eval (place R n) xs = t • 1) ∨
    (∃ x : Atom (Site ν), ∀ᶠ n in atTop,
      eval (place R n) [x] * eval (place R n) xs = -(eval (place R n) xs * eval (place R n) [x])) := by
  classical
  by_cases triv : ∀ j, letters xs j = none
  · left; refine ⟨scalar xs,?_⟩
    let sites := (xs.map Prod.fst).toFinset
    filter_upwards [scalar_place R xs, sites.eventually_all.mpr fun j _ => letters_place R xs j] with n hp hl
    have empty : letters (move (place R n) xs) = fun _ => none := by
      funext j
      by_cases hj : j ∈ (move (place R n) xs).map Prod.fst
      · obtain ⟨⟨i,a⟩,hi,rfl⟩ := (by simpa [move,List.map_map,Function.comp_def] using hj :
          ∃ x ∈ xs, place R n x.1 = j)
        exact (hl i (by simpa [sites] using List.mem_map_of_mem (f := Prod.fst) hi)).trans (triv _)
      · exact off _ hj
    rw [normal,hp,empty,word_empty]
  · push_neg at triv
    obtain ⟨i,hi⟩ := triv
    cases h : letters xs i with
    | none => exact (hi h).elim
    | some b =>
      right; refine ⟨(i,b+1),?_⟩
      filter_upwards [letters_place R xs i] with n hn
      have flip := flip_at (hn.trans h)
      rw [normal (place R n) xs]
      simp only [eval_cons,eval_nil,mul_one,Matrix.mul_smul,Matrix.smul_mul,flip,smul_neg]
end LocalWord
end DSFTomography.HT
