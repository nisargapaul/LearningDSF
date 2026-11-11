import DSFTomography.HTLocalWords

/-! Finite formal sums of site strings. Applying the Hamiltonian commutator
to a string uses the product rule, so only bonds incident on its letters enter. -/
noncomputable section
namespace DSFTomography.HT.LocalWord
open DSFTomography Pauli
abbrev Form (S : Type*) := List (ℂ × Script S)
namespace Form
variable {S : Type*} {E : Type*} [AddCommMonoid E] [Module ℂ E]

def apply (u : Form S) (f : Script S → E) := (u.map fun p => p.1 • f p.2).sum
def mass (u : Form S) := (u.map fun p => ‖p.1‖).sum
def subst (u : Form S) (v : Script S → Form S) : Form S :=
  u.flatMap fun p => (v p.2).map fun q => (p.1*q.1,q.2)
def changeWords (u : Form S) (f : Script S → Script S) : Form S := u.map fun p => (p.1, f p.2)
@[simp] theorem apply_nil (f : Script S → E) : apply [] f = 0 := rfl
@[simp] theorem apply_cons (p : ℂ × Script S) (u : Form S) (f : Script S → E) :
    apply (p::u) f = p.1 • f p.2 + apply u f := rfl
@[simp] theorem apply_append (u v : Form S) (f : Script S → E) : apply (u++v) f = apply u f + apply v f := by
  simp [apply,List.sum_append]
@[simp] theorem mass_nil : mass ([] : Form S) = 0 := rfl
@[simp] theorem mass_cons (p : ℂ × Script S) (u : Form S) : mass (p::u) = ‖p.1‖ + mass u := rfl
@[simp] theorem mass_append (u v : Form S) : mass (u++v) = mass u + mass v := by simp [mass,List.sum_append]
@[simp] theorem apply_changeWords (u : Form S) (g : Script S → Script S) (f : Script S → E) :
    apply (changeWords u g) f = apply u (fun q => f (g q)) := by simp [apply,changeWords,List.map_map,Function.comp_def]
@[simp] theorem mass_changeWords (u : Form S) (g : Script S → Script S) : mass (changeWords u g) = mass u := by
  simp [mass,changeWords,List.map_map,Function.comp_def]

theorem map_apply {E' : Type*} [AddCommMonoid E'] [Module ℂ E'] (L : E →ₗ[ℂ] E') (u : Form S) (f : Script S → E) :
    L (apply u f) = apply u (fun q => L (f q)) := by induction u <;> simp_all
theorem apply_subst (u : Form S) (v : Script S → Form S) (f : Script S → E) :
    apply (subst u v) f = apply u (fun q => apply (v q) f) := by
  have scale (c : ℂ) (w : Form S) :
      apply (w.map fun p => (c*p.1,p.2)) f = c • apply w f := by
    induction w <;> simp_all [mul_smul,smul_add]
  induction u <;> simp_all [subst,List.flatMap_cons]

theorem mass_nonneg (u : Form S) : 0 ≤ mass u := by induction u <;> simp_all [add_nonneg,norm_nonneg]
theorem mass_subst_le (u : Form S) (v : Script S → Form S) {M : ℝ}
    (bound : ∀ p ∈ u, mass (v p.2) ≤ M) : mass (subst u v) ≤ mass u * M := by
  have scale (c : ℂ) (w : Form S) :
      mass (w.map fun p => (c*p.1,p.2)) = ‖c‖ * mass w := by
    induction w <;> simp_all [mul_add]
  induction u with
  | nil => simp [subst]
  | cons p u ih =>
    simp only [subst,List.flatMap_cons,mass_append,scale,mass_cons,add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (bound p (by simp)) (norm_nonneg _))
      (ih fun q hq => bound q (by simp [hq]))

theorem norm_apply_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (u : Form S) (f : Script S → V)
    {M : ℝ} (bound : ∀ p ∈ u, ‖f p.2‖ ≤ M) : ‖apply u f‖ ≤ mass u * M := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [apply_cons,mass_cons,add_mul]
    apply (norm_add_le ..).trans
    rw [norm_smul]
    exact add_le_add (mul_le_mul_of_nonneg_left (bound p (by simp)) (norm_nonneg _))
      (ih fun q hq => bound q (by simp [hq]))

end Form

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
private def bondsAt (i : Site ν) : Shape R → List (Script (Site ν))
  | .inl a => [[(i,a)]]
  | .inr (d,a,b) => [[(i,a),(i+d,b)],[(i-d,a),(i,b)]]

private def spinStep (x : Atom (Site ν)) : Form (Site ν) :=
  (Finset.univ : Finset (Shape R)).toList.flatMap fun s =>
    (bondsAt R x.1 s).flatMap fun w =>
      [(strength R h J s,x::w),(-strength R h J s,w++[x])]

def step : Script (Site ν) → Form (Site ν)
  | [] => []
  | x::xs => Form.changeWords (spinStep R h J x) (· ++ xs) ++
      Form.changeWords (step xs) (x::·)

/-- The local commutator lists have the same addresses for all strengths,
including at zero couplings. Only the coefficients change. -/
theorem step_words (w : Script (Site ν)) :
    (step R h J w).map Prod.snd = (step R 0 0 w).map Prod.snd := by
  have keys (x : Atom (Site ν)) :
      (spinStep R h J x).map Prod.snd = (spinStep R 0 0 x).map Prod.snd := by
    simp only [spinStep,List.map_flatMap,List.map_cons,List.map_nil]
  have change (u v : Form (Site ν)) (f : Script (Site ν) → Script (Site ν))
      (same : u.map Prod.snd = v.map Prod.snd) :
      (Form.changeWords u f).map Prod.snd = (Form.changeWords v f).map Prod.snd := by
    simpa only [Form.changeWords,List.map_map,Function.comp_def] using congrArg (List.map f) same
  induction w with
  | nil => rfl
  | cons x xs ih =>
    simp only [step,List.map_append]
    rw [change _ _ _ (keys x),change _ _ _ ih]

private theorem spin_mass (x : Atom (Site ν)) : Form.mass (spinStep R h J x) ≤ 2*incidentBound R h J := by
  let ss := strength R h J
  have shape (s : Shape R) : Form.mass ((bondsAt R x.1 s).flatMap fun w =>
      [(ss s,x::w),(-ss s,w++[x])]) ≤ 4*‖ss s‖ := by
    rcases s with a|⟨d,a,b⟩ <;> simp [bondsAt] <;> linarith [norm_nonneg (ss (.inl a))]
  have many (l : List (Shape R)) : Form.mass (l.flatMap fun s => (bondsAt R x.1 s).flatMap fun w =>
      [(ss s,x::w),(-ss s,w++[x])]) ≤ (l.map fun s => 4*‖ss s‖).sum := by
    induction l with
    | nil => simp
    | cons s l ih => simpa only [List.flatMap_cons,Form.mass_append,List.map_cons,List.sum_cons] using add_le_add (shape s) ih
  have b := many (Finset.univ : Finset (Shape R)).toList
  rw [Finset.sum_map_toList] at b
  apply b.trans
  change _ ≤ 2*(1 + ∑ s : Shape R, 2*‖ss s‖)
  rw [mul_add,Finset.mul_sum]
  have eq (s : Shape R) : 2*(2*‖ss s‖) = 4*‖ss s‖ := by ring
  simp_rw [eq]
  linarith

theorem step_mass (xs : Script (Site ν)) : Form.mass (step R h J xs) ≤ 2 * incidentBound R h J * xs.length := by
  induction xs with
  | nil => simp [step]
  | cons x xs ih =>
    simp only [step, Form.mass_append,Form.mass_changeWords,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [spin_mass R h J x]

theorem step_length (xs : Script (Site ν)) (p) (hp : p ∈ step R h J xs) : p.2.length ≤ xs.length+2 := by
  induction xs generalizing p with
  | nil => simp [step] at hp
  | cons x xs ih =>
    rcases List.mem_append.mp hp with ha|hb
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      obtain ⟨s,_,w,hw,hp⟩ := (by simpa only [spinStep,List.mem_flatMap] using hq :
        ∃ s ∈ (Finset.univ : Finset (Shape R)).toList, ∃ w ∈ bondsAt R x.1 s, q ∈ [(_,x::w),(_,w++[x])])
      have short : w.length ≤ 2 := by rcases s with a|⟨d,a,b⟩ <;> simp_all [bondsAt]; aesop
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp <;> omega
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
      have := ih q hq
      simp; omega

private theorem disjoint_zero {B : Type*} [Fintype B] [DecidableEq B] {i : B} {a : Axis}
    {w : Label B} (hw : i ∉ supp w) : bracket (word (oneLabel i a)) (word w) = 0 := by
  have hd : Disjoint (supp (oneLabel i a)) (supp w) := by simpa [supp_one] using hw
  rw [Pauli.commutator,phase_eq_of_disjoint hd,sub_self,zero_smul]

private theorem spinStep_eval (n : ℕ) (x : Atom (Site ν)) :
    Form.apply (spinStep R h J x) (eval (place R n)) =
      ad (boxInteraction R h J n).matrix (eval (place R n) [x]) := by
  classical
  let f := place R n
  let X := word (oneLabel (f x.1) x.2)
  let v := fun s i => word (termLabel R n (s,i))
  have conv (s : Shape R) :
      ((bondsAt R x.1 s).map (fun w => bracket X (eval f w))).sum =
      ∑ i, bracket X (v s i) := by
    rcases s with a|⟨d,a,b⟩
    · rw [Finset.sum_eq_single (f x.1)]
      · simp [bondsAt,v,termLabel]
      · intro j _ hj
        exact disjoint_zero (by simpa [supp_one,termLabel] using hj.symm)
      · simp
    · let e := f d
      have nonzero : e ≠ 0 := (periodicBonds R n).nonzero _ (Finset.mem_image_of_mem _ d.property)
      have add (i j : Site ν) : f (i+j) = f i+f j := by funext k; simp [f,place,periodicSite,reduceBond]
      have sub (i j : Site ν) : f (i-j) = f i-f j := by funext k; simp [f,place,periodicSite,reduceBond]
      have pair (j : Box R n) : word (oneLabel j a) * word (oneLabel (j+e) b) = v (.inr (d,a,b)) j := by
        simpa [v,termLabel,e,f,string,inBasis] using string_pair (1 : (Op (Config (Box R n)))ˣ)
          (show j ≠ j+e from Ne.symm (by simpa using nonzero)) a b
      let K : Finset (Box R n) := {f x.1, f x.1-e}
      rw [← Finset.sum_subset (Finset.subset_univ K) (by
        intro j _ hj
        apply disjoint_zero
        simp only [termLabel,supp_two,Finset.mem_insert,Finset.mem_singleton]
        have h : j ≠ f x.1 ∧ j ≠ f x.1-e := by simpa [K] using hj
        exact fun h' => h'.elim h.1.symm (fun he => h.2 (eq_sub_iff_add_eq.mpr he.symm)))]
      have ne : f x.1 ≠ f x.1-e := by intro he; exact nonzero (by simpa using (eq_sub_iff_add_eq.mp he))
      have second := pair (f x.1-e)
      simp only [sub_add_cancel] at second
      simp [K,bondsAt,add,sub,pair,second,e,ne]
  have eval_list (s : Shape R) (ws : List (Script (Site ν))) :
      Form.apply (ws.flatMap fun w => [(strength R h J s,x::w),(-strength R h J s,w++[x])]) (eval f) =
      strength R h J s • (ws.map fun w => bracket X (eval f w)).sum := by
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simp only [List.flatMap_cons,Form.apply_append,Form.apply_cons,Form.apply_nil,add_zero,
        eval_cons,eval_append,eval_nil,mul_one,neg_smul,List.map_cons,List.sum_cons,smul_add,ih]
      simp [X,bracket,sub_eq_add_neg]
  have all (ss : List (Shape R)) :
      Form.apply (ss.flatMap fun s => (bondsAt R x.1 s).flatMap fun w =>
        [(strength R h J s,x::w),(-strength R h J s,w++[x])]) (eval f) =
        (ss.map fun s => strength R h J s • ∑ i, bracket X (v s i)).sum := by
    induction ss with
    | nil => simp
    | cons s ss ih => simp only [List.flatMap_cons,Form.apply_append,eval_list,conv,ih,List.map_cons,List.sum_cons]
  rw [spinStep,all,Finset.sum_map_toList]
  simp only [eval_cons,eval_nil,mul_one]
  change _ = X * (boxInteraction R h J n).matrix - (boxInteraction R h J n).matrix * X
  simp only [PauliInteraction.matrix,Fintype.sum_prod_type,boxInteraction,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.mul_smul,Matrix.smul_mul,← Finset.sum_sub_distrib,← smul_sub,Finset.smul_sum,bracket,v]

theorem step_eval (n : ℕ) (xs : Script (Site ν)) :
    Form.apply (step R h J xs) (eval (place R n)) =
      ad (boxInteraction R h J n).matrix (eval (place R n) xs) := by
  induction xs with
  | nil => simp [step,ad]
  | cons x xs ih =>
    let X := word (oneLabel (place R n x.1) x.2)
    let B := eval (place R n) xs
    have left := Form.map_apply (LinearMap.mulRight ℂ B) (spinStep R h J x) (eval (place R n))
    have right := Form.map_apply (LinearMap.mulLeft ℂ X) (step R h J xs) (eval (place R n))
    simp only [LinearMap.mulRight_apply,LinearMap.mulLeft_apply,spinStep_eval,ih] at left right
    simp only [step,Form.apply_append,Form.apply_changeWords,eval_append,eval_cons]
    change Form.apply _ (fun q => eval (place R n) q * B) + Form.apply _ (fun q => X * eval (place R n) q) = _
    rw [← left,← right]
    simp only [eval_cons,eval_nil,mul_one]
    exact (mul_bracket X B _).symm

end DSFTomography.HT.LocalWord
