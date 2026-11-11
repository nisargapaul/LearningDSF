import DSFTomography.SFResponse

/-! Product-basis matrix elements of an arbitrary oriented lattice Hamiltonian.
Configurations are expressed in the cyclic field frame (j,k,i)=(X,Y,Z). -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def bitConfig (A : Finset S) : Config S := fun t => if t ∈ A then 1 else 0

private def oneBlock (h : Axis → ℝ) (i : Axis) (p q : Fin 2) : ℂ :=
  ∑ a, (h (axisInLab i a) : ℂ) * pauli (some a) p q

private def oneEntry (h : Axis → ℝ) (i : Axis) (t : S) (x y : Config S) : ℂ :=
  if ∀ s ≠ t, x s = y s then oneBlock h i (x t) (y t) else 0

private def twoEntry (K : Axis → Axis → ℝ) (i : Axis) (t u : S) (x y : Config S) : ℂ :=
  if ∀ s, s ≠ t → s ≠ u → x s = y s then bondEntry K i (x t,x u) (y t,y u) else 0

def fieldFrame (V : Volume S) (i : Axis) := qubitH V.R
  (fun a => V.h (axisInLab i a)) (fun d a b => V.J d (axisInLab i a) (axisInLab i b))

omit [AddCommGroup S] in
theorem word_one (t : S) (a : Axis) (x y : Config S) :
    word (oneLabel t a) x y = if ∀ s ≠ t, x s = y s then pauli (some a) (x t) (y t) else 0 := by
  classical
  change (∏ s, pauli (oneLabel t a s) (x s) (y s)) = _
  split_ifs with outside
  · rw [Finset.prod_eq_single t]
    · simp [oneLabel]
    · intro s _ ne; simp only [oneLabel,if_neg ne,pauli,Matrix.one_apply,if_pos (outside s ne)]
    · simp
  · push_neg at outside
    obtain ⟨s,ne,diff⟩ := outside
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [oneLabel,ne,pauli,Matrix.one_apply_ne diff])

omit [AddCommGroup S] in
private theorem word_two (t u : S) (ne : t≠u) (a b : Axis) (x y : Config S) :
    word (twoLabel t u a b) x y = if ∀ s, s ≠ t → s ≠ u → x s = y s then
      pauli (some a) (x t) (y t) * pauli (some b) (x u) (y u) else 0 := by
  classical
  let f := fun s => pauli (twoLabel t u a b s) (x s) (y s)
  change (∏ s, f s) = _
  split_ifs with outside
  · rw [← Finset.mul_prod_erase _ f (Finset.mem_univ t),Finset.prod_eq_single u]
    · simp [f,twoLabel,ne.symm]
    · intro s hs nu
      have nt := Finset.ne_of_mem_erase hs
      simp only [f,twoLabel,if_neg nt,if_neg nu,pauli,Matrix.one_apply,if_pos (outside s nt nu)]
    · simp [ne.symm]
  · push_neg at outside
    obtain ⟨s,nt,nu,diff⟩ := outside
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [f,twoLabel,nt,nu,pauli,Matrix.one_apply_ne diff])

theorem fieldFrame_entries (V : Volume S) (i : Axis) (x y : Config S) :
    fieldFrame V i x y = (∑ t, oneEntry V.h i t x y) +
      ∑ d ∈ V.R.dirs, ∑ t, twoEntry (V.J d) i t (t+d) x y := by
  unfold fieldFrame qubitH realH
  rw [H_words (qubitSpins 1) 1 (fun _ _ => rfl)]
  simp only [string,inBasis,Units.val_one,one_mul,inv_one,mul_one,Matrix.add_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [word_one]
    by_cases same : ∀ s ≠ t, x s = y s <;> simp [oneEntry,oneBlock,same]
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro t _
    have ne : t≠t+d := Ne.symm (by simpa using V.R.nonzero d hd)
    simp only [word_two _ _ ne]
    by_cases same : ∀ s, s ≠ t → s ≠ t+d → x s = y s <;> simp [twoEntry,bondEntry,same,mul_assoc]

/-- A transition changing both endpoints of an oriented bond isolates that
bond in the full many-spin Hamiltonian. This applies to hopping and to pair
creation even if other bonds share either endpoint. -/
theorem isolate_transition (V : Volume S) (i : Axis) {d : S} (hd : d∈V.R.dirs)
    (r : S) (x y : Config S) (left : x r ≠ y r) (right : x (r+d) ≠ y (r+d))
    (outside : ∀ s, s ≠ r → s ≠ r+d → x s = y s) :
    fieldFrame V i x y = bondEntry (V.J d) i (x r,x (r+d)) (y r,y (r+d)) := by
  have ne : r ≠ r+d := Ne.symm (by simpa using V.R.nonzero d hd)
  rw [fieldFrame_entries,Finset.sum_eq_zero (f := fun t => oneEntry V.h i t x y)
    (fun t _ => ?_),zero_add]
  · have select (e t : S) (he : e ∈ V.R.dirs) (same : ∀ s, s ≠ t → s ≠ t+e → x s = y s) :
        t=r ∧ e=d := by
      have loc (s : S) (diff : x s ≠ y s) : s=t ∨ s=t+e := by
        by_contra! no; exact diff (same s no.1 no.2)
      rcases loc r left with h|h <;> rcases loc (r+d) right with k|k
      · exact (ne (h.trans k.symm)).elim
      · exact ⟨h.symm,(add_left_cancel (h ▸ k)).symm⟩
      · exfalso
        apply V.R.oriented d hd e he
        have h' : r+(d+e)=r := by rw [←add_assoc,k,←h]
        simpa using h'
      · exact (ne (h.trans k.symm)).elim
    rw [Finset.sum_eq_single d]
    · rw [Finset.sum_eq_single r]
      · exact if_pos outside
      · intro t _ htr
        simp only [twoEntry]; split_ifs with hs
        · exact (htr (select d t hd hs).1).elim
        · rfl
      · simp
    · intro e he hed
      apply Finset.sum_eq_zero
      intro t _
      simp only [twoEntry]; split_ifs with hs
      · exact (hed (select e t he hs).2).elim
      · rfl
    · simp [hd]
  · dsimp only [oneEntry]
    split_ifs with same
    · by_cases h : t = r
      · subst t; exact (right (same _ ne.symm)).elim
      · exact (left (same _ (Ne.symm h))).elim
    · rfl

/-- The two transitions have the same selected bond and different input
configurations. The incoming ket fixes the sign in the sine harmonic. -/
theorem flip_entries (V : Volume S) (i : Axis) {d : S} (hd : d∈V.R.dirs) (r : S) :
    fieldFrame V i (bitConfig {r}) (bitConfig {r+d}) = bondEntry (V.J d) i (1,0) (0,1) ∧
    fieldFrame V i (bitConfig {r,r+d}) (bitConfig ∅) = bondEntry (V.J d) i (1,1) (0,0) := by
  have ne : r ≠ r+d := Ne.symm (by simpa using V.R.nonzero d hd)
  constructor <;> rw [isolate_transition V i hd r] <;> simp_all [bitConfig]

/-- Relative to the vacuum a single reversed spin changes one on-site energy
and the two ends of every bond type. Spectator terms cancel exactly. -/
theorem flip_energy_shift (V : Volume S) (i : Axis) (r : S) :
    (fieldFrame V i (bitConfig {r}) (bitConfig {r}) -
     fieldFrame V i (bitConfig ∅) (bitConfig ∅)) =
    (-2 * V.h i - 4 * ∑ d ∈ V.R.dirs, V.J d i i : ℝ) := by
  let f := bitConfig ({r} : Finset S)
  let o := bitConfig (∅ : Finset S)
  have on (t : S) : oneEntry V.h i t f f - oneEntry V.h i t o o =
      if t=r then -2*(V.h i : ℂ) else 0 := by
    by_cases h : t=r
    · subst t
      simp [oneEntry,oneBlock,f,o,bitConfig,axisInLab,Fin.sum_univ_three,pauliValues]; ring
    · simp [oneEntry,f,o,bitConfig,h]
  have bond (d : S) (hd : d ∈ V.R.dirs) (t : S) :
      twoEntry (V.J d) i t (t+d) f f - twoEntry (V.J d) i t (t+d) o o =
      (if t=r then -2*(V.J d i i : ℂ) else 0) +
      (if t=r-d then -2*(V.J d i i : ℂ) else 0) := by
    have nd := V.R.nonzero d hd
    have entry := polarized_bond_entries (V.J d) i
    by_cases h : t=r
    · subst t
      have ne : r+d ≠ r := by simpa using nd
      have nr : r ≠ r-d := fun h => ne ((eq_sub_iff_add_eq).mp h)
      simpa [twoEntry,f,o,bitConfig,ne,nr] using entry.2.2.1
    · by_cases he : t+d=r
      · have hs := eq_sub_iff_add_eq.mpr he
        simpa [twoEntry,f,o,bitConfig,h,he,hs,nd] using entry.2.2.2
      · have hs : t ≠ r-d := fun h => he (eq_sub_iff_add_eq.mp h)
        simp [twoEntry,f,o,bitConfig,h,he,hs]
  change fieldFrame V i f f - fieldFrame V i o o = _
  rw [fieldFrame_entries,fieldFrame_entries,add_sub_add_comm,← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  simp_rw [on]
  have subs (d : S) (hd : d∈V.R.dirs) :
      (∑ t, twoEntry (V.J d) i t (t+d) f f) - (∑ t, twoEntry (V.J d) i t (t+d) o o) =
        -4*(V.J d i i:ℂ) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [bond d hd]
    rw [Finset.sum_add_distrib]
    simp; ring
  rw [Finset.sum_congr rfl subs]
  simp [← Finset.mul_sum]; ring

/-- In the shifted unit-field Hamiltonian a one-flip state costs two and a
two-flip state costs four. -/
def flipGap (x : Config S) : ℂ := 2 * ((Finset.univ.filter (fun s => x s = 1)).card : ℂ)

omit [AddCommGroup S] in
theorem flipGap_bits (A : Finset S) : flipGap (bitConfig A) = 2*(A.card : ℂ) := by
  have eq : Finset.univ.filter (fun s => bitConfig A s = 1) = A := by
    ext s; by_cases h : s∈A <;> simp [bitConfig,h]
  simp [flipGap,eq]

omit [AddCommGroup S] [Fintype S] in
theorem bitConfig_injective : Function.Injective (bitConfig (S := S)) := by
  intro a b eq; ext s
  have atS := congrFun eq s
  by_cases h : s∈a <;> by_cases k : s∈b <;> simp_all [bitConfig]

omit [AddCommGroup S] in
theorem transverse_pair_column {r s : S} (ne : r≠s) (a b : Axis) (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    (x : Config S) :
    word (twoLabel r s a b) x (bitConfig ∅) =
       (pauli (some a) 1 0 * pauli (some b) 1 0) * ket (bitConfig {r,s}) x := by
  let o := bitConfig (∅ : Finset S)
  let p := bitConfig ({r,s} : Finset S)
  change word _ x o = _ * ket p x
  rw [word_two r s ne]
  by_cases eq : x=p
  · subst x
    have off (z : S) (nr : z ≠ r) (ns : z ≠ s) : p z = o z := by simp [p,o,bitConfig,nr,ns]
    rw [if_pos off]
    simp [p,o,bitConfig,ket]
  · rw [show ket p x = 0 from if_neg eq,mul_zero]
    split_ifs with outside
    · have h : x r = 0 ∨ x s = 0 := by
        by_contra! both
        apply eq
        funext z
        by_cases hr : z=r
        · subst z; have h1 : x r = 1 := by have := (x r).isLt; omega
          simp [p,bitConfig,h1]
        · by_cases hs : z=s
          · subst z; have h1 : x s = 1 := by have := (x s).isLt; omega
            simp [p,bitConfig,h1]
          · simpa [p,o,bitConfig,hr,hs] using outside z hr hs
      rcases h with h|h <;> rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
        simp [h,o,bitConfig,pauliValues]
    · rfl

end DSFTomography.SF
