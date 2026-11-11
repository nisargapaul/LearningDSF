import DSFTomography.HTDiagonalFeatures

noncomputable section
namespace DSFTomography.HT.Diagonal
open DSFTomography HT
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

omit [AddCommGroup S] [Fintype S] in
private theorem two_same {r s : S} (hrs : r ≠ s) (a b u v : Axis) :
    twoLabel r s a b = twoLabel r s u v ↔ a=u ∧ b=v := by
  constructor
  · intro h
    exact ⟨by simpa [twoLabel] using congrFun h r, by simpa [twoLabel,hrs.symm] using congrFun h s⟩
  · rintro ⟨rfl,rfl⟩; rfl

omit [AddCommGroup S] in
private theorem spins_pair {r s : S} (hrs : r ≠ s) (u v : Axis) :
    spin r u * spin s v = word (twoLabel r s u v) := by
  simpa [spin,string,inBasis] using string_pair (1 : (Op (Config S))ˣ) hrs u v

omit [AddCommGroup S] in
private theorem unused_site {i j r s : S} (a b u v : Axis) (hrs : r ≠ s)
    (absent : (r ≠ i ∧ r ≠ j) ∨ (s ≠ i ∧ s ≠ j)) :
    (spin i a * spin j b * word (twoLabel r s u v)).trace = 0 := by
  simp only [spin,word,tensor_mul,trace_tensor]
  have tr (k : Axis) : (pauli (some k)).trace = 0 := by
    simpa [show pauli none = 1 from rfl] using trace_pauli_pair (some k) none
  rcases absent with ⟨hi,hj⟩|⟨hi,hj⟩
  · apply Finset.prod_eq_zero (Finset.mem_univ r)
    simp [oneLabel,twoLabel,hi,hj,show pauli none = 1 from rfl,tr]
  · apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [oneLabel,twoLabel,hrs.symm,hi,hj,show pauli none = 1 from rfl,tr]

omit [AddCommGroup S] in
private theorem fourTrace {r s : S} (hrs : r ≠ s) (i j : S) (a b u v : Axis) :
    (spin i a * spin j b * word (twoLabel r s u v)).trace =
      (if i=r ∧ j=s ∧ a=u ∧ b=v then dim S else 0) +
      (if i=s ∧ j=r ∧ a=v ∧ b=u then dim S else 0) := by
  by_cases h : i=r ∧ j=s
  · obtain ⟨hi,hj⟩ := h; subst i; subst j; rw [spins_pair hrs,word_overlap]; simp [two_same hrs,hrs,dim]
  by_cases k : i=s ∧ j=r
  · obtain ⟨hi,hj⟩ := k; subst i; subst j
    have swap : twoLabel s r a b = twoLabel r s b a := by
      funext t; by_cases h₁ : t=r <;> by_cases h₂ : t=s <;> simp_all [twoLabel]
    rw [spins_pair hrs.symm,swap,word_overlap]; simp [two_same hrs,hrs.symm,and_comm,dim]
  have absent : (r≠i ∧ r≠j) ∨ (s≠i ∧ s≠j) := by grind
  rw [unused_site a b u v hrs absent,if_neg (by tauto),if_neg (by tauto),add_zero]

theorem fieldCorrelation (R : Bonds S) (h : Axis → ℝ) {d : S} (hd : d ∈ R.dirs) (u v : Axis) :
    quadraticCorrelation (qubitH R h (fun _ => 0)) d u v = (h u : ℂ)*h v := by
  have pure : qubitH R h (fun _ => 0) = ∑ i, ∑ a, (h a : ℂ) • spin i a := by
    simp [qubitH,realH,H,qubitSpins,string,inBasis,spin]
  have calcSite (r : S) : ((qubitH R h (fun _ => 0))*(qubitH R h (fun _ => 0))*
      (spin r u * spin (r+d) v)).trace / (2*dim S) = (h u : ℂ)*h v := by
    have hrs : r ≠ r+d := Ne.symm (by simpa using R.nonzero d hd)
    rw [pure,spins_pair hrs]
    simp only [Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_sum,
      Matrix.trace_smul,smul_eq_mul,fourTrace hrs,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
    simp [ite_and,mul_ite,Finset.sum_ite_irrel,dim]
    field_simp; ring
  simp [quadraticCorrelation,calcSite,avg,Fintype.card_ne_zero]
end DSFTomography.HT.Diagonal
