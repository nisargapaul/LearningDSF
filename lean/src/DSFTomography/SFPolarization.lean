import DSFTomography.SFGroundState

noncomputable section
namespace DSFTomography.SF
open DSFTomography HT HT.Pauli
variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem comm_site {r s : S} (ne : r ≠ s) (a b : Axis) :
    spinAt r a * spinAt s b = spinAt s b * spinAt r a := by
  apply sub_eq_zero.mp
  simpa [ne,qubitSpins,string,inBasis,spinAt] using (qubitSpins (1 : (Op (Config S))ˣ)).pauli r a s b

private theorem anti_site (r : S) {i a : Axis} (ne : i ≠ a) :
    spinAt r i * spinAt r a = -(spinAt r a * spinAt r i) := by
  have si : sign i a = -sign a i ∧ third i a = third a i := by
    have axes (b : Axis) : b=0 ∨ b=1 ∨ b=2 := by fin_cases b <;> decide
    rcases axes i with rfl|rfl|rfl <;> rcases axes a with rfl|rfl|rfl <;> simp [axisTable]
  have p := string_same_site (1 : (Op (Config S))ˣ) r i a ne
  have q := string_same_site (1 : (Op (Config S))ˣ) r a i ne.symm
  simp only [string,inBasis,Units.val_one,inv_one,one_mul,mul_one] at p q
  rw [spinAt,spinAt,p,q,si.1,si.2,mul_neg,neg_smul]

private theorem norm_sides (ρ : State (Config S)) (r : S) (i : Axis)
    (pol : 1-(ρ.ev (spinAt r i)).re ≤ 1/2048)
    (A : Op (Config S)) (self : A.conjTranspose=A) (unit : A*A=1) :
    ‖ρ.ev ((1-spinAt r i)*A)‖ ≤ 1/32 ∧ ‖ρ.ev (A*(1-spinAt r i))‖ ≤ 1/32 := by
  let Z := spinAt r i
  have square : Z*Z=1 := by simpa [Z,spinAt,word_hermitian] using word_unit (oneLabel r i)
  have zz : (1-Z)*(1-Z) = 1-Z + (1-Z) := by noncomm_ring [square]
  have herm : (1-Z).conjTranspose=1-Z := by simp [Z,spinAt,word_hermitian]
  have l := ρ.cs (1-Z) A
  have r := ρ.cs A (1-Z)
  simp only [herm,self,unit,zz,map_add,map_sub,ρ.normed,Complex.add_re,Complex.sub_re,Complex.one_re,mul_one,one_mul] at l r
  change 1-(ρ.ev Z).re ≤ 1/2048 at pol
  constructor <;> nlinarith

/-- Uniform control of the two-spin static matrix, including its off-diagonal
components. The numerical constant is a sufficient field bound. -/
theorem ground_correlation {T : Type*} [Fintype T] (ρ : State (Config S))
    (I : PauliInteraction S T) {g B : ℝ} (hB : 0 < B) (hg : 0≤g) (incident : I.SiteBound g)
    (large : 4096*g ≤ B) (i : Axis) (ground : ρ.Ground (zeeman B i + I.matrix))
    {r s : S} (ne : r≠s) (a b : Axis) :
    ‖ρ.ev (spinAt r a * spinAt s b) - polarizedCorrelation i a b‖ ≤ 1/16 := by
  have pol (t : S) : 1-(ρ.ev (spinAt t i)).re ≤ 1/2048 :=
    (ground_polarization ρ I hB hg incident i ground t).trans ((div_le_iff₀ hB).mpr (by linarith))
  let A := spinAt r a * spinAt s b
  have commute := comm_site ne a b
  have self : A.conjTranspose=A := by simpa [A,spinAt,word_hermitian] using commute.symm
  have sq (t : S) (c : Axis) : spinAt t c * spinAt t c = 1 := by
    simpa [spinAt,word_hermitian] using word_unit (oneLabel t c)
  have unit : A*A=1 := by
    change (spinAt r a * spinAt s b) * (spinAt r a * spinAt s b) = 1
    conv_lhs => lhs; rw [commute]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (spinAt r a),sq,one_mul,sq]
  have off (t : S) (anti : spinAt t i*A = -(A*spinAt t i)) : ‖ρ.ev A‖ ≤ 1/16 := by
    have e : (1-spinAt t i)*A + A*(1-spinAt t i) = A+A := by
      simp [Matrix.sub_mul,Matrix.mul_sub,anti]
    have l := norm_sides ρ t i (pol t) A self unit
    have bnd := norm_add_le (ρ.ev ((1-spinAt t i)*A)) (ρ.ev (A*(1-spinAt t i)))
    rw [← map_add,e,map_add,← two_mul,norm_mul] at bnd
    norm_num at bnd; linarith [l.1,l.2]
  by_cases ha : a=i
  · subst a
    by_cases hb : b=i
    · subst b
      have sides := norm_sides ρ r i (pol r) (spinAt s i) (word_hermitian _) (sq s i)
      have endpt := (norm_sides ρ s i (pol s) 1 (by simp) (by simp)).1
      have e : 1 - spinAt r i * spinAt s i = (1-spinAt r i)*spinAt s i + (1-spinAt s i) := by noncomm_ring
      simp only [mul_one] at endpt
      simp only [polarizedCorrelation,and_self,ite_true]
      rw [norm_sub_rev,← ρ.normed,← map_sub,e,map_add]
      exact (norm_add_le ..).trans (by linarith [sides.1])
    · simp only [polarizedCorrelation,hb,and_false,ite_false,sub_zero]
      apply off s
      dsimp [A]
      rw [← Matrix.mul_assoc,comm_site ne.symm,Matrix.mul_assoc,anti_site _ (Ne.symm hb),Matrix.mul_neg,Matrix.mul_assoc]
  · simp only [polarizedCorrelation,ha,false_and,ite_false,sub_zero]
    apply off r
    dsimp [A]
    rw [← Matrix.mul_assoc,anti_site _ (Ne.symm ha),neg_mul,Matrix.mul_assoc,comm_site ne i b,Matrix.mul_assoc]

end DSFTomography.SF
