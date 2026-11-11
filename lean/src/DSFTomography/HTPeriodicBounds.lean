import DSFTomography.HTGibbsRecursion
noncomputable section
namespace DSFTomography.HT
open DSFTomography Pauli
variable {ν : ℕ} (R : Bonds (Site ν))
abbrev Shape := Axis ⊕ (R.dirs × Axis × Axis)
abbrev periodicSite (n : ℕ) : Site ν → Box R n := reduceBond (periodIndex R n)
variable (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
def strength : Shape R → ℂ
  | .inl a => h a
  | .inr (d,a,b) => J d a b

def termLabel (n : ℕ) : Shape R × Box R n → Label (Box R n)
  | (.inl a,i) => oneLabel i a
  | (.inr (d,a,b),i) => twoLabel i (i+periodicSite R n d) a b

theorem supp_one {B : Type*} [Fintype B] [DecidableEq B] (i : B) (a : Axis) :
    supp (oneLabel i a) = {i} := by ext j; simp [supp,oneLabel]
theorem supp_two {B : Type*} [Fintype B] [DecidableEq B] (i j : B) (a b : Axis) :
    supp (twoLabel i j a b) = {i,j} := by
  ext s; by_cases hi : s=i <;> by_cases hj : s=j <;> simp_all [supp,twoLabel]

def boxInteraction (n : ℕ) : PauliInteraction (Box R n) (Shape R × Box R n) where
  label := termLabel R n
  weight t := strength R h J t.1
  two := by
    rintro ⟨a,i⟩
    rcases a with a|⟨d,a,b⟩
    · simp [termLabel,supp_one]
    · simpa only [termLabel,supp_two] using Finset.card_le_two

theorem boxInteraction_matrix (n : ℕ) :
    (boxInteraction R h J n).matrix = qubitH (periodicBonds R n) h (periodicVolume R h J n).J := by
  classical
  unfold qubitH realH
  rw [H_words (qubitSpins 1) 1 (fun _ _ => rfl)]
  simp only [PauliInteraction.matrix, boxInteraction, Fintype.sum_prod_type, Fintype.sum_sum_type,
    termLabel, strength, string, inBasis, Units.val_one, inv_one, one_mul, mul_one]
  apply congrArg₂ (· + ·)
  · exact Finset.sum_comm
  · rw [show (periodicBonds R n).dirs = R.dirs.image (periodicSite R n) from rfl,
      Finset.sum_image (injects_dirs R n), ← Finset.sum_attach R.dirs]
    apply Finset.sum_congr rfl
    intro d _
    simp only [periodicSite, image_coupling R h J n d.property]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    exact Finset.sum_comm

/-- Twice the sum of the strengths of the term shapes bounds the total at
one site, counting the two possible endpoints of each translated bond. -/
def incidentBound : ℝ := 1 + ∑ s : Shape R, 2 * ‖strength R h J s‖

theorem incidentBound_pos : 0 < incidentBound R h J := by unfold incidentBound; positivity

theorem boxInteraction_incident (n : ℕ) : (boxInteraction R h J n).SiteBound (incidentBound R h J) := by
  intro x
  rw [Fintype.sum_prod_type]
  apply le_trans _ (by unfold incidentBound; linarith : (∑ s : Shape R, 2 * ‖strength R h J s‖) ≤ _)
  apply Finset.sum_le_sum
  intro s _
  rcases s with a|⟨d,a,b⟩
  · simp [boxInteraction, termLabel, supp_one]
    linarith [norm_nonneg (strength R h J (.inl a))]
  · let e := periodicSite R n d.val
    let v := ‖strength R h J (.inr (d,a,b))‖
    change (∑ i, (if x ∈ supp (twoLabel i (i+e) a b) then v else 0)) ≤ 2 * v
    calc
      _ ≤ ∑ i, ((if i=x then v else 0) + (if i=x-e then v else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        have shift : x=i+e ↔ i=x-e := by rw [eq_sub_iff_add_eq]; exact eq_comm
        simp only [supp_two, Finset.mem_insert, Finset.mem_singleton, shift, @eq_comm _ x i]
        have hv : 0 ≤ v := norm_nonneg _
        have cover (A B : Prop) [Decidable A] [Decidable B] :
            (if A ∨ B then v else 0) ≤ (if A then v else 0) + (if B then v else 0) := by
          by_cases ha : A <;> by_cases hb : B <;> simp [ha,hb,hv]
        exact cover _ _
      _ = _ := by simp [Finset.sum_add_distrib, two_mul]

def bulkRadius : ℝ := (4 * incidentBound R h J)⁻¹
theorem bulkRadius_pos : 0 < bulkRadius R h J := inv_pos.mpr (mul_pos (by norm_num) (incidentBound_pos ..))

theorem periodic_zeroFree_bounded (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ bulkRadius R h J) :
    (periodicVolume R h J n).partition z ≠ 0 ∧ ∀ w : Label (Box R n),
      ‖((periodicVolume R h J n).boltzmann z * word w).trace‖ ≤ ‖(periodicVolume R h J n).partition z‖ := by
  have g := incidentBound_pos R h J
  refine Volume.zeroFree_and_bounded (periodicVolume R h J n) (boxInteraction R h J n) (boxInteraction_matrix R h J n) g.le
    (boxInteraction_incident R h J n) z ?_
  have hh : ‖z‖*(4*incidentBound R h J) ≤ 1 := by
    simpa only [one_div] using (le_div_iff₀ (by positivity : 0 < 4*incidentBound R h J)).mp (by simpa [bulkRadius,one_div] using hz)
  linarith

end DSFTomography.HT
