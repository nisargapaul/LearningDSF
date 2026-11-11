import DSFTomography.PauliWords
import Mathlib.Analysis.Calculus.MeanValue

/-! Strong-field leading amplitudes for an oriented bond in the polarized
basis, their inverse, and stability of the inverse to a finite-field correction. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography
/-- In the frame polarized along i, the axes (i+1,i+2,i) are (X,Y,Z). -/
def axisInLab (i : Axis) : Axis → Axis := ![i+1,i+2,i]

/-- Matrix element of the actual two-site exchange between configurations in
the rotated Pauli basis. The first subscript is the source end of the bond. -/
def bondEntry (K : Axis → Axis → ℝ) (i : Axis) (p q : Fin 2 × Fin 2) : ℂ :=
  ∑ a, ∑ b, (K (axisInLab i a) (axisInLab i b) : ℂ) * HT.pauli (some a) p.1 q.1 * HT.pauli (some b) p.2 q.2

set_option maxHeartbeats 2000000 in
/-- Hopping in the one-flip subspace, pair creation from the vacuum, and the
diagonal shift when either endpoint flips. Here 0 means spin up. -/
theorem polarized_bond_entries (K : Axis → Axis → ℝ) (i : Axis) :
    let j := i+1
    let k := i+2
    bondEntry K i (1,0) (0,1) = (K j j + K k k : ℝ) - Complex.I*(K j k - K k j : ℝ) ∧
    bondEntry K i (1,1) (0,0) = (K j j - K k k : ℝ) + Complex.I*(K j k + K k j : ℝ) ∧
    bondEntry K i (1,0) (1,0) - bondEntry K i (0,0) (0,0) = -2*(K i i : ℂ) ∧
    bondEntry K i (0,1) (0,1) - bondEntry K i (0,0) (0,0) = -2*(K i i : ℂ) := by
  simp only [bondEntry,Fin.sum_univ_three,HT.pauliValues,axisInLab, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,Complex.ofReal_add,Complex.ofReal_sub]
  refine ⟨?_,?_,?_,?_⟩ <;> apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im] <;> ring


variable {D : Type*} [Fintype D]
abbrev Params (D : Type*) := (Axis → ℝ) × (D → Axis → Axis → ℝ)
abbrev Harmonics (D : Type*) := (Axis → ℝ) × (D → Axis → Fin 4 → ℝ)

/-- Constant centered harmonic and, in order, centered cosine, centered sine,
static difference cosine and static cross cosine. D indexes oriented bonds. -/
def leading (p : Params D) : Harmonics D := (
  fun i => -2*p.1 i - 4*∑ d, p.2 d i i,
  fun d i => let j := i+1; let k := i+2
    ![2*(p.2 d j j+p.2 d k k), 2*(p.2 d j k-p.2 d k j),
      p.2 d k k-p.2 d j j, -(p.2 d j k+p.2 d k j)])

/-- The four real bond harmonics in terms of physical spin-flip amplitudes.
The sine sign corresponds to the forward Fourier phase exp(+i q⋅d). -/
theorem leading_bond (p : Params D) (d : D) (i : Axis) :
    let hop := bondEntry (p.2 d) i (1,0) (0,1)
    let pair := bondEntry (p.2 d) i (1,1) (0,0)
    (leading p).2 d i = ![2*hop.re,-2*hop.im,-pair.re,-pair.im] := by
  obtain ⟨a,b,_,_⟩ := polarized_bond_entries (p.2 d) i
  simp [a,b,leading]; ring

def exchange (v : Harmonics D) (d : D) (a b : Axis) : ℝ :=
  if a=b then v.2 d (a+2) 0 / 4 - v.2 d (a+2) 2 / 2
  else if b=a+1 then v.2 d (a+2) 1 / 4 - v.2 d (a+2) 3 / 2
  else -v.2 d (b+2) 1 / 4 - v.2 d (b+2) 3 / 2

set_option maxHeartbeats 2000000 in
theorem exchange_leading (p : Params D) (d : D) (a b : Axis) : exchange (leading p) d a b = p.2 d a b := by
  have extract (u : Axis) : ((u+2)+1) = u ∧ ((u+2)+2) = u+1 := by fin_cases u <;> decide
  have diff : ∀ u v : Axis, u≠v → v≠u+1 → v+1=u := by decide
  unfold exchange
  split_ifs with ha hb
  · subst b; simp [leading,extract]; ring
  · subst b; simp [leading,extract]; ring
  · have t := diff a b ha hb
    simp [leading,extract,t]; ring



def readout (v : Harmonics D) : Params D :=
  (fun i => -v.1 i / 2 - 2*∑ d, exchange v d i i, exchange v)

theorem readout_leading (p : Params D) : readout (leading p) = p := by
  apply Prod.ext
  · funext i; simp only [readout,exchange_leading]; dsimp [leading]; ring
  · funext d a b; exact exchange_leading p d a b

/-- The decoder is a bounded linear map, including the subtraction of all
diagonal exchanges from the field readout. -/
def decoder : Harmonics D →L[ℝ] Params D :=
  LinearMap.toContinuousLinearMap {
    toFun := readout
    map_add' := by
      intro v w
      have add (d : D) (a b : Axis) : exchange (v+w) d a b = exchange v d a b + exchange w d a b := by
        unfold exchange; split_ifs <;> simp <;> ring
      apply Prod.ext
      · funext i; simp [readout,add,Finset.sum_add_distrib]; ring
      · funext d a b; exact add d a b
    map_smul' := by
      intro c v
      have scale (d : D) (a b : Axis) : exchange (c • v) d a b = c*exchange v d a b := by
        unfold exchange; split_ifs <;> simp <;> ring
      apply Prod.ext
      · funext i; simp [readout,scale,← Finset.mul_sum]; ring
      · funext d a b; exact scale d a b }

theorem finiteField_injective {domain : Set (Params D)} (cvx : Convex ℝ domain)
    (measured : Params D → Harmonics D) (dρ : Params D → Params D →L[ℝ] Harmonics D)
    {B C : ℝ} (hB : 0 < B) (large : ‖(decoder (D := D))‖*C < B)
    (derivative : ∀ p ∈ domain, HasFDerivWithinAt (fun q => measured q - leading q) (dρ p) domain p)
    (bound : ∀ p ∈ domain, ‖dρ p‖ ≤ C/B) : Set.InjOn measured domain := by
  intro p hp q hq same
  have growth := cvx.norm_image_sub_le_of_norm_hasFDerivWithin_le derivative bound hq hp
  rw [same] at growth
  have cancel : (measured q-leading p) - (measured q-leading q) = -(leading p-leading q) := by abel
  rw [cancel,norm_neg] at growth
  have inverse := (decoder (D := D)).le_opNorm (leading p-leading q)
  rw [map_sub,show decoder (leading p) = p from readout_leading p,
    show decoder (leading q) = q from readout_leading q] at inverse
  have contraction := inverse.trans (mul_le_mul_of_nonneg_left growth (norm_nonneg _))
  have small : ‖(decoder (D := D))‖*(C/B) < 1 := by rw [← mul_div_assoc,div_lt_one hB]; exact large
  by_contra ne
  have pos := norm_pos_iff.mpr (sub_ne_zero.mpr ne)
  nlinarith [mul_lt_mul_of_pos_right small pos]

end DSFTomography.SF
