import DSFTomography.SFSmallFieldModel
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Spin-flip amplitudes for the high-field cluster equation. A configuration
labels the sites flipped from the vacuum. Products of X strings add these
labels modulo two. The ℓ¹ norm counts amplitudes per interaction translate. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT
open scoped BigOperators
variable {S : Type*} [Fintype S] [DecidableEq S]
abbrev Amp (S : Type*) [Fintype S] := PiLp 1 (fun _ : Config S => ℂ)

def basis (x : Config S) : Amp S := WithLp.toLp 1 (fun y => if y=x then 1 else 0)
omit [DecidableEq S] in
@[simp] theorem basis_at (x y : Config S) : basis x y = if y=x then 1 else 0 := rfl
@[simp] theorem norm_basis (x : Config S) : ‖basis x‖ = 1 := by
  simp [PiLp.norm_eq_of_L1,apply_ite]

theorem sum_basis (v : Amp S) : ∑ x, (v x) • basis x = v := by
  apply WithLp.ofLp_injective; funext k
  let φ := PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Config S => ℂ) 1 k
  change φ (∑ x, v x • basis x) = v k
  simp only [map_sum,map_smul]
  change (∑ x, (v x : ℂ) * (if k=x then 1 else 0)) = v k
  simp [mul_ite]

def columns (f : Config S → Amp S) : Amp S →L[ℂ] Amp S :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => ∑ x, (v x) • f x
    map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
    map_smul' := by intros; simp [Finset.smul_sum,mul_smul] }

theorem columns_apply (f : Config S → Amp S) (v : Amp S) :
    columns f v = ∑ x, v x • f x := rfl
@[simp] theorem columns_basis (f : Config S → Amp S) (x : Config S) :
    columns f (basis x) = f x := by simp [columns_apply,ite_smul]
theorem columns_norm_le (f : Config S → Amp S) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, ‖f x‖ ≤ c) :
    ‖columns f‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  rw [columns_apply,PiLp.norm_eq_of_L1 v,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => by
    rw [norm_smul,mul_comm c]; gcongr; exact h x)

def flip (x : Config S) := columns (fun y => basis (x+y))
theorem flip_bound (x : Config S) : ‖flip x‖ ≤ 1 :=
  columns_norm_le _ zero_le_one (by simp)

def convolution (v : Amp S) : Amp S →L[ℂ] Amp S := ∑ x, v x • flip x

theorem convolution_bound (v : Amp S) : ‖convolution v‖ ≤ ‖v‖ := by
  rw [PiLp.norm_eq_of_L1 v]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (flip_bound x))

def convolute : Amp S →L[ℂ] (Amp S →L[ℂ] Amp S) :=
  LinearMap.toContinuousLinearMap {
    toFun := convolution
    map_add' := by
      intro u v; unfold convolution; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => add_smul (u x : ℂ) (v x) (flip x))
    map_smul' := by intros; simp [convolution,Finset.smul_sum,mul_smul] }

theorem convolute_bound : ‖convolute (S := S)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using convolution_bound (S := S))

def flipCount (x : Config S) := (Finset.univ.filter fun s => x s ≠ 0).card

/-- Z on each of the sites in D changes the sign of a flip amplitude by
the product of the one-site signs. Repeated sites cancel. -/
def phase (D : List S) (x : Config S) : ℂ :=
  (D.map fun s => if x s=0 then (1:ℂ) else -1).prod

omit [Fintype S] [DecidableEq S] in
@[simp] theorem norm_phase (D : List S) (x : Config S) : ‖phase D x‖ = 1 := by
  induction D with
  | nil => simp [phase]
  | cons s D ih =>
    change ‖(if x s=0 then (1:ℂ) else -1)* phase D x‖ = _
    split <;> simp [ih]

variable [AddCommGroup S]
def translated (t : S) (x : Config S) : Config S := fun s => x (s-t)

omit [DecidableEq S] in
/-- Summing over all possible anchors costs exactly the number of excited
sites, which cancels the unperturbed excitation-energy denominator. -/
private theorem touches (s : S) (x : Config S) :
    (∑ t : S, if translated t x s = 0 then (0:ℝ) else 1) = flipCount x := by
  let e : S ≃ S := (Equiv.neg S).trans (Equiv.addLeft s)
  have h := e.sum_comp (fun t => if x t=0 then (0:ℝ) else 1)
  have e_eq (t : S) : e t = s-t := by simp [e,sub_eq_add_neg]
  simp only [e_eq] at h
  rw [show (∑ t, if translated t x s = 0 then (0:ℝ) else 1) =
    ∑ t, if x (s-t)=0 then (0:ℝ) else 1 from rfl,h]
  simp [flipCount,← Finset.sum_boole]

omit [DecidableEq S] in
theorem phase_cost (D : List S) (x : Config S) :
    ∑ t : S, ‖phase D (translated t x) - 1‖ ≤ 2*D.length*flipCount x := by
  induction D with
  | nil => simp [phase]
  | cons s D ih =>
    have one (t : S) : ‖phase (s::D) (translated t x)-1‖ ≤
        (if translated t x s=0 then 0 else 2) + ‖phase D (translated t x)-1‖ := by
      change ‖(if translated t x s=0 then (1:ℂ) else -1)*phase D (translated t x) -1‖ ≤ _
      split_ifs
      · simp
      · let z := phase D (translated t x)
        change ‖-1*z-1‖ ≤ 2+‖z-1‖
        calc
          _ = ‖(-2:ℂ)*z+(z-1)‖ := by congr 1; ring
          _ ≤ _ := (norm_add_le ..).trans (by simp [z])
    have count := congrArg (fun a : ℝ => 2*a) (touches s x)
    simp only [Finset.mul_sum,mul_ite,mul_zero,mul_one] at count
    exact (Finset.sum_le_sum fun t _ => one t).trans (by
      rw [Finset.sum_add_distrib,count,List.length_cons,Nat.cast_add_one]; linarith)

def responseColumn (D : List S) (x : Config S) : Amp S :=
  (2*(flipCount x : ℂ))⁻¹ • ∑ t : S, (phase D (translated t x)-1) • basis (translated t x)

def response (D : List S) := columns (responseColumn D)

theorem response_bound (D : List S) : ‖response D‖ ≤ D.length := by
  apply columns_norm_le _ (by positivity)
  intro x
  rw [responseColumn,norm_smul]
  by_cases hx : flipCount x=0
  · simp [hx]
  have pos : 0 < (2:ℝ)*flipCount x := by positivity
  simp only [norm_inv,norm_mul,Complex.norm_two,Complex.norm_natCast]
  rw [← div_eq_inv_mul,div_le_iff₀ pos]
  calc
    _ ≤ ∑ t : S, ‖(phase D (translated t x)-1) • basis (translated t x)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul,norm_basis,mul_one]
    _ ≤ _ := (phase_cost D x).trans_eq (by ring)

end DSFTomography.SF.Cluster
