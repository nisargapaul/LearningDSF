import DSFTomography.SFClusterAlgebra

/-! Exact conjugation of a Pauli term by the exponential of commuting spin
flips. The excitation denominator is applied before summing over translates. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT NormedSpace
variable {S : Type*} [Fintype S] [DecidableEq S]
abbrev Operator (S : Type*) [Fintype S] := Amp S →L[ℂ] Amp S

local instance : SMul (Operator S) (Operator S) := ⟨(· * ·)⟩
local instance : IsScalarTower ℂ (Operator S) (Operator S) := ⟨fun _ _ _ => rfl⟩
local instance : SMulCommClass ℂ (Operator S) (Operator S) := ⟨fun z A B => by ext x : 1; exact (A.map_smul z (B x)).symm⟩

theorem operator_ext {A B : Operator S} (h : ∀ x, A (basis x) = B (basis x)) : A=B := by
  ext v : 1
  conv_lhs => rw [← sum_basis v,map_sum]
  conv_rhs => rw [← sum_basis v,map_sum]
  simp only [map_smul,h]

@[simp] theorem flip_basis (x y : Config S) : flip x (basis y) = basis (x+y) := columns_basis ..
theorem flip_comm (x y : Config S) : Commute (flip x) (flip y) := by
  apply operator_ext
  intro z; simp [ContinuousLinearMap.mul_apply,add_left_comm]

theorem convolution_comm (v w : Amp S) : Commute (convolute v) (convolute w) := by
  change Commute (∑ x, v x • flip x) (∑ y, w y • flip y)
  exact Commute.sum_left _ _ _ (fun x _ => Commute.sum_right _ _ _ fun y _ =>
    ((flip_comm x y).smul_left (v x : ℂ)).smul_right (w y : ℂ))

theorem convolution_basis (x : Config S) : convolute (basis x) = flip x := by
  change ∑ y, (basis x y) • flip y = _; rw [Finset.sum_eq_single x]
  · simp
  · intro y _ ne
    change (if y=x then (1:ℂ) else 0) • (flip y) = 0
    rw [if_neg ne]; ext v : 1; change (0:ℂ) • flip y v = 0; simp
  · simp

/-- Diagonal Z string on the given list of sites. -/
def signOp (D : List S) := columns fun x => phase D x • basis x

omit [Fintype S] [DecidableEq S] in
theorem phase_add (D : List S) (x y : Config S) : phase D (x+y) = phase D x * phase D y := by
  induction D with
  | nil => simp [phase]
  | cons s D ih =>
    let z := fun n : Fin 2 => if n=0 then (1:ℂ) else -1
    have hz (a b : Fin 2) : z (a+b) = z a*z b := by fin_cases a <;> fin_cases b <;> norm_num [z]; decide
    change z (x s+y s) * phase D (x+y) = (z (x s)*phase D x)*(z (y s)*phase D y)
    rw [hz,ih]; ring

omit [Fintype S] [DecidableEq S] in
@[simp] theorem phase_zero (D : List S) : phase D (0 : Config S) = 1 := by simp [phase]
@[simp] theorem sign_basis (D : List S) (x : Config S) :
    signOp D (basis x) = phase D x • basis x := columns_basis ..
theorem sign_convolve (D : List S) (v : Amp S) :
    signOp D * convolute v = convolute (signOp D v) * signOp D := by
  have single (x : Config S) :
      signOp D * flip x = phase D x • (flip x * signOp D) := by
    apply operator_ext; intro y
    simp [ContinuousLinearMap.mul_apply,phase_add,smul_smul]
  change signOp D * (∑ x, v x • flip x) = _
  conv_rhs => rw [← sum_basis v,map_sum,map_sum]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,map_smul,sign_basis,
    convolution_basis,single,smul_smul]

/-- Intertwining survives the norm-convergent exponential series. -/
theorem exp_intertwine {A B T : Operator S} (h : T*A=B*T) :
    T * exp ℂ A = exp ℂ B * T := by
  have pw (n : ℕ) : T*A^n=B^n*T := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,pow_succ,← mul_assoc,ih,mul_assoc,h,mul_assoc]
  have l := ((ContinuousLinearMap.mul ℂ (Operator S)) T).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℂ) A)
  have r := ((ContinuousLinearMap.mul ℂ (Operator S)).flip T).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℂ) B)
  exact (l.congr_fun (fun n => by
    symm
    change T*((n.factorial : ℂ)⁻¹ • A^n) = ((n.factorial : ℂ)⁻¹ • B^n)*T
    rw [mul_smul_comm,smul_mul_assoc,pw])).unique r

/-- The dressed Pauli acts as an exponential of local differences followed
by the original Pauli. This identity is exact at any coupling. -/
theorem dress_sign (D : List S) (k : Amp S) :
    exp ℂ (-convolute k) * signOp D * exp ℂ (convolute k) =
      exp ℂ (convolute (signOp D k - k)) * signOp D := by
  rw [mul_assoc,exp_intertwine (sign_convolve D k),← mul_assoc,
    ← exp_add_of_commute ((convolution_comm k (signOp D k)).neg_left)]
  simp [sub_eq_add_neg,add_comm]

variable [AddCommGroup S]
def translateAmp (r : S) := columns fun x : Config S => basis (translated r x)
@[simp] theorem translate_basis (r : S) (x : Config S) : translateAmp r (basis x) = basis (translated r x) := columns_basis ..

omit [Fintype S] [DecidableEq S] in
@[simp] theorem translated_add (s t : S) (x : Config S) :
    translated s (translated t x) = translated (s+t) x := by
  funext j; simp [translated,sub_sub]

def generatorColumn (x : Config S) : Amp S :=
  (2*(flipCount x : ℂ))⁻¹ • ∑ t : S, basis (translated t x)
def generator := columns (generatorColumn (S := S))

theorem generator_invariant (r : S) (v : Amp S) : translateAmp r (generator v) = generator v := by
  have single (x : Config S) : translateAmp r (generatorColumn x) = generatorColumn x := by
    simp only [generatorColumn,map_smul,map_sum,translate_basis,translated_add]
    exact congrArg (_ • ·) (Equiv.sum_comp (Equiv.addLeft r) (fun t => basis (translated t x)))
  simp only [generator,columns_apply,map_sum,map_smul] at *
  unfold translateAmp at single ⊢
  simp only [columns_apply] at single
  exact Finset.sum_congr rfl fun x _ => congrArg (v x • ·) (single x)

theorem response_eq (D : List S) (v : Amp S) : response D v = signOp D (generator v)-generator v := by
  have single (x : Config S) : responseColumn D x =
      signOp D (generatorColumn x) - generatorColumn x := by
    simp [generatorColumn,responseColumn,map_sum,sub_smul,Finset.sum_sub_distrib,smul_sub]
  simp only [response,generator,columns_apply,map_sum,map_smul,single,smul_sub,Finset.sum_sub_distrib]

end DSFTomography.SF.Cluster
