import DSFTomography.HTLocalExpansion

noncomputable section
namespace DSFTomography.HT.LocalWord
open DSFTomography Filter Pauli
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def terms (x : Atom (Site ν)) : ℕ → Form (Site ν)
  | 0 => [(1,[x])]
  | k+1 => Form.subst (terms x k) (step R h J)

theorem terms_length (x : Atom (Site ν)) (k : ℕ) (p) (hp : p ∈ terms R h J x k) :
    p.2.length ≤ 2*k+1 := by
  induction k generalizing p with
  | zero => simp [terms] at hp; simp [hp]
  | succ k ih =>
    obtain ⟨q,hq,r,hstep,he⟩ := (by simpa only [terms,Form.subst,List.mem_flatMap,List.mem_map] using hp :
      ∃ q ∈ terms R h J x k, ∃ r ∈ step R h J q.2, (q.1*r.1,r.2) = p)
    subst p
    have := ih q hq
    have := step_length R h J _ r hstep
    simp; omega

theorem terms_mass (x : Atom (Site ν)) (k : ℕ) :
    Form.mass (terms R h J x k) ≤ (4*incidentBound R h J)^k * k.factorial := by
  let g := incidentBound R h J
  have hg : 0 ≤ g := (incidentBound_pos ..).le
  induction k with
  | zero => simp [terms]
  | succ k ih =>
    have each (p) (hp : p ∈ terms R h J x k) : Form.mass (step R h J p.2) ≤ 4*g*(k+1) := by
      have len : (p.2.length : ℝ) ≤ 2*k+1 := by exact_mod_cast terms_length R h J x k p hp
      calc
        _ ≤ 2*g * p.2.length := step_mass .. 
        _ ≤ 2*g*(2*k+1) := mul_le_mul_of_nonneg_left len (by positivity)
        _ ≤ _ := by nlinarith
    refine (Form.mass_subst_le _ _ each).trans ?_
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one,pow_succ]
    calc
      _ ≤ ((4*g)^k * k.factorial) * (4*g*(k+1)) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = _ := by dsimp [g]; ring

theorem terms_eval (n : ℕ) (x : Atom (Site ν)) (k : ℕ) :
    Form.apply (terms R h J x k) (eval (place R n)) =
    (ad (boxInteraction R h J n).matrix ^ k) (eval (place R n) [x]) := by
  induction k with
  | zero => simp [terms]
  | succ k ih =>
    rw [terms,Form.apply_subst]
    simp_rw [step_eval]
    rw [← Form.map_apply,ih,pow_succ',Module.End.mul_apply]

def state (n : ℕ) (z : ℂ) : Op (Config (Box R n)) →ₗ[ℂ] ℂ :=
  ((periodicVolume R h J n).partition z)⁻¹ • Volume.traceTest ((periodicVolume R h J n).boltzmann z)

theorem state_apply (n : ℕ) (z : ℂ) (A) : state R h J n z A =
    ((periodicVolume R h J n).boltzmann z * A).trace / (periodicVolume R h J n).partition z := by
  simp [state,Volume.traceTest,div_eq_inv_mul]

def value (xs : Script (Site ν)) (n : ℕ) (z : ℂ) := state R h J n z (eval (place R n) xs)

theorem value_bound (xs : Script (Site ν)) (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ bulkRadius R h J) :
    ‖value R h J xs n z‖ ≤ 1 := by
  obtain ⟨nonzero,bound⟩ := periodic_zeroFree_bounded R h J n z hz
  rw [value,normal,map_smul,norm_smul,scalar_norm,one_mul,state_apply,norm_div]
  exact (div_le_one (norm_pos_iff.mpr nonzero)).mpr (bound _)

def level (x : Atom (Site ν)) (xs : Script (Site ν)) (n : ℕ) (z : ℂ) (k : ℕ) :=
  z^k/k.factorial * Form.apply (terms R h J x k) (fun w => value R h J ((x::xs)++w) n z)

theorem level_series (x : Atom (Site ν)) (xs : Script (Site ν)) (n : ℕ) (z : ℂ) :
    HasSum (level R h J x xs n z) (value R h J xs n z) := by
  let V := periodicVolume R h J n
  let U := eval (place R n) [x]
  let Q := eval (place R n) (x::xs)
  have sq : U*U=1 := by simpa [U,string,inBasis] using string_square (1 : (Op (Config (Box R n)))ˣ) (place R n x.1) x.2
  have uq : U*Q=eval (place R n) xs := by
    rw [show Q = U*eval (place R n) xs by simp [U,Q]]
    rw [← Matrix.mul_assoc,sq,one_mul]
  have hs := (V.kms_series z Q U).div_const (V.partition z)
  rw [Matrix.mul_assoc _ U Q,uq] at hs
  rw [value,state_apply]
  refine hs.congr_fun ?_
  intro k
  let L := (state R h J n z).comp (LinearMap.mulLeft ℂ Q)
  have eq := Form.map_apply L (terms R h J x k) (eval (place R n))
  rw [terms_eval] at eq
  simp only [L,LinearMap.comp_apply,LinearMap.mulLeft_apply,boxInteraction_matrix] at eq
  unfold level
  simp only [value,eval_append]
  rw [← eq,state_apply,← Matrix.mul_assoc]
  rw [mul_div_assoc]
  rfl

theorem level_zero (x : Atom (Site ν)) (xs : Script (Site ν)) (n : ℕ) (z : ℂ)
    (flip : eval (place R n) [x] * eval (place R n) xs = -(eval (place R n) xs * eval (place R n) [x])) :
    level R h J x xs n z 0 = -value R h J xs n z := by
  let U := eval (place R n) [x]
  let P := eval (place R n) xs
  have sq : U*U=1 := by simpa [U,string,inBasis] using string_square (1 : (Op (Config (Box R n)))ˣ) (place R n x.1) x.2
  have qu : (U*P)*U = -P := by rw [show U*P = -(P*U) from flip,neg_mul,Matrix.mul_assoc,sq,mul_one]
  simp only [level,terms,Form.apply_cons,Form.apply_nil,add_zero,one_smul,pow_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,one_mul,value,eval_append]
  rw [show eval (place R n) (x::xs) = U*P by simp [U,P]]
  change state R h J n z ((U*P)*U) = -state R h J n z P
  rw [qu,map_neg]

end DSFTomography.HT.LocalWord
