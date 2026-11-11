import DSFTomography.HTCommutators

/-! Cyclicity of the finite Gibbs trace gives a convergent imaginary-time
commutator series. The trace remains unnormalized throughout the zero-free proof. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Pauli
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

namespace Volume
private abbrev basis (V : Volume S) := energyBasis V.R V.h V.J
private abbrev energy (V : Volume S) := energies V.R V.h V.J

private theorem iter_entry (V : Volume S) (A : Op (Config S)) (k : ℕ) (i j : Config S) :
    inBasis V.basis ((ad (qubitH V.R V.h V.J) ^ k) A) i j =
      ((V.energy j : ℂ) - V.energy i)^k * inBasis V.basis A i j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have diag := (rotate_H V.R V.h V.J V.basis).symm.trans (diagonalized V.R V.h V.J)
    rw [pow_succ', Module.End.mul_apply]
    let X := (ad (qubitH V.R V.h V.J) ^ k) A
    change inBasis V.basis (X * qubitH V.R V.h V.J - qubitH V.R V.h V.J * X) i j = _
    rw [show ∀ X Y : Op (Config S), inBasis V.basis (X-Y) = inBasis V.basis X - inBasis V.basis Y by
      intros; simp [inBasis, Matrix.mul_sub, Matrix.sub_mul]]
    simp only [← inBasis_mul, diag, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, X, ih]
    ring

private theorem ordered_trace (V : Volume S) (z : ℂ) (Q A : Op (Config S)) :
    (V.boltzmann z * Q * A).trace = ∑ i, ∑ j, Complex.exp (-z * V.energy i) *
      inBasis V.basis Q i j * inBasis V.basis A j i := by
  rw [← Matrix.trace_units_conj V.basis (V.boltzmann z * Q * A), ← inBasis,
    ← inBasis_mul, ← inBasis_mul, boltzmann_diagonal]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem kms_series (V : Volume S) (z : ℂ) (Q A : Op (Config S)) :
    HasSum (fun k : ℕ => z^k / k.factorial *
      (V.boltzmann z * Q * ((ad (qubitH V.R V.h V.J)^k) A)).trace)
      ((V.boltzmann z * A * Q).trace) := by
  let e := V.energy
  have term (i j : Config S) : HasSum (fun k : ℕ => (z^k / k.factorial) *
      (Complex.exp (-z * e i) * inBasis V.basis Q i j *
      (((e i : ℂ) - e j)^k * inBasis V.basis A j i)))
      (Complex.exp (-z * e j) * inBasis V.basis A j i * inBasis V.basis Q i j) := by
    have hs := (NormedSpace.expSeries_div_hasSum_exp ℂ (z*((e i : ℂ)-e j))).mul_right
      (Complex.exp (-z * e i) * inBasis V.basis Q i j * inBasis V.basis A j i)
    rw [← Complex.exp_eq_exp_ℂ] at hs
    convert hs using 1
    · funext k; rw [mul_pow]; ring
    · have add : z * ((e i : ℂ) - e j) + -z * e i = -z * e j := by ring
      rw [← add, Complex.exp_add]
      ring
  simp_rw [ordered_trace, iter_entry, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => Complex.exp (-z * V.energy i) *
    inBasis V.basis A i j * inBasis V.basis Q j i)]
  exact hasSum_sum (fun i _ => hasSum_sum (fun j _ => term i j))

def traceTest (A : Op (Config S)) : Op (Config S) →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap _ ℂ ℂ).comp (LinearMap.mulLeft ℂ A)

private theorem tail_bound {T : Type*} [Fintype T] (V : Volume S) (I : PauliInteraction S T)
    (model : I.matrix = qubitH V.R V.h V.J) {z : ℂ} {g M : ℝ} (hg : 0 ≤ g)
    (incident : I.SiteBound g) (small : ‖z‖*(2*g) ≤ 1/2) (hM : 0 ≤ M)
    (cap : ∀ w : Label S, ‖(V.boltzmann z * word w).trace‖ ≤ M)
    (w : Label S) (hw : w ≠ fun _ => none) :
    2 * ‖(V.boltzmann z * word w).trace‖ ≤ M := by
  obtain ⟨i,a,flip⟩ := Pauli.flip hw
  let u := oneLabel i a
  let U := word u
  let P := word w
  let Q := U * P
  let G := V.boltzmann z
  have sq : U * U = 1 := by simpa [U,u,string,inBasis] using string_square (1 : (Op (Config S))ˣ) i a
  have uq : U * Q = P := by rw [show U*Q = (U*U)*P by simp [Q, Matrix.mul_assoc],sq,one_mul]
  have qu : Q * U = -P := by
    change U * P * U = -P
    rw [show U * P = -(P * U) from flip, neg_mul, Matrix.mul_assoc, sq, mul_one]
  let L := traceTest (G*Q)
  have capL (v : Label S) : ‖L (word v)‖ ≤ M := by
    change ‖(G * (word u * word w) * word v).trace‖ ≤ M
    rw [Matrix.mul_assoc, product u w, Matrix.smul_mul, product, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
    simpa only [norm_smul, phase_norm, one_mul] using cap (combine (combine u w) v)
  have su : (supp u).card ≤ 1 := by
    have eq : supp u = {i} := by ext j; simp [u,supp,oneLabel]
    simp [eq]
  let f := fun k : ℕ => z^k / k.factorial * L ((ad I.matrix ^ k) U)
  have bound (k : ℕ) : ‖f k‖ ≤ (1/2 : ℝ)^k * M := by
    have b := I.iter_bound hg hM incident L capL k u 1 su
    rw [Nat.one_ascFactorial] at b
    change ‖z^k / (k.factorial : ℂ) * _‖ ≤ _
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (‖z‖^k / k.factorial) * (M * (2*g)^k * k.factorial) :=
        mul_le_mul_of_nonneg_left b (by positivity)
      _ = (‖z‖*(2*g))^k * M := by simp only [mul_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) small k) hM
  have sum : HasSum f (G*P).trace := by
    have h := V.kms_series z Q U
    rw [Matrix.mul_assoc G U Q, uq] at h
    simpa only [f, L, traceTest, LinearMap.comp_apply, Matrix.traceLinearMap_apply,
      LinearMap.mulLeft_apply, model] using h
  have h0 : f 0 = -(G*P).trace := by
    simp [f,L,traceTest,qu]
  have tail := (hasSum_nat_add_iff' 1).mpr sum
  simp only [Finset.sum_range_one, h0, sub_neg_eq_add] at tail
  have geom : HasSum (fun k : ℕ => (1/2 : ℝ)^(k+1) * M) M := by
    have h := ((hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one
      (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num))).mul_right M
    norm_num at h
    exact h
  have sn := geom.summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => bound (k+1))
  have le := (norm_tsum_le_tsum_norm sn).trans (sn.tsum_le_tsum (fun k => bound (k+1)) geom.summable)
  rw [tail.tsum_eq, geom.tsum_eq, ← two_mul, norm_mul] at le
  simpa using le

theorem zeroFree_and_bounded {T : Type*} [Fintype T] (V : Volume S) (I : PauliInteraction S T)
    (model : I.matrix = qubitH V.R V.h V.J) {g : ℝ} (hg : 0 ≤ g) (incident : I.SiteBound g)
    (z : ℂ) (small : ‖z‖*(2*g) ≤ 1/2) :
    V.partition z ≠ 0 ∧ ∀ w : Label S, ‖(V.boltzmann z * word w).trace‖ ≤ ‖V.partition z‖ := by
  classical
  let m := fun w : Label S => ‖(V.boltzmann z * word w).trace‖
  obtain ⟨w, _, hm⟩ := Finset.exists_max_image Finset.univ m Finset.univ_nonempty
  have cap (v : Label S) : m v ≤ m w := hm v (Finset.mem_univ v)
  have all : ∀ v : Label S, m v ≤ ‖V.partition z‖ := by
    by_cases hw : w = fun _ => none
    · simpa [m, hw, word_empty, partition] using cap
    · have le := tail_bound V I model hg incident small (norm_nonneg _) cap w hw
      intro v
      exact (cap v).trans ((by linarith [show 0 ≤ m w from norm_nonneg _] : m w ≤ 0).trans (norm_nonneg _))
  refine ⟨?_,all⟩
  intro hz
  have van (v : Label S) : (V.boltzmann z * word v).trace = 0 :=
    norm_le_zero_iff.mp (by simpa [hz,m] using all v)
  obtain ⟨u,hu⟩ := Matrix.isUnit_exp ℂ ((-z) • qubitH V.R V.h V.J)
  have h := trace_separates _ van (↑u⁻¹)
  change (V.boltzmann z * ↑u⁻¹).trace = 0 at h
  rw [show V.boltzmann z = ↑u from hu.symm, Units.mul_inv, Matrix.trace_one] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h

end Volume
end DSFTomography.HT
