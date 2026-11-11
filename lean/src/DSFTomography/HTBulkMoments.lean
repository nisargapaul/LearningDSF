import DSFTomography.HTThermodynamic
import DSFTomography.HTDiagonal

/-! Frequency moments before the volume limit. For n=0 and n=2 these are
the actual Fourier harmonics of the diagonal Gibbs DSF. Iterating the local
commutator gives a finite list of Pauli words independent of the period. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace DSFTomography.HT.Diagonal.Bulk
open DSFTomography HT LocalWord Filter Metric
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def test (V : Volume S) (A : Op (Config S)) (z : ℂ) :=
  (V.boltzmann z * A).trace / V.partition z

theorem realTest (V : Volume S) (A : Op (Config S)) (β : ℝ) :
    test V A β = mean (gibbs β (energies V.R V.h V.J)) (inBasis (energyBasis V.R V.h V.J) A) := by
  rw [test,V.trace_test_eq_sum,V.partition_eq_sum]
  simp only [mean,gibbs,Complex.ofReal_div,Complex.ofReal_sum,← Complex.ofReal_exp,
    ← Complex.ofReal_neg,← Complex.ofReal_mul,div_mul_eq_mul_div,Finset.sum_div]

theorem holTest (V : Volume S) (A : Op (Config S)) {D : Set ℂ} (reg : ∀ z ∈ D, V.partition z ≠ 0) :
    DifferentiableOn ℂ (test V A) D := by
  change DifferentiableOn ℂ (fun z => (V.boltzmann z * A).trace / V.partition z) D
  simp only [V.trace_test_eq_sum,V.partition_eq_sum] at *
  exact DifferentiableOn.div (DifferentiableOn.fun_sum fun _ _ => by fun_prop)
    (DifferentiableOn.fun_sum fun _ _ => by fun_prop) reg

abbrev normTrace {ι : Type*} [Fintype ι] (A : Op ι) := A.trace / (Fintype.card ι : ℂ)
theorem test_zero (V : Volume S) (A : Op (Config S)) : test V A 0 = normTrace A := by
  simp [test,Volume.partition,Volume.boltzmann,normTrace]

theorem test_slope (V : Volume S) (A : Op (Config S)) :
    HasDerivAt (fun β : ℝ => test V A β) (-normTrace (qubitH V.R V.h V.J * A)) 0 := by
  let U := energyBasis V.R V.h V.J
  let K := qubitH V.R V.h V.J
  have slope := mean_slope (energies V.R V.h V.J) (inBasis U A) (realH (qubitSpins U) V.R V.h V.J)
    (diagonalized ..) (H_traceless _ U (fun _ _ => rfl) _ _ _)
  rw [rotate_H,inBasis_mul] at slope
  simp only [inBasis,Matrix.trace_units_conj] at slope
  simpa only [realTest,neg_div,normTrace,U,K,inBasis] using slope

abbrev repeated (V : Volume S) (k : ℕ) (r d : S) (a : Axis) :=
  ((ad (qubitH V.R V.h V.J))^k) (spin r a) * spin (r+d) a

private theorem test_origin (V : Volume S) (k : ℕ) (r d : S) (a : Axis) (z : ℂ) :
    test V (repeated V k r d a) z = test V (repeated V k 0 d a) z := by
  have sp (s : S) : translate r (spin s a) = spin (s+r) a := by
    have eq := translate_spin r s a
    change translate r ((qubitSpins 1).σ s a) = (qubitSpins 1).σ (s+r) a at eq
    simpa [qubitSpins,string,inBasis,spin] using eq
  have iter (k : ℕ) : translate r ((ad (qubitH V.R V.h V.J)^k) (spin 0 a)) =
      (ad (qubitH V.R V.h V.J)^k) (spin r a) := by
    induction k with
    | zero => simpa using sp 0
    | succ k ih =>
      simp only [pow_succ',Module.End.mul_apply]
      change translate r (_ * _ - _ * _) = _ * _ - _ * _
      rw [map_sub,map_mul,map_mul,translate_H V,ih]
  have sh := Volume.trace_translate r (V.boltzmann z * repeated V k 0 d a)
  simp only [map_mul,V.translate_boltzmann,repeated,iter,sp,zero_add,add_comm d r] at sh
  simpa only [test,repeated,zero_add] using congrArg (· / V.partition z) sh

private theorem basisIter (V : Volume S) (k : ℕ) (r : S) (a : Axis) :
    let U := energyBasis V.R V.h V.J
    let E := energies V.R V.h V.J
    ∀ i j, inBasis U ((ad (qubitH V.R V.h V.J)^k) (spin r a)) i j =
      ((E j:ℂ)-E i)^k * (qubitSpins U).σ r a i j := by
  intro U E
  have diag := (rotate_H V.R V.h V.J U).symm.trans (diagonalized V.R V.h V.J)
  induction k with
  | zero => intro i j; simp [spin,qubitSpins,string]
  | succ k ih =>
    intro i j
    simp only [pow_succ' (ad _),Module.End.mul_apply]
    change inBasis U (_ * _ - _ * _) i j = _
    rw [show ∀ A B, inBasis U (A-B) = inBasis U A-inBasis U B by intros; simp [inBasis,Matrix.mul_sub,Matrix.sub_mul],
      ← inBasis_mul,← inBasis_mul,diag]
    simp only [Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,ih,pow_succ]
    ring

/-- Lehmann representation weighted by the kth power of the transition energy. -/
def moment (V : Volume S) (k : ℕ) (d : S) (a : Axis) (β : ℝ) :=
  let P := qubitSpins (energyBasis V.R V.h V.J)
  let E := energies V.R V.h V.J
  harmonic (toMomentum (fun e => avg fun r => ∑ i, gibbs β E i *
    ∑ j, ((E j:ℂ)-E i)^k * P.σ r a i j * P.σ (r+e) a j i)) d

theorem moment_eq_test (V : Volume S) (k : ℕ) (d : S) (a : Axis) (β : ℝ) :
    moment V k d a β = test V (repeated V k 0 d a) β := by
  unfold moment; rw [harmonic_toMomentum]
  let P := qubitSpins (energyBasis V.R V.h V.J)
  let E := energies V.R V.h V.J
  have eqr (r : S) : (∑ i, gibbs β E i * ∑ j, ((E j:ℂ)-E i)^k * P.σ r a i j * P.σ (r+d) a j i) =
      test V (repeated V k 0 d a) β := by
    rw [← test_origin V k r d a β,realTest,repeated,← inBasis_mul]
    simp only [mean,Matrix.mul_apply,basisIter]; rfl
  change avg (fun r => ∑ i, gibbs β E i * ∑ j, ((E j:ℂ)-E i)^k * P.σ r a i j * P.σ (r+d) a j i) = _
  simp_rw [eqr]; simp [avg,Fintype.card_ne_zero]

theorem static_moment (V : Volume S) (d : S) (a : Axis) :
    V.observable (.bond d a a) = moment V 0 d a := by
  funext β; unfold moment; simp only [harmonic_toMomentum,pow_zero,one_mul]
  exact harmonic_toMomentum _ _

theorem second_moment (V : Volume S) (d : S) (a : Axis) :
    coeff₂ (qubitSpins (energyBasis V.R V.h V.J)) (energies V.R V.h V.J) d a = moment V 2 d a := by
  funext β; rw [coeff₂_eq,moment,harmonic_toMomentum]
  simp only [localSecond,second,Finset.mul_sum,mul_assoc]

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
def form (k : ℕ) (d : Site ν) (a : Axis) := Form.changeWords (terms R h J (0,a) k) (· ++ [(d,a)])
def extension (k : ℕ) (d : Site ν) (a : Axis) (n : ℕ) (z : ℂ) :=
  Form.apply (form R h J k d a) (fun w => value R h J w n z)

theorem extension_eq (k : ℕ) (d : Site ν) (a : Axis) (n : ℕ) (z : ℂ) :
    extension R h J k d a n z =
    test (periodicVolume R h J n) (repeated (periodicVolume R h J n) k 0 (place R n d) a) z := by
  let f := place R n
  let L := (state R h J n z).comp (LinearMap.mulRight ℂ (spin (f d) a))
  have eq := Form.map_apply L (terms R h J (0,a) k) (eval f)
  rw [terms_eval,boxInteraction_matrix] at eq
  rw [extension,form,Form.apply_changeWords]
  simp only [value,eval_append,eval_cons,eval_nil,mul_one]
  have origin : f 0 = 0 := by funext i; simp [f,place,periodicSite,reduceBond]
  change Form.apply _ (fun w => L (eval f w)) = _
  rw [← eq]
  simp only [L,LinearMap.comp_apply,LinearMap.mulRight_apply,eval_cons,eval_nil,mul_one,
    state_apply,zero_add,test,repeated]
  simp only [show place R n 0 = 0 from origin,spin,f]
  rfl

end DSFTomography.HT.Diagonal.Bulk
