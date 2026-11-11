import DSFTomography.SFClusterCharts
import DSFTomography.SFClusterObservables
import DSFTomography.SFClusterTranslation

/-! Identification of the bounded analytic columns with normalized
ground-state matrix elements, including the energy-centered dynamic moment. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace Matrix
open scoped Topology
variable {ν : ℕ} {R : Bonds (Site ν)}

namespace Branch
variable (b : Branch R)
def good (p : Sources R) := (∀ n, FiniteEquation (boxFlips R n) (boxSigns R n) p ((b.a p).val n)) ∧
  (1+b.rel p)*b.inverse p=1
theorem eventually_good : ∀ᶠ p in 𝓝 0, b.good p :=
  (b.solves.and b.inverse_ok).mono fun _ h => ⟨equation_in_boxes R _ _ h.1,h.2⟩
end Branch

structure BoxState (b : Branch R) (n : ℕ) (i : Axis) (p : Params R.dirs) where
  good : b.good (sourceMap R i p)
  u : Amp (Box R n)
  c : ℂ
  ket : u=c • eigenKet ((b.a (sourceMap R i p)).val n)
  normed : bra u u=1

namespace BoxState
variable {b : Branch R} {n : ℕ} {i : Axis} {p : Params R.dirs} (g : BoxState b n i p)
def offset := unitHamiltonian (periodicBonds R n) i (boxParams R n p) - (Ebox R n (b.a (sourceMap R i p)).val + 2) • 1
def dynamic (r s : Box R n) :=
  bra g.u (asOperator (spinAt r 0) (asOperator (offset (b:=b) (n:=n) (i:=i) (p:=p)) (asOperator (spinAt s 0) g.u)))

theorem decode (x : Local R) :
    g.c * bra g.u (exp ℂ (convolute (generator ((b.a (sourceMap R i p)).val n))) (x.val n)) =
      (sample R (b.inverse (sourceMap R i p) x)) (n : OnePoint ℕ) := by
  let q := sourceMap R i p
  let y := b.inverse q x
  have inv : (1+b.rel q) y = x := congrArg (fun L : Local R →L[ℂ] Local R => L x) g.good.2
  have boxed := congrArg (fun z : Local R => atBox R n z.val) inv
  change atBox R n (y.val + (b.rel q y).val) = x.val n at boxed
  rw [map_add,b.val_rel,error_atBox] at boxed
  have step := left_column (boxFlips R n) (boxSigns R n) q ((b.a q).val n) (g.good.1 n)
    (unitHamiltonian (periodicBonds R n) i (boxParams R n p)) (unitHamiltonian_self ..) (physical_matrix R n i p)
    g.u g.c g.ket g.normed (y.val n)
  exact (congrArg (fun w => g.c * bra g.u (exp ℂ (convolute (generator ((b.a q).val n))) w)) boxed.symm).trans step

theorem word (A D : Pattern ν) :
    bra g.u (pauliOp (placed R n A) (D.map (periodicSite R n)) g.u) =
      b.obs A D (sourceMap R i p) (n : OnePoint ℕ) := by
  let q := sourceMap R i p
  let x := b.wordColumn A D q
  have col : atBox R n x.val = flip (placed R n A) (ampExp (response (D.map (periodicSite R n)) ((b.a q).val n))) := by
    change flip _ (atBox R n (localExp R _).val) = _
    rw [val_localExp,atBox_exp]; rfl
  conv_lhs => arg 2; rw [g.ket,map_smul,word_eigenKet,← col]
  rw [map_smul,smul_eq_mul]
  exact g.decode x

theorem mean_word (r : Site ν) (a : Axis) :
    bra g.u (asOperator (spinAt (periodicSite R n r) a) g.u) =
      axisPhase a * b.obs (xSites r a) (zSites r a) (sourceMap R i p) (n : OnePoint ℕ) := by
  rw [spin_signed,ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul]
  exact congrArg (_ * ·) (by simpa [placed,bit_map,site_map] using g.word (xSites r a) (zSites r a))

theorem pair_word (r s : Site ν) (ne : periodicSite R n r≠periodicSite R n s) (a e : Axis) :
    bra g.u (asOperator (spinAt (periodicSite R n r) a) (asOperator (spinAt (periodicSite R n s) e) g.u)) =
      (axisPhase a * axisPhase e) * b.obs (xSites r a ++ xSites s e) (zSites r a ++ zSites s e) (sourceMap R i p) (n : OnePoint ℕ) := by
  rw [spin_signed,spin_signed,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,map_smul,map_smul,map_smul,smul_eq_mul,smul_eq_mul,← mul_assoc]
  apply congrArg (fun z : ℂ => (axisPhase a * axisPhase e)*z)
  have h := g.word (xSites r a ++ xSites s e) (zSites r a ++ zSites s e)
  rw [placed_append] at h
  simpa only [placed,bit_map,List.map_append,site_map,← pauli_disjoint _ _ ne,ContinuousLinearMap.mul_apply] using h

private theorem Xspin (s : Box R n) : asOperator (spinAt s 0) = flip (siteBit s) := by
  rw [spin_signed]; simp [axisPhase,pauliOp,toggle,sites,show signOp ([] : List (Box R n)) = 1 by
    apply operator_ext; intro x; simp [phase]]
private theorem gap_single (s : Box R n) : gapOp (basis (siteBit s)) = (2:ℂ) • basis (siteBit s) := by
  have h : (Finset.univ.filter fun t => siteBit s t ≠ 0) = {s} := by ext t; simp [siteBit]
  rw [gapOp,columns_basis,excitationEnergy,flipCount,h]; simp

theorem centered_word (r s : Site ν) :
    g.dynamic (periodicSite R n r) (periodicSite R n s) = b.cen r s (sourceMap R i p) (n : OnePoint ℕ) := by
  let q := sourceMap R i p
  let w := (b.a q).val n
  let K := exp ℂ (convolute (generator w))
  let H₀ := clusterH (boxFlips R n) (boxSigns R n) q
  let e := Ebox R n (b.a q).val
  let C := correction (boxFlips R n) (boxSigns R n) q w
  let a := siteBit (periodicSite R n r)
  let y := siteBit (periodicSite R n s)
  have opOne : asOperator (1 : Op (Config (Box R n))) = 1 := by ext z : 1; simp [asOp_apply]
  have mat : asOperator (offset (b:=b) (n:=n) (i:=i) (p:=p)) = H₀ - (e+2) • 1 := by
    unfold offset; rw [map_sub,map_smul,opOne]; exact congrArg (· - _) (physical_matrix R n i p).symm
  have into (x : Config (Box R n)) : flip x g.u = g.c • K (basis x) := by
    rw [g.ket,map_smul]; apply congrArg (_ • ·)
    simpa [K,ContinuousLinearMap.mul_apply,eigenKet,ampExp] using
      congrArg (fun L : Operator (Box R n) => L (basis 0)) (flip_exp_comm x w).eq
  have eq := congrArg (fun L : Operator (Box R n) => L (basis y)) (dressed_H _ _ _ _ (g.good.1 n))
  change H₀ (K (basis y)) = K (e • basis y + (1+C) (gapOp (basis y))) at eq
  rw [gap_single] at eq
  have centered : (H₀ - (e+2) • 1 : Operator (Box R n)) (K (basis y)) = (2:ℂ) • K (C (basis y)) := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,eq,
      map_add,map_smul,ContinuousLinearMap.add_apply,smul_add,add_smul]; abel
  let col := XOp R [r] (b.rel q (Branch.singleFlip (R:=R) s))
  have single (t : Site ν) : bitSum ([t].map (periodicSite R n)) = siteBit (periodicSite R n t) := by
    simp [bitSum]; rfl
  have colEq : atBox R n col.val = flip a (C (basis y)) := by
    change flip _ (atBox R n (b.rel q _).val) = _
    rw [single,b.val_rel,error_atBox]; apply congrArg (flip a); apply congrArg C
    change flip _ (basis 0) = basis y; rw [single,flip_basis,add_zero]
  have comm (z) : flip a (K z) = K (flip a z) := congrArg (fun L : Operator (Box R n) => L z) (flip_exp_comm a w).eq
  change bra g.u (asOperator _ (asOperator _ (asOperator _ g.u))) = _
  rw [Xspin,Xspin,mat,into,map_smul,centered]
  change bra g.u (flip a (g.c • ((2:ℂ) • K (C (basis y))))) = _
  simp only [map_smul,comm,← colEq]
  change g.c * (2 * bra g.u (K (col.val n))) = 2 * sample R (b.inverse q col) (n : OnePoint ℕ)
  rw [← g.decode]; ring

end BoxState
end DSFTomography.SF.Cluster
