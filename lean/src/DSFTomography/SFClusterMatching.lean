import DSFTomography.SFClusterMatrixElements
import DSFTomography.SFClusterRows

/-! The analytic rows equal the paper's translation-averaged, connected
static and centered dynamic readout on one common physical neighborhood. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter Matrix
open scoped Topology
variable {ν : ℕ} {R : Bonds (Site ν)}
namespace BoxState
variable {b : Branch R} {n : ℕ} {i : Axis} {p : Params R.dirs} (g : BoxState b n i p)

theorem invariant (r : Box R n) : translateAmp r g.u = g.u := by
  conv_lhs => rw [g.ket,map_smul,ket_invariant]
  exact g.ket.symm
private theorem move (r : Box R n) (L M : Operator (Box R n))
    (eq : translateAmp r * L = M * translateAmp r) : bra g.u (M g.u) = bra g.u (L g.u) := by
  have act := congrArg (fun K : Operator (Box R n) => K g.u) eq
  change translateAmp r (L g.u) = M (translateAmp r g.u) at act
  rw [g.invariant] at act
  simpa only [g.invariant,act] using bra_shift r g.u (L g.u)

private theorem compose {t : Box R n} {A B C D : Operator (Box R n)}
    (h : translateAmp t*A=B*translateAmp t) (j : translateAmp t*C=D*translateAmp t) :
    translateAmp t*(A*C)=(B*D)*translateAmp t := by rw [← mul_assoc,h,mul_assoc,j,mul_assoc]

theorem shift_one (t r : Box R n) (a : Axis) :
    bra g.u (asOperator (spinAt (r+t) a) g.u) = bra g.u (asOperator (spinAt r a) g.u) :=
  g.move t _ _ (shift_spin t r a)
theorem shift_pair (t r s : Box R n) (a e : Axis) :
    bra g.u (asOperator (spinAt (r+t) a) (asOperator (spinAt (s+t) e) g.u)) =
      bra g.u (asOperator (spinAt r a) (asOperator (spinAt s e) g.u)) :=
  g.move t _ _ (compose (shift_spin t r a) (shift_spin t s e))
theorem shift_dynamic (t r s : Box R n) : g.dynamic (r+t) (s+t) = g.dynamic r s := by
  let q := sourceMap R i p
  let H := clusterH (boxFlips R n) (boxSigns R n) q
  let M := asOperator (offset (b:=b) (n:=n) (i:=i) (p:=p))
  let tr := translateAmp t
  have hH (w) : tr (H w) = H (tr w) := congrArg (fun A : Operator (Box R n) => A w) (clusterH_commutes t _ _ q).eq
  have comm : tr * M=M*tr := by
    ext w : 1
    have one : asOperator (1 : Op (Config (Box R n))) = 1 := by ext z : 1; simp [asOp_apply]
    have mat : M = H - (Ebox R n (b.a q).val+2) • 1 := by
      unfold M offset; rw [map_sub,map_smul,one]; exact congrArg (· - _) (physical_matrix R n i p).symm
    simp only [mat,ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply,map_sub,map_smul,hH]
  exact g.move t _ _ (compose (shift_spin t r 0) (compose comm (shift_spin t s 0)))

private theorem average_eq {S : Type*} [Fintype S] [Nonempty S] (f : S → ℂ) (k : ℂ) (h : ∀ r, f r=k) : avg f=k := by
  simp [avg,h,Fintype.card_ne_zero]

variable (G : GroundChart (periodicBonds R n) i)
local notation "x₀" => boxParams R n p
theorem mean_matches (ψ : G.ψ x₀ = WithLp.ofLp g.u) (a : Axis) :
    G.meanAt x₀ a = b.mean a (sourceMap R i p) (n : Boxes) := by
  apply average_eq; intro t
  rw [ψ,bra_matrix]
  have h := g.mean_word 0 a
  have origin : periodicSite R n 0=0 := by funext j; simp [periodicSite,reduceBond]
  rw [origin] at h
  simpa [Branch.mean] using (by simpa using g.shift_one t 0 a : bra g.u (asOperator (spinAt t a) g.u) = _).trans h

theorem static_matches (ψ : G.ψ x₀ = WithLp.ofLp g.u) (d : R.dirs) (t : Box R n) (a e : Axis) :
    G.staticAt x₀ t (t+periodicSite R n d) a e = b.pair d a e (sourceMap R i p) (n : Boxes) := by
  let v := periodicSite R n d
  have nz : v ≠ 0 := (periodicBonds R n).nonzero _ (bondInBox R n d).property
  have ne : t ≠ t+v := Ne.symm (by simpa using nz)
  have origin : periodicSite R n 0=0 := by funext j; simp [periodicSite,reduceBond]
  have h := g.pair_word 0 d.val (by simpa [origin] using Ne.symm nz) a e
  rw [origin] at h
  have eq := string_pair (1 : (Op (Config (Box R n)))ˣ) ne a e
  have mul : spinAt t a * spinAt (t+v) e = HT.word (twoLabel t (t+v) a e) := by simpa [spinAt,string,inBasis] using eq
  unfold GroundChart.staticAt
  rw [ψ,← mul,bra_matrix,asOp_mul,ContinuousLinearMap.mul_apply,g.mean_matches G ψ,g.mean_matches G ψ]
  apply congrArg (fun z : ℂ => z - b.mean a (sourceMap R i p) (n:Boxes)*b.mean e (sourceMap R i p) (n:Boxes))
  exact (by simpa [add_comm v] using g.shift_pair t 0 v a e :
    bra g.u (asOperator (spinAt t a) (asOperator (spinAt (t+v) e) g.u)) = _).trans h

theorem centered_matches (ψ : G.ψ x₀ = WithLp.ofLp g.u)
    (energy : G.E x₀ = Ebox R n (b.a (sourceMap R i p)).val) (t : Box R n) (r s : Site ν) :
    G.centeredAt x₀ (periodicSite R n r+t) (periodicSite R n s+t) =
      b.centered r s (sourceMap R i p) (n : Boxes) := by
  let u := periodicSite R n r+t
  let w := periodicSite R n s+t
  have shift : offset (b:=b) (n:=n) (i:=i) (p:=p) =
      Matrix.diagonal (fun k => flipGap k - G.E x₀ - 2) + fieldFrame (withParams (periodicBonds R n) x₀) i := by
    rw [energy]; ext j k; by_cases h : j=k <;> simp [offset,unitHamiltonian,h]; ring
  have ap (t : Box R n) : G.applied x₀ t 0 = (spinAt t 0) *ᵥ G.ψ x₀ := rfl
  unfold GroundChart.centeredAt
  rw [← shift,ap,ap,← sandwich_probes _ _ _ _ (word_hermitian _),ψ,bra_matrix,asOp_mul,asOp_mul,
    ContinuousLinearMap.mul_apply,ContinuousLinearMap.mul_apply,g.mean_matches G ψ]
  change g.dynamic _ _ + _ = _ + _
  rw [g.shift_dynamic,g.centered_word]; rfl

end BoxState
end DSFTomography.SF.Cluster
