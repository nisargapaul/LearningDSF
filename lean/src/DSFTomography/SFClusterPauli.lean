import DSFTomography.SFClusterPeriodic

/-! Identification of the spin-flip representation with the qubit matrices
used in the DSF. The source coefficients include the ordered phase Y=iXZ. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace DSFTomography.SF.Cluster
open DSFTomography HT Matrix
variable {S : Type*} [Fintype S] [DecidableEq S] [AddCommGroup S]

def asOperator : Op (Config S) →ₗ[ℂ] Operator S where
  toFun M := LinearMap.toContinuousLinearMap ((WithLp.linearEquiv 1 ℂ _).symm.conj (Matrix.toLin' M))
  map_add' M N := by ext v : 1; exact congrArg (WithLp.toLp 1) (Matrix.add_mulVec M N (WithLp.ofLp v))
  map_smul' c M := by ext v : 1; exact congrArg (WithLp.toLp 1) (Matrix.smul_mulVec c M (WithLp.ofLp v))

omit [AddCommGroup S] in
theorem asOp_apply (M : Op (Config S)) (v : Amp S) : asOperator M v = WithLp.toLp 1 (M *ᵥ WithLp.ofLp v) := rfl
omit [AddCommGroup S] in
theorem asOp_mul (M N : Op (Config S)) : asOperator (M*N) = asOperator M * asOperator N := by
  ext v : 1; exact congrArg (WithLp.toLp 1) (Matrix.mulVec_mulVec _ _ _).symm

def siteBit (s : S) : Config S := fun t => if t=s then 1 else 0
def axisPhase (a : Axis) : ℂ := if a=1 then Complex.I else 1
def toggle (s : S) (a : Axis) : Config S := if a=2 then 0 else siteBit s
def sites (s : S) (a : Axis) : List S := if a=0 then [] else [s]

omit [AddCommGroup S] in
theorem spin_signed (s : S) (a : Axis) :
    asOperator (spinAt s a) = axisPhase a • pauliOp (toggle s a) (sites s a) := by
  apply operator_ext; intro y
  apply WithLp.ofLp_injective; funext x
  have col : (asOperator (spinAt s a) (basis y)) x = word (oneLabel s a) x y := by
    simp [asOp_apply,Matrix.mulVec,dotProduct,basis,spinAt,mul_ite]
  change (asOperator (spinAt s a) (basis y)) x = _
  rw [col,word_one]
  simp only [ContinuousLinearMap.smul_apply,pauliOp,ContinuousLinearMap.mul_apply,sign_basis,
    map_smul,flip_basis]
  change (if ∀ j ≠ s, x j=y j then pauli (some a) (x s) (y s) else 0) = axisPhase a * (phase (sites s a) y * (if x=toggle s a+y then 1 else 0))
  have same (h : ∀ j ≠ s, x j=y j) : x = toggle s a + y ↔ x s = toggle s a s + y s := by
    constructor
    · intro eq; exact congrFun eq s
    · intro eq; funext j; by_cases hj : j=s
      · subst j; exact eq
      · simp [toggle,siteBit,hj,h j hj,ite_apply]
  by_cases h : ∀ j ≠ s, x j=y j
  · simp only [if_pos h,same h]
    fin_cases a <;> generalize hx : x s = u <;> generalize hy : y s = v
    all_goals fin_cases u <;> fin_cases v <;> simp [sites,toggle,siteBit,axisPhase,phase,pauliValues,hy]
  · have ne : x ≠ toggle s a + y := by
      intro eq; apply h; intro j hj; simp [eq,toggle,siteBit,hj,ite_apply]
    simp [h,ne]

omit [AddCommGroup S] in
theorem pauli_disjoint (s t : S) (ne : s≠t) (a b : Axis) :
    pauliOp (toggle s a) (sites s a) * pauliOp (toggle t b) (sites t b) =
      pauliOp (toggle s a + toggle t b) (sites s a ++ sites t b) := by
  apply operator_ext; intro y
  simp only [pauliOp,ContinuousLinearMap.mul_apply,sign_basis,map_smul,flip_basis,smul_smul]
  have phase' (D) (x z : Config S) : phase D (x+z) = phase D x * phase D z := phase_add D x z
  have dis : phase (sites s a) (toggle t b) = 1 := by
    by_cases ha : a=0 <;> by_cases hb : b=2 <;> simp [sites,toggle,phase,siteBit,ha,hb,ne]
  have append : phase (sites s a ++ sites t b) y = phase (sites s a) y * phase (sites t b) y := by
    simp [phase]
  simp only [phase',dis,one_mul,append,add_assoc]; rw [mul_comm]

omit [Fintype S] [DecidableEq S] in
private theorem translate_sign (t : S) (D : List S) (x : Config S) :
    phase D (translated (-t) x) = phase (D.map (· + t)) x := by
  simp [phase,translated,List.map_map,Function.comp_def]

theorem translate_word (t : S) (x : Config S) (D : List S) :
    translateAmp t * pauliOp x D * translateAmp (-t) =
      pauliOp (translated t x) (D.map (· + t)) := by
  apply operator_ext; intro y
  simp only [pauliOp,ContinuousLinearMap.mul_apply,translate_basis,sign_basis,map_smul,flip_basis,
    translate_sign, show ∀ z z' : Config S, translated t (z+z') = translated t z+translated t z' from fun _ _ => rfl,
    translated_add,add_neg_cancel,show translated (0:S) y = y from by funext s; simp [translated]]

variable {ν : ℕ} (R : Bonds (Site ν))
def source (i : Axis) (p : Params R.dirs) : Sources R
  | .inl a => (p.1 (axisInLab i a) : ℂ) * axisPhase a
  | .inr (d,a,b) => (p.2 d (axisInLab i a) (axisInLab i b) : ℂ) * (axisPhase a * axisPhase b)

theorem bit_map (n) (s : Site ν) (a : Axis) :
    bitSum ((xSites s a).map (periodicSite R n)) = toggle (periodicSite R n s) a := by
  by_cases h : a=2 <;> simp [xSites,bitSum,toggle,h]; rfl
theorem site_map (n) (s : Site ν) (a : Axis) :
    (zSites s a).map (periodicSite R n) = sites (periodicSite R n s) a := by
  by_cases h : a=0 <;> simp [zSites,sites,h]
omit [Fintype S] in
theorem tr_bit (s t : S) (a : Axis) : translated t (toggle s a) = toggle (s+t) a := by
  funext j; by_cases h : a=2 <;> simp [toggle,translated,siteBit,h,sub_eq_iff_eq_add]
omit [Fintype S] [DecidableEq S] in
theorem tr_site (s t : S) (a : Axis) : (sites s a).map (· + t) = sites (s+t) a := by
  by_cases h : a=0 <;> simp [sites,h]

theorem physical_matrix (n : ℕ) (i : Axis) (p : Params R.dirs) :
    clusterH (boxFlips R n) (boxSigns R n) (source R i p) =
      asOperator (Matrix.diagonal flipGap + fieldFrame (withParams (periodicBonds R n) (boxParams R n p)) i) := by
  let S := Box R n
  let B := periodicBonds R n
  have origin : periodicSite R n 0 = 0 := by funext j; simp [periodicSite,reduceBond]
  have free : (Fintype.card S : ℂ) • (1 : Operator S) - periodicTerm 0 [0] = asOperator (Matrix.diagonal flipGap) := by
    apply operator_ext; intro x
    have acted (y : Config S) : asOperator (Matrix.diagonal flipGap) (basis y) = flipGap y • basis y := by
      apply WithLp.ofLp_injective; funext z
      by_cases eq : z=y <;> simp [eq,asOp_apply,Matrix.mulVec_diagonal,PiLp.smul_apply,basis,smul_eq_mul]
    have field0 (r : S) : translateAmp r * pauliOp (0 : Config S) [0] * translateAmp (-r) =
        pauliOp 0 [r] := by simpa [show translated r (0:Config S)=0 from rfl] using translate_word r (0:Config S) [0]
    rw [acted]; unfold periodicTerm
    simp_rw [field0]
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,ContinuousLinearMap.sum_apply,
      pauliOp,ContinuousLinearMap.mul_apply,flip_zero,sign_basis,← Finset.sum_smul,
      ← sub_smul]
    apply congrArg (fun c : ℂ => c • basis x)
    have h := sum_sign x
    simp only [phase,translated,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,zero_sub] at h ⊢
    have reidx := Equiv.sum_comp (Equiv.neg S) (fun t => if x t=0 then (1:ℂ) else -1)
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
    rw [show (∑ t : S, if x (-t)=0 then (1:ℂ) else -1) = _ from reidx] at h
    have count : flipGap x = 2*(flipCount x : ℂ) := by
      unfold flipCount flipGap; congr 3; ext t; simp; have := (x t).isLt; omega
    rw [count]; exact (neg_sub _ _).symm.trans (by rw [h]; ring)
  rw [clusterH,map_add,free]; congr 1
  have field (r : S) (a : Axis) : translateAmp r * pauliOp (boxFlips R n (.inl a)) (boxSigns R n (.inl a)) * translateAmp (-r) =
      pauliOp (toggle r a) (sites r a) := by
    rw [translate_word]; simp [boxFlips,boxSigns,flipSites,signSites,bit_map,site_map,origin,tr_bit,tr_site]
  have bond (r : S) (d : R.dirs) (a b : Axis) :
      translateAmp r * pauliOp (boxFlips R n (.inr (d,a,b))) (boxSigns R n (.inr (d,a,b))) * translateAmp (-r) =
        pauliOp (toggle r a) (sites r a) * pauliOp (toggle (r+periodicSite R n d) b) (sites (r+periodicSite R n d) b) := by
    have ne : r≠r+periodicSite R n d := Ne.symm (by simpa using B.nonzero _ (bondInBox R n d).property)
    rw [translate_word,pauli_disjoint _ _ ne]
    have sumBits (A D : List S) : bitSum (A++D) = bitSum A+bitSum D := by simp [bitSum]
    simp [boxFlips,boxSigns,flipSites,signSites,sumBits,site_map,origin,
      show ∀ x y : Config S, translated r (x+y)=translated r x+translated r y from fun _ _ => rfl,
      tr_site,add_comm r]
    rw [bit_map,bit_map,tr_bit,tr_bit,origin,zero_add]
  have frame (V : Volume S) :
      fieldFrame V i = (∑ r : S, ∑ a, (V.h (axisInLab i a):ℂ) • spinAt r a) +
        ∑ d ∈ V.R.dirs, ∑ r : S, ∑ a, ∑ b, (V.J d (axisInLab i a) (axisInLab i b):ℂ) • (spinAt r a * spinAt (r+d) b) := by
    simp [fieldFrame,qubitH,realH,H,qubitSpins,string,inBasis,spinAt]
  rw [frame]
  change _ = asOperator ((∑ r : S, ∑ a, (p.1 (axisInLab i a) : ℂ) • spinAt r a) +
      ∑ d ∈ B.dirs, ∑ r : S, ∑ a, ∑ b, ((withParams B (boxParams R n p)).J d (axisInLab i a) (axisInLab i b) : ℂ) •
        (spinAt r a * spinAt (r+d) b))
  rw [← Finset.sum_attach B.dirs]
  have reindex (f : B.dirs → Op (Config S)) : ∑ x ∈ B.dirs.attach, f x = ∑ d : R.dirs, f (bondInBox R n d) :=
    (Equiv.sum_comp (bondInBox R n) f).symm
  rw [reindex]
  simp only [map_add,map_sum,map_smul,asOp_mul,spin_signed,Fintype.sum_sum_type,Fintype.sum_prod_type,
    periodicTerm,field,bond,source,Finset.smul_sum,smul_smul]
  congr 1
  · rw [Finset.sum_comm]
  · apply Finset.sum_congr rfl; intro d _
    have cycle (f : Axis → Axis → S → Operator S) :
        (∑ x, ∑ y, ∑ z, f x y z) = ∑ z, ∑ x, ∑ y, f x y z := by
      conv_lhs => enter [2,x]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [cycle]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ext u : 1
    have e : (withParams B (boxParams R n p)).J (bondInBox R n d) (axisInLab i a) (axisInLab i b) =
        p.2 d (axisInLab i a) (axisInLab i b) := by
      simp [withParams,boxParams]
    rw [e]
    let X := pauliOp (toggle r a) (sites r a)
    let Y := pauliOp (toggle (r+periodicSite R n d) b) (sites (r+periodicSite R n d) b)
    let c : ℂ := p.2 d (axisInLab i a) (axisInLab i b)
    change (c * (axisPhase a * axisPhase b)) • X (Y u) = c • (axisPhase a • X (axisPhase b • Y u))
    rw [map_smul,smul_smul,smul_smul,mul_assoc]

end DSFTomography.SF.Cluster
