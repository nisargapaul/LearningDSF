import DSFTomography.HTDiagonalMap

/-! The small antisymmetric-exchange witness. Divide just the principal-minor
rows of its Jacobian by their common factor −8ε. The resulting Jacobian is
continuous down to ε=0, where its kernel can be read off explicitly. -/
noncomputable section
namespace DSFTomography.HT.Diagonal
open DSFTomography HT Filter
open scoped Topology ContDiff
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
variable (R : Bonds S)
def witness (ε : ℝ) : Params R
  | .inl _ => 1/2
  | .inr (_,a,b) => ε*(sign a b).re

private def line (x v : Params R) (t : ℝ) : Params R := x + t • v
omit [Fintype S] in
private theorem lineDeriv (x v : Params R) : HasDerivAt (line R x v) v 0 := by
  simpa [line] using (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)

private theorem rowDeriv (aux : Bool) (x v : Params R) (i : Index R) :
    HasDerivAt (fun t => polynomialRows R aux (line R x v t) i)
      (fderiv ℝ (polynomialRows R aux) x v i) 0 := by
  have hx : line R x v 0 = x := by simp [line]
  have h := ((rows_smooth R aux).differentiable (by simp)).differentiableAt (x := line R x v 0)
  have hd := h.hasFDerivAt.comp_hasDerivAt 0 (lineDeriv R x v)
  rw [hx] at hd
  exact (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt _ hd

private theorem sigs (a : Axis) :
    sign a a = 0 ∧ sign (a+1) (a+1)=0 ∧ sign (a+2) (a+2)=0 ∧
    sign (a+1) (a+2)=1 ∧ sign (a+2) (a+1)= -1 := by fin_cases a <;> repeat' constructor
private theorem axes (a : Axis) : a=0 ∨ a=1 ∨ a=2 := by fin_cases a <;> decide
private theorem adds : (1+1:Axis)=2 ∧ (1+2:Axis)=0 ∧ (2+1:Axis)=0 ∧ (2+2:Axis)=1 := by decide

omit [Fintype S] in
private theorem bondLine (e : ℝ) (v : Params R) (d : R.dirs) (a b : Axis) (t : ℝ) :
    exch R (line R (witness R e) v t) d a b = e*(sign a b).re + t*v (.inr (d,a,b)) := by
  simp [exch,line,witness,d.property]

omit [Fintype S] in
private theorem exchangeDeriv (e : ℝ) (v : Params R) (d : R.dirs) (a b : Axis) :
    HasDerivAt (fun t => exch R (line R (witness R e) v t) d a b) (v (.inr (d,a,b))) 0 := by
  simp only [bondLine]
  simpa only [Pi.add_apply,id_eq,zero_add,one_mul] using (hasDerivAt_const (0:ℝ) (e*(sign a b).re)).add ((hasDerivAt_id (0:ℝ)).mul_const (v (.inr (d,a,b))))

private theorem minorDerivative (e : ℝ) (v : Params R) (d : R.dirs) (a : Axis) :
    fderiv ℝ (polynomialRows R false) (witness R e) v (.inr (d,a,1)) =
      -8*e*(v (.inr (d,a+1,a+2))-v (.inr (d,a+2,a+1))) := by
  let b := a+1; let c := a+2
  have D := exchangeDeriv R e v d
  have h := (((D b b).mul (D c c)).sub ((D b c).mul (D c b))).const_mul (-8)
  have same := (rowDeriv R false (witness R e) v (.inr (d,a,1))).unique h
  rw [same]; simp [bondLine,b,c,sigs]; ring

private theorem antiDerivative (e : ℝ) (v : Params R) (d : R.dirs) (a : Axis) :
    fderiv ℝ (polynomialRows R true) (witness R e) v (.inr (d,a,1)) =
      v (.inr (d,a+1,a+2))-v (.inr (d,a+2,a+1)) :=
  (rowDeriv R true (witness R e) v (.inr (d,a,1))).unique
    ((exchangeDeriv R e v d _ _).sub (exchangeDeriv R e v d _ _))

private theorem cubicDerivative (v : Params R) (d : R.dirs) (a : Axis) :
    fderiv ℝ (polynomialRows R true) (witness R 0) v (.inr (d,a,2)) =
      v (.inr (d,a+1,a+1))+v (.inr (d,a+2,a+2))-
      v (.inr (d,a+1,a+2))-v (.inr (d,a+2,a+1)) := by
  let x := witness R 0
  let b := a+1; let c := a+2
  have E := exchangeDeriv R 0 v d
  have Q (u z : Axis) := ((qt_smooth R d u z).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    0 (lineDeriv R x v)
  have q0 (u z : Axis) : qt R (line R x v 0) d u z = 1/4 := by
    have ex : exch R x = fun _ => 0 := by
      funext e i j; simp [exch,x,witness]
    simp only [line,zero_smul,add_zero,qt,ham,ex,fieldCorrelation R _ d.property]
    norm_num [x,fields,witness]
  have dif := (((((E b b).mul (Q c c)).add ((E c c).mul (Q b b))).sub
    ((E b c).mul (Q c b))).sub ((E c b).mul (Q b c))).const_mul 4
  rw [(rowDeriv R true x v (.inr (d,a,2))).unique dif]
  dsimp only [Function.comp_apply,x,b,c] at q0 ⊢
  simp only [q0,bondLine,zero_mul,add_zero]
  ring

private theorem auxiliary_regular : Function.Injective (fderiv ℝ (polynomialRows R true) (witness R 0)) := by
  apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective (fderiv ℝ (polynomialRows R true) (witness R 0)).toLinearMap)
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change fderiv ℝ (polynomialRows R true) (witness R 0) v = 0 at hv
  have zd (d : R.dirs) (a : Axis) : v (.inr (d,a,a))=0 := by
    have hh := (rowDeriv R true (witness R 0) v (.inr (d,a,0))).unique ((exchangeDeriv R 0 v d a a).neg)
    rw [hv] at hh; simpa using hh.symm
  have allEx (d : R.dirs) (i j : Axis) : v (.inr (d,i,j))=0 := by
    have off (a : Axis) : v (.inr (d,a+1,a+2))=0 ∧ v (.inr (d,a+2,a+1))=0 := by
      have ha := antiDerivative R 0 v d a
      have hc := cubicDerivative R v d a
      rw [hv] at ha hc
      simp only [Pi.zero_apply,zd] at ha hc
      constructor <;> linarith
    have h₀ := off 0; have h₁ := off 1; have h₂ := off 2
    rcases axes i with rfl|rfl|rfl <;> rcases axes j with rfl|rfl|rfl <;> first | exact zd d _ | exact h₀.1 | exact h₀.2 | exact h₁.1 | exact h₁.2 | exact h₂.1 | exact h₂.2
  have fieldLine (t : ℝ) : exch R (line R (witness R 0) v t) = fun _ => 0 := by
    funext d a b; by_cases hd : d ∈ R.dirs
    · simpa [bondLine,allEx] using bondLine R 0 v ⟨d,hd⟩ a b t
    · simp [exch,hd]
  have onsite (a : Axis) : v (.inl (a+1))+v (.inl (a+2))=0 := by
    have row := rowDeriv R true (witness R 0) v (.inl a)
    change HasDerivAt (fun t => onsiteRow (qubitH R _ (exch R (line R (witness R 0) v t))) a) _ 0 at row
    simp_rw [fieldLine,onsite_field] at row
    rw [hv] at row
    let h (a : Axis) := (hasDerivAt_const (0:ℝ) (1/2:ℝ)).add ((hasDerivAt_id (0:ℝ)).mul_const (v (.inl a)))
    have eq := row.unique ((((h (a+1)).pow 2).add ((h (a+2)).pow 2)).const_mul 4)
    norm_num at eq; linarith
  have hx := onsite 0; have hy := onsite 1; have hz := onsite 2
  simp only [zero_add,adds] at hx hy hz
  funext i; cases i with
  | inl a => rcases axes a with rfl|rfl|rfl <;> change _ = (0:ℝ) <;> linarith
  | inr i => exact allEx i.1 i.2.1 i.2.2

/-- Every sufficiently small positive ε in the paper's one-parameter family
gives a nonsingular Jacobian of the measured feature map. -/
theorem regular_witness : ∀ᶠ e in 𝓝[>] (0:ℝ), Function.Injective (fderiv ℝ (paperFeatures R) (witness R e)) := by
  have wc : Continuous (witness R) := by
    apply continuous_pi; intro i; cases i with
    | inl a => exact continuous_const
    | inr i => exact continuous_id.mul continuous_const
  have hd := (rows_smooth R true).fderiv_right (m := 0) (by simp)
  have hc := ContinuousLinearMap.continuous_det.comp (hd.continuous.comp wc)
  have near := hc.continuousAt.eventually_ne ((det_iff _).2 (auxiliary_regular R))
  filter_upwards [nhdsWithin_le_nhds near,self_mem_nhdsWithin] with e he ep
  have inj := (det_iff _).1 he
  rw [paper_eq]
  apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective (fderiv ℝ (polynomialRows R false) (witness R e)).toLinearMap)
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply inj; rw [map_zero]
  funext i
  change fderiv ℝ (polynomialRows R false) (witness R e) v = 0 at hv
  have same (j : Index R) (eq : ∀ p, polynomialRows R true p j = polynomialRows R false p j) :=
    (rowDeriv R false (witness R e) v j).unique ((rowDeriv R true (witness R e) v j).congr_of_eventuallyEq (Eventually.of_forall (fun t => (eq _).symm)))
  cases i with
  | inl a => exact (same _ (fun _ => rfl)).symm.trans (congrFun hv _)
  | inr i =>
    obtain ⟨d,a,k⟩ := i
    rcases axes k with rfl|rfl|rfl
    · exact (same _ (fun _ => rfl)).symm.trans (congrFun hv _)
    · change fderiv ℝ (polynomialRows R true) (witness R e) v (.inr (d,a,1)) = 0
      rw [antiDerivative]
      have hm := minorDerivative R e v d a
      rw [hv] at hm
      exact (mul_eq_zero.mp hm.symm).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt ep))
    · exact (same _ (fun _ => rfl)).symm.trans (congrFun hv _)

theorem diagonalHT : ∀ᵐ p ∂MeasureTheory.volume, LocallySolvable (paperFeatures R) p := by
  obtain ⟨e,he⟩ := (regular_witness R).exists
  apply generic_of_witness (w := witness R e) _ he
  rw [paper_eq]; exact rows_smooth R false
end DSFTomography.HT.Diagonal
