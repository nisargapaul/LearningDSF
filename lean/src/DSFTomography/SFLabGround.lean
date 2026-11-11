import DSFTomography.SFFrame

/-! Compare the field-frame ground ket with the lowest eigenvector chosen
by the laboratory spectral theorem. The diagonal expectation is independent
of their phases and of all excited-state degeneracies. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Matrix Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem column_nonzero {Q : Op ι} (left : Q.conjTranspose*Q=1) (m : ι) :
    Q.col m ≠ 0 := by
  intro z
  have eq := congrFun (congrFun left m) m
  have col (j : ι) : Q j m = 0 := congrFun z j
  simp [Matrix.mul_apply,col] at eq

omit [DecidableEq ι] in
private theorem sandwich_column (Q A : Op ι) (m : ι) :
    (Q.conjTranspose*A*Q) m m = sandwich (Q.col m) A (Q.col m) := by
  simp only [sandwich,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.col_apply,
    Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]

private theorem sandwich_id (ψ : ι → ℂ) (normed : ∑ x, Complex.normSq (ψ x) = 1) :
    sandwich ψ 1 ψ = 1 := by
  simp [sandwich,Matrix.one_apply,mul_ite,ite_mul,
    ← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_sum,normed]

private theorem spectral_ground_column {Q H : Op ι} (left : Q.conjTranspose*Q=1)
    (right : Q*Q.conjTranspose=1) {f : ι → ℂ} (inter : H*Q = Q*Matrix.diagonal f)
    (m : ι) (minim : ∀ j, (f m).re ≤ (f j).re) {ψ : ι → ℂ} {e : ℂ}
    (normed : ∑ j, Complex.normSq (ψ j)=1) (eig : H *ᵥ ψ = e • ψ)
    (low : ∀ μ (v : ι → ℂ), v ≠ 0 → H *ᵥ v = μ • v → μ.re ≤ e.re →
      μ=e ∧ ∃ c : ℂ, v=c • ψ) :
    f m=e ∧ ∀ A, (Q.conjTranspose*A*Q) m m = sandwich ψ A ψ := by
  let z := Q.conjTranspose *ᵥ ψ
  have recover : Q *ᵥ z = ψ := by simp [z,Matrix.mulVec_mulVec,right]
  have nz : z ≠ 0 := by
    intro eq; rw [eq,Matrix.mulVec_zero] at recover
    simp [← recover] at normed
  obtain ⟨j,hj⟩ := Function.ne_iff.mp nz
  have diag : Matrix.diagonal f *ᵥ z = e • z := by
    have pull : Q.conjTranspose*H = Matrix.diagonal f*Q.conjTranspose := by
      calc
        Q.conjTranspose*H = Q.conjTranspose*(H*Q)*Q.conjTranspose := by
          simp only [Matrix.mul_assoc,right,Matrix.mul_one]
        _ = _ := by rw [inter,← Matrix.mul_assoc Q.conjTranspose Q,left,Matrix.one_mul]
    change Matrix.diagonal f *ᵥ (Q.conjTranspose *ᵥ ψ) = _
    rw [Matrix.mulVec_mulVec,← pull,← Matrix.mulVec_mulVec,eig,Matrix.mulVec_smul]
  have eqj := congrFun diag j
  rw [Matrix.mulVec_diagonal] at eqj
  have fj : f j = e := mul_right_cancel₀ hj eqj
  have mv : H *ᵥ Q.col m = f m • Q.col m := by
    funext k
    have row := congrFun (congrFun inter k) m
    rw [Matrix.mul_diagonal] at row
    simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.col_apply,mul_comm] using row
  obtain ⟨energy,c,v⟩ := low (f m) _ (column_nonzero left m) mv (fj ▸ minim j)
  refine ⟨energy,?_⟩
  have ev (A : Op ι) : (Q.conjTranspose*A*Q) m m = (star c*c)*sandwich ψ A ψ := by
    rw [sandwich_column,v]
    simp only [sandwich,Pi.smul_apply,smul_eq_mul,star_mul',Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  have cc := ev 1
  rw [Matrix.mul_one,left,Matrix.one_apply_eq,sandwich_id ψ normed,mul_one] at cc
  intro A; rw [ev,← cc,one_mul]

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {R : Bonds S}

/-- The canonical lowest eigenstate of the driven laboratory Hamiltonian and
the physical chart give exactly the same expectation for every observable. -/
theorem laboratory_minimum (g : GroundChart R i) {B : ℝ} (hB : 0 < B) (p : Params R.dirs)
    (physical : IsGroundPair R i (B⁻¹ • p) (g.ψ (B⁻¹ • p)) (g.E (B⁻¹ • p))) (m : Config S)
    (low : ∀ j, energies R (driven (withParams R p) B i).h (withParams R p).J m ≤
      energies R (driven (withParams R p) B i).h (withParams R p).J j) :
    let x := B⁻¹ • p
    let W := driven (withParams R p) B i
    (energies W.R W.h W.J m : ℂ) = (B:ℂ)*(g.E x - Fintype.card S) ∧
    ∀ A, (eigenState W m).ev (toLab i*A*(toLab i).conjTranspose) = sandwich (g.ψ x) A (g.ψ x) := by
  let x := B⁻¹ • p
  let W := driven (withParams R p) B i
  let H := unitHamiltonian R i x
  let L := qubitH W.R W.h W.J
  let U : Op (Config S) := (qubitH_hermitian W.R W.h W.J).eigenvectorUnitary
  let T := toLab (S := S) i
  let Q := T.conjTranspose*U
  let e := energies W.R W.h W.J
  let f := fun k => (e k:ℂ)/(B:ℂ)+(Fintype.card S:ℂ)
  have leftT : T.conjTranspose*T = 1 := (toLab_unit i).1
  have rightT : T*T.conjTranspose = 1 := (toLab_unit i).2
  have leftU : U.conjTranspose*U=1 := unitary.coe_star_mul_self _
  have rightU : U*U.conjTranspose=1 := unitary.coe_mul_star_self _
  have qstar : Q.conjTranspose = U.conjTranspose*T := by simp [Q,Matrix.conjTranspose_mul]
  have qleft : Q.conjTranspose*Q=1 := by
    rw [qstar]; simp only [Q,← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ T T.conjTranspose,rightT,Matrix.mul_one,leftU]
  have qright : Q*Q.conjTranspose=1 := by
    rw [qstar]; simp only [Q,← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ U U.conjTranspose,rightU,Matrix.mul_one,leftT]
  have hrel : T*((B:ℂ) • H)*T.conjTranspose = ((B:ℂ)*Fintype.card S) • 1 + L :=
    toLab_driven R i hB p
  have labdiag : U.conjTranspose*L*U=Matrix.diagonal (fun j => (e j:ℂ)) :=
    (qubitH_hermitian W.R W.h W.J).star_mul_self_mul_eq_diagonal
  have scale : (B:ℂ) • (Q.conjTranspose*H*Q) = (↑B * ↑(Fintype.card S) : ℂ) • 1 + Matrix.diagonal (fun j => (e j:ℂ)) := by
    calc
      _ = U.conjTranspose*(T*((B:ℂ) • H)*T.conjTranspose)*U := by
        rw [qstar]; simp [Q,Matrix.mul_assoc]
      _ = _ := by rw [hrel,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
                       Matrix.mul_one,leftU,labdiag]
  have Bnz : (B:ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have diag : Q.conjTranspose*H*Q = Matrix.diagonal f := by
    ext j k
    have eq := congrFun (congrFun scale j) k
    by_cases same : j=k
    · subst k; simp [Matrix.smul_apply] at eq; simp [f]; field_simp [Bnz]; linear_combination eq
    · simp [Matrix.smul_apply,same,hB.ne'] at eq ⊢; exact eq
  have inter : H*Q=Q*Matrix.diagonal f := by
    calc
      H*Q = (Q*Q.conjTranspose)*(H*Q) := by rw [qright,Matrix.one_mul]
      _ = Q*(Q.conjTranspose*H*Q) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [diag]
  have row (v : Config S → ℂ) (k : Config S) :
      (H *ᵥ v) k = flipGap k*v k + ∑ j, fieldFrame (withParams R x) i k j*v j := by
    change ((Matrix.diagonal flipGap + fieldFrame (withParams R x) i) *ᵥ v) k = _
    rw [Matrix.add_mulVec,Pi.add_apply,Matrix.mulVec_diagonal]; rfl
  have eig : H *ᵥ g.ψ x = g.E x • g.ψ x := by
    funext k; rw [row]; exact physical.2.1 k
  have min (j : Config S) : (f m).re ≤ (f j).re := by
    simp only [f,← Complex.ofReal_div,Complex.add_re,Complex.ofReal_re,add_le_add_iff_right]
    exact div_le_div_of_nonneg_right (low j) hB.le
  obtain ⟨em,ev⟩ := spectral_ground_column qleft qright inter m min physical.1 eig
    (fun μ v nz eigv below => physical.2.2 μ v nz (fun k => (row v k).symm.trans (congrFun eigv k)) below)
  refine ⟨?_,?_⟩
  · change (e m:ℂ) = (B:ℂ)*(g.E x - Fintype.card S)
    rw [← em]; dsimp [f]; field_simp [Bnz]; ring
  · intro A
    change (U.conjTranspose*(T*A*T.conjTranspose)*U) m m = _
    rw [← ev A,qstar]; simp [Q,Matrix.mul_assoc]


theorem laboratory_ground (g : GroundChart R i) {B : ℝ} (hB : 0 < B) (p : Params R.dirs)
    (physical : IsGroundPair R i (B⁻¹ • p) (g.ψ (B⁻¹ • p)) (g.E (B⁻¹ • p))) :
    let x := B⁻¹ • p
    let W := driven (withParams R p) B i
    (energies W.R W.h W.J (lowest W) : ℂ) = (B:ℂ)*(g.E x - Fintype.card S) ∧
    ∀ A, (eigenState W (lowest W)).ev (toLab i*A*(toLab i).conjTranspose) = sandwich (g.ψ x) A (g.ψ x) :=
  laboratory_minimum g hB p physical _ (lowest_le _)

end DSFTomography.SF
