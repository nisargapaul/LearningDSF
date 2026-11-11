import DSFTomography.SFSixAccess

/-! Identify the coherent subtraction with the entire measured elastic line
when the strong-field ground state is simple. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Spectral Matrix
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {R : Bonds S}

/-- A physical ground chart implies that the canonical lowest energy has
multiplicity one. Excited-energy degeneracies remain unrestricted. -/
theorem ground_energy_simple {i : Axis} (g : GroundChart R i) {B : ℝ} (pos : 0<B)
    (p : Params R.dirs)
    (physical : IsGroundPair R i (B⁻¹ • p) (g.ψ (B⁻¹ • p)) (g.E (B⁻¹ • p))) :
    let W := driven (withParams R p) B i
    ∀ j, energies W.R W.h W.J j=energies W.R W.h W.J (lowest W) → j=lowest W := by
  intro W j equal
  have low : ∀ k, energies W.R W.h W.J j ≤ energies W.R W.h W.J k := by
    intro k; rw [equal]; exact lowest_le W k
  have e0 := (laboratory_ground g pos p physical).2
  have ej := (laboratory_minimum g pos p physical j low).2
  let T := toLab (S := S) i
  let U := energyBasis W.R W.h W.J
  let D : Op (Config S) := Matrix.diagonal (fun k => if k=lowest W then 1 else 0)
  let O := inBasis U⁻¹ D
  have undo : T*(T.conjTranspose*O*T)*T.conjTranspose=O := by
    calc
      _ = (T*T.conjTranspose)*O*(T*T.conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = O := by rw [(toLab_unit i).2,Matrix.one_mul,Matrix.mul_one]
  have same := (ej (T.conjTranspose*O*T)).trans (e0 (T.conjTranspose*O*T)).symm
  change (eigenState W j).ev (T*(T.conjTranspose*O*T)*T.conjTranspose)=
    (eigenState W (lowest W)).ev (T*(T.conjTranspose*O*T)*T.conjTranspose) at same
  rw [undo] at same
  change inBasis U O j j=inBasis U O (lowest W) (lowest W) at same
  have cancel : inBasis U O=D := by simp [O,inBasis,Matrix.mul_assoc]
  rw [cancel] at same
  by_contra ne
  simpa [D,ne] using same

/-- Full frequency-zero intensity of the diagonal q=0 DSF, divided by 2πN. -/
def elasticZero (V : Volume S) (m : Config S) (a : Axis) : ℂ :=
  let E := energies V.R V.h V.J
  let L := momentumLines (qubitSpins (energyBasis V.R V.h V.J)) (pureWeight m) E 1 a a
  (∑ d : S, ∑ r : S, ∑ i : Config S, ∑ j : Config S,
    if E j-E i=0 then L.weight (d,r,i,j) else 0)/(Fintype.card S:ℂ)

theorem elasticZero_eq (V : Volume S) (m : Config S)
    (simple : ∀ j, energies V.R V.h V.J j=energies V.R V.h V.J m → j=m) (a : Axis) :
    elasticZero V m a=coherentZero V m a := by
  have iff (j : Config S) : energies V.R V.h V.J j-energies V.R V.h V.J m=0 ↔ j=m :=
    ⟨fun h => simple j (sub_eq_zero.mp h),fun h => by simp [h]⟩
  unfold elasticZero coherentZero
  dsimp only
  apply congrArg (fun z : ℂ => z/(Fintype.card S:ℂ))
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.sum_eq_single m]
  · simp only [iff]
    simp [momentumLines,pureWeight]
  · intro i _ ne
    apply Finset.sum_eq_zero; intro j _
    simp [momentumLines,pureWeight,ne]
  · simp

/-- The diagonal implementation may use the observed elastic peak itself. -/
theorem connected_from_diagonal_elastic (V : Volume S) (m : Config S)
    (simple : ∀ j, energies V.R V.h V.J j=energies V.R V.h V.J m → j=m) (d : S) (a : Axis) :
    (connected (groundDSF V m).harmonics).static d a a =
      (groundDSF V m).harmonics.static d a a-elasticZero V m a := by
  rw [elasticZero_eq V m simple a,coherentZero_eq]
  rfl

end DSFTomography.SF.DiagonalSix
