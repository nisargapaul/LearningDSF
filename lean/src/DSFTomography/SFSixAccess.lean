import DSFTomography.SFSixFinite
import DSFTomography.DSFMomentum

/-! The input interface contains diagonal spectra only. Coherent elastic
intensity at zero momentum supplies the connected subtraction in the same
channel; no crossed spin measurement is part of this interface. -/
noncomputable section
namespace DSFTomography.SF.DiagonalSix
open DSFTomography HT Spectral

structure DiagonalData (S : Type*) where
  static : S → Axis → ℂ
  first : S → Axis → ℂ

def diagonalData {S : Type*} (A : Data S) : DiagonalData S :=
  ⟨fun d a => A.static d a a, fun d a => A.first d a a⟩

variable {S D : Type*} [AddCommGroup S]

def diagonalHarmonics (disp : D → S) (B : ℝ) (A : Axis → DiagonalData S) : Harmonics D :=
  let c i d := (A i).first d (i+1)-2*(B:ℂ)*(A i).static d (i+1)
  let e i d := (A i).static d (i+1)-(A i).static d (i+2)
  (fun i => (c i 0).re, fun d i =>
    ![cosAmp (c i (disp d)) (c i (-disp d)),sinAmp (c i (disp d)) (c i (-disp d)),
      (B/2)*cosAmp (e i (disp d)) (e i (-disp d)),0])

/-- Three coordinate scans and the xx channel of each tilted frame.
Every entry is a diagonal zeroth or first spectral moment. -/
def fromDiagonal (disp : D → S) (B : ℝ) (coordinate : Axis → DiagonalData S)
    (tilted : Pair → DiagonalData S) : Harmonics D :=
  assemble (diagonalHarmonics disp B coordinate) fun t d =>
    cosAmp ((tilted t).first (disp d) 0-2*(B:ℂ)*(tilted t).static (disp d) 0)
      ((tilted t).first (-disp d) 0-2*(B:ℂ)*(tilted t).static (-disp d) 0)

/-- Factorization of the certified measurement map through diagonal data.
All unused crossed entries may be changed arbitrarily. -/
theorem diagonal_factorization (disp : D → S) (B : ℝ)
    (A : Axis → Data S) (T : Pair → Axis → Data S) :
    fromDiagonal disp B (fun i => diagonalData (A i)) (fun t => diagonalData (T t 2)) =
      assemble (paperHarmonics disp B A) (fun t d => (paperHarmonics disp B (T t)).2 d 2 0) := by
  apply Prod.ext
  · rfl
  · funext d i k
    fin_cases k <;>
      simp [fromDiagonal,assemble,diagonalHarmonics,diagonal,diagonalData,paperHarmonics,
        Matrix.cons_val_two,Matrix.cons_val_three,show (2:Axis)+1=0 by decide]

variable [Fintype S] [DecidableEq S]

/-- Ground-to-ground contribution to the diagonal zero-momentum elastic
line, divided by N (and with the common 2π normalization removed). -/
def coherentZero (V : Volume S) (m : Config S) (a : Axis) : ℂ :=
  let P := qubitSpins (energyBasis V.R V.h V.J)
  let E := energies V.R V.h V.J
  (∑ d : S, ∑ r : S, (momentumLines P (pureWeight m) E 1 a a).weight (d,r,m,m))/(Fintype.card S:ℂ)

theorem coherentZero_eq (V : Volume S) (m : Config S) (a : Axis) :
    coherentZero V m a = (groundDSF V m).harmonics.mag a * (groundDSF V m).harmonics.mag a := by
  rw [mag_ground]
  let f := fun r => (eigenState V m).ev (spinAt r a)
  have shift (r : S) : ∑ d : S, f (r+d)=∑ s : S, f s := Equiv.sum_comp (Equiv.addLeft r) f
  change coherentZero V m a=avg f*avg f
  simp only [coherentZero,momentumLines,pureWeight,ite_true,eq_self,one_mul,mul_one,AddChar.one_apply]
  change (∑ d : S, ∑ r : S, (1/(Fintype.card S:ℂ))*f r*f (r+d))/(Fintype.card S:ℂ)=_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,shift]
  simp only [avg,← Finset.sum_mul,← Finset.mul_sum]
  ring

/-- The connected diagonal moments are obtained without Data.mag or any
crossed DSF channel: subtract the measured coherent elastic intensity. -/
def observedDiagonal (V : Volume S) (m : Config S) : DiagonalData S where
  static d a := (groundDSF V m).harmonics.static d a a-coherentZero V m a
  first d a := (groundDSF V m).harmonics.first d a a

theorem observedDiagonal_eq (V : Volume S) (m : Config S) :
    observedDiagonal V m=diagonalData (connected (groundDSF V m).harmonics) := by
  simp only [observedDiagonal,diagonalData,connected,coherentZero_eq]

theorem finite_diagonal_access (R : Bonds S) (B : ℝ) (p : Params R.dirs) :
    fromDiagonal Subtype.val B
      (fun i => let W := driven (withParams R p) B i; observedDiagonal W (lowest W))
      (fun t => let W := driven (withParams R (rotate t p)) B 2; observedDiagonal W (lowest W)) =
      finiteReadout R B p := by
  simp only [observedDiagonal_eq]
  exact diagonal_factorization Subtype.val B
    (fun i => let W := driven (withParams R p) B i; connected (groundDSF W (lowest W)).harmonics)
    (fun t i => let W := driven (withParams R (rotate t p)) B i; connected (groundDSF W (lowest W)).harmonics)

end DSFTomography.SF.DiagonalSix
