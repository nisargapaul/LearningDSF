import DSFTomography.SFFinite
import DSFTomography.SFReadout

/-! Normalized connected zeroth moments and ordered first moments for the
paper's strong-field measurement. The forward Fourier phase is exp(+iq·d). -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT

variable {S D : Type*} [AddCommGroup S]

/-- Coefficients of cos(q·d) and sin(q·d) in the real part of the spectrum,
given its complex coefficients at the two oriented displacements. -/
def cosAmp (u v : ℂ) : ℝ := (u + v).re
def sinAmp (u v : ℂ) : ℝ := (v - u).im

theorem real_fourier_pair (z u v : ℂ) :
    (z*u + star z*v).re = z.re*cosAmp u v + z.im*sinAmp u v := by
  simp [cosAmp,sinAmp,Complex.mul_re]; ring

/-- The four slots are the centered cosine, centered sine, static difference
cosine and real cross-channel cosine. The first projection is the constant
term of the centered transverse channel. All input moments are divided by 2π. -/
def paperHarmonics (disp : D → S) (B : ℝ) (A : Axis → Data S) : Harmonics D :=
  let centered i d := (A i).first d (i+1) (i+1) - (2*(B:ℂ))*(A i).static d (i+1) (i+1)
  let diff i d := (A i).static d (i+1) (i+1) - (A i).static d (i+2) (i+2)
  let cross i d := (A i).static d (i+1) (i+2)
  (fun i => (centered i 0).re, fun e i =>
    let d := disp e
    ![cosAmp (centered i d) (centered i (-d)), sinAmp (centered i d) (centered i (-d)),
      (B/2)*cosAmp (diff i d) (diff i (-d)), B*cosAmp (cross i d) (cross i (-d))])

variable [Fintype S] [DecidableEq S]

def paperFromDSF (disp : D → S) (B : ℝ) (spectra : Axis → Data (Momentum S)) : Harmonics D :=
  paperHarmonics disp B (fun i => connected (spectra i).harmonics)

def groundPaperReadout (V : Volume S) (B : ℝ) (disp : D → S) : Harmonics D :=
  paperFromDSF disp B fun i => let W := driven V B i; groundDSF W (lowest W)

/-- Ordered first moment in the physical basis. Only the commutator with the
left spin is required. Terms of the Hamiltonian disjoint from it commute. -/
theorem first_ground (V : Volume S) (m : Config S) (d : S) (a b : Axis) :
    (groundDSF V m).harmonics.first d a b =
      avg (fun t => (eigenState V m).ev
        (bracket (spinAt t a) (qubitH V.R V.h V.J) * spinAt (t+d) b)) := by
  rw [harmonics_ground]
  change avg _ = avg _
  apply congrArg avg
  funext t
  rw [firstMoment]
  let U := energyBasis V.R V.h V.J
  have diag := (rotate_H V.R V.h V.J U).symm.trans (diagonalized V.R V.h V.J)
  rw [← diag]
  change mean (pureWeight m) ((inBasis U _ * inBasis U _ - inBasis U _ * inBasis U _) * inBasis U _) = _
  simp only [inBasis_mul]
  have sub (A C : Op (Config S)) : inBasis U A - inBasis U C = inBasis U (A-C) := by
    simp [inBasis,Matrix.mul_sub,Matrix.sub_mul]
  rw [sub,inBasis_mul]
  simp [mean,pureWeight,ite_mul,eigenState,U,bracket]

/-- Change of energy units for the actual Lehmann sum. -/
theorem first_scale {ι : Type*} [Fintype ι] (w E : ι → ℂ) (k : ℂ) (A C : Op ι) :
    m₁ w (fun j => k * E j) A C = k * m₁ w E A C := by
  unfold m₁
  simp_rw [← mul_sub, mul_assoc]
  simp only [← Finset.mul_sum,mul_left_comm]

def energyScale (k : ℝ) (A : Data S) : Data S where
  static := A.static
  first d a b := (k:ℂ) * A.first d a b

theorem measured_energyScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Spins S ι) (w E : ι → ℂ) (k : ℝ) :
    measured P w (fun j => (k:ℂ)*E j) = energyScale k (measured P w E) := by
  apply congrArg₂ Data.mk rfl
  funext d a b
  simp [measured,first_scale,avg,← Finset.mul_sum,mul_div_assoc]

omit [Fintype S] [DecidableEq S] in
theorem harmonics_energyScale (disp : D → S) (B : ℝ) (A : Axis → Data S) :
    paperHarmonics disp B (fun i => energyScale B (A i)) = B • paperHarmonics disp 1 A := by
  have cent (u v : ℂ) : (B:ℂ)*u - 2*(B:ℂ)*v = (B:ℂ)*(u-2*v) := by ring
  apply Prod.ext
  · funext i; simp [paperHarmonics,energyScale,cent,Complex.mul_re]
  · funext d i l; fin_cases l <;>
      simp [paperHarmonics,energyScale,cent,cosAmp,sinAmp,Complex.mul_re,Complex.mul_im] <;> ring

end DSFTomography.SF
