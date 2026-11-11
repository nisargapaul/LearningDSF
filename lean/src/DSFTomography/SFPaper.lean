import DSFTomography.SFPolarizedSlope
import DSFTomography.SFRemainder
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

def parameters (V : Volume S) : Params V.R.dirs := (V.h,fun d => V.J d)

/-- Projection of the *local ordered* centered moment and covariances.
The second term in each bond amplitude traverses that bond in reverse. -/
def localReadout (R : Bonds S)
    (c : Axis → S → S → ℂ) (s : Axis → S → S → Axis → Axis → ℂ) : Harmonics R.dirs :=
  (fun i => (avg (fun r => c i r r)).re, fun d i =>
    let v := (d : S)
    let plus := avg fun r => c i r (r+v)
    let minus := avg fun r => c i (r+v) r
    let st := fun a b => avg fun r => s i r (r+v) a b
    ![cosAmp plus minus, sinAmp plus minus,
      (st 0 0 - st 1 1).re, (st 0 1 + st 1 0).re])

namespace EigenRay
variable {V : Volume S} {i : Axis} (g : EigenRay V i)
def meanProbe (a : Axis) (t : ℝ) := avg fun r => sandwich (g.ψ t) (spinAt r a) (g.ψ t)
theorem transverse_mean_zero (a : Axis) (ha : a=0 ∨ a=1) : g.meanProbe a 0 = 0 := by
  have at0 (r : S) : spinAt r a (vacuum S) (vacuum S) = 0 := by
    simp only [spinAt,word_one]
    rcases ha with rfl|rfl <;> simp [vacuum,bitConfig,pauliValues]
  simp [meanProbe,g.vacuum_at,sandwich,ket,apply_ite,ite_mul,at0,avg]

theorem mean_smooth (a : Axis) : DifferentiableAt ℝ (g.meanProbe a) 0 := by
  let z := fun (r : S) (x y : Config S) => spinAt r a x y
  have d (r : S) (x y : Config S) := (((g.smooth_ket x).hasDerivAt.star.mul_const (z r x y)).mul
    (g.smooth_ket y).hasDerivAt)
  exact ((HasDerivAt.fun_sum (u := Finset.univ) (fun r _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun y _ => d r x y)))).div_const (Fintype.card S:ℂ)).differentiableAt

def covariance (r s : S) (a b : Axis) (t : ℝ) := g.staticPair r s a b t - g.meanProbe a t*g.meanProbe b t

def connectedCentered (r s : S) (t : ℝ) :=
  g.centeredPair r s t + 2*(g.meanProbe 0 t*g.meanProbe 0 t)

theorem dcov (r s : S) (a b : Axis) (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    {z : ℂ} (der : HasDerivAt (g.staticPair r s a b) z 0) :
    HasDerivAt (g.covariance r s a b) z 0 :=
  connected_response der (g.mean_smooth a).hasDerivAt (g.mean_smooth b).hasDerivAt
    (g.transverse_mean_zero a ha) (g.transverse_mean_zero b hb)

theorem dcenter (r s : S) {z : ℂ} (der : HasDerivAt (g.centeredPair r s) z 0) :
    HasDerivAt (g.connectedCentered r s) z 0 := by
  have dm := (g.mean_smooth 0).hasDerivAt
  simpa [connectedCentered,g.transverse_mean_zero 0 (Or.inl rfl)] using der.add ((dm.mul dm).const_mul 2)

end EigenRay

/-- Unit-field DSF readout along a coupling ray, in the three cyclic spin frames. -/
def rayReadout (V : Volume S) (g : ∀ i, EigenRay V i) (t : ℝ) : Harmonics V.R.dirs :=
  localReadout V.R (fun i r s => (g i).connectedCentered r s t)
    (fun i r s a b => (g i).covariance r s a b t)

omit [DecidableEq S] in
private theorem avg_deriv {f : S → ℝ → ℂ} {z : ℂ} (df : ∀ r, HasDerivAt (f r) z 0) :
    HasDerivAt (fun t => avg (fun r => f r t)) z 0 := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => df r)).div_const (Fintype.card S:ℂ)
  simpa [avg,Fintype.card_ne_zero] using h

private theorem deriv_re {f : ℝ → ℂ} {z : ℂ} (h : HasDerivAt f z 0) :
    HasDerivAt (fun t => (f t).re) z.re 0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h
private theorem deriv_im {f : ℝ → ℂ} {z : ℂ} (h : HasDerivAt f z 0) :
    HasDerivAt (fun t => (f t).im) z.im 0 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 h

/-- The directional derivative is the entire leading matrix of the manuscript:
three constants and four real amplitudes per field and oriented displacement. -/
theorem paper_directional_slope (V : Volume S) (g : ∀ i, EigenRay V i) :
    HasDerivAt (rayReadout V g) (leading (parameters V)) 0 := by
  classical
  have onsite (i : Axis) : HasDerivAt (fun t => (rayReadout V g t).1 i)
      ((leading (parameters V)).1 i) 0 := by
    have atR (r : S) := (g i).dcenter r r ((g i).centered_slope r r)
    have df (r : S) : HasDerivAt ((g i).connectedCentered r r)
        ((-2*V.h i-4*∑ e∈V.R.dirs, V.J e i i : ℝ):ℂ) 0 := by
      rw [← flip_energy_shift V i r]; simpa using atR r
    have sum : (∑ d : V.R.dirs, V.J d i i) = ∑ e∈V.R.dirs,V.J e i i :=
      Finset.sum_attach V.R.dirs fun e => V.J e i i
    simpa only [rayReadout,localReadout,leading,parameters,sum,Complex.ofReal_re] using deriv_re (avg_deriv df)
  apply HasDerivAt.prodMk (hasDerivAt_pi.mpr onsite)
  apply hasDerivAt_pi.mpr; intro d; apply hasDerivAt_pi.mpr; intro i; apply hasDerivAt_pi.mpr; intro k
  have p1 := avg_deriv (fun r => (g i).dcenter _ _ ((g i).centered_slopes d.property r).1)
  have p2 := avg_deriv (fun r => (g i).dcenter _ _ ((g i).centered_slopes d.property r).2.1)
  have s00 := avg_deriv (fun r => (g i).dcov _ _ 0 0 (Or.inl rfl) (Or.inl rfl) ((g i).static_slopes d.property r).1)
  have s11 := avg_deriv (fun r => (g i).dcov _ _ 1 1 (Or.inr rfl) (Or.inr rfl) ((g i).static_slopes d.property r).2.1)
  have s01 := avg_deriv (fun r => (g i).dcov _ _ 0 1 (Or.inl rfl) (Or.inr rfl) ((g i).static_slopes d.property r).2.2.1)
  have s10 := avg_deriv (fun r => (g i).dcov _ _ 1 0 (Or.inr rfl) (Or.inl rfl) ((g i).static_slopes d.property r).2.2.2)
  change HasDerivAt (fun t => (rayReadout V g t).2 d i k) ((leading (parameters V)).2 d i k) 0
  rw [leading_bond]
  fin_cases k
  · convert deriv_re (p1.add p2) using 1; simp [parameters,two_mul]
  · convert deriv_im (p2.sub p1) using 1; simp [parameters]; ring
  · convert deriv_re (s00.sub s11) using 1; simp [parameters]; ring
  · convert deriv_re (s01.add s10) using 1; simp [parameters]

end DSFTomography.SF
