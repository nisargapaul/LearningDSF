import DSFTomography.SFHarmonics
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

/-! First variation of the ordered, centered DSF at a polarized product
state. No derivatives of excited eigenvectors enter this calculation. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ket representing a product configuration in the polarization basis. -/
def ket (o : ι) (x : ι) : ℂ := if x = o then 1 else 0

/-- A matrix element with the bra written on the left. -/
def sandwich (v : ι → ℂ) (A : Op ι) (w : ι → ℂ) : ℂ :=
  ∑ x, ∑ y, star (v x) * A x y * w y

omit [DecidableEq ι] in
theorem sandwich_deriv {v w : ℝ → ι → ℂ} {T : ℝ → Op ι}
    {dv dw : ι → ℂ} {dT : Op ι}
    (hv : ∀ x, HasDerivAt (fun t => v t x) (dv x) 0)
    (hw : ∀ x, HasDerivAt (fun t => w t x) (dw x) 0)
    (hT : ∀ x y, HasDerivAt (fun t => T t x y) (dT x y) 0) :
    HasDerivAt (fun t => sandwich (v t) (T t) (w t))
      (sandwich dv (T 0) (w 0) + sandwich (v 0) dT (w 0) + sandwich (v 0) (T 0) dw) 0 := by
  have one (x y) := (((hv x).star.mul (hT x y)).mul (hw y))
  simpa [sandwich,Finset.sum_add_distrib,add_mul,mul_add,add_assoc,mul_assoc,mul_comm,mul_left_comm] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun y _ => one x y))

/-- Shift the polarized ground energy to zero; gap(k) is the excitation
energy at unit field. The vacuum row fixes E' and every nonvacuum row
fixes its own excitation amplitude. -/
theorem eigenpair_response (o : ι) (gap : ι → ℂ) (V : Op ι) {ψ : ℝ → ι → ℂ}
    {E : ℝ → ℂ} {u : ι → ℂ} {e : ℂ}
    (vac : ψ 0 = ket o) (g0 : gap o = 0) (E0 : E 0 = 0)
    (dψ : ∀ k, HasDerivAt (fun t => ψ t k) (u k) 0) (dE : HasDerivAt E e 0)
    (eigen : ∀ᶠ t in 𝓝 (0:ℝ), ∀ k, gap k * ψ t k + (t:ℂ)*(∑ l, V k l * ψ t l) = E t * ψ t k) :
    e = V o o ∧ ∀ k ≠ o, gap k * u k = -V k o := by
  have dtime := (hasDerivAt_id (0:ℝ)).ofReal_comp
  have rows (k : ι) : gap k * u k + V k o = e * ket o k := by
    have dv := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (dψ l).const_mul (V k l))
    have h := ((dψ k).const_mul (gap k)).add (dtime.mul dv)
    have equal := h.congr_of_eventuallyEq (eigen.mono (fun t ht => (ht k).symm))
    simpa [vac,ket,E0,mul_ite] using equal.unique (dE.mul (dψ k))
  constructor
  · simpa [g0,ket] using (rows o).symm
  · intro k hk
    simpa [ket,hk] using eq_neg_of_add_eq_zero_left (show gap k * u k + V k o = 0 by simpa [ket,hk] using rows k)

/-- Static response of a probe whose vacuum column and row connect only to
the configuration k. For transverse probes on a bond k is the two-flip
state and its excitation energy is four. -/
theorem static_response (o k : ι) (A : Op ι) {s r : ℂ}
    (col : ∀ l, A l o = s * ket k l) (row : ∀ l, A o l = r * ket k l)
    {ψ : ℝ → ι → ℂ} {u : ι → ℂ} (vac : ψ 0 = ket o)
    (dψ : ∀ l, HasDerivAt (fun t => ψ t l) (u l) 0) :
    HasDerivAt (fun t => sandwich (ψ t) A (ψ t)) (star (u k)*s + r*u k) 0 := by
  have h := sandwich_deriv (T := fun _ => A) dψ dψ (dT := 0) (fun x y => hasDerivAt_const 0 (A x y))
  simpa [vac,sandwich,ket,mul_ite,ite_mul,col,row,apply_ite,star_one,star_zero] using h

/-- Ordered centered moment between two transverse probes. v,w are the
probe-applied ground kets. At zero coupling they are one-flip kets with
energy 2. This annihilates both derivatives of those kets. -/
theorem centered_response (l r : ι) (gap : ι → ℂ) (V : Op ι)
    {E : ℝ → ℂ} {e : ℂ} (E0 : E 0 = 0) (dE : HasDerivAt E e 0)
    {v w : ℝ → ι → ℂ} {dv dw : ι → ℂ}
    (left : v 0 = ket l) (right : w 0 = ket r) (gl : gap l = 2) (gr : gap r = 2)
    (hv : ∀ x, HasDerivAt (fun t => v t x) (dv x) 0)
    (hw : ∀ x, HasDerivAt (fun t => w t x) (dw x) 0) :
    HasDerivAt (fun t => sandwich (v t)
      (Matrix.diagonal (fun x => gap x-E t-2) + (t:ℂ) • V) (w t))
      (V l r - if l=r then e else 0) 0 := by
  let T := fun t : ℝ => Matrix.diagonal (fun x => gap x-E t-2) + (t:ℂ) • V
  let dT := V - Matrix.diagonal (fun _ => e)
  have dt := (hasDerivAt_id (0:ℝ)).ofReal_comp
  have hT (x y) : HasDerivAt (fun t => T t x y) (dT x y) 0 := by
    by_cases h : x=y
    · subst y
      simp only [T,dT,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.diagonal_apply_eq]
      convert ((((hasDerivAt_const (0:ℝ) (gap x)).sub dE).sub_const 2).add (dt.mul_const (V x x))) using 1
      simp; ring
    · simpa [T,dT,Matrix.diagonal_apply_ne _ h] using dt.mul_const (V x y)
  have der := sandwich_deriv hv hw hT
  have zeroRow (x : ι) : T 0 l x = 0 := by
    by_cases h : l = x
    · subst x; simp [T,E0,gl]
    · simp [T,Matrix.diagonal_apply_ne _ h]
  have zeroCol (x : ι) : T 0 x r = 0 := by
    by_cases h : x = r
    · subst x; simp [T,E0,gr]
    · simp [T,Matrix.diagonal_apply_ne _ h]
  have bra (a : ι) (A : Op ι) (b : ι → ℂ) : sandwich (ket a) A b = ∑ y, A a y * b y := by
    simp [sandwich,ket,apply_ite,ite_mul,Finset.sum_ite_irrel]
  have endKet (b : ι → ℂ) (A : Op ι) (a : ι) : sandwich b A (ket a) = ∑ y, star (b y)*A y a := by
    simp [sandwich,ket,mul_ite]
  rw [left,right,endKet,endKet,bra] at der
  have vanishL : (∑ y, star (dv y)*T 0 y r) = 0 := by simp only [zeroCol,mul_zero,Finset.sum_const_zero]
  have vanishR : (∑ y, T 0 l y * dw y) = 0 := by simp only [zeroRow,zero_mul,Finset.sum_const_zero]
  have mid : (∑ y, star (ket l y)*dT y r) = dT l r := by simp [ket,ite_mul,apply_ite]
  rw [vanishL,vanishR,mid,zero_add,add_zero] at der
  simpa only [dT,Matrix.sub_apply,Matrix.diagonal_apply] using der

/-- The disconnected subtraction has zero slope when both probes are
transverse. This holds also for the constant spatial harmonic. -/
theorem connected_response {f g h : ℝ → ℂ} {u v w : ℂ}
    (df : HasDerivAt f u 0) (dg : HasDerivAt g v 0) (dh : HasDerivAt h w 0)
    (g0 : g 0 = 0) (h0 : h 0 = 0) :
    HasDerivAt (fun t => f t - g t*h t) u 0 := by
  simpa [g0,h0] using df.sub (dg.mul dh)

end DSFTomography.SF
