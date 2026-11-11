import DSFTomography.SFPaper

/-! Equality of the Fourier extraction used on the spectra and the average
over ordered local probes used to differentiate the readout. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
private theorem avg_shifted (f : S → ℂ) (d : S) : avg (fun r => f (r+d)) = avg f := by
  unfold avg
  exact congrArg (· / (Fintype.card S:ℂ)) (Equiv.sum_comp (Equiv.addRight d) f)

/-- Translation-averaged centered and connected static functions in the
cyclic transverse chart. The static exchange-of-endpoints identity is
needed only on distinct sites, where local probes commute. -/
theorem localReadout_eq_paper (R : Bonds S) (B : ℝ) (A : Axis → Data S)
    (c : Axis → S → S → ℂ) (s : Axis → S → S → Axis → Axis → ℂ)
    (center : ∀ i d, (A i).first d (i+1) (i+1) - 2*(B:ℂ)*(A i).static d (i+1) (i+1) =
      avg fun r => c i r (r+d))
    (stat : ∀ i d a b, (A i).static d (axisInLab i a) (axisInLab i b) = avg fun r => s i r (r+d) a b)
    (swap : ∀ i r t, r ≠ t → ∀ a b, s i r t a b = s i t r b a) :
    paperHarmonics Subtype.val B A = localReadout R c (fun i r t a b => (B:ℂ)*s i r t a b) := by
  have rev (f : S → S → ℂ) (d : S) : avg (fun r => f r (r+ -d)) = avg (fun r => f (r+d) r) := by
    simpa only [add_neg_cancel_right] using (avg_shifted (fun r => f r (r + -d)) d).symm
  have revS (i : Axis) (d : R.dirs) (a b : Axis) :
      avg (fun r => s i r (r + -d.val) a b) = avg (fun r => s i r (r+d.val) b a) := by
    apply (rev (fun r t => s i r t a b) d).trans
    apply congrArg avg; funext r
    exact swap i _ _ (by simpa using R.nonzero _ d.property) a b
  have scaled (f : S → ℂ) : avg (fun r => (B:ℂ)*f r) = (B:ℂ)*avg f := by
    simp [avg,← Finset.mul_sum,mul_div_assoc]
  apply Prod.ext
  · funext i; simp [paperHarmonics,localReadout,center]
  · funext d i k
    have st00 := stat i d.val 0 0
    have st11 := stat i d.val 1 1
    have st01 := stat i d.val 0 1
    have sm00 := (stat i (-d.val) 0 0).trans (revS i d 0 0)
    have sm11 := (stat i (-d.val) 1 1).trans (revS i d 1 1)
    have sm01 := (stat i (-d.val) 0 1).trans (revS i d 0 1)
    simp only [axisInLab,Matrix.cons_val_zero,Matrix.cons_val_one] at st00 st11 st01 sm00 sm11 sm01
    fin_cases k <;>
      simp [paperHarmonics,localReadout,cosAmp,sinAmp,center,st00,st11,st01,sm00,sm11,sm01,
        rev,scaled,Complex.mul_re] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Direct Lehmann formula in an orthonormal energy basis, with Hermitian
probes, written as a centered matrix element on the probe-applied kets. -/
theorem centered_lehmann (m : ι) (E : ι → ℂ) (B : ℝ) (L R : Op ι) (herm : L.IsHermitian) :
    m₁ (fun j => if j=m then 1 else 0) E L R -
      2*(B:ℂ)*m₀ (fun j => if j=m then 1 else 0) L R =
    sandwich (fun j => L j m) (Matrix.diagonal (fun j => E j-E m-2*(B:ℂ))) (fun j => R j m) := by
  have left (x : ι) : star (L x m) = L m x := congrFun (congrFun herm m) x
  simp only [m₁,m₀,sandwich,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,left,
    Matrix.diagonal_apply,mul_ite,ite_mul,mul_zero,Finset.sum_ite_eq]
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end DSFTomography.SF
