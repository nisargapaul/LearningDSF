import DSFTomography.HTSpectrum

/-! Second Lehmann moments of the diagonal DSF. The signed populations below
are algebraic weights for evaluating traces, never additional measurements. -/
noncomputable section
namespace DSFTomography.HT.Diagonal
open DSFTomography HT
variable {ι : Type*} [Fintype ι]

def second (w E : ι → ℂ) (A B : Op ι) : ℂ :=
  ∑ i, ∑ j, (w i * (E j - E i)^2) * (A i j * B j i)

private theorem signedFirst (w E : ι → ℂ) (A B : Op ι) :
    m₁ w E A B + m₁ w E B A =
      ∑ i, ∑ j, ((w i - w j)*(E j-E i)) * (A i j * B j i) := by
  unfold m₁
  simp_rw [Finset.mul_sum]
  conv_lhs => rhs; rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem second_zero (c : ℂ) (E : ι → ℂ) (A B : Op ι) :
    second (fun _ => c) E A B =
      m₁ (fun i => -c * E i) E A B + m₁ (fun i => -c * E i) E B A := by
  rw [signedFirst]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem second_slope_symm (c : ℂ) (E : ι → ℂ) (A B : Op ι) :
    (second (fun i => -c * E i) E A B + second (fun i => -c * E i) E B A)/2 =
      m₁ (fun i => c * E i^2/2) E A B + m₁ (fun i => c * E i^2/2) E B A := by
  rw [signedFirst]
  unfold second
  conv_lhs => lhs; rhs; rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib,Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem second_swap (w E : ι → ℝ) (A B : Op ι) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (second (fun i => (w i : ℂ)) (fun i => (E i : ℂ)) B A).re =
    (second (fun i => (w i : ℂ)) (fun i => (E i : ℂ)) A B).re := by
  unfold second
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have h₁ : star (A i j) = A j i := congrFun (congrFun hA j) i
  have h₂ : star (B j i) = B i j := congrFun (congrFun hB i) j
  rw [← h₁, ← h₂]
  have weight : (w i : ℂ) * ((E j : ℂ) - E i)^2 = ((w i * (E j-E i)^2 : ℝ) : ℂ) := by push_cast; rfl
  simp only [weight,Complex.re_ofReal_mul]
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

/-- At β=0 the ordered second moment itself is real for Hermitian probes. -/
theorem second_uniform_real (c : ℝ) (E : ι → ℝ) (A B : Op ι)
    (ha : A.IsHermitian) (hb : B.IsHermitian) :
    (second (fun _ => (c:ℂ)) (fun i => (E i : ℂ)) A B).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold second
  simp only [map_sum,map_mul,map_pow,map_sub,Complex.conj_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have h₁ : star (A j i) = A i j := congrFun (congrFun ha i) j
  have h₂ : star (B i j) = B j i := congrFun (congrFun hb j) i
  simp only [Complex.star_def] at h₁ h₂
  rw [h₁,h₂]; ring

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] [DecidableEq ι]
def localSecond (P : Spins S ι) (w E : ι → ℂ) (d : S) (a : Axis) :=
  avg fun r => second w E (P.σ r a) (P.σ (r+d) a)

def scan (P : Spins S ι) (E : ι → ℝ) (β : ℝ) (q : Momentum S) (a : Axis) :=
  toMomentum (fun d => localSecond P (gibbs β E) (fun i => (E i : ℂ)) d a) q

def coeff₂ (P : Spins S ι) (E : ι → ℝ) (d : S) (a : Axis) (β : ℝ) :=
  harmonic (fun q => scan P E β q a) d

theorem coeff₂_eq (P : Spins S ι) (E : ι → ℝ) (d : S) (a : Axis) (β : ℝ) :
    coeff₂ P E d a β = localSecond P (gibbs β E) (fun i => (E i : ℂ)) d a :=
  harmonic_toMomentum _ _

omit [DecidableEq S] in
private theorem avg_reverse (f : S → S → ℂ) (d : S) :
    avg (fun r => f (r+d) r) = avg (fun r => f r (r + -d)) := by
  unfold avg
  exact congrArg (· / (Fintype.card S:ℂ)) (by
    have eq := Equiv.sum_comp (Equiv.addRight d) (fun r => f r (r + -d))
    change (∑ r, f (r+d) ((r+d) + -d)) = _ at eq
    simpa only [add_neg_cancel_right] using eq)

theorem avg_pair (P : Spins S ι) (w E : ι → ℂ) (d : S) (a : Axis) :
    avg (fun r => m₁ w E (P.σ r a) (P.σ (r+d) a) + m₁ w E (P.σ (r+d) a) (P.σ r a)) =
      (measured P w E).force d a a := by
  change _ = avg _ + avg _
  rw [← avg_reverse (fun r s => m₁ w E (P.σ r a) (P.σ s a)) d]
  simp [avg,Finset.sum_add_distrib,add_div]

theorem coeff₂_zero (P : Spins S ι) (E : ι → ℝ) (d : S) (a : Axis) :
    coeff₂ P E d a 0 = (measured P (fun i => -(Fintype.card ι : ℂ)⁻¹ * E i)
      (fun i => (E i : ℂ))).force d a a := by
  rw [coeff₂_eq, localSecond]
  have pop : gibbs 0 E = fun _ => (Fintype.card ι : ℂ)⁻¹ := by ext; simp [gibbs]
  rw [pop]
  simp_rw [second_zero]
  exact avg_pair _ _ _ _ _

theorem coeff₂_deriv [Nonempty ι] (P : Spins S ι) (E : ι → ℝ) (hE : ∑ i, E i = 0)
    (d : S) (a : Axis) :
    HasDerivAt (coeff₂ P E d a)
      (localSecond P (fun i => -(Fintype.card ι : ℂ)⁻¹ * E i) (fun i => (E i : ℂ)) d a) 0 := by
  simp only [funext (coeff₂_eq P E d a),localSecond,avg,second]
  apply HasDerivAt.div_const
  repeat' (apply HasDerivAt.fun_sum; intro _ _)
  apply HasDerivAt.mul_const
  apply HasDerivAt.mul_const
  simpa [div_eq_mul_inv,mul_comm] using gibbs_slope E hE _

theorem coeff₂_slope [Nonempty ι] (P : Spins S ι) (E : ι → ℝ) (hE : ∑ i, E i = 0)
    (herm : ∀ r a, (P.σ r a).IsHermitian) (d : S) (a : Axis) :
    (derivWithin (coeff₂ P E d a) (Set.Ici 0) 0).re =
      ((measured P (fun i => (Fintype.card ι : ℂ)⁻¹ * (E i : ℂ)^2/2)
        (fun i => (E i : ℂ))).force d a a).re := by
  rw [(coeff₂_deriv P E hE d a).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0),
    ← avg_pair,localSecond]
  simp_rw [← second_slope_symm]
  have point (r : S) := second_swap (fun i => -(Fintype.card ι : ℝ)⁻¹ * E i) E
    _ _ (herm r a) (herm (r+d) a)
  push_cast at point
  have avg_re (f : S → ℂ) : (avg f).re = (∑ r, (f r).re)/(Fintype.card S : ℝ) := by
    simp [avg,← Complex.ofReal_natCast,Complex.div_ofReal_re]
  rw [avg_re,avg_re]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [show (2:ℂ) = ((2:ℝ):ℂ) from rfl,Complex.div_ofReal_re,Complex.add_re,point]
  ring
end DSFTomography.HT.Diagonal
