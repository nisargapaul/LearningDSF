import DSFTomography.DSFRecovery
import DSFTomography.HTLocalKMS
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform spectral bounds for local probes. These control the high-frequency
tails needed to identify moments of a thermodynamic spectral distribution. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord SF Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowNorm (A : Op ι) (i : ι) : ℝ := ‖WithLp.toLp 2 (fun j => A i j)‖
def colNorm (A : Op ι) (i : ι) : ℝ := ‖WithLp.toLp 2 (fun j => A j i)‖
theorem rowNorm_sq (A : Op ι) (i : ι) : (rowNorm A i)^2 = ∑ j, ‖A i j‖^2 := by
  simp [rowNorm,PiLp.norm_sq_eq_of_L2]
theorem colNorm_sq (A : Op ι) (i : ι) : (colNorm A i)^2 = ∑ j, ‖A j i‖^2 := by
  simp [colNorm,PiLp.norm_sq_eq_of_L2]
theorem rowNorm_unit (A : Op ι) (unit : A*A.conjTranspose=1) (i : ι) : rowNorm A i = 1 := by
  have eq := congrArg (fun X : Op ι => (X i i).re) unit
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Matrix.one_apply_eq] at eq
  have sq : ∑ j, ‖A i j‖^2 = 1 := by
    simpa only [Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.one_re,Complex.sq_norm] using eq
  have nonneg : 0 ≤ rowNorm A i := norm_nonneg _
  rw [← rowNorm_sq] at sq
  nlinarith

theorem colNorm_unit (A : Op ι) (unit : A.conjTranspose*A=1) (i : ι) : colNorm A i = 1 := by
  have eq := rowNorm_unit A.conjTranspose (by simpa using unit) i
  simpa [rowNorm,colNorm,PiLp.norm_eq_of_L2,Matrix.conjTranspose_apply] using eq

/-- Absolute spectral moments omit the raw factor 2π. -/
def Lines.absMoment {I : Type*} [Fintype I] (L : Lines I) (k : ℕ) : ℝ :=
  ∑ i, ‖L.weight i‖*|L.frequency i|^k

theorem lehmann_absMoment_bound (p : ι → ℝ) (positive : ∀ i, 0 ≤ p i)
    (normed : ∑ i, p i = 1) (E : ι → ℝ) (A B D : Op ι) (k : ℕ) (M : ℝ)
    (entries : ∀ i j, D i j = ((E j-E i:ℝ):ℂ)^k*A i j)
    (rows : ∀ i, rowNorm D i ≤ M) (cols : ∀ i, colNorm B i ≤ 1) :
    (lehmann (fun i => (p i:ℂ)) E A B).absMoment k ≤ M := by
  have each (i : ι) : (∑ j, |E j-E i|^k*‖A i j‖*‖B j i‖) ≤ M := by
    have bound := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖D i j‖) (fun j => ‖B j i‖)
    rw [← rowNorm_sq,← colNorm_sq] at bound
    have sn : 0 ≤ ∑ j, ‖D i j‖*‖B j i‖ := Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have rn : 0 ≤ rowNorm D i := norm_nonneg _
    have cn : 0 ≤ colNorm B i := norm_nonneg _
    have le : (∑ j, ‖D i j‖*‖B j i‖) ≤ rowNorm D i*colNorm B i := by
      apply (sq_le_sq₀ sn (mul_nonneg rn cn)).mp
      simpa only [mul_pow] using bound
    have eq : ∀ j, ‖D i j‖ = |E j-E i|^k*‖A i j‖ := by
      intro j; rw [entries,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    simp_rw [eq] at le
    exact le.trans ((mul_le_of_le_one_right rn (cols i)).trans (rows i))
  simp only [Lines.absMoment,lehmann,Fintype.sum_prod_type,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (positive _)]
  have eq (i j : ι) : p i*‖A i j‖*‖B j i‖*|E j-E i|^k = p i*(|E j-E i|^k*‖A i j‖*‖B j i‖) := by ring
  simp_rw [eq,← Finset.mul_sum]
  calc
    _ ≤ ∑ i, p i*M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (each i) (positive i)
    _ = M := by rw [← Finset.sum_mul,normed,one_mul]

def rowLinear (i : ι) : Op ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun A := WithLp.toLp 2 (fun j => A i j)
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
theorem energy_star (V : Volume S) (A : Op (Config S)) :
    inBasis (energyBasis V.R V.h V.J) A.conjTranspose =
      (inBasis (energyBasis V.R V.h V.J) A).conjTranspose := by
  let U := (qubitH_hermitian V.R V.h V.J).eigenvectorUnitary
  change (U:Op (Config S)).conjTranspose*A.conjTranspose*(U:Op (Config S)) =
    ((U:Op (Config S)).conjTranspose*A*(U:Op (Config S))).conjTranspose
  simp [Matrix.mul_assoc]

theorem energy_word_unit (V : Volume S) (w : S → Letter) :
    inBasis (energyBasis V.R V.h V.J) (word w) *
      (inBasis (energyBasis V.R V.h V.J) (word w)).conjTranspose = 1 := by
  rw [← energy_star,word_hermitian,inBasis_mul]
  have unit := word_unit w
  rw [word_hermitian] at unit
  rw [unit]; simp [inBasis]

theorem iterated_energy_entry (V : Volume S) (A : Op (Config S)) (k : ℕ) (i j : Config S) :
    inBasis (energyBasis V.R V.h V.J) ((ad (qubitH V.R V.h V.J)^k) A) i j =
      ((energies V.R V.h V.J j-energies V.R V.h V.J i:ℝ):ℂ)^k *
        inBasis (energyBasis V.R V.h V.J) A i j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have diag := (rotate_H V.R V.h V.J (energyBasis V.R V.h V.J)).symm.trans (diagonalized V.R V.h V.J)
    rw [pow_succ',Module.End.mul_apply]
    let X := (ad (qubitH V.R V.h V.J)^k) A
    change inBasis _ (X*qubitH V.R V.h V.J-qubitH V.R V.h V.J*X) i j = _
    rw [show ∀ U : (Op (Config S))ˣ, ∀ X Y, inBasis U (X-Y)=inBasis U X-inBasis U Y by
      intros; simp [inBasis,Matrix.mul_sub,Matrix.sub_mul]]
    simp only [← inBasis_mul,diag,Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,X,ih,Complex.ofReal_sub]
    ring

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

def localLines (p : ∀ n, Config (Box R n) → ℝ) (n : ℕ) (x y : Atom (Site ν)) :=
  let V := periodicVolume R h J n
  lehmann (fun i => (p n i:ℂ)) (energies V.R V.h V.J)
    (inBasis (energyBasis V.R V.h V.J) (eval (place R n) [x]))
    (inBasis (energyBasis V.R V.h V.J) (eval (place R n) [y]))

def momentBound (k : ℕ) : ℝ := (4*incidentBound R h J)^k*k.factorial

theorem local_absMoment_bound (p : ∀ n, Config (Box R n) → ℝ)
    (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (n : ℕ) (x y : Atom (Site ν)) (k : ℕ) :
    (localLines R h J p n x y).absMoment k ≤ momentBound R h J k := by
  let V := periodicVolume R h J n
  let U := energyBasis V.R V.h V.J
  let D := inBasis U ((ad (qubitH V.R V.h V.J)^k) (eval (place R n) [x]))
  apply lehmann_absMoment_bound _ (positive n) (normed n) _ _ _ D k _
    (iterated_energy_entry V _ k)
  · intro i
    let L : Op (Config (Box R n)) →ₗ[ℂ] EuclideanSpace ℂ (Config (Box R n)) :=
      (rowLinear i).comp ({
        toFun := inBasis U
        map_add' := by intros; simp [inBasis,Matrix.mul_add,Matrix.add_mul]
        map_smul' := by intros; simp [inBasis] } : Op (Config (Box R n)) →ₗ[ℂ] Op (Config (Box R n)))
    have eq := Form.map_apply L (terms R h J x k) (eval (place R n))
    rw [terms_eval,boxInteraction_matrix] at eq
    have bound : ∀ w ∈ terms R h J x k, ‖L (eval (place R n) w.2)‖ ≤ 1 := by
      intro w _
      change rowNorm (inBasis U (eval (place R n) w.2)) i ≤ 1
      rw [normal]
      have smul (c : ℂ) (A : Op (Config (Box R n))) :
          rowNorm (inBasis U (c • A)) i = ‖c‖*rowNorm (inBasis U A) i := by
        change ‖L (c • A)‖ = _
        rw [map_smul,norm_smul]; rfl
      rw [smul,scalar_norm,one_mul,rowNorm_unit _ (energy_word_unit V _)]
    have cap := Form.norm_apply_le (terms R h J x k) (fun w => L (eval (place R n) w)) bound
    rw [← eq,mul_one] at cap
    exact cap.trans (terms_mass R h J x k)
  · intro i
    have eq : eval (place R n) [y] = word (oneLabel (place R n y.1) y.2) := by simp
    rw [eq]
    have unit := energy_word_unit V (oneLabel (place R n y.1) y.2)
    have herm : (inBasis U (word (oneLabel (place R n y.1) y.2))).conjTranspose =
        inBasis U (word (oneLabel (place R n y.1) y.2)) := by rw [← energy_star,word_hermitian]
    rw [herm] at unit
    exact (colNorm_unit _ (by rw [herm]; exact unit) i).le

theorem Lines.moment_bound {T : Type*} [Fintype T] (L : Lines T) (k : ℕ) :
    ‖L.moment k‖ ≤ (2*Real.pi)*L.absMoment k := by
  rw [Lines.moment,norm_mul,show ‖(2*Real.pi:ℂ)‖=2*Real.pi by norm_cast; rw [Real.norm_eq_abs,abs_of_pos (by positivity)]]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Lines.absMoment,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] using
    norm_sum_le Finset.univ (fun i => L.weight i*(L.frequency i:ℂ)^k)

end DSFTomography.Spectral
