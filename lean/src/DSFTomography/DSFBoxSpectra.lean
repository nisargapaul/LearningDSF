import DSFTomography.DSFInfiniteBounds

/-! Translation-averaged local spectra are the displacement harmonics of the
measured DSF. Averaging also accommodates stationary states in degenerate
energy sectors without assuming a translation-invariant eigenvector. -/
noncomputable section
namespace DSFTomography.Spectral
open DSFTomography HT HT.LocalWord SF Matrix

variable {Q I : Type*} [Fintype Q] [Nonempty Q] [Fintype I]
def averageLines (L : Q → Lines I) : Lines (Q × I) where
  frequency ri := (L ri.1).frequency ri.2
  weight ri := (L ri.1).weight ri.2/(Fintype.card Q:ℂ)

theorem average_absMoment (L : Q → Lines I) (k : ℕ) :
    (averageLines L).absMoment k = (∑ r, (L r).absMoment k)/(Fintype.card Q:ℝ) := by
  simp only [Lines.absMoment,averageLines,Fintype.sum_prod_type,norm_div,Complex.norm_natCast,
    div_mul_eq_mul_div,Finset.sum_div]

theorem average_absMoment_bound (L : Q → Lines I) (k : ℕ) (M : ℝ)
    (bound : ∀ r, (L r).absMoment k ≤ M) : (averageLines L).absMoment k ≤ M := by
  rw [average_absMoment]
  have pos : (0:ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ pos).mpr
  simpa [mul_comm] using Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => bound r)

theorem average_moment (L : Q → Lines I) (k : ℕ) :
    (averageLines L).moment k = avg (fun r => (L r).moment k) := by
  simp only [Lines.moment,averageLines,Fintype.sum_prod_type,avg,div_mul_eq_mul_div,
    ← Finset.sum_div,Finset.mul_sum]
  simp only [← Finset.mul_sum]
  ring

variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
def siteLift (n : ℕ) (r : Box R n) : Site ν := fun i => (r i).val

theorem place_siteLift (n : ℕ) (r : Box R n) : place R n (siteLift R n r) = r := by
  ext i
  simp [place,siteLift,periodicSite,reduceBond]

theorem place_add (n : ℕ) (x y : Site ν) : place R n (x+y) = place R n x+place R n y := by
  ext i; simp [place,periodicSite,reduceBond]

def boxLines (p : ∀ n, Config (Box R n) → ℝ) (n : ℕ) (d : Site ν) (a b : Axis) :=
  averageLines fun r : Box R n =>
    localLines R h J p n (siteLift R n r,a) (siteLift R n r+d,b)

theorem box_absMoment_bound (p : ∀ n, Config (Box R n) → ℝ)
    (positive : ∀ n i, 0 ≤ p n i) (normed : ∀ n, ∑ i, p n i=1)
    (n : ℕ) (d : Site ν) (a b : Axis) (k : ℕ) :
    (boxLines R h J p n d a b).absMoment k ≤ momentBound R h J k :=
  average_absMoment_bound _ _ _ fun r => local_absMoment_bound R h J p positive normed n _ _ k

theorem box_zeroth (p : ∀ n, Config (Box R n) → ℝ) (n : ℕ) (d : Site ν) (a b : Axis) :
    (boxLines R h J p n d a b).moment 0 = (2*Real.pi:ℂ)*
      (FD.mixtureData (periodicVolume R h J n) (p n)).static (place R n d) a b := by
  rw [boxLines,average_moment]
  simp only [localLines,zeroth_moment,eval_cons,eval_nil,mul_one,place_siteLift,place_add]
  simp only [FD.mixtureData,measured,qubitSpins,string]
  simp only [avg,← Finset.mul_sum]
  ring

theorem box_first (p : ∀ n, Config (Box R n) → ℝ) (n : ℕ) (d : Site ν) (a b : Axis) :
    (boxLines R h J p n d a b).moment 1 = (2*Real.pi:ℂ)*
      (FD.mixtureData (periodicVolume R h J n) (p n)).first (place R n d) a b := by
  rw [boxLines,average_moment]
  simp only [localLines,first_moment,eval_cons,eval_nil,mul_one,place_siteLift,place_add]
  simp only [FD.mixtureData,measured,qubitSpins,string]
  simp only [avg,← Finset.mul_sum]
  ring

def gibbsPop (β : ℝ) (n : ℕ) := FD.Accuracy.population (periodicVolume R h J n) β

theorem gibbsPop_positive (β : ℝ) : ∀ n i, 0 ≤ gibbsPop R h J β n i :=
  fun n => FD.Accuracy.population_pos (periodicVolume R h J n) β

theorem gibbsPop_normalized (β : ℝ) : ∀ n, ∑ i, gibbsPop R h J β n i = 1 :=
  fun n => FD.Accuracy.population_sum (periodicVolume R h J n) β

def channelIndex : Channel (Site ν) → Site ν × Axis × Axis
  | .bond d a b => (d,a,b)
  | .onsite k => (0,k+1,k+2)

theorem box_static_channel (β : ℝ) (n : ℕ) (c : Channel (Site ν)) :
    (boxLines R h J (gibbsPop R h J β) n (channelIndex c).1
      (channelIndex c).2.1 (channelIndex c).2.2).moment 0 = (2*Real.pi:ℂ)*
        (periodicVolume R h J n).observable (periodicChannel R c n) β := by
  have zero : place R n 0 = 0 := by ext i; simp [place,periodicSite,reduceBond]
  cases c <;> simp only [channelIndex,box_zeroth,periodicChannel,Volume.observable,
    staticHarmonic,gibbsStaticDSF,momentumMoments,harmonic_toMomentum,zero]
  all_goals rfl

theorem average_correlation (L : Q → Lines I) (t : ℝ) :
    (averageLines L).correlation t = avg (fun r => (L r).correlation t) := by
  simp only [Lines.correlation,averageLines,Fintype.sum_prod_type,avg,div_mul_eq_mul_div,Finset.sum_div]

theorem box_time_gibbs (β : ℝ) (n : ℕ) (d : Site ν) (a b : Axis) (t : ℝ) :
    (boxLines R h J (gibbsPop R h J β) n d a b).correlation t =
      avg (fun r : Box R n => physicalCorrelation (periodicVolume R h J n) β t
        (word (oneLabel r a)) (word (oneLabel (r+place R n d) b))) := by
  rw [boxLines,average_correlation]
  apply congrArg avg; funext r
  simp only [localLines,← timeCorrelation_eq,physicalCorrelation_eq,eval_cons,eval_nil,mul_one,
    place_siteLift,place_add]
  rfl

/-- Identification with every diagonal moment used in the volume-first HT proof. -/
theorem box_diagonal_moment (β : ℝ) (n : ℕ) (d : Site ν) (a : Axis) (k : ℕ) :
    (boxLines R h J (gibbsPop R h J β) n d a a).moment k = (2*Real.pi:ℂ)*
      HT.Diagonal.Bulk.moment (periodicVolume R h J n) k (place R n d) a β := by
  rw [boxLines,average_moment]
  simp only [localLines,Lines.moment,lehmann,Fintype.sum_prod_type,eval_cons,eval_nil,mul_one,
    place_siteLift,place_add,HT.Diagonal.Bulk.moment,harmonic_toMomentum,qubitSpins,string]
  have weights (i : Config (Box R n)) :
      (gibbsPop R h J β n i:ℂ) = gibbs β (energies (periodicBonds R n)
        (periodicVolume R h J n).h (periodicVolume R h J n).J) i := rfl
  simp only [weights,Complex.ofReal_sub,avg,← Finset.mul_sum]
  rw [← mul_div_assoc]
  congr 2
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  dsimp [periodicVolume]
  ring

end DSFTomography.Spectral
