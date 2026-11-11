import DSFTomography.HTBulkMoments

/-! Match the physical displacement labels to the labels in each periodic box.
The coordinate change is the same permutation for parameters and features. -/
noncomputable section
namespace DSFTomography.HT.Diagonal.Bulk
open DSFTomography HT LocalWord
variable {ν : ℕ} (R : Bonds (Site ν))

def bondEquiv (n : ℕ) : R.dirs ≃ (periodicBonds R n).dirs :=
  Equiv.ofBijective (fun d => ⟨place R n d,Finset.mem_image_of_mem _ d.property⟩) (by
    constructor
    · intro d e h; exact Subtype.ext (injects_dirs R n d.property e.property (congrArg Subtype.val h))
    · intro e
      obtain ⟨d,hd,hh⟩ := Finset.mem_image.mp e.property
      exact ⟨⟨d,hd⟩,Subtype.ext hh⟩)

def indexEquiv (n : ℕ) : Index R ≃ Index (periodicBonds R n) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (bondEquiv R n) (Equiv.refl _))

def coordinates (n : ℕ) : Params R ≃L[ℝ] Params (periodicBonds R n) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ => ℝ) (indexEquiv R n)).toContinuousLinearEquiv

theorem coord_apply (n : ℕ) (p : Params R) (i : Index R) :
    coordinates R n p (indexEquiv R n i) = p i := by
  change p ((indexEquiv R n).symm ((indexEquiv R n) i)) = _
  rw [Equiv.symm_apply_apply]

private theorem field_eq (n : ℕ) (p : Params R) :
    fields (periodicBonds R n) (coordinates R n p) = fields R p :=
  funext fun a => coord_apply R n p (.inl a)

private theorem exchange_eq (n : ℕ) (p : Params R) :
    exch (periodicBonds R n) (coordinates R n p) = (periodicVolume R (fields R p) (exch R p) n).J := by
  funext d a b
  by_cases hd : d ∈ (periodicBonds R n).dirs
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    rw [image_coupling R _ _ n he]
    simp only [exch,dif_pos hd,dif_pos he]
    exact coord_apply R n p (.inr (⟨e,he⟩,a,b))
  · simp only [exch,dif_neg hd,periodicVolume]
    have none (e : Site ν) (he : e ∈ R.dirs) : reduceBond (periodIndex R n) e ≠ d := by
      intro eq; exact hd (Finset.mem_image.mpr ⟨e,he,eq⟩)
    rw [Finset.sum_eq_zero (fun e he => if_neg (none e he))]
    rfl

/-- Each coordinate specifies a frequency moment and either its intercept
or its right slope. The order within each bond is static slope, second
intercept, real second slope, as in the finite-volume readout. -/
structure Setting (S : Type*) where
  k : ℕ
  d : S
  a : Axis
  derivative : Bool

def setting : Index R → Setting (Site ν)
  | .inl a => ⟨2,0,a,false⟩
  | .inr (d,a,k) => ![⟨0,d,a,true⟩,⟨2,d,a,false⟩,⟨2,d,a,true⟩] k

def extract (s : Setting (Site ν)) (f : ℝ → ℂ) : ℝ :=
  if s.derivative then (derivWithin f (Set.Ici 0) 0).re else (f 0).re

def finiteCurve (n : ℕ) (p : Params R) (i : Index R) : ℝ → ℂ :=
  let s := setting R i
  moment (periodicVolume R (fields R p) (exch R p) n) s.k (place R n s.d) s.a

def finiteFeatures (n : ℕ) (p : Params R) : Params R := fun i =>
  extract (setting R i) (finiteCurve R n p i)

theorem box_features (n : ℕ) : finiteFeatures R n =
    (coordinates R n).symm ∘ paperFeatures (periodicBonds R n) ∘ coordinates R n := by
  funext p i
  have back (q : Params (periodicBonds R n)) : (coordinates R n).symm q i = q (indexEquiv R n i) := by
    simpa using (coord_apply R n ((coordinates R n).symm q) i).symm
  simp only [Function.comp_apply,back]
  let V := periodicVolume R (fields R p) (exch R p) n
  let P := qubitSpins (energyBasis V.R V.h V.J)
  let E := energies V.R V.h V.J
  have static (d a) : staticHarmonic (gibbsStaticDSF V.R V.h V.J) d a a = moment V 0 d a := static_moment V d a
  have second (d a) : coeff₂ P E d a = moment V 2 d a := second_moment V d a
  have data : gibbsData (periodicBonds R n) (coordinates R n p) =
     ⟨fun β q a => gibbsStaticDSF V.R V.h V.J β q a a,scan P E⟩ := by
    unfold gibbsData; rw [field_eq,exchange_eq]; rfl
  simp only [paperFeatures,data]
  cases i with
  | inl a =>
    change (moment V 2 (place R n 0) a 0).re = (coeff₂ P E 0 a 0).re
    rw [second]; rfl
  | inr i =>
    obtain ⟨d,a,k⟩ := i
    rcases (show k=0 ∨ k=1 ∨ k=2 by fin_cases k <;> decide) with rfl|rfl|rfl
    · change (derivWithin (moment V 0 (place R n d) a) _ _).re =
        (derivWithin (staticHarmonic (gibbsStaticDSF V.R V.h V.J) _ _ _) _ _).re
      rw [static]; rfl
    · change (moment V 2 (place R n d) a 0).re = (coeff₂ P E _ a 0).re
      rw [second]; rfl
    · change (derivWithin (moment V 2 (place R n d) a) _ _).re =
        (derivWithin (coeff₂ P E _ a) _ _).re
      rw [second]; rfl

end DSFTomography.HT.Diagonal.Bulk
