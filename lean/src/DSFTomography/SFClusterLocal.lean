import DSFTomography.SFClusterGround
import DSFTomography.HTLocalWords

/-! Fixed spatial patterns in growing boxes. Coefficients of a local pattern,
the number of flips and the anchors touched by a local sign string all
stabilize once its finitely many physical addresses separate. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν))
abbrev Pattern (ν : ℕ) := List (Site ν)
def placed (n : ℕ) (A : Pattern ν) : Config (Box R n) := bitSum (A.map (periodicSite R n))
def localKet (A : Pattern ν) : Amplitudes R := localFlip R A (vacuumFamily R)

theorem localKet_at (A : Pattern ν) (n) : atBox R n (localKet R A) = basis (placed R n A) := by
  change flip _ (basis 0) = _; simp [placed]

theorem place_add (n) (s t : Site ν) : periodicSite R n (s+t) = periodicSite R n s + periodicSite R n t := by
  funext j; simp [periodicSite,reduceBond]
theorem place_sub (n) (s t : Site ν) : periodicSite R n (s-t) = periodicSite R n s - periodicSite R n t := by
  funext j; simp [periodicSite,reduceBond]

theorem placed_append (n) (A D : Pattern ν) : placed R n (A++D) = placed R n A+placed R n D := by
  simp [placed,bitSum]
private theorem bit_cons {S : Type*} [DecidableEq S] (r : S) (A : List S) (t : S) :
    bitSum (r::A) t = (if t=r then 1 else 0) + bitSum A t := rfl

private theorem bit_off {S : Type*} [DecidableEq S] (A : List S) {t} (ht : t∉A) : bitSum A t=0 := by
  induction A with
  | nil => rfl
  | cons r A ih => simp only [List.mem_cons,not_or] at ht; simp [bit_cons,ht.1,ih ht.2]

theorem placed_at (A : Pattern ν) (t : Site ν) :
    ∀ᶠ n in atTop, placed R n A (periodicSite R n t) = bitSum A t := by
  induction A with
  | nil => exact Eventually.of_forall fun _ => rfl
  | cons r A ih =>
    filter_upwards [ih,LocalWord.eventual_eq_test R t r] with n hv he
    simpa only [placed,List.map_cons,bit_cons,he] using congrArg ((if t=r then 1 else 0) + ·) hv

private theorem resolves (T : Finset (Site ν)) :
    ∀ᶠ n in atTop, Set.InjOn (periodicSite R n) (T : Set (Site ν)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_resolves T)
  exact (eventually_ge_atTop N).mono fun n hn => hN _ (hn.trans (Nat.le_add_left n _))

def weight (A : Pattern ν) := (A.toFinset.filter fun s => bitSum A s ≠ 0).card

theorem placed_count (A : Pattern ν) : ∀ᶠ n in atTop, flipCount (placed R n A) = weight A := by
  let U := A.toFinset.filter fun s => bitSum A s ≠ 0
  have all := (Finset.eventually_all (I := A.toFinset)).mpr (fun s _ => placed_at R A s)
  filter_upwards [resolves R A.toFinset,all] with n hinj hv
  have eq : (Finset.univ.filter fun t => placed R n A t ≠ 0) = U.image (periodicSite R n) := by
    ext t; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro ne
      have mem : t∈A.map (periodicSite R n) := by by_contra no; exact ne (bit_off _ no)
      obtain ⟨s,sm,rfl⟩ := List.mem_map.mp mem
      have m : s∈A.toFinset := by simpa using sm
      exact ⟨s,Finset.mem_filter.mpr ⟨m,hv s m ▸ ne⟩,rfl⟩
    · rintro ⟨s,hs,rfl⟩; obtain ⟨m,ne⟩ := Finset.mem_filter.mp hs; rwa [hv s m]
  rw [flipCount,eq,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]; rfl

theorem placed_translate (r : Site ν) (A : Pattern ν) (n) :
    translated (periodicSite R n r) (placed R n A) = placed R n (A.map (· + r)) := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    funext j; change placed R n (s::A) (j-periodicSite R n r) = _
    simp only [placed,List.map_cons,bit_cons,place_add,sub_eq_iff_eq_add]
    exact congrArg (_ + ·) (congrFun ih j)

theorem phase_placed (D A : Pattern ν) : ∀ᶠ n in atTop,
    phase (D.map (periodicSite R n)) (placed R n A) = phase D (bitSum A) := by
  induction D with
  | nil => exact Eventually.of_forall fun _ => rfl
  | cons t D ih =>
    filter_upwards [ih,placed_at R A t] with n hi hx
    simp only [List.map_cons,phase,List.prod_cons] at hi ⊢
    rw [hx,hi]

/-- Finite sums of fixed spin-flip patterns, allowing a finite prefix of
arbitrary boxes. We take their norm closure in the uniform ℓ¹ norm. -/
def raw : Submodule ℂ (Amplitudes R) := Submodule.span ℂ
  (Set.range (localKet R) ∪ {v | ∀ᶠ n in atTop, atBox R n v=0})
def localSpace := (raw R).topologicalClosure

theorem raw_pattern (A : Pattern ν) : localKet R A ∈ raw R :=
  Submodule.subset_span (Or.inl ⟨A,rfl⟩)
theorem raw_congr {x y : Amplitudes R} (eq : ∀ᶠ n in atTop, atBox R n x=atBox R n y) (hy : y ∈ raw R) :
    x ∈ raw R := by
  have d : x-y ∈ raw R := Submodule.subset_span (Or.inr (eq.mono fun n h => by simp [h]))
  simpa using (raw R).add_mem d hy

private def shifts (D A : Pattern ν) := (D.flatMap fun t => A.map (t-·)).toFinset

private theorem phase_trivial {S : Type*} [DecidableEq S] (D : List S) (x : Config S)
    (off : ∀ t ∈ D, x t=0) : phase D x=1 := by
  induction D with
  | nil => rfl
  | cons t D ih =>
    change (if x t=0 then (1:ℂ) else -1)*phase D x=1
    rw [if_pos (off t (by simp)),one_mul,ih (fun s hs => off s (by simp [hs]))]

/-- Outside the finite list of offsets d-a, the sign is trivial. Here all
addresses are periodized before comparing them. -/
private theorem off_shifts (D A : Pattern ν) (n) (t : Box R n)
    (notmem : t ∉ (shifts D A).image (periodicSite R n)) :
    phase (D.map (periodicSite R n)) (translated t (placed R n A)) = 1 := by
  apply phase_trivial
  rintro q hq; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
  change bitSum (A.map (periodicSite R n)) (periodicSite R n s - t) = 0
  apply bit_off; intro hit; obtain ⟨u,hu,eq⟩ := List.mem_map.mp hit
  apply notmem
  refine Finset.mem_image.mpr ⟨s-u,?_,?_⟩
  · simp only [shifts,List.mem_toFinset,List.mem_flatMap,List.mem_map]
    exact ⟨s,hs,u,hu,rfl⟩
  · rw [place_sub,eq]; abel

theorem response_local (D A : Pattern ν) : localResponse R D (localKet R A) ∈ raw R := by
  let T := shifts D A
  let w := fun r : Site ν => A.map (· + r)
  let b := fun r : Site ν => (phase D (bitSum (w r))-1) • localKet R (w r)
  let c := (2*(weight A:ℂ))⁻¹
  have h : ∀ᶠ n in atTop, atBox R n (localResponse R D (localKet R A)) = atBox R n (c • ∑ r ∈ T, b r) := by
    have all := (Finset.eventually_all (I := T)).mpr fun r _ => phase_placed R D (w r)
    filter_upwards [all,placed_count R A,resolves R T] with n hp hc hi
    change response _ (atBox R n (localKet R A)) = _
    rw [localKet_at,response,columns_basis,responseColumn,hc,map_smul,map_sum]
    apply congrArg (c • ·)
    let f := fun t : Box R n => (phase (D.map (periodicSite R n)) (translated t (placed R n A))-1) • basis (translated t (placed R n A))
    change ∑ t, f t = _
    rw [← Finset.sum_subset (Finset.subset_univ (T.image (periodicSite R n))) (fun t _ no => by simp [f,off_shifts R D A n t no]),
      Finset.sum_image hi]
    apply Finset.sum_congr rfl; intro r hr
    simp only [f,b,map_smul,localKet_at,placed_translate]
    rw [hp r hr]
  apply raw_congr R h
  exact (raw R).smul_mem _ ((raw R).sum_mem fun r _ => (raw R).smul_mem _ (raw_pattern R _))

/-- On two local basis configurations, the excited column only sums over
the same finite offset set (with opposite translations on the second word). -/
theorem excitation_local (D B A : Pattern ν) :
    localExcitation R D (localKet R B) (localKet R A) ∈ raw R := by
  let T := shifts D A
  let w := fun r : Site ν => A.map (· + r)
  let out := fun r : Site ν => A ++ B.map (· + -r)
  let b := fun r : Site ν => (phase D (bitSum (w r))-1) • localKet R (out r)
  let c := (2*(weight A:ℂ))⁻¹
  have h : ∀ᶠ n in atTop, atBox R n (localExcitation R D (localKet R B) (localKet R A)) =
      atBox R n (c • ∑ r ∈ T, b r) := by
    have all := (Finset.eventually_all (I := T)).mpr fun r _ => phase_placed R D (w r)
    filter_upwards [all,placed_count R A,resolves R T] with n hp hc hi
    change excitation _ (atBox R n (localKet R B)) (atBox R n (localKet R A)) = _
    rw [localKet_at,localKet_at]
    change columns _ (basis (placed R n A)) = _
    rw [columns_basis,excitedColumn,hc,map_smul,map_sum]
    apply congrArg (c • ·)
    let f := fun t : Box R n => (phase (D.map (periodicSite R n)) (translated (-t) (placed R n A))-1) •
        flip (placed R n A) (translateAmp t (basis (placed R n B)))
    change ∑ t, f t = _
    rw [← Equiv.sum_comp (Equiv.neg (Box R n)) f]
    let g := fun t : Box R n => f (-t)
    change ∑ t, g t = _
    rw [← Finset.sum_subset (Finset.subset_univ (T.image (periodicSite R n))) (fun t _ no => by
      simp [g,f,off_shifts R D A n t no]),Finset.sum_image hi]
    apply Finset.sum_congr rfl; intro r hr
    have negp : -periodicSite R n r=periodicSite R n (-r) := by funext j; simp [periodicSite,reduceBond]
    simp only [g,f,neg_neg,translate_basis,negp,placed_translate,flip_basis,b,map_smul,localKet_at,placed_append,out]
    rw [hp r hr]
  exact raw_congr R h ((raw R).smul_mem _ ((raw R).sum_mem fun r _ => (raw R).smul_mem _ (raw_pattern R _)))

theorem convolution_local (B A : Pattern ν) : convolutionFamily R (localKet R B) (localKet R A) ∈ raw R := by
  apply raw_congr R (y := localKet R (B++A)) _ (raw_pattern R _)
  apply Eventually.of_forall; intro n
  change convolute (atBox R n (localKet R B)) (atBox R n (localKet R A)) = _
  rw [localKet_at,localKet_at,localKet_at,convolution_basis,flip_basis,placed_append]

private theorem raw_linear (L : Operators R)
    (pat : ∀ A, L (localKet R A) ∈ raw R)
    (null : ∀ x, (∀ᶠ n in atTop, atBox R n x=0) → ∀ᶠ n in atTop, atBox R n (L x)=0) :
    ∀ x ∈ raw R, L x ∈ raw R := by
  intro x hx
  apply Submodule.span_induction (p := fun v _ => L v ∈ raw R) _ _ _ _ hx
  · rintro v (⟨A,rfl⟩|h); exact pat A; exact Submodule.subset_span (Or.inr (null _ h))
  · simp
  · intro x y _ _ a b; simpa using (raw R).add_mem a b
  · intro c x _ h; simpa using (raw R).smul_mem c h

private theorem closed_lift (L : Operators R) (pres : ∀ x ∈ raw R, L x ∈ localSpace R) :
    ∀ x ∈ localSpace R, L x ∈ localSpace R := by
  intro x hx
  exact (closure_minimal pres ((raw R).isClosed_topologicalClosure.preimage L.continuous)) hx

theorem response_preserves (D : Pattern ν) : ∀ x ∈ localSpace R, localResponse R D x ∈ localSpace R := by
  apply closed_lift
  have fin := raw_linear R (localResponse R D) (response_local R D) (fun x h => h.mono fun n hn => by
    change response _ (atBox R n x) = 0; simp [hn])
  exact fun x hx => (raw R).le_topologicalClosure (fin x hx)

private theorem bilinear_preserves (L : Amplitudes R →L[ℂ] Operators R)
    (pat : ∀ A B, L (localKet R A) (localKet R B) ∈ raw R)
    (null : ∀ x y n, atBox R n x=0 ∨ atBox R n y=0 → atBox R n (L x y)=0) :
    ∀ x ∈ localSpace R, ∀ y ∈ localSpace R, L x y ∈ localSpace R := by
  have h₁ (A) := raw_linear R (L (localKet R A)) (pat A) fun x h => h.mono fun n hn => null _ _ n (Or.inr hn)
  have h₂ (y) (hy : y ∈ raw R) := raw_linear R (L.flip y) (fun A => h₁ A y hy) fun x h =>
    h.mono fun n hn => null _ _ n (Or.inl hn)
  intro x hx
  apply closed_lift; intro y hy
  exact closed_lift R (L.flip y) (fun z hz => (raw R).le_topologicalClosure (h₂ y hy z hz)) x hx

theorem convolution_preserves : ∀ x ∈ localSpace R, ∀ y ∈ localSpace R, convolutionFamily R x y ∈ localSpace R := bilinear_preserves R (convolutionFamily R) (convolution_local R)
  (fun x y n h => by change convolute (atBox R n x) (atBox R n y) = 0; rcases h with h|h <;> simp [h])
theorem excitation_preserves (D : Pattern ν) : ∀ x ∈ localSpace R, ∀ y ∈ localSpace R, localExcitation R D x y ∈ localSpace R := bilinear_preserves R (localExcitation R D) (excitation_local R D)
  (fun x y n h => by change excitation _ (atBox R n x) (atBox R n y) = 0; rcases h with h|h <;> simp [h])

theorem vacuum_local : vacuumFamily R ∈ localSpace R := by
  apply (raw R).le_topologicalClosure
  apply raw_congr R (y := localKet R []) _ (raw_pattern R _)
  exact Eventually.of_forall fun n => (localKet_at R [] n).symm

theorem flip_preserves (A : Pattern ν) (x) (hx : x ∈ localSpace R) : localFlip R A x ∈ localSpace R := by
  have eq : localFlip R A x = convolutionFamily R (localKet R A) x := by
    apply Subtype.ext; funext n
    change flip _ (x n) = convolute (atBox R n (localKet R A)) (x n)
    rw [localKet_at,convolution_basis]; rfl
  exact eq ▸ convolution_preserves R _ ((raw R).le_topologicalClosure (raw_pattern R A)) _ hx

end DSFTomography.SF.Cluster
