import DSFTomography.HTBulkMoments

/-! Exact stabilization at orders zero and one. Trace cyclicity and a local
Pauli involution replace the extensive Hamiltonian in a thermal slope by
the commutator of that involution with the Hamiltonian. -/
noncomputable section
namespace DSFTomography.HT.Diagonal.Bulk
open DSFTomography HT LocalWord Filter
open scoped Topology
variable {ν : ℕ} (R : Bonds (Site ν))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem flip_trace (U A : Op ι) (sq : U*U=1) (flip : U*A= -(A*U)) :
    A.trace = 0 := by
  have zero := Matrix.trace_mul_cycle U A U
  rw [sq,Matrix.one_mul,flip,Matrix.neg_mul,Matrix.mul_assoc,sq,Matrix.mul_one,Matrix.trace_neg] at zero
  linear_combination -(1/2:ℂ)*zero

private theorem flip_slope (U A K : Op ι) (sq : U*U=1) (flip : U*A= -(A*U)) :
    -normTrace (K*A) = normTrace (ad K U * (U*A)) / 2 := by
  have conj : (U*A)*U = -A := by rw [flip,neg_mul,Matrix.mul_assoc,sq,Matrix.mul_one]
  have cycle : (U*(K*(U*A))).trace = -(K*A).trace := by
    rw [Matrix.trace_mul_comm,Matrix.mul_assoc,conj,Matrix.mul_neg,Matrix.trace_neg]
  have op : (ad K U)*(U*A) = U*(K*(U*A))-K*A := by
    change (U*K-K*U)*(U*A) = _
    rw [Matrix.sub_mul,Matrix.mul_assoc,Matrix.mul_assoc K U,← Matrix.mul_assoc U U,sq,Matrix.one_mul]
  rw [op,normTrace,normTrace,Matrix.trace_sub,cycle]; ring

private theorem single_sq (n : ℕ) (x : Atom (Site ν)) :
    eval (place R n) [x] * eval (place R n) [x] = 1 := by
  simpa [string,inBasis] using string_square (1 : (Op (Config (Box R n)))ˣ) (place R n x.1) x.2

private theorem trace_stable (w : Script (Site ν)) :
    ∃ t : ℂ, ∀ᶠ n : ℕ in atTop, normTrace (eval (place R n) w) = t := by
  rcases classify R w with ⟨t,ht⟩|⟨x,hx⟩
  · refine ⟨t,ht.mono fun n hn => ?_⟩
    rw [hn]; simp [normTrace,Matrix.trace_smul,smul_eq_mul]
  · exact ⟨0,hx.mono fun n hn => by simp [normTrace,flip_trace _ _ (single_sq R n x) hn]⟩

private theorem apply_eq {T E : Type*} [AddCommMonoid E] [Module ℂ E] (u : Form T)
    {f g : Script T → E} (h : ∀ w ∈ u.map Prod.snd, f w=g w) : Form.apply u f = Form.apply u g := by
  induction u with
  | nil => rfl
  | cons p u ih =>
    simp only [Form.apply_cons,h p.2 (by simp)]
    rw [ih fun w hw => h w (by simp [hw])]

/-- Only the words in the commutator list depend on the lattice. The same
finite set works over the entire coupling domain. -/
theorem term_words (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ) (x : Atom (Site ν)) (k : ℕ) :
    (terms R h J x k).map Prod.snd = (terms R 0 0 x k).map Prod.snd := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have keys (u : Form (Site ν)) (v : Script (Site ν) → Form (Site ν)) :
        (Form.subst u v).map Prod.snd = (u.map Prod.snd).flatMap (fun w => (v w).map Prod.snd) := by
      simp [Form.subst,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    simp only [terms,keys,ih,step_words R h J]

variable (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)
def wordSlope (w : Script (Site ν)) (n : ℕ) :=
  -normTrace (qubitH (periodicBonds R n) h (periodicVolume R h J n).J * eval (place R n) w)

private theorem slope_as_local (n : ℕ) (w : Script (Site ν)) (x : Atom (Site ν))
    (flip : eval (place R n) [x]*eval (place R n) w = -(eval (place R n) w*eval (place R n) [x])) :
    wordSlope R h J w n = Form.apply (terms R h J x 1)
      (fun q => normTrace (eval (place R n) (q ++ (x::w)))) / 2 := by
  let f := place R n
  let A := eval f (x::w)
  let L : Op (Config (Box R n)) →ₗ[ℂ] ℂ :=
    (Fintype.card (Config (Box R n)) : ℂ)⁻¹ • (Volume.traceTest (1 : Op (Config (Box R n)))).comp
      (LinearMap.mulRight ℂ A)
  have act (T) : L T = normTrace (T*A) := by simp [L,Volume.traceTest,normTrace,div_eq_inv_mul]
  have eq := Form.map_apply L (terms R h J x 1) (eval f)
  simp only [act] at eq
  rw [wordSlope,flip_slope _ _ _ (single_sq R n x) flip]
  simp only [eval_append]
  rw [← eq]
  simp [A,f,terms_eval,boxInteraction_matrix]

private theorem word_jet_stable (w : Script (Site ν)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ),
      normTrace (eval (place R n) w) = normTrace (eval (place R m) w) ∧
      wordSlope R h J w n = wordSlope R h J w m := by
  obtain ⟨t,N,hN⟩ := (show ∃ t, ∃ N, ∀ n ≥ N, normTrace (eval (place R n) w) = t by
    obtain ⟨t,ht⟩ := trace_stable R w; exact ⟨t,eventually_atTop.mp ht⟩)
  rcases classify R w with ⟨c,hc⟩|⟨x,hx⟩
  · obtain ⟨M,hM⟩ := eventually_atTop.mp hc
    have vanish (n) (hn : M ≤ n) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ) :
        wordSlope R h J w n = 0 := by
      simp only [wordSlope,hM n hn,Matrix.mul_smul,Matrix.mul_one,normTrace,Matrix.trace_smul]
      have tr := H_traceless (qubitSpins (1 : (Op (Config (Box R n)))ˣ)) 1 (fun _ _ => rfl)
        (periodicBonds R n) (fun a => (h a : ℂ)) (fun d a b => ((periodicVolume R h J n).J d a b : ℂ))
      simp [qubitH,realH,tr]
    exact ⟨max N M,fun n hn m hm h J => ⟨(hN n (le_trans (le_max_left ..) hn)).trans
      (hN m (le_trans (le_max_left ..) hm)).symm, (vanish n (le_trans (le_max_right ..) hn) h J).trans
      (vanish m (le_trans (le_max_right ..) hm) h J).symm⟩⟩
  · classical
    choose c hc using fun q : Script (Site ν) => trace_stable R (q ++ (x::w))
    let keys := ((terms R 0 0 x 1).map Prod.snd).toFinset
    obtain ⟨M,hM⟩ := eventually_atTop.mp (hx.and (keys.eventually_all.mpr fun q _ => hc q))
    refine ⟨max N M,fun n hn m hm h J => ⟨(hN n (le_trans (le_max_left ..) hn)).trans
      (hN m (le_trans (le_max_left ..) hm)).symm,?_⟩⟩
    have nOK := hM n (le_trans (le_max_right ..) hn)
    have mOK := hM m (le_trans (le_max_right ..) hm)
    rw [slope_as_local R h J n w x nOK.1,slope_as_local R h J m w x mOK.1]
    congr 1
    apply apply_eq; intro q hq
    rw [term_words] at hq
    exact (nOK.2 q (List.mem_toFinset.mpr hq)).trans (mOK.2 q (List.mem_toFinset.mpr hq)).symm

def intercept (k : ℕ) (d : Site ν) (a : Axis) (n : ℕ) :=
  Form.apply (form R h J k d a) (fun w => normTrace (eval (place R n) w))
def slope (k : ℕ) (d : Site ν) (a : Axis) (n : ℕ) :=
  Form.apply (form R h J k d a) (fun w => wordSlope R h J w n)

theorem moment_jet_stable (k : ℕ) (d : Site ν) (a : Axis) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ),
      intercept R h J k d a n = intercept R h J k d a m ∧ slope R h J k d a n = slope R h J k d a m := by
  classical
  choose N hN using word_jet_stable R
  let keys := ((form R 0 0 k d a).map Prod.snd).toFinset
  refine ⟨keys.sup N,fun n hn m hm h J => ?_⟩
  have atWord (w) (hw : w ∈ (form R h J k d a).map Prod.snd) := by
    have e : (form R h J k d a).map Prod.snd = (form R 0 0 k d a).map Prod.snd := by
      simpa only [form,Form.changeWords,List.map_map,Function.comp_def] using
        congrArg (List.map (fun q => q ++ [(d,a)])) (term_words R h J (0,a) k)
    have bound := Finset.le_sup (f := N) (s := keys) (List.mem_toFinset.mpr (e ▸ hw))
    exact hN w n (bound.trans hn) m (bound.trans hm) h J
  exact ⟨apply_eq _ (fun w hw => (atWord w hw).1),apply_eq _ (fun w hw => (atWord w hw).2)⟩
end DSFTomography.HT.Diagonal.Bulk
