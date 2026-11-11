import DSFTomography.SFClusterPauli
import DSFTomography.SFClusterGround

/-! All three laboratory fields share a physical neighborhood in every box.
The complex source at a Y letter carries its Pauli phase. -/
noncomputable section
namespace DSFTomography.SF.Cluster
open DSFTomography HT Filter NormedSpace
open scoped Topology ContDiff
variable {ν : ℕ} (R : Bonds (Site ν))

def unbox (n : ℕ) : Params (periodicBonds R n).dirs →L[ℝ] Params R.dirs :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => (p.1, fun d => p.2 (bondInBox R n d))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem unbox_box (n) (p : Params R.dirs) : unbox R n (boxParams R n p) = p := by
  apply Prod.ext; · rfl
  funext d; simp [unbox,boxParams]
@[simp] theorem box_unbox (n) (p : Params (periodicBonds R n).dirs) : boxParams R n (unbox R n p) = p := by
  apply Prod.ext; · rfl
  funext d; simp [unbox,boxParams]

def sourceMap (i : Axis) : Params R.dirs →L[ℝ] Sources R :=
  LinearMap.toContinuousLinearMap {
    toFun := source R i
    map_add' := by intro p q; funext j; cases j <;> simp [source,add_mul]
    map_smul' := by intro c p; funext j; cases j <;> simp [source,Complex.real_smul,mul_assoc] }

def normalize {S : Type*} [Fintype S] [DecidableEq S] (w : Amp S) (k : Config S) : ℂ :=
  w k / (Real.sqrt (∑ j, Complex.normSq (w j)) : ℂ)

theorem normalized {S : Type*} [Fintype S] [DecidableEq S] (w : Amp S) (wne : w ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ j, normalize w j = c * w j) ∧ ∑ j, Complex.normSq (normalize w j) = 1 := by
  let q := ∑ j, Complex.normSq (w j)
  have nz : 0 < q := by
    apply Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
    by_contra! zero
    apply wne; apply WithLp.ofLp_injective; funext k
    exact Complex.normSq_eq_zero.mp (le_antisymm (zero k (Finset.mem_univ k)) (Complex.normSq_nonneg _))
  let l : ℂ := Real.sqrt q
  have n : l ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr nz).ne'
  refine ⟨l⁻¹,inv_ne_zero n,fun k => by simp [normalize,l,q,div_eq_inv_mul],?_⟩
  simp only [normalize,map_div₀,← Finset.sum_div]
  change q / Complex.normSq l = 1
  rw [show Complex.normSq l = q by simp [l,Complex.normSq_ofReal,← sq,Real.sq_sqrt nz.le]]
  exact div_self nz.ne'

def Ebox (n : ℕ) (v : Amplitudes R) : ℂ := -(Fintype.card (Box R n):ℂ) * v n 0

theorem physical_branch {a : Sources R → Amplitudes R} {n : ℕ} {i : Axis} {p : Params R.dirs}
    (h : let v := a (sourceMap R i p) n
         let H := clusterH (boxFlips R n) (boxSigns R n) (sourceMap R i p)
         let E := Ebox R n (a (sourceMap R i p))
         eigenKet v ≠ 0 ∧ H (eigenKet v) = E • eigenKet v ∧
         ∀ μ (ξ : Amp (Box R n)), ξ ≠ 0 → H ξ = μ • ξ → μ.re ≤ E.re + 1 →
           μ = E ∧ ∃ c : ℂ, ξ = c • eigenKet v) :
    IsGroundPair (periodicBonds R n) i (boxParams R n p)
      (normalize (eigenKet (a (sourceMap R i p) n))) (Ebox R n (a (sourceMap R i p))) := by
  let w := eigenKet (a (sourceMap R i p) n)
  let E := Ebox R n (a (sourceMap R i p))
  let V := withParams (periodicBonds R n) (boxParams R n p)
  let H := clusterH (boxFlips R n) (boxSigns R n) (sourceMap R i p)
  obtain ⟨nz,eig,low⟩ := h
  obtain ⟨c,hc,amp,normed⟩ := normalized w nz
  have row (v : Amp (Box R n)) (k : Config (Box R n)) :
      H v k = flipGap k * v k + ∑ j, fieldFrame V i k j * v j := by
    change clusterH _ _ (source R i p) v k = _
    rw [physical_matrix,map_add,ContinuousLinearMap.add_apply,PiLp.add_apply,asOp_apply,asOp_apply]
    simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul,V]
  refine ⟨normed,?_,?_⟩
  · intro k
    have measured := congrArg (fun z : Amp (Box R n) => z k) eig
    change H w k = E*w k at measured
    rw [row] at measured
    change flipGap k * normalize w k + ∑ j, fieldFrame V i k j * normalize w j = E * normalize w k
    simp only [amp]
    calc _ = c * (flipGap k*w k + ∑ j, fieldFrame V i k j*w j) := by
              simp [mul_add,Finset.mul_sum,mul_left_comm]
         _ = E * (c*w k) := by rw [measured]; ring
  · intro μ ξ nx test bound
    let u : Amp (Box R n) := WithLp.toLp 1 ξ
    have nonzero : u ≠ 0 := fun bad => nx (congrArg WithLp.ofLp bad)
    have hx : H u = μ • u := by apply WithLp.ofLp_injective; funext k; exact (row u k).trans (test k)
    obtain ⟨e,t,equ⟩ := low μ u nonzero hx (by linarith)
    refine ⟨e,t/c,?_⟩; funext k
    have rel := congrArg (fun z : Amp (Box R n) => z k) equ
    change ξ k = t*w k at rel
    change ξ k = t/c * normalize w k
    rw [rel,amp]; field_simp

/-- A single positive ball of couplings works in every box and every field
orientation. The charts are the normalized, simple lowest eigenstates of
the very matrices used by the finite spectral readout. -/
theorem charts_of_branch (a : Sources R → Amplitudes R) (ha : AnalyticAt ℂ a 0) (zero : a 0=0)
    (ground : GroundNeighborhood R a) :
    ∃ G : BoxCharts R, (∀ n i p, let x := boxParams R n p
      (G n i).ψ x = normalize (eigenKet (a (sourceMap R i p) n)) ∧ (G n i).E x = Ebox R n (a (sourceMap R i p))) ∧ ∀ᶠ p in 𝓝 (0 : Params R.dirs), ∀ n i,
      let x := boxParams R n p
      IsGroundPair (periodicBonds R n) i x ((G n i).ψ x) ((G n i).E x) := by
  unfold GroundNeighborhood at ground
  have all : ∀ᶠ p in 𝓝 (0 : Params R.dirs), ∀ i n,
      IsGroundPair (periodicBonds R n) i (boxParams R n p)
        (normalize (eigenKet (a (sourceMap R i p) n))) (Ebox R n (a (sourceMap R i p))) := by
    apply eventually_all.mpr; intro i
    have cv : Tendsto (sourceMap R i) (𝓝 0) (𝓝 0) := by simpa using (sourceMap R i).continuous.continuousAt (x := 0) |>.tendsto
    exact (cv.eventually ground).mono fun p hp n => physical_branch R (hp n)
  let G (n : ℕ) (i : Axis) : GroundChart (periodicBonds R n) i := by
    let P := Params (periodicBonds R n).dirs
    let v := fun x : P => a (sourceMap R i (unbox R n x))
    have vz : v 0=0 := by simp [v,zero]
    have sm : ContDiffAt ℝ 2 v 0 := by
      have hz : sourceMap R i (unbox R n 0) = 0 := by simp
      have reg : ContDiffAt ℝ 2 a (sourceMap R i (unbox R n 0)) := hz ▸ ha.contDiffAt.restrict_scalars ℝ
      let L := (sourceMap R i).comp (unbox R n)
      exact reg.comp (g := a) (f := L) 0 L.contDiff.contDiffAt
    let w := fun x : P => eigenKet (v x n)
    have smoothKet : ContDiffAt ℝ 2 w 0 := by
      let L := (convolute (S := Box R n)).comp (generator (S := Box R n))
      have smooth := ((exp_analytic (𝕂 := ℂ) (L (v 0 n))).contDiffAt (n:=2)).restrict_scalars ℝ
      let col := ContinuousLinearMap.apply ℂ (Amp (Box R n)) (basis (0 : Config (Box R n)))
      have hl : ContDiffAt ℝ 2 (fun x => L (v x n)) 0 :=
        ((L.comp (atBox R n)).restrictScalars ℝ).contDiff.contDiffAt.comp 0 sm
      have he : ContDiffAt ℝ 2 (fun x => exp ℂ (L (v x n))) 0 := smooth.comp 0 hl
      exact (col.restrictScalars ℝ).contDiff.contDiffAt.comp 0 he
    have wz : w 0=basis 0 := by simp [w,vz,eigenKet,ampExp]
    have sk (k) : ContDiffAt ℝ 2 (fun x => w x k) 0 :=
      ((PiLp.proj 1 (fun _ : Config (Box R n) => ℂ) k : Amp (Box R n) →L[ℂ] ℂ).restrictScalars ℝ).contDiff.contDiffAt.comp 0 smoothKet
    let q := fun x => ∑ k, Complex.normSq (w x k)
    have q0 : q 0=1 := by simp [q,wz,apply_ite]
    have sq0 (z : ℂ) : ContDiffAt ℝ 2 Complex.normSq z := by
      change ContDiffAt ℝ 2 (fun z : ℂ => z.re*z.re+z.im*z.im) z
      exact (Complex.reCLM.contDiff.contDiffAt.mul Complex.reCLM.contDiff.contDiffAt).add
        (Complex.imCLM.contDiff.contDiffAt.mul Complex.imCLM.contDiff.contDiffAt)
    have sq : ContDiffAt ℝ 2 q 0 := ContDiffAt.sum fun j _ => (sq0 _).comp 0 (sk j)
    have sr : ContDiffAt ℝ 2 (fun x => Real.sqrt (q x)) 0 := sq.sqrt (by simp [q0])
    have si : ContDiffAt ℝ 2 (fun x => (Real.sqrt (q x))⁻¹) 0 := sr.inv (by simp [q0])
    have sz : ContDiffAt ℝ 2 (fun x => Ebox R n (v x)) 0 := by
      let proj := (PiLp.proj 1 (fun _ : Config (Box R n) => ℂ) (0 : Config (Box R n)) : Amp (Box R n) →L[ℂ] ℂ)
      exact contDiffAt_const.mul ((proj.restrictScalars ℝ).contDiff.contDiffAt.comp 0 (((atBox R n).restrictScalars ℝ).contDiff.contDiffAt.comp 0 sm))
    refine { ψ := fun x => normalize (w x), E := fun x => Ebox R n (v x), smoothE := sz,
             smoothψ := contDiffAt_pi.mpr (fun k => by
               change ContDiffAt ℝ 2 (fun x => w x k / (Real.sqrt (q x) : ℂ)) 0
               simpa only [Function.comp_apply,Complex.ofRealCLM_apply,div_eq_mul_inv,Complex.ofReal_inv] using (sk k).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 si)),
             E0 := by simp [vz,Ebox], vac := ?_, physical := ?_ }
    · funext k
      change w 0 k / (Real.sqrt (q 0) : ℂ) = _
      rw [q0,wz]; simp [basis_at,ket,vacuum]; rfl
    · have cv : Tendsto (unbox R n) (𝓝 0) (𝓝 0) := by simpa using (unbox R n).continuous.continuousAt (x := 0) |>.tendsto
      filter_upwards [cv.eventually all] with x hx
      simpa [w,v] using hx i n
  refine ⟨G,fun n i p => by simp [G,unbox_box],all.mono fun p h n i => ?_⟩
  simpa only [G,unbox_box] using h i n

end DSFTomography.SF.Cluster
