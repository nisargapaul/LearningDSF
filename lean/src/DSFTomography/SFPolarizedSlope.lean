import DSFTomography.SFTransitions

/-! Slopes of the actual local transverse probes on a finite lattice. The
ground eigenpair is taken along a real coupling ray in the unit-field chart.
Its derivatives, including its phase choice, need not be supplied as data. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography HT Filter
open scoped Topology
variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

abbrev vacuum (S : Type*) [DecidableEq S] : Config S := bitConfig (∅ : Finset S)
abbrev flip (r : S) : Config S := bitConfig {r}

/-- Eigenvalue equation after shifting the polarized energy to zero.
All three field settings use the same cyclic X,Y,Z chart. -/
structure EigenRay (V : Volume S) (i : Axis) where
  ψ : ℝ → Config S → ℂ
  E : ℝ → ℂ
  vacuum_at : ψ 0 = ket (vacuum S)
  energy_at : E 0 = 0
  smooth_ket : ∀ k, DifferentiableAt ℝ (fun t => ψ t k) 0
  smooth_energy : DifferentiableAt ℝ E 0
  eigen : ∀ᶠ t in 𝓝 (0:ℝ), ∀ k,
    flipGap k * ψ t k + (t:ℂ)*(∑ l, fieldFrame V i k l * ψ t l) = E t * ψ t k

namespace EigenRay
variable {V : Volume S} {i : Axis} (g : EigenRay V i)
private def u (x : Config S) := deriv (fun t => g.ψ t x) 0
private theorem du (x : Config S) : HasDerivAt (fun t => g.ψ t x) (g.u x) 0 :=
  (g.smooth_ket x).hasDerivAt

private theorem response : deriv g.E 0 = fieldFrame V i (vacuum S) (vacuum S) ∧
    ∀ k ≠ vacuum S, flipGap k * g.u k = -fieldFrame V i k (vacuum S) :=
  eigenpair_response (vacuum S) flipGap (fieldFrame V i) g.vacuum_at
  (by simp [vacuum,flipGap_bits]) g.energy_at g.du g.smooth_energy.hasDerivAt g.eigen

def staticPair (r s : S) (a b : Axis) (t : ℝ) :=
  sandwich (g.ψ t) (word (twoLabel r s a b)) (g.ψ t)

/-- Individual ordered static slopes. At opposite displacements XX and YY
have the same slopes, and XY and YX have the same slopes at zero coupling. -/
theorem static_slopes {d : S} (hd : d ∈ V.R.dirs) (r : S) :
    let pair := bondEntry (V.J d) i (1,1) (0,0)
    HasDerivAt (g.staticPair r (r+d) 0 0) (-(pair.re : ℂ)/2) 0 ∧
    HasDerivAt (g.staticPair r (r+d) 1 1) ((pair.re : ℂ)/2) 0 ∧
    HasDerivAt (g.staticPair r (r+d) 0 1) (-(pair.im : ℂ)/2) 0 ∧
    HasDerivAt (g.staticPair r (r+d) 1 0) (-(pair.im : ℂ)/2) 0 := by
  intro pair
  let s := r+d
  let k := bitConfig ({r,s} : Finset S)
  have ne : r ≠ s := Ne.symm (by simpa [s] using V.R.nonzero d hd)
  have kv : k ≠ vacuum S := fun eq => by simpa [k,vacuum] using bitConfig_injective eq
  have four : flipGap k = 4 := by norm_num [k,flipGap_bits,ne]
  have uval : g.u k = -pair/4 := by
    have h := g.response.2 k kv
    rw [four,(flip_entries V i hd r).2] at h
    linear_combination h / 4
  have derivPair (a b : Axis) (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
      let z := pauli (some a) 1 0 * pauli (some b) 1 0
      HasDerivAt (g.staticPair r s a b) (star (-pair/4)*z + star z*(-pair/4)) 0 := by
    intro z
    have col := transverse_pair_column ne a b ha hb
    have row (l : Config S) : word (twoLabel r s a b) (vacuum S) l = star z * ket k l := by
      have h := congrFun (congrFun (word_hermitian (twoLabel r s a b)) (vacuum S)) l
      rw [← h,Matrix.conjTranspose_apply,col]
      change star (z*ket k l) = star z * ket k l
      by_cases same : l=k <;> simp [ket,same]
    simpa only [uval] using static_response (vacuum S) k (word (twoLabel r s a b)) col row g.vacuum_at g.du
  have X := derivPair 0 0 (Or.inl rfl) (Or.inl rfl)
  have Y := derivPair 1 1 (Or.inr rfl) (Or.inr rfl)
  have XY := derivPair 0 1 (Or.inl rfl) (Or.inr rfl)
  have YX := derivPair 1 0 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_,?_,?_,?_⟩
  · convert X using 1; apply Complex.ext <;> norm_num [pauliValues,Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im] <;> ring
  · convert Y using 1; apply Complex.ext <;> norm_num [pauliValues,Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im] <;> ring
  · convert XY using 1; apply Complex.ext <;> norm_num [pauliValues,Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]; ring
  · convert YX using 1; apply Complex.ext <;> norm_num [pauliValues,Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]; ring

def probeKet (r : S) (t : ℝ) (x : Config S) :=
  ∑ y, spinAt r 0 x y * g.ψ t y

theorem probe_at (r : S) : g.probeKet r 0 = ket (flip r) := by
  funext x
  simp only [probeKet,g.vacuum_at,ket,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [spinAt,word_one]
  by_cases hx : x = flip r
  · subst x
    have outside (s : S) (ne : s ≠ r) : flip r s = vacuum S s := by simp [flip,vacuum,bitConfig,ne]
    rw [if_pos outside]
    simp [flip,vacuum,bitConfig,pauliValues]
  · rw [if_neg hx]
    split_ifs with outside
    · have zero : x r = 0 := by
        by_contra nz; apply hx; funext t
        by_cases h : t=r
        · subst t; have one : x r = 1 := by have := (x r).isLt; omega
          simp [flip,bitConfig,one]
        · simpa [flip,vacuum,bitConfig,h] using outside t h
      simp [vacuum,bitConfig,zero,pauliValues]
    · rfl

private theorem dprobe (r : S) (x : Config S) :
    HasDerivAt (fun t => g.probeKet r t x) (∑ y, spinAt r 0 x y * g.u y) 0 :=
  HasDerivAt.fun_sum fun y _ => (g.du y).const_mul _

/-- Raw centered transverse moment. The connected correction is a product
of transverse means with zero polarized expectation (connected_response). -/
def centeredPair (r s : S) (t : ℝ) :=
  sandwich (g.probeKet r t)
    (Matrix.diagonal (fun x => flipGap x-g.E t-2) + (t:ℂ) • fieldFrame V i) (g.probeKet s t)

theorem centered_slope (r s : S) :
    HasDerivAt (g.centeredPair r s) (fieldFrame V i (flip r) (flip s) -
      if r=s then fieldFrame V i (vacuum S) (vacuum S) else 0) 0 := by
  have eq : flip r = flip s ↔ r=s := by simp [flip,bitConfig_injective.eq_iff]
  simpa [centeredPair,g.response.1,eq] using
    centered_response (flip r) (flip s) flipGap (fieldFrame V i) g.energy_at g.smooth_energy.hasDerivAt
      (g.probe_at r) (g.probe_at s) (by simp [flip,flipGap_bits]) (by simp [flip,flipGap_bits])
      (g.dprobe r) (g.dprobe s)

theorem centered_slopes {d : S} (hd : d ∈ V.R.dirs) (r : S) :
    let hop := bondEntry (V.J d) i (1,0) (0,1)
    HasDerivAt (g.centeredPair r (r+d)) hop 0 ∧
    HasDerivAt (g.centeredPair (r+d) r) (star hop) 0 ∧
    HasDerivAt (g.centeredPair r r) ((-2*V.h i - 4*∑ e ∈ V.R.dirs, V.J e i i : ℝ) : ℂ) 0 := by
  have ne : r ≠ r+d := Ne.symm (by simpa using V.R.nonzero d hd)
  have fwd := (flip_entries V i hd r).1
  have herm : (fieldFrame V i).IsHermitian := qubitH_hermitian .. 
  have rev := congrFun (congrFun herm (flip (r+d))) (flip r)
  rw [Matrix.conjTranspose_apply,fwd] at rev
  exact ⟨by simpa only [if_neg ne,fwd,sub_zero] using g.centered_slope r (r+d),
    by simpa only [if_neg (Ne.symm ne),← rev,sub_zero] using g.centered_slope (r+d) r,
    by rw [← flip_energy_shift V i r]; simpa using g.centered_slope r r⟩

end EigenRay
end DSFTomography.SF
