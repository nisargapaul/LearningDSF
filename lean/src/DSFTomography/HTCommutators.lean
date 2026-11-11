import DSFTomography.HTWordAlgebra

noncomputable section
namespace DSFTomography.HT
open DSFTomography Pauli
variable {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T]

def ad {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Op ι) : Module.End ℂ (Op ι) :=
  LinearMap.mulRight ℂ H - LinearMap.mulLeft ℂ H

structure PauliInteraction (S T : Type*) [Fintype S] [Fintype T] where
  label : T → Label S
  weight : T → ℂ
  two : ∀ t, (supp (label t)).card ≤ 2

namespace PauliInteraction
variable (I : PauliInteraction S T)
def matrix := ∑ t, I.weight t • word (I.label t)
def touching (w : Label S) := Finset.univ.filter (fun t => ¬Disjoint (supp w) (supp (I.label t)))
def stepWeight (w : Label S) (t : T) :=
  I.weight t * (unitPhase w (I.label t) - unitPhase (I.label t) w)

def SiteBound (g : ℝ) := ∀ i : S, ∑ t, (if i ∈ supp (I.label t) then ‖I.weight t‖ else 0) ≤ g

theorem touch_mass {g : ℝ} (incident : I.SiteBound g) (w : Label S) :
    ∑ t ∈ I.touching w, ‖I.weight t‖ ≤ (supp w).card * g := by
  classical
  rw [touching, Finset.sum_filter]
  calc
    _ ≤ ∑ t, ∑ i ∈ supp w, if i ∈ supp (I.label t) then ‖I.weight t‖ else 0 := by
      apply Finset.sum_le_sum
      intro t _
      by_cases h : Disjoint (supp w) (supp (I.label t))
      · simp only [h, not_true_eq_false, if_false]; positivity
      · rw [if_pos h]
        obtain ⟨i,hi,ht⟩ := Finset.not_disjoint_iff.mp h
        simpa [ht] using Finset.single_le_sum
          (f := fun i => if i ∈ supp (I.label t) then ‖I.weight t‖ else 0)
          (fun i _ => by positivity) hi
    _ ≤ _ := by
      rw [Finset.sum_comm]
      simpa using Finset.sum_le_sum (s := supp w) (fun i _ => incident i)

theorem ad_word (w : Label S) : ad I.matrix (word w) =
    ∑ t ∈ I.touching w, I.stepWeight w t • word (combine w (I.label t)) := by
  classical
  change word w * I.matrix - I.matrix * word w = _
  simp only [matrix, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.sum_sub_distrib, ← smul_sub]
  rw [touching, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  change I.weight t • bracket (word w) (word (I.label t)) = _
  rw [Pauli.commutator, smul_smul]
  by_cases h : Disjoint (supp w) (supp (I.label t))
  · simp [h, phase_eq_of_disjoint h]
  · simp [h, stepWeight]

omit [DecidableEq S] in
theorem norm_step (w : Label S) (t : T) : ‖I.stepWeight w t‖ ≤ ‖I.weight t‖ * 2 := by
  rw [stepWeight, norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (by norm_num [phase_norm])) (norm_nonneg _)

/-- k nested commutators can reach only k new sites. The bound is valid for
any functional bounded on the individual Pauli words, even at complex β. -/
theorem iter_bound {g M : ℝ} (hg : 0 ≤ g) (hM : 0 ≤ M) (incident : I.SiteBound g)
    (l : Op (Config S) →ₗ[ℂ] ℂ) (cap : ∀ w, ‖l (word w)‖ ≤ M) (k : ℕ)
    (w : Label S) (s : ℕ) (hs : (supp w).card ≤ s) :
    ‖l ((ad I.matrix ^ k) (word w))‖ ≤ M * (2*g)^k * s.ascFactorial k := by
  induction k generalizing w s with
  | zero => simpa using cap w
  | succ k ih =>
    let B := M * (2*g)^k * (s+1).ascFactorial k
    have hB : 0 ≤ B := by dsimp [B]; positivity
    rw [pow_succ, Module.End.mul_apply, ad_word, map_sum, map_sum]
    calc
      _ ≤ ∑ t ∈ I.touching w, ‖I.weight t‖ * (2*B) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro t ht
        have touch := (Finset.mem_filter.mp ht).2
        have hs' := (card_step touch (I.two t)).trans (Nat.add_le_add_right hs 1)
        simp only [map_smul, smul_eq_mul, norm_mul]
        exact (mul_le_mul (I.norm_step w t) (ih _ _ hs') (norm_nonneg _) (by positivity)).trans_eq
          (mul_assoc ..)
      _ ≤ (s*g) * (2*B) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right ((I.touch_mass incident w).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hg)) (by positivity)
      _ = _ := by
        have f : (s : ℝ) * (s+1).ascFactorial k = (s.ascFactorial (k+1) : ℝ) := by
          exact_mod_cast (Nat.succ_ascFactorial s k).trans Nat.ascFactorial_succ.symm
        dsimp [B]
        rw [pow_succ, ← f]
        ring

end PauliInteraction
end DSFTomography.HT
