import DSFTomography.HTLocalKMS
import DSFTomography.HTBulk

/-! Compare two volumes via the local Gibbs recursion. Each finite truncation
has the same lattice addresses in both volumes. Its coefficient mass contracts
by a factor of two, while the discarded tail is uniformly geometric. -/
noncomputable section
namespace DSFTomography.HT
open DSFTomography Filter Metric
open scoped Topology
namespace LocalWord
variable {ν : ℕ} (R : Bonds (Site ν)) (h : Axis → ℝ) (J : Site ν → Matrix Axis Axis ℝ)

private theorem geometric (M : ℝ) (K : ℕ) :
    HasSum (fun k : ℕ => (1/2 : ℝ)^(k+K+1)*M) ((1/2 : ℝ)^K*M) := by
  have hs := (hasSum_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)).mul_right ((1/2:ℝ)^K*(1/2)*M)
  convert hs using 1
  · funext k; rw [pow_succ,pow_add]; ring
  · norm_num; ring

private theorem series_bound {f : ℕ → ℂ} {v : ℂ} {D M : ℝ} (K : ℕ)
    (hs : HasSum f v) (global : ∀ k, ‖f k‖ ≤ (1/2 : ℝ)^(k+1)*M)
    (part : ∀ k < K, ‖f k‖ ≤ (1/2 : ℝ)^(k+1)*D) (hD : 0 ≤ D) :
    ‖v‖ ≤ D+(1/2:ℝ)^K*M := by
  have tail := (hasSum_nat_add_iff' K).mpr hs
  have maj := geometric M K
  have sn := maj.summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => global (k+K))
  have le := (norm_tsum_le_tsum_norm sn).trans (sn.tsum_le_tsum (fun k => global (k+K)) maj.summable)
  rw [tail.tsum_eq,maj.tsum_eq] at le
  have whole := geometric D 0
  simp only [Nat.add_zero,pow_zero,one_mul] at whole
  have first := (norm_sum_le (Finset.range K) f).trans (Finset.sum_le_sum fun k hk => part k (Finset.mem_range.mp hk))
  have leD := whole.summable.sum_le_tsum (Finset.range K) (fun i _ => mul_nonneg (by positivity) hD)
  rw [whole.tsum_eq] at leD
  have tri := norm_add_le (∑ k ∈ Finset.range K, f k) (v - ∑ k ∈ Finset.range K, f k)
  rw [add_sub_cancel] at tri
  linarith

def diskRadius := bulkRadius R h J / 2
theorem diskRadius_pos : 0 < diskRadius R h J := half_pos (bulkRadius_pos ..)

private theorem diff_level (x : Atom (Site ν)) (xs : Script (Site ν)) (n m k : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ diskRadius R h J) {D : ℝ} (hD : 0 ≤ D)
    (bound : ∀ p ∈ terms R h J x k,
      ‖value R h J ((x::xs)++p.2) n z - value R h J ((x::xs)++p.2) m z‖ ≤ D) :
    ‖level R h J x xs n z k - level R h J x xs m z k‖ ≤ (1/2:ℝ)^k*D := by
  let g := incidentBound R h J
  have hg : 0 < g := incidentBound_pos ..
  have small : ‖z‖*(4*g) ≤ 1/2 := by
    change ‖z‖ ≤ (4*g)⁻¹/2 at hz
    calc
      _ ≤ ((4*g)⁻¹/2)*(4*g) := mul_le_mul_of_nonneg_right hz (by positivity)
      _ = _ := by field_simp
  have sub (u : Form (Site ν)) (f e : Script (Site ν) → ℂ) :
      Form.apply u f - Form.apply u e = Form.apply u (fun w => f w - e w) := by
    induction u with
    | nil => simp
    | cons p u ih => simp only [Form.apply_cons,smul_sub,← ih]; abel
  rw [level,level,← mul_sub,sub,norm_mul,norm_div,norm_pow,Complex.norm_natCast]
  have le := (Form.norm_apply_le _ (fun w => value R h J ((x::xs)++w) n z - value R h J ((x::xs)++w) m z) bound).trans (mul_le_mul_of_nonneg_right (terms_mass R h J x k) hD)
  calc
    _ ≤ (‖z‖^k / k.factorial) * (((4*g)^k * k.factorial) * D) :=
      mul_le_mul_of_nonneg_left le (by positivity)
    _ = (‖z‖*(4*g))^k*D := by simp only [mul_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) small k) hD

private def oscillation (xs : Script (Site ν)) (D : ℝ) := ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ z : ℂ, ‖z‖ ≤ diskRadius R h J →
      ‖value R h J xs n z - value R h J xs m z‖ ≤ D+ε

private theorem trivial_diff (xs : Script (Site ν)) (n m : ℕ) (z : ℂ) (hz : ‖z‖ ≤ diskRadius R h J) :
    ‖value R h J xs n z - value R h J xs m z‖ ≤ 2 := by
  have hrad := bulkRadius_pos R h J
  have hle : ‖z‖ ≤ bulkRadius R h J := hz.trans (by unfold diskRadius; linarith)
  exact (norm_sub_le ..).trans (by linarith [value_bound R h J xs n z hle,value_bound R h J xs m z hle])

private theorem contract {D : ℝ} (hD : 0≤D) (bound : ∀ xs, oscillation R h J xs D)
    (xs : Script (Site ν)) : oscillation R h J xs (D/2) := by
  intro ε hε
  rcases classify R xs with ⟨t,ht⟩|⟨x,hx⟩
  · obtain ⟨N,hN⟩ := eventually_atTop.mp ht
    refine ⟨N,fun n hn m hm z hz => ?_⟩
    have val (n : ℕ) (hn : N ≤ n) : value R h J xs n z = t := by
      have hr := bulkRadius_pos R h J
      have nz := (periodic_zeroFree_bounded R h J n z (hz.trans (by unfold diskRadius; linarith))).1
      rw [value,hN n hn,map_smul,state_apply,mul_one]
      change t * ((periodicVolume R h J n).partition z / (periodicVolume R h J n).partition z) = t
      rw [div_self nz,mul_one]
    rw [val n hn,val m hm,sub_self,norm_zero]; linarith
  · obtain ⟨L,hL⟩ := eventually_atTop.mp hx
    have decay := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul 2
    obtain ⟨K,hK⟩ := (decay.eventually_lt_const (by simpa using hε)).exists
    classical
    let keys := (Finset.range K).biUnion (fun k => (terms R h J x (k+1)).toFinset)
    choose N hN using fun p : ℂ × Script (Site ν) => bound ((x::xs)++p.2) ε hε
    refine ⟨max L (keys.sup N),fun n hn m hm z hz => ?_⟩
    have tail (n : ℕ) (hn : L ≤ n) := (hasSum_nat_add_iff' 1).mpr (level_series R h J x xs n z)
    have series (n : ℕ) (hn : L ≤ n) : HasSum (fun k => level R h J x xs n z (k+1)) (2*value R h J xs n z) := by
      simpa only [Finset.sum_range_one,level_zero R h J x xs n z (hL _ hn),sub_neg_eq_add,two_mul] using tail n hn
    let f := fun k => level R h J x xs n z (k+1) - level R h J x xs m z (k+1)
    have sum : HasSum f (2*(value R h J xs n z-value R h J xs m z)) := by
      rw [mul_sub]
      exact (series n ((le_max_left ..).trans hn)).sub (series m ((le_max_left ..).trans hm))
    have le := series_bound K sum (M := 2) (D := D+ε)
      (fun k => diff_level R h J x xs n m (k+1) z hz (by norm_num) fun _ _ => trivial_diff R h J _ n m z hz)
      (fun k hk => diff_level R h J x xs n m (k+1) z hz (by linarith) (fun p hp => by
        have mem : p ∈ keys := Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr hk,List.mem_toFinset.mpr hp⟩
        have leN := (Finset.le_sup (f := N) mem).trans (le_max_right L _)
        exact hN p n (leN.trans hn) m (leN.trans hm) z hz)) (by linarith)
    rw [norm_mul] at le
    norm_num at le
    linarith

theorem uniform (xs : Script (Site ν)) : UniformCauchySeqOn (value R h J xs) atTop
    (Metric.closedBall (0 : ℂ) (diskRadius R h J)) := by
  have stages (k : ℕ) : ∀ w, oscillation R h J w (2*(1/2:ℝ)^k) := by
    induction k with
    | zero => intro w ε hε; exact ⟨0,fun n _ m _ z hz => by linarith [trivial_diff R h J w n m z hz,pow_zero (1/2:ℝ)]⟩
    | succ k ih =>
      intro w
      convert contract R h J (by positivity) ih w using 1
      rw [pow_succ]; ring
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have decay := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul 2
  obtain ⟨k,hk⟩ := (decay.eventually_lt_const (show 2*(0:ℝ) < ε/2 by linarith)).exists
  obtain ⟨N,hN⟩ := stages k xs (ε/2) (half_pos hε)
  refine ⟨N,fun n hn m hm z hz => ?_⟩
  rw [dist_eq_norm]
  exact (hN n hn m hm z (by simpa [Metric.mem_closedBall] using hz)).trans_lt (by linarith)
end LocalWord
end DSFTomography.HT
