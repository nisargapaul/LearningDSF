import DSFTomography.SFRemainder

/-! A common geometric bound on local response coefficients gives an explicit
finite-field estimate simultaneously in every periodic box. The number 6 is
the sum of (k+2) 2⁻ᵏ over k ≥ 0. -/
noncomputable section
namespace DSFTomography.SF
open DSFTomography Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [Fintype D]

/-- On the half-radius ball the nonlinear tail is Lipschitz in the two
couplings with a constant proportional to their distance from polarization. -/
theorem local_tail_bound {Φ : Params D → Harmonics D}
    {P : FormalMultilinearSeries ℝ (Params D) (Harmonics D)} {r : ℝ≥0} {K : ℝ}
    (expands : HasFPowerSeriesOnBall Φ P 0 r) (hr : 0 < (r:ℝ)) (hK : 0 ≤ K)
    (bound : ∀ k, ‖P k‖*(r:ℝ)^k ≤ K) (x y : Params D)
    (small : max ‖x‖ ‖y‖ ≤ r/2) :
    ‖Φ x - Φ y - fderiv ℝ Φ 0 (x-y)‖ ≤ (6*K/(r:ℝ)^2)*max ‖x‖ ‖y‖*‖x-y‖ := by
  let m := max ‖x‖ ‖y‖
  have mr : m < r := by dsimp [m]; linarith
  have mem {v : Params D} (h : ‖v‖ ≤ m) : v ∈ EMetric.ball 0 (r:ℝ≥0∞) := by
    rw [EMetric.mem_ball, edist_zero_right]; exact ENNReal.coe_lt_coe.mpr (h.trans_lt mr)
  let term (n : ℕ) := P n (fun _ => x) - P n (fun _ => y)
  have tail : HasSum (fun k => term (k+2)) (Φ x - Φ y - fderiv ℝ Φ 0 (x-y)) := by
    have hx := expands.hasSum (mem (le_max_left ..)); have hy := expands.hasSum (mem (le_max_right ..))
    simp only [zero_add] at hx hy
    convert (hasSum_nat_add_iff' 2).2 (hx.sub hy) using 1
    rw [Finset.sum_range_succ,Finset.sum_range_one,expands.hasFPowerSeriesAt.hasFDerivAt.fderiv]
    have c0 : P 0 (fun _ => x) = P 0 (fun _ => y) := congrArg _ (funext Fin.elim0)
    simp only [c0,sub_self,zero_add]
    rw [map_sub]; rfl
  let factor := K/(r:ℝ)^2*m*‖x-y‖
  have term_bound (k : ℕ) : ‖term (k+2)‖ ≤ factor*((k+2:ℝ)*(1/2:ℝ)^k) := by
    calc
      ‖term (k+2)‖ ≤ ‖P (k+2)‖ * ↑(k+2) * m^(k+1) * ‖x-y‖ := by
        simpa only [term,Fintype.card_fin,pi_norm_const,Prod.norm_def,Pi.sub_def,Nat.add_sub_cancel,
          Nat.reduceSub, show k+2-1=k+1 by omega] using
            (P (k+2)).norm_image_sub_le (fun _ => x) (fun _ => y)
      _ = ‖P (k+2)‖ * m^k * ((k+2:ℝ)*m*‖x-y‖) := by push_cast; rw [pow_succ]; ring
      _ ≤ (K/(r:ℝ)^(k+2)) * ((r:ℝ)/2)^k * ((k+2:ℝ)*m*‖x-y‖) := by
        have hp : ‖P (k+2)‖ ≤ K/(r:ℝ)^(k+2) := (le_div_iff₀ (pow_pos hr _)).mpr (bound _)
        have hm : 0 ≤ m := (norm_nonneg x).trans (le_max_left ..)
        gcongr
      _ = factor*((k+2:ℝ)*(1/2:ℝ)^k) := by
        simp only [factor,div_pow,pow_add,one_pow]; field_simp
  have half : ‖(1/2:ℝ)‖ < 1 := by norm_num
  have vals : HasSum (fun k : ℕ => (k+2:ℝ)*(1/2:ℝ)^k) 6 := by
    have v := (hasSum_coe_mul_geometric_of_norm_lt_one half).add ((hasSum_geometric_of_norm_lt_one half).mul_left 2)
    norm_num at v
    simpa [add_mul] using v
  have result := tail.norm_le_of_bounded (vals.mul_left factor) term_bound
  convert result using 1; dsimp [factor,m]; ring

/-- Field rescaling gives the two-point error bound directly. This estimate
uses the same r and K for every box for which the input bound holds. -/
theorem field_tail_bound {Φ : Params D → Harmonics D}
    {P : FormalMultilinearSeries ℝ (Params D) (Harmonics D)} {r : ℝ≥0} {K B : ℝ}
    (expands : HasFPowerSeriesOnBall Φ P 0 r) (hr : 0 < (r:ℝ)) (hK : 0 ≤ K)
    (bound : ∀ k, ‖P k‖*(r:ℝ)^k ≤ K) (jet : fderiv ℝ Φ 0 = leadingCLM)
    (large : 2/(r:ℝ) ≤ B) {p q : Params D} (hp : p ∈ couplingCube D) (hq : q ∈ couplingCube D) :
    ‖(atField Φ B p - leading p) - (atField Φ B q - leading q)‖ ≤ (6*K/(r:ℝ)^2/B)*‖p-q‖ := by
  have pos : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2/(r:ℝ)) large
  have norm_scale (v : Params D) : ‖B⁻¹ • v‖ = B⁻¹*‖v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos)]
  have inside {v : Params D} (hv : v ∈ couplingCube D) : ‖B⁻¹ • v‖ ≤ B⁻¹ := by
    rw [norm_scale]; apply mul_le_of_le_one_right (inv_nonneg.mpr pos.le); simpa [couplingCube] using hv
  have size := max_le (inside hp) (inside hq)
  have small : B⁻¹ ≤ (r:ℝ)/2 := by
    rw [inv_eq_one_div,div_le_iff₀ pos]; linarith [(div_le_iff₀ hr).mp large,mul_comm B (r:ℝ)]
  have localEst := local_tail_bound expands hr hK bound _ _ (size.trans small)
  rw [jet,← smul_sub,map_smul,norm_scale (p-q)] at localEst
  have cancel : (atField Φ B p - leading p) - (atField Φ B q - leading q) =
      B • (Φ (B⁻¹ • p) - Φ (B⁻¹ • q) - B⁻¹ • leadingCLM (p-q)) := by
    simp only [atField,smul_sub,smul_smul,mul_inv_cancel₀ pos.ne',one_smul,map_sub]
    change _ = B • Φ (B⁻¹ • p) - B • Φ (B⁻¹ • q) - (leading p-leading q)
    abel
  rw [cancel,norm_smul,Real.norm_eq_abs,abs_of_pos pos]
  apply (mul_le_mul_of_nonneg_left localEst pos.le).trans
  calc
    _ ≤ B*((6*K/(r:ℝ)^2)*B⁻¹*(B⁻¹*‖p-q‖)) := by gcongr
    _ = _ := by field_simp

end DSFTomography.SF
