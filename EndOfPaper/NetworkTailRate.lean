import EndOfPaper.NetworkRateGrowth
import EndOfPaper.SqrtLogNetworkMajorant

/-!
Convert the exact confidence-radius bound to the displayed two-regime tail rate, retaining its original constants and the trivial small-deviation case.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_radius_at_exponential {s : ℝ} (hs : 0 ≤ s) :
    networkDepthRadius (24*Real.exp 1*Real.exp (-(s^2))) = s := by
  have hC : (24 : ℝ)*Real.exp 1 ≠ 0 := mul_ne_zero (by norm_num) (Real.exp_ne_zero _)
  have hr : 24*Real.exp 1/(24*Real.exp 1*Real.exp (-(s^2))) = Real.exp (s^2) := by
    rw [Real.exp_neg]
    field_simp [hC,Real.exp_ne_zero]
  unfold networkDepthRadius
  rw [hr,Real.log_exp,Real.sqrt_sq_eq_abs,abs_of_nonneg hs]

theorem network_profile_implies_two_regime_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (L : ℕ) {d M A C : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hTail : ∀ u ∈ Ioo (0 : ℝ) 1,
      μ.real {ω | C*networkDepthRadius u*(M+A*networkDepthRadius u/Real.sqrt d)^L < Y ω} ≤ u)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | C*(M+A)^L*t < Y ω} ≤
      24*Real.exp 1*Real.exp (-networkRatePower L d t) := by
  let s := networkRateInverse L d t
  have hp := network_rate_inverse_properties L hd ht
  let u := 24*Real.exp 1*Real.exp (-(s^2))
  have hu0 : 0 < u := mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (Real.exp_pos _)
  have huEq : u = 24*Real.exp 1*Real.exp (-networkRatePower L d t) := by
    dsimp only [u,s]
    rw [hp.2.2.2]
  rw [← huEq]
  by_cases hu : u < 1
  · have hr : networkDepthRadius u = s := network_radius_at_exponential hp.1
    have hb := hTail u ⟨hu0,hu⟩
    rw [hr] at hb
    have hSize : C*s*(M+A*s/Real.sqrt d)^L ≤ C*(M+A)^L*t := by
      have hh := mul_le_mul_of_nonneg_left (network_depth_at_rate_inverse L hd hM hA ht) hC
      simpa only [mul_assoc] using hh
    exact (measureReal_mono (fun ω hω => lt_of_le_of_lt hSize hω)).trans hb
  · exact (measureReal_le_one (μ := μ)).trans (le_of_not_gt hu)

end ScalarMonotone.EndOfPaper
end
