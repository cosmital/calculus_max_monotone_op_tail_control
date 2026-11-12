import EndOfPaper.NetworkTailRate
import EndOfPaper.NetworkRateDimensions

/-!
The displayed equal-width profile implies a dimension-uniform two-regime tail estimate whenever the batch-to-width ratio and norm medians are bounded.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_depth_tail_implies_uniform_rate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (L : ℕ) {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) {c M m A : ℝ}
    (hRatio : (N : ℝ)/(d : ℝ) ≤ c) (hm : 0 ≤ m) (hmM : m ≤ M) (hA : 0 ≤ A)
    (hTail : ∀ u ∈ Ioo (0 : ℝ) 1,
      μ.real {ω | A*Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ))*networkDepthRadius u*
        (m+A*networkDepthRadius u/Real.sqrt (((d*min N 2 : ℕ) : ℝ)))^L < Y ω} ≤ u)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | A*Real.sqrt (1+c*(L : ℝ)/2)*(M+A)^L*t < Y ω} ≤
      24*Real.exp 1*Real.exp (-networkRatePower L (d : ℝ) t) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply network_profile_implies_two_regime_tail L hdR (hm.trans hmM) hA
    (mul_nonneg hA (Real.sqrt_nonneg _)) _ ht
  intro u hu
  have hh := network_depth_threshold_uniform L hN hd hRatio hm hmM hA
    (Real.sqrt_nonneg (Real.log (24*Real.exp 1/u)))
  exact (measureReal_mono (fun ω hω => lt_of_le_of_lt hh hω)).trans (hTail u hu)

end ScalarMonotone.EndOfPaper
end
