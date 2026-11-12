import EndOfPaper.GaussianProductMarginal

/-!
The genuine finite-dimensional Gaussian midpoint log-integral inequality, proved by induction using the actual coordinate integration identity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_finite_midpoint_log_integral (n : ℕ) {KF KG : ℝ≥0}
    {F G : EuclideanSpace ℝ (Fin n) → ℝ} (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    {b : ℝ} (hCompare : ∀ z w, F z+G w ≤ b+(dist z w)^2/4) :
    Real.log (gaussianExpIntegral F)+Real.log (gaussianExpIntegral G) ≤ b := by
  induction n with
  | zero =>
      rw [gaussianExpIntegral_zero,gaussianExpIntegral_zero,Real.log_exp,Real.log_exp]
      simpa only [dist_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,add_zero] using hCompare 0 0
  | succ n ih =>
      rw [gaussianExpIntegral_marginal hF,gaussianExpIntegral_marginal hG]
      exact ih (gaussian_log_marginal_lipschitz hF) (gaussian_log_marginal_lipschitz hG)
        (gaussian_log_marginal_midpoint_bound hF hG hCompare)

end ScalarMonotone.EndOfPaper
end
