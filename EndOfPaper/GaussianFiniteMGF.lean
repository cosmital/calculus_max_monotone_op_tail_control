import EndOfPaper.GaussianFiniteMidpoint

/-!
The exact Gaussian copy exponential bound, derived from the proved finite-dimensional midpoint inequality for arbitrary real tilts.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_tilt_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f : E → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) :
    LipschitzWith ⟨|a|,abs_nonneg a⟩ (fun x => a*f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg a)
  simpa only [Real.dist_eq,← mul_sub,abs_mul,NNReal.coe_one,one_mul,NNReal.coe_mk] using hh

theorem gaussian_tilt_pair_bound {E : Type*} [PseudoMetricSpace E]
    {f : E → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) (x y : E) :
    a*f x+(-a)*f y ≤ a^2+(dist x y)^2/4 := by
  have hLip : |f x-f y| ≤ dist x y := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul x y
  have hlin : a*(f x-f y) ≤ |a| * dist x y := by
    apply (le_abs_self (a*(f x-f y))).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hLip (abs_nonneg a)
  nlinarith [sq_nonneg (dist x y/2-|a|),sq_abs a]

theorem gaussian_finite_lipschitz_copy_mgf {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) :
    gaussianExpIntegral (fun x => a*f x)*gaussianExpIntegral (fun x => (-a)*f x) ≤ Real.exp (a^2) := by
  have hF := gaussian_tilt_lipschitz hf a
  have hG := gaussian_tilt_lipschitz hf (-a)
  have hh := gaussian_finite_midpoint_log_integral n hF hG (gaussian_tilt_pair_bound hf a)
  have hExp := Real.exp_le_exp.mpr hh
  rwa [Real.exp_add,Real.exp_log (gaussianExpIntegral_positive hF),
    Real.exp_log (gaussianExpIntegral_positive hG)] at hExp

end ScalarMonotone.EndOfPaper
end
