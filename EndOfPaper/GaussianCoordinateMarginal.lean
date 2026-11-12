import EndOfPaper.GaussianVectorSplit
import EndOfPaper.GaussianRealMidpoint
import EndOfPaper.LogExpMarginal
import EndOfPaper.GaussianLipschitzGeneral

/-!
Actual one-coordinate Gaussian integration preserves the Lipschitz and quadratic midpoint hypotheses required by the finite-dimensional induction.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianLogMarginal {n : ℕ} (F : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.log (∫ s : ℝ, Real.exp (F (gaussianCons s u)) ∂gaussianReal 0 1)

theorem gaussian_coordinate_slice_lipschitz {n : ℕ} {K : ℝ≥0}
    {F : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hF : LipschitzWith K F) (u : EuclideanSpace ℝ (Fin n)) :
    LipschitzWith K (fun s : ℝ => F (gaussianCons s u)) := by
  simpa only [mul_one] using hF.comp (gaussianCons_coordinate_isometry u).lipschitz

theorem gaussian_log_marginal_lipschitz {n : ℕ} {K : ℝ≥0}
    {F : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hF : LipschitzWith K F) :
    LipschitzWith K (gaussianLogMarginal F) := by
  have hInt (u : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun s : ℝ => Real.exp (F (gaussianCons s u))) (gaussianReal 0 1) :=
    gaussian_real_exp_integrable_lipschitz (gaussian_coordinate_slice_lipschitz hF u)
  have hMod (u v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
      |F (gaussianCons s u)-F (gaussianCons s v)| ≤ (K : ℝ)*dist u v := by
    have hh := hF.dist_le_mul (gaussianCons s u) (gaussianCons s v)
    rw [(gaussianCons_isometry s).dist_eq u v] at hh
    simpa only [Real.dist_eq] using hh
  simpa only [gaussianLogMarginal,logExpIntegral] using log_exp_integral_lipschitz hInt hMod

theorem gaussian_log_marginal_midpoint_bound {n : ℕ} {KF KG : ℝ≥0}
    {F G : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    {b : ℝ} (hCompare : ∀ z w, F z+G w ≤ b+(dist z w)^2/4)
    (u v : EuclideanSpace ℝ (Fin n)) :
    gaussianLogMarginal F u+gaussianLogMarginal G v ≤ b+(dist u v)^2/4 := by
  have hFs := gaussian_coordinate_slice_lipschitz hF u
  have hGs := gaussian_coordinate_slice_lipschitz hG v
  apply gaussian_real_midpoint_log_integral hFs.continuous hGs.continuous
    (gaussian_real_exp_integrable_lipschitz hFs) (gaussian_real_exp_integrable_lipschitz hGs)
  intro s t
  have hh := hCompare (gaussianCons s u) (gaussianCons t v)
  rw [gaussianCons_dist_sq] at hh
  linarith only [hh]

end ScalarMonotone.EndOfPaper
end
