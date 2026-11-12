import EndOfPaper.GaussianSquareSumLaplace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Gaussian exponential integrability for every finite Lipschitz constant, including zero, needed for repeated one-coordinate marginal integration.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem lipschitz_general_exponential_majorant {E : Type*} [NormedAddCommGroup E]
    {K : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith K f) (x : E) :
    Real.exp (f x) ≤ Real.exp (|f 0| + (K : ℝ)^2)*Real.exp ((1/4 : ℝ)*‖x‖^2) := by
  have hLip : |f x-f 0| ≤ (K : ℝ)*‖x‖ := by
    simpa only [Real.dist_eq,dist_zero_right] using hf.dist_le_mul x 0
  have hBound : f x ≤ |f 0| + (K : ℝ)*‖x‖ := by
    have hh := (abs_le.mp hLip).2
    linarith [le_abs_self (f 0)]
  have hQuad : f x ≤ |f 0| + (K : ℝ)^2+(1/4 : ℝ)*‖x‖^2 := by
    nlinarith [sq_nonneg (‖x‖/2-(K : ℝ))]
  exact (Real.exp_le_exp.mpr hQuad).trans_eq (Real.exp_add _ _)

theorem gaussian_real_exp_integrable_lipschitz {K : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith K f) :
    Integrable (fun x : ℝ => Real.exp (f x)) (gaussianReal 0 1) := by
  have hi := gaussian_square_exponential_integrable (by norm_num : (1/4 : ℝ) < 1/2)
  have hm : Measurable (fun x : ℝ => Real.exp (f x)) := hf.continuous.measurable.exp
  apply (hi.const_mul (Real.exp (|f 0| + (K : ℝ)^2))).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [Real.norm_eq_abs,sq_abs] using lipschitz_general_exponential_majorant hf x

theorem gaussian_exp_integrable_lipschitz {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {K : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith K f) :
    Integrable (fun ω => Real.exp (f (X ω))) μ := by
  have hsq (ω : Ω) : ‖X ω‖^2 = ∑ i, (X ω i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  have hQ := (gaussian_square_sum_laplace hi hm hLaw (by norm_num : (1/4 : ℝ) < 1/2)).1
  have hNorm : Integrable (fun ω => Real.exp ((1/4 : ℝ)*‖X ω‖^2)) μ := by
    simpa only [hsq] using hQ
  have hMeas : Measurable (fun ω => Real.exp (f (X ω))) := (hf.continuous.measurable.comp hX).exp
  apply (hNorm.const_mul (Real.exp (|f 0| + (K : ℝ)^2))).mono' hMeas.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact lipschitz_general_exponential_majorant hf (X ω)

end ScalarMonotone.EndOfPaper
end
