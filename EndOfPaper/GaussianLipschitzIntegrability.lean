import EndOfPaper.GaussianNormMedian

/-!
Actual Gaussian exponential integrability of every Lipschitz observation, derived from the square-Laplace formula rather than assumed as an input.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem lipschitz_exponential_quadratic_majorant {E : Type*} [NormedAddCommGroup E]
    {f : E → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) (x : E) :
    Real.exp (a*f x) ≤ Real.exp (|a| * |f 0| + a^2)*Real.exp ((1/4 : ℝ)*‖x‖^2) := by
  have hLip : |f x-f 0| ≤ ‖x‖ := by
    simpa only [Real.dist_eq,dist_zero_right,NNReal.coe_one,one_mul] using hf.dist_le_mul x 0
  have hfabs : |f x| ≤ |f 0| + ‖x‖ := by
    calc
      _ = |(f x-f 0)+f 0| := by congr 1; ring
      _ ≤ |f x-f 0| + |f 0| := abs_add _ _
      _ ≤ _ := by linarith only [hLip]
  have hlin : a*f x ≤ |a| * (|f 0| + ‖x‖) :=
    (le_abs_self (a*f x)).trans ((by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hfabs (abs_nonneg a)))
  have hquad : a*f x ≤ |a| * |f 0| + a^2+(1/4 : ℝ)*‖x‖^2 := by
    nlinarith [sq_nonneg (‖x‖/2-|a|),sq_abs a]
  exact (Real.exp_le_exp.mpr hquad).trans_eq (Real.exp_add _ _)

theorem gaussian_lipschitz_exponential_integrable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) :
    Integrable (fun ω => Real.exp (a*f (X ω))) μ := by
  have hsq (ω : Ω) : ‖X ω‖^2 = ∑ i, (X ω i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  have hInt := (gaussian_square_sum_laplace hi hm hLaw (by norm_num : (1/4 : ℝ) < 1/2)).1
  have hNorm : Integrable (fun ω => Real.exp ((1/4 : ℝ)*‖X ω‖^2)) μ := by
    simpa only [hsq] using hInt
  have hmeas : Measurable (fun ω => Real.exp (a*f (X ω))) := by
    exact (measurable_const.mul (hf.continuous.measurable.comp hX)).exp
  apply (hNorm.const_mul (Real.exp (|a| * |f 0| + a^2))).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact lipschitz_exponential_quadratic_majorant hf a (X ω)

end ScalarMonotone.EndOfPaper
end
