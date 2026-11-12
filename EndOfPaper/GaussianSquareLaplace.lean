import Mathlib.Probability.Distributions.Gaussian

/-!
Actual standard-Gaussian square Laplace integrals. These are ingredients for the Gaussian HS-norm bound, not an assumption of Gaussian concentration.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_square_exponential_density (t x : ℝ) :
    gaussianPDFReal 0 1 x*Real.exp (t*x^2) =
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(1/2-t)*x^2) := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,← Real.exp_add]
  have he : -(x^2)/2+t*x^2 = -(1/2-t)*x^2 := by ring
  rw [he]

theorem gaussian_square_exponential_integrable {t : ℝ} (ht : t < 1/2) :
    Integrable (fun x : ℝ => Real.exp (t*x^2)) (gaussianReal 0 1) := by
  have hw : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x*Real.exp (t*x^2)) volume := by
    simp_rw [gaussian_square_exponential_density]
    exact (integrable_exp_neg_mul_sq (by linarith : (0 : ℝ) < 1/2-t)).const_mul _
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all volume (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mpr
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hw

theorem gaussian_square_laplace_raw (t : ℝ) :
    (∫ x : ℝ, Real.exp (t*x^2) ∂gaussianReal 0 1) =
      (Real.sqrt (2*Real.pi))⁻¹*Real.sqrt (Real.pi/(1/2-t)) := by
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simp_rw [smul_eq_mul,gaussian_square_exponential_density]
  rw [integral_const_mul,integral_gaussian]

theorem gaussian_square_laplace {t : ℝ} (ht : t < 1/2) :
    (∫ x : ℝ, Real.exp (t*x^2) ∂gaussianReal 0 1) = (Real.sqrt (1-2*t))⁻¹ := by
  have hb : 0 < (1/2 : ℝ)-t := by linarith
  have ha : 0 < (1 : ℝ)-2*t := by linarith
  have hp : 0 < (2 : ℝ)*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hprod : Real.sqrt (Real.pi/(1/2-t))*Real.sqrt (1-2*t) = Real.sqrt (2*Real.pi) := by
    rw [← Real.sqrt_mul (div_nonneg Real.pi_pos.le hb.le)]
    congr 1
    field_simp [hb.ne']
    <;> ring
  rw [gaussian_square_laplace_raw]
  apply mul_right_cancel₀ (Real.sqrt_pos.mpr ha).ne'
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹*
        (Real.sqrt (Real.pi/(1/2-t))*Real.sqrt (1-2*t)) := by ring
    _ = 1 := by rw [hprod,inv_mul_cancel₀ (Real.sqrt_pos.mpr hp).ne']
    _ = _ := (inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne').symm

end ScalarMonotone.EndOfPaper
end
