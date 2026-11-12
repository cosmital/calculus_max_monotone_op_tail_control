import EndOfPaper.GaussianRealMidpoint
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Actual scalar Gaussian integration by parts, with integrability conditions local to this auxiliary identity. The density derivative is proved explicitly.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_real_pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have hExponent : HasDerivAt (fun y : ℝ => -(y^2)/2) (-x) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const 2) using 1 <;> simp only [id_eq] <;> ring
  have hh := hExponent.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  have hFun : gaussianPDFReal 0 1 = fun y : ℝ => (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(y^2)/2) :=
    funext gaussian_real_pdf_scalar
  rw [hFun]
  convert hh using 1 <;> ring

theorem gaussian_real_integral_weighted (g : ℝ → ℝ) :
    (∫ x, g x ∂gaussianReal 0 1) = ∫ x : ℝ, g x*gaussianPDFReal 0 1 x := by
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul,mul_comm]

theorem gaussian_real_integration_by_parts {f d : ℝ → ℝ}
    (hfd : ∀ x, HasDerivAt f (d x) x)
    (hf : Integrable f (gaussianReal 0 1)) (hd : Integrable d (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, d x ∂gaussianReal 0 1 := by
  have hF : Integrable (fun x => f x*gaussianPDFReal 0 1 x) volume := by
    simpa only [mul_comm] using (gaussian_real_integrable_iff_weighted f).mp hf
  have hD : Integrable (fun x => d x*gaussianPDFReal 0 1 x) volume := by
    simpa only [mul_comm] using (gaussian_real_integrable_iff_weighted d).mp hd
  have hXF : Integrable (fun x => f x*(-x*gaussianPDFReal 0 1 x)) volume := by
    convert ((gaussian_real_integrable_iff_weighted (fun x => x*f x)).mp hxf).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable hfd gaussian_real_pdf_hasDerivAt hXF hD hF
  have hLeft : (∫ x : ℝ, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, x*f x ∂gaussianReal 0 1) := by
    rw [gaussian_real_integral_weighted,← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hRight : (∫ x : ℝ, d x*gaussianPDFReal 0 1 x) = ∫ x, d x ∂gaussianReal 0 1 :=
    (gaussian_real_integral_weighted d).symm
  rw [hLeft,hRight] at hh
  exact neg_injective hh

end ScalarMonotone.EndOfPaper
end
