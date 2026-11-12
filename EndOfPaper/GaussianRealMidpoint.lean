import EndOfPaper.GaussianSquareLaplace
import EndOfPaper.GaussianMidpoint
import EndOfPaper.MidpointPrekopaLeindler

/-!
The actual one-dimensional Gaussian midpoint log-integral inequality, derived from the proved Lebesgue midpoint inequality and Gaussian density.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_real_pdf_scalar (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(x^2)/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]

theorem gaussian_real_integrable_iff_weighted (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x*g x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simpa only [toReal_gaussianPDF,smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (g := g) (measurable_gaussianPDF 0 1)
      (ae_of_all volume (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x))))

theorem gaussian_real_midpoint_log_integral {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFI : Integrable (fun x => Real.exp (F x)) (gaussianReal 0 1))
    (hGI : Integrable (fun x => Real.exp (G x)) (gaussianReal 0 1)) {b : ℝ}
    (hCompare : ∀ x y : ℝ, F x+G y ≤ b+(x-y)^2/4) :
    Real.log (∫ x, Real.exp (F x) ∂gaussianReal 0 1)+
      Real.log (∫ x, Real.exp (G x) ∂gaussianReal 0 1) ≤ b := by
  let c := (Real.sqrt (2*Real.pi))⁻¹
  have hφ : Continuous (gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  have hφpos (x : ℝ) : 0 < gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x one_ne_zero
  have hFW : Integrable (fun x => Real.exp (F x)*gaussianPDFReal 0 1 x) volume := by
    simpa only [mul_comm] using (gaussian_real_integrable_iff_weighted _).mp hFI
  have hGW : Integrable (fun x => Real.exp (G x)*gaussianPDFReal 0 1 x) volume := by
    simpa only [mul_comm] using (gaussian_real_integrable_iff_weighted _).mp hGI
  have hHW : Integrable (fun x => Real.exp (b/2)*gaussianPDFReal 0 1 x) volume :=
    (integrable_gaussianPDFReal 0 1).const_mul _
  have hPoint (x y : ℝ) :
      Real.sqrt ((Real.exp (F x)*gaussianPDFReal 0 1 x)*(Real.exp (G y)*gaussianPDFReal 0 1 y)) ≤
        Real.exp (b/2)*gaussianPDFReal 0 1 ((x+y)/2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨(mul_pos (Real.exp_pos _) (hφpos _)).le,?_⟩
    have hEnergy : x^2/2+y^2/2 = ((x+y)/2)^2+(x-y)^2/4 := by
      have hh := gaussian_midpoint_energy x y
      simpa only [Real.norm_eq_abs,sq_abs,smul_eq_mul,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
    have hExp : Real.exp ((F x+(-(x^2)/2))+(G y+(-(y^2)/2))) ≤
        (Real.exp (b/2+(-(((x+y)/2)^2)/2)))^2 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith only [hCompare x y,hEnergy]
    have hLeft : (Real.exp (F x)*gaussianPDFReal 0 1 x)*(Real.exp (G y)*gaussianPDFReal 0 1 y) =
        c^2*Real.exp ((F x+(-(x^2)/2))+(G y+(-(y^2)/2))) := by
      rw [gaussian_real_pdf_scalar x,gaussian_real_pdf_scalar y]
      dsimp only [c]
      simp only [Real.exp_add]
      ring
    have hRight : (Real.exp (b/2)*gaussianPDFReal 0 1 ((x+y)/2))^2 =
        c^2*(Real.exp (b/2+(-(((x+y)/2)^2)/2)))^2 := by
      rw [gaussian_real_pdf_scalar]
      dsimp only [c]
      simp only [Real.exp_add]
      ring
    rw [hLeft,hRight]
    exact mul_le_mul_of_nonneg_left hExp (sq_nonneg c)
  have hFIeq : (∫ x : ℝ, Real.exp (F x)*gaussianPDFReal 0 1 x) =
      ∫ x, Real.exp (F x) ∂gaussianReal 0 1 := by
    rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
    simp only [smul_eq_mul,mul_comm]
  have hGIeq : (∫ x : ℝ, Real.exp (G x)*gaussianPDFReal 0 1 x) =
      ∫ x, Real.exp (G x) ∂gaussianReal 0 1 := by
    rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
    simp only [smul_eq_mul,mul_comm]
  have hHIeq : (∫ x : ℝ, Real.exp (b/2)*gaussianPDFReal 0 1 x) = Real.exp (b/2) := by
    rw [integral_const_mul,integral_gaussianPDFReal_eq_one 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0),mul_one]
  have hPL := midpoint_prekopa_leindler_real ((Real.continuous_exp.comp hF).mul hφ)
    (fun x => mul_pos (Real.exp_pos _) (hφpos x)) hFW ((Real.continuous_exp.comp hG).mul hφ)
    (fun x => mul_pos (Real.exp_pos _) (hφpos x)) hGW hHW hPoint
  simp only [Function.comp_apply] at hPL
  rw [hFIeq,hGIeq,hHIeq] at hPL
  have hPosF := integral_exp_pos hFI
  have hPosG := integral_exp_pos hGI
  have hSq := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos (b/2)).le).mpr hPL
  have hExpSq : (Real.exp (b/2))^2 = Real.exp b := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [Real.sq_sqrt (mul_nonneg hPosF.le hPosG.le),hExpSq] at hSq
  have hLog := Real.log_le_log (mul_pos hPosF hPosG) hSq
  rwa [Real.log_mul hPosF.ne' hPosG.ne',Real.log_exp] at hLog

end ScalarMonotone.EndOfPaper
end
