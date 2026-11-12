import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
The sharp one-half independent-copy moment bound on a unit interval, including derived integrability.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem unit_interval_copy_rpow_bound {x y r : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hr : 1 ≤ r) : |x-y|^r ≤ x+y-2*(x*y) := by
  have hgap : |x-y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hy.1,hx.2]⟩
  apply (Real.rpow_le_self_of_le_one (abs_nonneg _) hgap hr).trans
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub]
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hx.2)]

theorem unit_interval_product_moment_le_half (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(ν.prod ν)) ≤ ENNReal.ofReal (1/2 : ℝ) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hX : Integrable (fun x : ℝ => x) ν := by
    apply (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable
    filter_upwards [hsupp] with x hx
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hFirst : Integrable (fun z : ℝ × ℝ => z.1) (ν.prod ν) := by
    simpa only [mul_one] using hX.mul_prod (integrable_const (1 : ℝ))
  have hSecond : Integrable (fun z : ℝ × ℝ => z.2) (ν.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hX
  have hMul : Integrable (fun z : ℝ × ℝ => z.1*z.2) (ν.prod ν) := hX.mul_prod hX
  have hSum : Integrable (fun z : ℝ × ℝ => z.1+z.2) (ν.prod ν) := hFirst.add hSecond
  have hG : Integrable (fun z : ℝ × ℝ => z.1+z.2-2*(z.1*z.2)) (ν.prod ν) :=
    hSum.sub (hMul.const_mul 2)
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1} :=
    (measurable_fst measurableSet_Icc).inter (measurable_snd measurableSet_Icc)
  have hPair : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae hset).mpr (hsupp.mono (fun x hx => hsupp.mono (fun y hy => ⟨hx,hy⟩)))
  have hDiff : Continuous (fun z : ℝ × ℝ => z.1-z.2) := continuous_fst.sub continuous_snd
  have hF : Measurable (fun z : ℝ × ℝ => |z.1-z.2|^r) :=
    ((Real.continuous_rpow_const hr0).comp hDiff.abs).measurable
  have hBound : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), |z.1-z.2|^r ≤ z.1+z.2-2*(z.1*z.2) :=
    hPair.mono (fun z hz => unit_interval_copy_rpow_bound hz.1 hz.2 hr)
  have hFi : Integrable (fun z : ℝ × ℝ => |z.1-z.2|^r) (ν.prod ν) := by
    apply hG.mono' hF.aestronglyMeasurable
    filter_upwards [hBound] with z hz
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)] using hz
  have hOne : (∫ z : ℝ × ℝ, z.1 ∂(ν.prod ν)) = ∫ x : ℝ, x ∂ν := by
    simpa using integral_prod_mul (μ := ν) (ν := ν) (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ))
  have hTwo : (∫ z : ℝ × ℝ, z.2 ∂(ν.prod ν)) = ∫ x : ℝ, x ∂ν := by
    simpa using integral_prod_mul (μ := ν) (ν := ν) (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x)
  have hBoth : (∫ z : ℝ × ℝ, z.1*z.2 ∂(ν.prod ν)) = (∫ x : ℝ, x ∂ν)*(∫ x : ℝ, x ∂ν) :=
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x)
  rw [← ofReal_integral_eq_lintegral_ofReal hFi
    (Eventually.of_forall (fun z : ℝ × ℝ => Real.rpow_nonneg (abs_nonneg (z.1-z.2)) r))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ z : ℝ × ℝ, z.1+z.2-2*(z.1*z.2) ∂(ν.prod ν) := integral_mono_ae hFi hG hBound
    _ = 2*(∫ x : ℝ, x ∂ν)-2*(∫ x : ℝ, x ∂ν)^2 := by
      rw [integral_sub hSum (hMul.const_mul 2),integral_add hFirst hSecond,
        integral_const_mul,hOne,hTwo,hBoth]
      ring
    _ ≤ 1/2 := by nlinarith [sq_nonneg ((∫ x : ℝ, x ∂ν)-1/2)]

end ScalarMonotone.EndOfPaper
end
