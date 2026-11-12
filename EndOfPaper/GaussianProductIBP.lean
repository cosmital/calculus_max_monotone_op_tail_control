import EndOfPaper.GaussianProductIntegralSplit
import EndOfPaper.GaussianIntegrationByParts

/-!
Actual finite Gaussian integration by parts. All slice integrability is derived from Fubini and the global L1 hypotheses of this auxiliary identity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_product_first_integration_by_parts {n : ℕ}
    {f d : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hf : Measurable f) (hd : Measurable d)
    (hfd : ∀ u : EuclideanSpace ℝ (Fin n), ∀ s : ℝ,
      HasDerivAt (fun t => f (gaussianCons t u)) (d (gaussianCons s u)) s)
    (hfI : Integrable (fun z => f (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)))
    (hdI : Integrable (fun z => d (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)))
    (hxfI : Integrable (fun z => z 0*f (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1))) :
    (∫ z, z 0*f (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1)) =
      ∫ z, d (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure n) := by unfold gaussianProductMeasure; infer_instance
  have hxMeas : Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)) => z 0) :=
    (measurable_pi_apply 0).comp (EuclideanSpace.equiv (Fin (n+1)) ℝ).continuous.measurable
  have hxf : Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)) => z 0*f z) := hxMeas.mul hf
  have hFProd := (gaussian_split_integrable_iff hf).mpr hfI
  have hDProd := (gaussian_split_integrable_iff hd).mpr hdI
  have hXFProd := (gaussian_split_integrable_iff hxf).mpr hxfI
  change (∫ z, gaussianProductVector (n+1) z 0*f (gaussianProductVector (n+1) z)
    ∂gaussianProductMeasure (n+1)) = _
  rw [gaussian_product_integral_split hxf hxfI,gaussian_product_integral_split hd hdI]
  apply integral_congr_ae
  filter_upwards [hFProd.prod_left_ae,hDProd.prod_left_ae,hXFProd.prod_left_ae] with u hFu hDu hXFu
  have hh := gaussian_real_integration_by_parts (hfd (gaussianProductVector n u)) hFu hDu hXFu
  simpa only [gaussianSplitIntegrand,gaussianCons_zero] using hh

end ScalarMonotone.EndOfPaper
end
