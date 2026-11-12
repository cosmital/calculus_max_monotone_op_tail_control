import EndOfPaper.GaussianProductMarginal

/-!
Genuine Gaussian product Fubini for general integrable observations, including the slice integrability needed for integration by parts.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianSplitIntegrand {n : ℕ} (g : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (p : ℝ × (Fin n → ℝ)) : ℝ := g (gaussianCons p.1 (gaussianProductVector n p.2))

theorem gaussian_split_integrand_representation {n : ℕ}
    (g : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (p : ℝ × (Fin n → ℝ)) :
    gaussianSplitIntegrand g p =
      g (gaussianProductVector (n+1) ((gaussianSplitMeasurableEquiv n).symm p)) := by
  have hh := gaussian_split_vector ((gaussianSplitMeasurableEquiv n).symm p)
  simp only [MeasurableEquiv.apply_symm_apply] at hh
  exact (congrArg g hh).symm

theorem gaussian_split_integrand_measurable {n : ℕ}
    {g : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hg : Measurable g) :
    Measurable (gaussianSplitIntegrand g) := by
  have heq : gaussianSplitIntegrand g = fun p =>
      g (gaussianProductVector (n+1) ((gaussianSplitMeasurableEquiv n).symm p)) :=
    funext (gaussian_split_integrand_representation g)
  rw [heq]
  exact hg.comp ((gaussian_product_vector_measurable (n+1)).comp (gaussianSplitMeasurableEquiv n).symm.measurable)

theorem gaussian_split_integrable_iff {n : ℕ}
    {g : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hg : Measurable g) :
    Integrable (gaussianSplitIntegrand g) ((gaussianReal 0 1).prod (gaussianProductMeasure n)) ↔
      Integrable (fun z => g (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)) := by
  rw [← (gaussian_split_measure_preserving n).map_eq]
  have hh := integrable_map_measure (μ := gaussianProductMeasure (n+1))
    (gaussian_split_integrand_measurable hg).aestronglyMeasurable
    (gaussianSplitMeasurableEquiv n).measurable.aemeasurable
  simpa only [Function.comp_def,gaussian_split_integrand_representation,MeasurableEquiv.symm_apply_apply] using hh

theorem gaussian_product_integral_split {n : ℕ}
    {g : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hg : Measurable g)
    (hI : Integrable (fun z => g (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1))) :
    (∫ z, g (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1)) =
      ∫ u, (∫ s, g (gaussianCons s (gaussianProductVector n u)) ∂gaussianReal 0 1) ∂gaussianProductMeasure n := by
  letI : IsProbabilityMeasure (gaussianProductMeasure n) := by unfold gaussianProductMeasure; infer_instance
  have hProd := (gaussian_split_integrable_iff hg).mpr hI
  calc
    _ = ∫ p, gaussianSplitIntegrand g p ∂(gaussianReal 0 1).prod (gaussianProductMeasure n) := by
      have hh := (gaussian_split_measure_preserving n).integral_comp' (gaussianSplitIntegrand g)
      simpa only [gaussian_split_integrand_representation,MeasurableEquiv.symm_apply_apply] using hh
    _ = _ := integral_prod_symm (gaussianSplitIntegrand g) hProd

end ScalarMonotone.EndOfPaper
end
