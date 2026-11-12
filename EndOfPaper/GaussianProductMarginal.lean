import EndOfPaper.GaussianProductMeasure
import EndOfPaper.GaussianCoordinateMarginal
import Mathlib.MeasureTheory.Integral.Prod

/-!
The exact Fubini identity for actual finite product Gaussian measures.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianSplitMeasurableEquiv (n : ℕ) :
    (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0

theorem gaussian_split_measure_preserving (n : ℕ) :
    MeasurePreserving (gaussianSplitMeasurableEquiv n) (gaussianProductMeasure (n+1))
      ((gaussianReal 0 1).prod (gaussianProductMeasure n)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0

theorem gaussian_split_vector {n : ℕ} (z : Fin (n+1) → ℝ) :
    gaussianProductVector (n+1) z =
      gaussianCons ((gaussianSplitMeasurableEquiv n z).1)
        (gaussianProductVector n ((gaussianSplitMeasurableEquiv n z).2)) := by
  ext i
  exact Fin.cases (by rfl) (fun j => by rfl) i

theorem gaussianExpIntegral_marginal {n : ℕ} {K : ℝ≥0}
    {F : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hF : LipschitzWith K F) :
    gaussianExpIntegral F = gaussianExpIntegral (gaussianLogMarginal F) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure n) := by unfold gaussianProductMeasure; infer_instance
  let e := gaussianSplitMeasurableEquiv n
  let h : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => Real.exp (F (gaussianProductVector (n+1) (e.symm p)))
  have hMP : MeasurePreserving e (gaussianProductMeasure (n+1))
      ((gaussianReal 0 1).prod (gaussianProductMeasure n)) := gaussian_split_measure_preserving n
  have hMeas : Measurable h :=
    (hF.continuous.measurable.comp ((gaussian_product_vector_measurable (n+1)).comp e.symm.measurable)).exp
  have hInt : Integrable h ((gaussianReal 0 1).prod (gaussianProductMeasure n)) := by
    rw [← hMP.map_eq]
    apply (integrable_map_measure hMeas.aestronglyMeasurable e.measurable.aemeasurable).mpr
    simpa only [h,Function.comp_def,MeasurableEquiv.symm_apply_apply] using gaussian_product_exp_integrable hF
  have hPair (s : ℝ) (u : Fin n → ℝ) :
      h (s,u) = Real.exp (F (gaussianCons s (gaussianProductVector n u))) := by
    dsimp only [h]
    congr 2
    simpa only [MeasurableEquiv.apply_symm_apply] using gaussian_split_vector (e.symm (s,u))
  calc
    gaussianExpIntegral F = ∫ p, h p ∂(gaussianReal 0 1).prod (gaussianProductMeasure n) := by
      simpa only [gaussianExpIntegral,h,MeasurableEquiv.symm_apply_apply] using hMP.integral_comp' h
    _ = ∫ u, (∫ s, h (s,u) ∂gaussianReal 0 1) ∂gaussianProductMeasure n := integral_prod_symm h hInt
    _ = gaussianExpIntegral (gaussianLogMarginal F) := by
      unfold gaussianExpIntegral gaussianLogMarginal
      apply integral_congr_ae
      filter_upwards [] with u
      have hSlice := gaussian_real_exp_integrable_lipschitz
        (gaussian_coordinate_slice_lipschitz hF (gaussianProductVector n u))
      rw [Real.exp_log (integral_exp_pos hSlice)]
      exact integral_congr_ae (ae_of_all _ (fun s => hPair s u))

end ScalarMonotone.EndOfPaper
end
