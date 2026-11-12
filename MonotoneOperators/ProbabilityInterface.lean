import MonotoneOperators.Survival

/-!
# Measurability only on the probability interval

The selection may behave arbitrarily outside `(0,1)`. Only almost-everywhere
measurability for the restricted uniform measure is required.
-/

open Set MeasureTheory ProbabilityTheory

namespace ScalarMonotone

theorem tailQuantile_selection_law_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ → ℝ} (hq : AEMeasurable q unitUniform)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p) :
    Measure.map q unitUniform = μ := by
  letI : IsProbabilityMeasure (Measure.map q unitUniform) := isProbabilityMeasure_map hq
  have htail : ∀ t : ℝ, Measure.map q unitUniform (Ioi t) = μ (Ioi t) := by
    intro t
    rw [Measure.map_apply_of_aemeasurable hq measurableSet_Ioi, unitUniform,
      Measure.restrict_apply' measurableSet_Ioo]
    exact tailQuantile_selection_tail_volume μ hsel t
  apply Measure.ext_of_Iic
  intro t
  calc
    Measure.map q unitUniform (Iic t) = 1 - Measure.map q unitUniform (Ioi t) := by
      simpa only [compl_Ioi, measure_univ] using
        (measure_compl (μ := Measure.map q unitUniform) measurableSet_Ioi (measure_ne_top _ _))
    _ = 1 - μ (Ioi t) := by rw [htail t]
    _ = μ (Iic t) := by
      symm
      simpa only [compl_Ioi, measure_univ] using
        (measure_compl (μ := μ) measurableSet_Ioi (measure_ne_top _ _))

end ScalarMonotone
