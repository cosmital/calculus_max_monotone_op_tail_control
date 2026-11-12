import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
The exact extended CDF representation of the independent-copy absolute moment, with arbitrary atoms and infinite expectations.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def copyCrossingIndicator (z : ℝ × ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Ico z.1 z.2).indicator (fun _ => 1) t+(Ico z.2 z.1).indicator (fun _ => 1) t

theorem copyCrossingIndicator_measurable :
    Measurable (fun p : (ℝ × ℝ) × ℝ => copyCrossingIndicator p.1 p.2) := by
  have hA : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 ≤ p.2 ∧ p.2 < p.1.2} :=
    (measurableSet_le measurable_fst.fst measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.snd)
  have hB : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.2 ≤ p.2 ∧ p.2 < p.1.1} :=
    (measurableSet_le measurable_fst.snd measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.fst)
  exact (measurable_const.indicator hA).add (measurable_const.indicator hB)

theorem copyCrossingIndicator_integral (z : ℝ × ℝ) :
    (∫⁻ t : ℝ, copyCrossingIndicator z t) = ENNReal.ofReal |z.1-z.2| := by
  have hA : Measurable ((Ico z.1 z.2).indicator (fun _ : ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_Ico
  simp only [copyCrossingIndicator]
  rw [lintegral_add_left hA _,lintegral_indicator_const measurableSet_Ico,
    lintegral_indicator_const measurableSet_Ico]
  simp only [one_mul,Real.volume_Ico]
  rcases le_total z.1 z.2 with h | h
  · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr h),add_zero,
      abs_of_nonpos (sub_nonpos.mpr h),neg_sub]
  · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr h),zero_add,
      abs_of_nonneg (sub_nonneg.mpr h)]

theorem copyCrossingIndicator_pair_integral (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    (∫⁻ z : ℝ × ℝ, copyCrossingIndicator z t ∂(ν.prod ν)) =
      ν (Iic t)*ν (Ioi t)+ν (Ioi t)*ν (Iic t) := by
  have hA : Measurable ((Iic t ×ˢ Ioi t).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_Iic.prod measurableSet_Ioi)
  calc
    _ = ∫⁻ z : ℝ × ℝ, (Iic t ×ˢ Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) z+
        (Ioi t ×ˢ Iic t).indicator (fun _ => (1 : ℝ≥0∞)) z ∂(ν.prod ν) := by
      apply lintegral_congr
      intro z
      simp only [copyCrossingIndicator,Set.indicator,mem_Ico,mem_prod,mem_Iic,mem_Ioi,and_comm]
    _ = _ := by
      rw [lintegral_add_left hA _,lintegral_indicator_const (measurableSet_Iic.prod measurableSet_Ioi),
        lintegral_indicator_const (measurableSet_Ioi.prod measurableSet_Iic)]
      simp only [one_mul,Measure.prod_prod]

theorem copy_moment_cdf_extended (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1-z.2| ∂(ν.prod ν)) =
      ∫⁻ t : ℝ, ν (Iic t)*ν (Ioi t)+ν (Ioi t)*ν (Iic t) := by
  calc
    _ = ∫⁻ z : ℝ × ℝ, ∫⁻ t : ℝ, copyCrossingIndicator z t ∂(volume : Measure ℝ) ∂(ν.prod ν) := by
      apply lintegral_congr
      intro z
      exact (copyCrossingIndicator_integral z).symm
    _ = ∫⁻ t : ℝ, ∫⁻ z : ℝ × ℝ, copyCrossingIndicator z t ∂(ν.prod ν) ∂(volume : Measure ℝ) :=
      lintegral_lintegral_swap copyCrossingIndicator_measurable.aemeasurable
    _ = _ := lintegral_congr (fun t => copyCrossingIndicator_pair_integral ν t)

end ScalarMonotone.EndOfPaper
end
