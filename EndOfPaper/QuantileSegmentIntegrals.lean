import EndOfPaper.HardyScalar
import MonotoneOperators.Survival

/-!
Prefix integrability, top-segment L1, and exact top-segment
means and finite averages, all derived from the full uniform-law L1
hypothesis before using the strong law.
-/

open Set MeasureTheory
open scoped BigOperators Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem uniform_prefix_integrable {q : ℝ → ℝ} (hi : Integrable q unitUniform)
    {p : ℝ} (hp : p ∈ Ioo 0 1) : IntervalIntegrable q volume 0 p := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.1.le).mpr
  have hsub : Ioo (0 : ℝ) p ⊆ Ioo (0 : ℝ) 1 :=
    fun u hu => ⟨hu.1, hu.2.trans hp.2⟩
  exact hi.mono_measure (Measure.restrict_mono hsub le_rfl)

theorem uniform_top_segment_integrable {q : ℝ → ℝ} (hi : Integrable q unitUniform)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    Integrable (fun u : ℝ => q (p*u)) unitUniform := by
  have hcomp := hardyScalar_dilation_integrable hp.1 (uniform_prefix_integrable hi hp)
  change Integrable (fun u : ℝ => q (p*u)) (volume.restrict (Ioo 0 1))
  simpa only [mul_comm] using
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (zero_le_one : (0 : ℝ) ≤ 1)).mp hcomp

theorem uniform_top_segment_mean (q : ℝ → ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ u, q (p*u) ∂unitUniform) = hardyScalar q p := by
  rw [hardyScalar_dilation q hp, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  simp only [unitUniform, mul_comm]

theorem uniform_top_average_integrable {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hi : ∀ i, Integrable (q i) unitUniform) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    Integrable (fun u : ℝ => (∑ i, q i (p*u))/(n : ℝ)) unitUniform :=
  (integrable_finset_sum _ (fun i _ => uniform_top_segment_integrable (hi i) hp)).div_const _

theorem uniform_top_average_mean {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hi : ∀ i, Integrable (q i) unitUniform) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    (∫ u, (∑ i, q i (p*u))/(n : ℝ) ∂unitUniform) =
      (∑ i, hardyScalar (q i) p)/(n : ℝ) := by
  rw [integral_div, integral_finset_sum _
    (fun i _ => uniform_top_segment_integrable (hi i) hp)]
  simp_rw [uniform_top_segment_mean _ hp.1]

end ScalarMonotone.EndOfPaper
end
