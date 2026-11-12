import MonotoneOperators.ProbabilityBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Original-space strict-tail right limits, exponential
perturbations and reciprocal-error removal. The logarithmic
probability budget includes zero area and zero threshold.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem strict_tail_bound_of_right_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {t a : ℝ} (hb : ∀ u, t < u → μ.real {ω | u < X ω} ≤ a) :
    μ.real {ω | t < X ω} ≤ a := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  have he (r : ℝ) : (Measure.map X μ).real (Ioi r) = μ.real {ω | r < X ω} := by
    rw [measureReal_def,Measure.map_apply hX measurableSet_Ioi]
    rfl
  rw [← he t]
  apply le_of_tendsto (survival_strict_tail_right_continuous (Measure.map X μ) t)
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [he]
  exact hb u hu

theorem strict_tail_bound_of_exponential_perturbations {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {t a : ℝ} (ht : 0 ≤ t)
    (hb : ∀ ε : ℝ, 0 < ε → μ.real {ω | t*Real.exp ε < X ω} ≤ a) :
    μ.real {ω | t < X ω} ≤ a := by
  by_cases ht0 : t = 0
  · simpa only [ht0,zero_mul] using hb 1 zero_lt_one
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    apply strict_tail_bound_of_right_bounds hX
    intro u hu
    have hup : 0 < u := htp.trans hu
    have hε : 0 < Real.log (u/t) := Real.log_pos ((one_lt_div htp).mpr hu)
    have he : t*Real.exp (Real.log (u/t)) = u := by
      rw [Real.exp_log (div_pos hup htp)]
      field_simp [htp.ne']
    simpa only [he] using hb (Real.log (u/t)) hε

theorem le_of_forall_positive_div_error {x a m : ℝ} (hm : 0 ≤ m)
    (hb : ∀ s : ℝ, 0 < s → x ≤ a+m/s) : x ≤ a := by
  by_contra hxa
  have hgap : 0 < x-a := sub_pos.mpr (lt_of_not_ge hxa)
  let s := (m+1)/(x-a)
  have hs : 0 < s := div_pos (by linarith) hgap
  have he : (x-a)*s = m+1 := by
    dsimp [s]
    field_simp [hgap.ne']
  have herr : m/s < x-a := (div_lt_iff₀ hs).mpr (by rw [he]; linarith)
  linarith [hb s hs]

theorem logarithmic_tail_budget {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {C t a b I : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (hb : 0 < b) (hI : 0 ≤ I)
    (hbound : ∀ s : ℝ, 0 < s → μ.real {ω | C*Real.exp s*t < X ω} ≤ a+2*I/s) :
    μ.real {ω | C*Real.exp (I/b)*t < X ω} ≤ a+2*b := by
  by_cases hI0 : I = 0
  · have htail : μ.real {ω | C*t < X ω} ≤ a := by
      apply strict_tail_bound_of_exponential_perturbations hX (mul_nonneg hC ht)
      intro ε hε
      have he : C*Real.exp ε*t = (C*t)*Real.exp ε := by ring
      simpa only [hI0,mul_zero,zero_div,add_zero,he] using hbound ε hε
    simpa only [hI0,zero_div,Real.exp_zero,mul_one] using
      htail.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) hb.le))
  · have hIp : 0 < I := lt_of_le_of_ne hI (Ne.symm hI0)
    have hs : 0 < I/b := div_pos hIp hb
    have he : 2*I/(I/b) = 2*b := by
      field_simp [hIp.ne',hb.ne']
      <;> ring
    simpa only [he] using hbound (I/b) hs

end ScalarMonotone.EndOfPaper
end
