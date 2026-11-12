import EndOfPaper.IndependentCopyTails
import EndOfPaper.ReplicationNecessity

/-!
Exact positive scaling of original-space medians and whole centered quantile graphs.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem isRealMedian_div_positive {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {m c : ℝ} (hm : IsRealMedian X μ m) (hc : 0 < c) :
    IsRealMedian (fun ω => X ω/c) μ (m/c) := by
  have hd (a b : ℝ) : a/c ≤ b/c ↔ a ≤ b := by
    constructor
    · intro h
      have hh := mul_le_mul_of_nonneg_right h hc.le
      simpa only [div_mul_cancel₀ _ hc.ne'] using hh
    · intro h
      exact div_le_div_of_nonneg_right h hc.le
  constructor
  · simpa only [hd] using hm.1
  · simpa only [hd] using hm.2

theorem tailQuantile_random_positive_scale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) {c : ℝ} (hc : 0 < c) :
    tailQuantile (Measure.map (fun ω => c*X ω) μ) =
      outputScale c (tailQuantile (Measure.map X μ)) := by
  change tailQuantile (Measure.map ((fun x : ℝ => c*x) ∘ X) μ) = _
  rw [← Measure.map_map (by fun_prop) hX,tailQuantile_positive_smul _ hc]

theorem centered_quantile_positive_normalization {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : Measurable X) (m : ℝ) {c : ℝ} (hc : 0 < c) :
    tailQuantile (Measure.map (fun ω => |X ω-m|) μ) =
      outputScale c (tailQuantile (Measure.map (fun ω => |X ω/c-m/c|) μ)) := by
  have he : (fun ω => c*|X ω/c-m/c|) = (fun ω => |X ω-m|) := by
    funext ω
    rw [← sub_div,abs_div,abs_of_pos hc,← mul_div_assoc]
    apply (div_eq_iff hc.ne').mpr
    ring
  rw [← tailQuantile_random_positive_scale ((hX.div_const c).sub_const (m/c)).abs hc,he]

end ScalarMonotone.EndOfPaper
end
