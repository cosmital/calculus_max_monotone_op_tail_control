import EndOfPaper.OneSidedCopyTail
import EndOfPaper.EndpointSymmetry

/-!
The coefficient-one median union estimate from the original joint-law baseline, without independence between the two norm observations.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem max_median_control_strict_tail {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {q : Operator}
    (hq : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    {K : ℝ≥0} (hK : 0 < (K : ℝ)) {f g : E → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g)
    {mf mg a t : ℝ} (hmf : IsRealMedian (f ∘ Z) μ mf)
    (hmg : IsRealMedian (g ∘ Z) μ mg) (ht : t ∈ q a) (ht0 : 0 ≤ t) :
    μ.real {ω | max mf mg+(K : ℝ)*t < max (f (Z ω)) (g (Z ω))} ≤ 2*a := by
  have hfm : Measurable f := hf.continuous.measurable
  have hgm : Measurable g := hg.continuous.measurable
  have hkt : 0 ≤ (K : ℝ)*t := mul_nonneg hK.le ht0
  have hft := (upper_median_independent_copy_tail (hfm.comp hZ) (hfm.comp hZ')
    (hi.comp hfm hfm) (he.comp hfm) hmf hkt).trans
    (scaled_lipschitz_tail_of_quantile_control hZ hZ' hq ht hK hf)
  have hgt := (upper_median_independent_copy_tail (hgm.comp hZ) (hgm.comp hZ')
    (hi.comp hgm hgm) (he.comp hgm) hmg hkt).trans
    (scaled_lipschitz_tail_of_quantile_control hZ hZ' hq ht hK hg)
  have hsub : {ω | max mf mg+(K : ℝ)*t < max (f (Z ω)) (g (Z ω))} ⊆
      {ω | mf+(K : ℝ)*t < f (Z ω)} ∪ {ω | mg+(K : ℝ)*t < g (Z ω)} := by
    intro ω hω
    change max mf mg+(K : ℝ)*t < max (f (Z ω)) (g (Z ω)) at hω
    rcases lt_max_iff.mp hω with hfω | hgω
    · exact Or.inl (lt_of_le_of_lt (add_le_add_right (le_max_left mf mg) _) hfω)
    · exact Or.inr (lt_of_le_of_lt (add_le_add_right (le_max_right mf mg) _) hgω)
  calc
    _ ≤ μ.real ({ω | mf+(K : ℝ)*t < f (Z ω)} ∪ {ω | mg+(K : ℝ)*t < g (Z ω)}) :=
      measureReal_mono hsub
    _ ≤ μ.real {ω | mf+(K : ℝ)*t < f (Z ω)}+
        μ.real {ω | mg+(K : ℝ)*t < g (Z ω)} := measureReal_union_le _ _
    _ ≤ a+a := add_le_add hft hgt
    _ = 2*a := by ring

end ScalarMonotone.EndOfPaper
end
