import EndOfPaper.EndpointSymmetry

/-!
Zero prescribed quantile control implies almost-sure
nonpositivity and zero Lipschitz copy differences. Positive
Lipschitz scaling and arbitrary original spaces are retained.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem eq_zero_of_nonnegative_unit_interval_bounds {x : ℝ} (hx : 0 ≤ x)
    (hb : ∀ p ∈ Ioo (0 : ℝ) 1, x ≤ p) : x = 0 := by
  by_contra hx0
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  let p := min (x/2) (1/2 : ℝ)
  have hp0 : 0 < p := lt_min (by linarith) (by norm_num)
  have hp1 : p < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hpx : p < x := (min_le_left _ _).trans_lt (by linarith)
  exact (not_lt_of_ge (hb p ⟨hp0,hp1⟩)) hpx

theorem ae_nonpositive_of_unit_interval_zero_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hb : ∀ p ∈ Ioo (0 : ℝ) 1, μ.real {ω | 0 < X ω} ≤ p) :
    ∀ᵐ ω ∂μ, X ω ≤ 0 := by
  have hp := eq_zero_of_nonnegative_unit_interval_bounds measureReal_nonneg hb
  have hD : μ {ω | 0 < X ω} = 0 := (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hp
  exact ae_iff.mpr (by simpa only [not_le] using hD)

theorem ae_nonpositive_of_quantile_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {q : Operator} (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, (0 : ℝ) ∈ q p) : ∀ᵐ ω ∂μ, X ω ≤ 0 := by
  apply ae_nonpositive_of_unit_interval_zero_tail_bounds
  intro p hp
  exact quantile_comparison_strict_tail hX hQ (hq0 p hp)

theorem lipschitz_difference_zero_of_quantile_zero {Ω E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') {q : Operator}
    (hcontrol : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, (0 : ℝ) ∈ q p)
    {K : ℝ≥0} (hK : 0 < (K : ℝ)) {f : E → ℝ} (hf : LipschitzWith K f) :
    (fun ω => f (Z ω)) =ᵐ[μ] (fun ω => f (Z' ω)) := by
  have ha : ∀ᵐ ω ∂μ, |f (Z ω)-f (Z' ω)| ≤ 0 := by
    apply ae_nonpositive_of_unit_interval_zero_tail_bounds
    intro p hp
    simpa only [mul_zero] using
      scaled_lipschitz_tail_of_quantile_control hZ hZ' hcontrol (hq0 p hp) hK hf
  filter_upwards [ha] with ω hω
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hω)

end ScalarMonotone.EndOfPaper
end
