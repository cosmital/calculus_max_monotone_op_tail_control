import EndOfPaper.Shortfall
import EndOfPaper.ScalarIntegration
import MonotoneOperators.ProbabilityBounds

/-!
The full finite-area mean-pivot theorem (prop:pivots). Finite extended area
first proves L1 integrability. The translated graph is maximal decreasing
and the survival comparison holds on its entire completed graph.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem maximal_decreasing_input_translate {β : Operator} (hβ : MaximalDecreasing β)
    (M : ℝ) : MaximalDecreasing (fun t => β (t-M)) := by
  refine ⟨increasing_iff_order.mpr ?_, ?_⟩
  · intro x u y v hu hv hxy
    change -u ∈ β (x-M) at hu
    change -v ∈ β (y-M) at hv
    have h := Decreasing.le_of_lt hβ.1 hu hv (by linarith : x-M < y-M)
    linarith
  · intro x u hc
    apply hβ.2
    have hb := compatible_iff_bounds.mp hc
    apply compatible_iff_bounds.mpr
    constructor
    · intro y v hv hyx
      have hv' : v ∈ negOut (fun t => β (t-M)) (y+M) := by
        simpa only [negOut, mem_setOf_eq, add_sub_cancel_right] using hv
      exact hb.1 hv' (by linarith)
    · intro y v hv hxy
      have hv' : v ∈ negOut (fun t => β (t-M)) (y+M) := by
        simpa only [negOut, mem_setOf_eq, add_sub_cancel_right] using hv
      exact hb.2 hv' (by linarith)

/-- Finite area of the actual operator envelope proves integrability before
the mean is used. The final comparison is the completed resolvent order and
holds at every translated fiber, not merely at positive scalar inputs. -/
theorem finite_operator_tail_area_mean_pivot {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (c : ℝ) {β : Operator} (hβ : MaximalDecreasing β)
    (hbound : DecLE (survival (Measure.map (fun ω => |X ω-c|) μ)) β)
    (hβ0 : ∀ t > 0, ∀ v ∈ β t, 0 ≤ v) {b : ℝ → ℝ}
    (hb : ∀ t > 0, b t ∈ β t)
    (hfinite : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b t)) < ∞) :
    let M : ℝ := ∫ t in Ioi (0 : ℝ), b t
    Integrable b (volume.restrict (Ioi (0 : ℝ))) ∧ Integrable X μ ∧
      |(∫ ω, X ω ∂μ)-c| ≤ M ∧
      MaximalDecreasing (fun t => β (t-M)) ∧
      DecLE (survival (Measure.map (fun ω => |X ω-(∫ ω, X ω ∂μ)|) μ))
        (fun t => β (t-M)) := by
  let Y : Ω → ℝ := fun ω => |X ω-c|
  have hY : Measurable Y := (hX.sub measurable_const).abs
  have hY0 : 0 ≤ᵐ[μ] Y := Eventually.of_forall (fun ω => abs_nonneg _)
  have hb0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hβ0 t ht (b t) (hb t ht)
  have hbm : AEMeasurable b (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
      (selection_antitoneOn hβ.1 hb)
  have hbi : Integrable b (volume.restrict (Ioi (0 : ℝ))) :=
    ⟨hbm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hb0).mpr hfinite⟩
  have htail := (survival_map_comparison_iff μ hY β).mp hbound
  have harea : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b t) := by
    apply expectation_le_tail_area μ hY.aemeasurable hY0
    intro t ht
    rw [← ofReal_measureReal (μ := μ) (s := {ω | t < Y ω})]
    exact ENNReal.ofReal_le_ofReal (htail (hb t ht))
  have hYi : Integrable Y μ :=
    ⟨hY.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hY0).mpr (harea.trans_lt hfinite)⟩
  have hcenter : Integrable (fun ω => X ω-c) μ :=
    hYi.mono' (hX.sub measurable_const).aestronglyMeasurable
      (Eventually.of_forall (fun ω => by simp [Y, Real.norm_eq_abs]))
  have hXi : Integrable X μ := by
    have h := hcenter.add (integrable_const c)
    change Integrable (fun ω => (X ω-c)+c) μ at h
    simpa only [sub_add_cancel] using h
  let M : ℝ := ∫ t in Ioi (0 : ℝ), b t
  have hM0 : 0 ≤ M := integral_nonneg_of_ae hb0
  have hEY : (∫ ω, Y ω ∂μ) ≤ M := by
    apply (ENNReal.ofReal_le_ofReal_iff hM0).mp
    rw [ofReal_integral_eq_lintegral_ofReal hYi hY0,
      ofReal_integral_eq_lintegral_ofReal hbi hb0]
    exact harea
  have hmc : |(∫ ω, X ω ∂μ)-c| ≤ M :=
    (mean_pivot_distance hXi c).trans hEY
  refine ⟨hbi, hXi, hmc, maximal_decreasing_input_translate hβ M, ?_⟩
  apply (survival_map_comparison_iff μ (hX.sub measurable_const).abs _).mpr
  intro t v hv
  have hsub : {ω | t < |X ω-(∫ ω, X ω ∂μ)|} ⊆ {ω | t-M < Y ω} := by
    intro ω hω
    change t < |X ω-(∫ ω, X ω ∂μ)| at hω
    have hp := pointwise_mean_pivot X (∫ ω, X ω ∂μ) c M hmc ω
    change t-M < |X ω-c|
    linarith
  exact (measureReal_mono hsub).trans (htail hv)

end ScalarMonotone.EndOfPaper
end
