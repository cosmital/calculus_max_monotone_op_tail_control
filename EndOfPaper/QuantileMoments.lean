import EndOfPaper.Moments
import MonotoneOperators.ProbabilityInterface
import MonotoneOperators.ProbabilityBounds
import EndOfPaper.ScalarIntegration

/-!
Extended moment and quantile identities (cor:moments). Arbitrary atomic laws,
arbitrary selections and infinite ENNReal integrals are retained. Quantile
selection measurability is derived on (0,1), not imposed as an extra hypothesis.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- Every nonnegative measurable expression transfers through any quantile
selection. Infinite integrals and arbitrary atomic laws are retained. -/
theorem quantile_selection_lintegral_comp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ → ℝ} (hq : AEMeasurable q unitUniform)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p)
    (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ x, ψ x ∂μ) = ∫⁻ p in Ioo (0 : ℝ) 1, ψ (q p) := by
  calc
    _ = ∫⁻ x, ψ x ∂Measure.map q unitUniform := by
      rw [tailQuantile_selection_law_ae μ hq hsel]
    _ = ∫⁻ p, ψ (q p) ∂unitUniform := lintegral_map' hψ.aemeasurable hq
    _ = _ := rfl

theorem randomVariable_quantile_lintegral_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    {q : ℝ → ℝ} (hq : AEMeasurable q unitUniform)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile (Measure.map Y μ) p)
    (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ ω, ψ (Y ω) ∂μ) = ∫⁻ p in Ioo (0 : ℝ) 1, ψ (q p) := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  calc
    _ = ∫⁻ x, ψ x ∂Measure.map Y μ := (lintegral_map hψ hY).symm
    _ = _ := quantile_selection_lintegral_comp (Measure.map Y μ) hq hsel ψ hψ

/-- Factor the positive real exponent out of the extended tail integral. -/
theorem moment_tail_area_factored {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1) * μ.real {ω | t < Y ω}) := by
  rw [moment_tail_area μ hY hY0 hr,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    ofReal_measureReal]
  ac_rfl

/-- The ordinary strict tail is a selection of the completed survival graph,
including at atoms of the original law. -/
theorem strict_tail_survival_selection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y) :
    SelectionOn (survival (Measure.map Y μ)) univ
      (fun t => μ.real {ω | t < Y ω}) := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  intro t _
  have h := survival_lower_mem (Measure.map Y μ) t
  simpa only [map_measureReal_apply hY measurableSet_Ioi, preimage_setOf_eq] using h

/-- Any survival selection gives the same extended moment integral. The
atomlessness used for selection independence is Lebesgue atomlessness in t;
the probability law of Y may have arbitrary atoms. -/
theorem moment_tail_selection_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r) {s : ℝ → ℝ}
    (hs : SelectionOn (survival (Measure.map Y μ)) (Ioi 0) s) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1) * s t) := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  rw [moment_tail_area_factored μ hY.aemeasurable hY0 hr]
  congr 1
  have hc : SelectionOn (survival (Measure.map Y μ)) (Ioi 0)
      (fun t => μ.real {ω | t < Y ω}) :=
    fun t _ => strict_tail_survival_selection μ hY t (mem_univ t)
  have he := decreasing_selections_ae_eq (survival_maximal (Measure.map Y μ)).1
    hc hs volume measurableSet_Ioi
  apply lintegral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

/-- The two identities in Corollary `cor:moments`, with the paper's arbitrary
selection convention and extended values, on the original probability space. -/
theorem moment_tail_quantile_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r) {s q : ℝ → ℝ}
    (hs : SelectionOn (survival (Measure.map Y μ)) (Ioi 0) s)
    (hq : AEMeasurable q unitUniform)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile (Measure.map Y μ) p) :
    ((∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1) * s t)) ∧
    ((∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((q p)^r)) := by
  refine ⟨moment_tail_selection_identity μ hY hY0 hr hs, ?_⟩
  exact randomVariable_quantile_lintegral_comp μ hY hq hsel
    (fun x : ℝ => ENNReal.ofReal (x^r))
    (ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const hr.le)).measurable

/-- No extra measurability assumption on the chosen quantile values is
required: it follows from their antitonicity on (0,1). -/
theorem moment_identities_of_selections {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r) {s q : ℝ → ℝ}
    (hs : ∀ t > 0, s t ∈ survival (Measure.map Y μ) t)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile (Measure.map Y μ) p) :
    ((∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1) * s t)) ∧
    ((∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((q p)^r)) := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  have hq : AEMeasurable q unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo
      (selection_antitoneOn (tailQuantile_maximal (Measure.map Y μ)).1 hsel)
  exact moment_tail_quantile_identity μ hY hY0 hr hs hq hsel

end ScalarMonotone.EndOfPaper
end
