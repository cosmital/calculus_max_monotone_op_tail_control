import EndOfPaper.HardyScalar
import EndOfPaper.Shortfall
import MonotoneOperators.Survival

/-!
# Quantile area and the scalar expected-shortfall formulas

Source: `expectationarea`, the excess-area identity, and `hardyvariational`.
A measurable selection is explicit. Its integrability is derived from its
pushforward law, rather than added as a stronger hypothesis.

These statements concern interior scalar values. Identification of a globally
defined operator-family integral, and the converse characterization of ALL
primal minimizers, are not asserted here.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- Integrability transfers to every measurable quantile selection. -/
theorem quantile_selection_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u) :
    Integrable q unitUniform := by
  have hmap : Integrable (fun x : ℝ => x) (Measure.map q unitUniform) := by
    rw [tailQuantile_selection_law μ hq hsel]
    exact hμ
  simpa only [Function.comp_apply] using hmap.comp_measurable hq

/-- The signed expectation equals the quantile area. -/
theorem quantile_selection_expectation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u) :
    (∫ u in Ioo (0 : ℝ) 1, q u) = ∫ x, x ∂μ := by
  have he : (∫ x, x ∂Measure.map q unitUniform) = ∫ u, q u ∂unitUniform :=
    integral_map hq.aemeasurable measurable_id.aestronglyMeasurable
  rw [tailQuantile_selection_law μ hq hsel] at he
  exact he.symm

/-- Interior truncations of the selection remain integrable, including their
right endpoint. The endpoint is inside (0,1), so no endpoint convention is used. -/
theorem quantile_selection_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) : IntervalIntegrable q volume 0 p := by
  have hi := quantile_selection_integrable μ hμ hq hsel
  have hsub : Ioc (0 : ℝ) p ⊆ Ioo 0 1 :=
    fun u hu => ⟨hu.1, hu.2.trans_lt hp.2⟩
  constructor
  · exact hi.mono_measure (Measure.restrict_mono hsub le_rfl)
  · simp [IntegrableOn, Ioc_eq_empty_of_le hp.1.le]

/-- Values to the left of a quantile fiber are above every value of that fiber. -/
theorem quantile_before_threshold (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u p a b : ℝ} (hu : b ∈ tailQuantile μ u) (ha : a ∈ tailQuantile μ p)
    (hup : u < p) : a ≤ b := by
  have hn := (increasing_iff_order.mp (tailQuantile_maximal μ).1)
    (show -b ∈ negOut (tailQuantile μ) u by simpa [negOut] using hu)
    (show -a ∈ negOut (tailQuantile μ) p by simpa [negOut] using ha) hup
  linarith

/-- At a quantile threshold, the positive excess has support in the top-p
part of the quantile parameter interval, up to the null point u=p. -/
theorem quantile_excess_indicator_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ → ℝ} (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p a : ℝ} (hp : p ∈ Ioo 0 1) (ha : a ∈ tailQuantile μ p) :
    (fun u => max (q u-a) 0) =ᵐ[unitUniform]
      (Ioo 0 p).indicator (fun u => q u-a) := by
  classical
  letI : NoAtoms unitUniform := by
    change NoAtoms (volume.restrict (Ioo (0 : ℝ) 1))
    infer_instance
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo,
    (Set.countable_singleton p).ae_not_mem unitUniform] with u hu hne
  have hup : u ≠ p := by simpa using hne
  rcases lt_or_gt_of_ne hup with hlt | hgt
  · have hqa := quantile_before_threshold μ (hsel u hu) ha hlt
    simp [Set.indicator_of_mem (show u ∈ Ioo 0 p from ⟨hu.1, hlt⟩),
      max_eq_left (sub_nonneg.mpr hqa)]
  · have hqa := quantile_before_threshold μ ha (hsel u hu) hgt
    have hnot : u ∉ Ioo 0 p := fun h => (not_lt_of_ge hgt.le) h.2
    simp [Set.indicator_of_not_mem hnot, max_eq_right (sub_nonpos.mpr hqa)]

/-- The atom-compatible excess-area identity. -/
theorem quantile_excess_area (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p a : ℝ} (hp : p ∈ Ioo 0 1) (ha : a ∈ tailQuantile μ p) :
    (∫ u in (0 : ℝ)..p, q u)-p*a = ∫ x, max (x-a) 0 ∂μ := by
  have hi := quantile_selection_intervalIntegrable μ hμ hq hsel hp
  have hm : Measurable (fun x : ℝ => max (x-a) 0) :=
    (measurable_id.sub measurable_const).max measurable_const
  have hmap : (∫ x, max (x-a) 0 ∂Measure.map q unitUniform) =
      ∫ u, max (q u-a) 0 ∂unitUniform :=
    integral_map hq.aemeasurable hm.aestronglyMeasurable
  rw [tailQuantile_selection_law μ hq hsel] at hmap
  have hsub : Ioo (0 : ℝ) p ⊆ Ioo 0 1 :=
    fun u hu => ⟨hu.1, hu.2.trans hp.2⟩
  have harea : (∫ x, max (x-a) 0 ∂μ) = ∫ u in Ioo (0 : ℝ) p, q u-a := by
    rw [hmap, integral_congr_ae (quantile_excess_indicator_ae μ hsel hp ha),
      integral_indicator measurableSet_Ioo]
    change (∫ u, q u-a ∂(volume.restrict (Ioo 0 1)).restrict (Ioo 0 p)) = _
    rw [Measure.restrict_restrict_of_subset hsub]
  rw [harea]
  have hinterval : (∫ u in (0 : ℝ)..p, q u-a) = ∫ u in Ioo (0 : ℝ) p, q u-a := by
    rw [intervalIntegral.integral_of_le hp.1.le, integral_Ioc_eq_integral_Ioo]
  rw [← hinterval, intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

/-- The Hardy scalar value equals the primal objective at any quantile threshold. -/
theorem hardyScalar_quantile_eq_shortfall (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p a : ℝ} (hp : p ∈ Ioo 0 1) (ha : a ∈ tailQuantile μ p) :
    hardyScalar q p = shortfallObjective μ (fun x => x) p a := by
  have h := quantile_excess_area μ hμ hq hsel hp ha
  unfold hardyScalar shortfallObjective
  rw [← h]
  field_simp [hp.1.ne'] <;> ring

/-- Both extrema are attained, and equal the actual scalar quantile average.
The weight lives on the original space of the law; atomlessness is not used. -/
theorem hardyScalar_quantile_variational (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    IsLeast (Set.range (shortfallObjective μ (fun x => x) p)) (hardyScalar q p) ∧
    IsGreatest (dualCandidates μ (fun x => x) p) (hardyScalar q p) := by
  obtain ⟨a, ha⟩ := tailQuantile_fiber_nonempty μ hp
  have hbr : μ.real {x : ℝ | a < x} ≤ p ∧ p ≤ μ.real {x : ℝ | a ≤ x} := ha
  have hv := hardyScalar_quantile_eq_shortfall μ hμ hq hsel hp ha
  have hatt := shortfall_attainment hp.1 measurable_id hμ hbr.1 hbr.2
  constructor
  · constructor
    · exact ⟨a, hv.symm⟩
    · rintro z ⟨b, rfl⟩
      rw [hv]
      exact hatt.2 b
  · rw [hv]
    exact hatt.1

/-- Equality with the separate dual scalar functional is a conclusion, not a
redefinition of the Hardy average. -/
theorem hardyScalar_quantile_eq_dualShortfall (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    hardyScalar q p = dualShortfall μ (fun x => x) p :=
  (hardyScalar_quantile_variational μ hμ hq hsel hp).2.csSup_eq.symm

end ScalarMonotone.EndOfPaper

end -- noncomputable section
