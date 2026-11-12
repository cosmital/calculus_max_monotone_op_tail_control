import EndOfPaper.HardyIntegral
import EndOfPaper.QuantileArea
import EndOfPaper.ShortfallMinimizers

/-!
Full variational formulas for the actual completed Hardy integral of a
quantile graph (lem:hardyvariational). The primal minimum, normalized dual
maximum, literal unnormalized product supremum, and entire minimizer set
are identified on the original probability space, with arbitrary atoms.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem tailQuantile_domain_interior (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    interior (dom (tailQuantile μ)) = Ioo 0 1 := by
  have hsub : dom (tailQuantile μ) ⊆ Icc 0 1 := by
    rintro p ⟨a, ha⟩
    change μ.real (Ioi a) ≤ p ∧ p ≤ μ.real (Ici a) at ha
    exact ⟨measureReal_nonneg.trans ha.1, ha.2.trans measureReal_le_one⟩
  apply Subset.antisymm
  · simpa only [interior_Icc] using interior_mono hsub
  · exact interior_maximal (fun p hp => tailQuantile_fiber_nonempty μ hp) isOpen_Ioo

theorem hardy_tailQuantile_fiber (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile μ u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    hardyFamilyIntegral (interior (dom (tailQuantile μ))) (tailQuantile μ) p =
      {hardyScalar q p} := by
  rw [tailQuantile_domain_interior]
  have hdom : Ioo (0 : ℝ) 1 ⊆ interior (dom (tailQuantile μ)) := by
    rw [tailQuantile_domain_interior]
  have hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, c*u ∈ Ioo (0 : ℝ) 1 := by
    intro c hc u hu
    exact ⟨mul_pos hc.1 hu.1, (mul_le_of_le_one_left hu.1.le hc.2).trans_lt hu.2⟩
  exact (hardyFamilyIntegral_well_defined (tailQuantile_maximal μ)
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr zero_lt_one) hdom
    (fun _ hu => hu.1) hscale hsel
    (fun _ hu => quantile_selection_intervalIntegrable μ hμ hq hsel hu)).2.2.2.1 p hp

variable {Ω : Type*} [MeasurableSpace Ω]

theorem shortfallObjective_map {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) (p a : ℝ) :
    shortfallObjective (Measure.map X μ) (fun x : ℝ => x) p a =
      shortfallObjective μ X p a := by
  have hm : Measurable (fun x : ℝ => max (x-a) 0) :=
    (measurable_id.sub measurable_const).max measurable_const
  have he : (∫ x : ℝ, max (x-a) 0 ∂Measure.map X μ) =
      ∫ ω, max (X ω-a) 0 ∂μ := integral_map hX.aemeasurable hm.aestronglyMeasurable
  unfold shortfallObjective
  rw [he]

theorem hardyScalar_quantile_original_variational {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : Measurable X) (hXi : Integrable X μ)
    {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ u ∈ Ioo 0 1, q u ∈ tailQuantile (Measure.map X μ) u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    IsLeast (Set.range (shortfallObjective μ X p)) (hardyScalar q p) ∧
      IsGreatest (dualCandidates μ X p) (hardyScalar q p) := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hXm.aemeasurable
  have hμ : Integrable (fun x : ℝ => x) (Measure.map X μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hXm.aemeasurable).mpr hXi
  obtain ⟨a, ha⟩ := tailQuantile_fiber_nonempty (Measure.map X μ) hp
  have hbr := (tailQuantile_map_mem_iff hXm a p).mp ha
  have hv := (hardyScalar_quantile_eq_shortfall (Measure.map X μ) hμ hq hsel hp ha).trans
    (shortfallObjective_map hXm p a)
  have hatt := shortfall_attainment hp.1 hXm hXi hbr.1 hbr.2
  rw [hv]
  exact ⟨⟨⟨a, rfl⟩, fun _ ⟨b, hb⟩ => hb ▸ hatt.2 b⟩, hatt.1⟩

def weightedProductCandidates (μ : Measure Ω) (X : Ω → ℝ) (p : ℝ) : Set ℝ :=
  {w | ∃ Z : Ω → ℝ, AEMeasurable Z μ ∧
    (∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) ∧
    (∫ ω, Z ω ∂μ) = p ∧ w = ∫ ω, X ω*Z ω ∂μ}

theorem dualCandidates_greatest_unnormalized {μ : Measure Ω} {X : Ω → ℝ}
    {p v : ℝ} (hp : 0 < p) (hv : IsGreatest (dualCandidates μ X p) v) :
    IsGreatest (weightedProductCandidates μ X p) (p*v) := by
  obtain ⟨Z, hZm, hz, hm, he⟩ := hv.1
  constructor
  · refine ⟨Z, hZm, hz, hm, ?_⟩
    rw [he]
    field_simp [hp.ne']
  · rintro w ⟨W, hWm, hw, hWmean, rfl⟩
    have h := hv.2 (show (∫ ω, X ω*W ω ∂μ)/p ∈ dualCandidates μ X p from
      ⟨W, hWm, hw, hWmean, rfl⟩)
    exact (div_le_iff₀ hp).mp h |>.trans_eq (mul_comm v p)

/-- Full original-space statement: H is the completed Aumann dilation-family
integral, every primal minimizer is retained, and the weight is on Ω itself. -/
theorem hardy_quantile_original_variational {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : Measurable X) (hXi : Integrable X μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ v : ℝ,
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map X μ))))
        (tailQuantile (Measure.map X μ)) p = {v} ∧
      IsLeast (Set.range (shortfallObjective μ X p)) v ∧
      IsGreatest (dualCandidates μ X p) v ∧
      IsGreatest (weightedProductCandidates μ X p) (p*v) ∧
      v = sSup (weightedProductCandidates μ X p) / p ∧
      {a | ∀ b : ℝ, shortfallObjective μ X p a ≤ shortfallObjective μ X p b} =
        tailQuantile (Measure.map X μ) p := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hXm.aemeasurable
  have hμ : Integrable (fun x : ℝ => x) (Measure.map X μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hXm.aemeasurable).mpr hXi
  obtain ⟨q, hq, hsel⟩ := exists_global_measurable_selection
    (Or.inr (tailQuantile_maximal (Measure.map X μ)).1) measurableSet_Ioo
    (fun _ hu => tailQuantile_fiber_nonempty (Measure.map X μ) hu)
  have hv := hardyScalar_quantile_original_variational hXm hXi hq hsel hp
  have hw := dualCandidates_greatest_unnormalized hp.1 hv.2
  refine ⟨hardyScalar q p, hardy_tailQuantile_fiber _ hμ hq hsel hp,
    hv.1, hv.2, hw, ?_, shortfall_minimizers_eq_tailQuantile hXm hXi hp⟩
  rw [hw.csSup_eq]
  field_simp [hp.1.ne']

end ScalarMonotone.EndOfPaper
end
