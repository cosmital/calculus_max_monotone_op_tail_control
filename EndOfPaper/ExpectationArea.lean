import EndOfPaper.PositiveSurvivalCompletion
import EndOfPaper.QuantileArea

/-!
The complete extended expectation/survival/inverse area correspondence, and the signed original-space quantile identity for arbitrary selections with L1 derived.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_survival_inverse_positive_domain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    Ioi 0 ⊆ dom (inverse (positiveSurvivalCompletion ν)) := by
  intro p hp
  rcases lt_trichotomy p 1 with hlt | rfl | hgt
  · change (inverse (positiveSurvivalCompletion ν) p).Nonempty
    rw [positive_survival_inverse_interior ν hν ⟨hp,hlt⟩]
    exact tailQuantile_fiber_nonempty ν ⟨hp,hlt⟩
  · refine ⟨0,?_⟩
    change (1 : ℝ) ∈ positiveSurvivalCompletion ν 0
    rw [positive_survival_zero]
    exact measureReal_le_one
  · change (inverse (positiveSurvivalCompletion ν) p).Nonempty
    rw [positive_survival_inverse_above_one ν hgt]
    exact ⟨0,rfl⟩

theorem positive_survival_inverse_area_restriction (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {q : ℝ → ℝ} (hq : SelectionOn (inverse (positiveSurvivalCompletion ν)) (Ioi 0) q) :
    (∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (q p)) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (q p) := by
  classical
  have he : (fun p => ENNReal.ofReal (q p)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Ioo (0 : ℝ) 1).indicator (fun p => ENNReal.ofReal (q p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (Set.countable_singleton (1 : ℝ)).ae_not_mem (volume.restrict (Ioi (0 : ℝ)))]
      with p hp hne
    by_cases hp1 : p < 1
    · rw [Set.indicator_of_mem (show p ∈ Ioo (0 : ℝ) 1 from ⟨hp,hp1⟩)]
    · have hgt : 1 < p := lt_of_le_of_ne (le_of_not_gt hp1) (Ne.symm (by simpa using hne))
      have hzero := hq p hp
      rw [positive_survival_inverse_above_one ν hgt] at hzero
      have hz : q p = 0 := hzero
      rw [Set.indicator_of_not_mem (show p ∉ Ioo (0 : ℝ) 1 from fun h => hp1 h.2),
        hz,ENNReal.ofReal_zero]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)]

theorem positive_survival_expectation_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : 0 ≤ᵐ[μ] Y) {s q : ℝ → ℝ}
    (hs : SelectionOn (positiveSurvivalCompletion (Measure.map Y μ)) (Ioi 0) s)
    (hq : SelectionOn (inverse (positiveSurvivalCompletion (Measure.map Y μ))) (Ioi 0) q) :
    ((∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (s t)) ∧
    ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (s t)) =
      ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (q p)) ∧
    ((∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (q p)) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (q p)) := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  have hν : ∀ᵐ x ∂Measure.map Y μ, 0 ≤ x := by
    exact (ae_map_iff hY.aemeasurable measurableSet_Ici).mpr hY0
  have hs' : ∀ t > 0, s t ∈ survival (Measure.map Y μ) t := by
    intro t ht
    have h := hs t ht
    rwa [(positive_survival_properties (Measure.map Y μ)).2.2.2 t ht] at h
  have hq' : ∀ p ∈ Ioo (0 : ℝ) 1, q p ∈ tailQuantile (Measure.map Y μ) p := by
    intro p hp
    rw [← positive_survival_inverse_interior (Measure.map Y μ) hν hp]
    exact hq p hp.1
  have hi := moment_identities_of_selections μ hY hY0 zero_lt_one hs' hq'
  have ht : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (s t) := by
    simpa only [Real.rpow_one,sub_self,Real.rpow_zero,one_mul,ENNReal.ofReal_one] using hi.1
  have hqt : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (q p) := by
    simpa only [Real.rpow_one] using hi.2
  have he := positive_survival_inverse_area_restriction (Measure.map Y μ) hq
  exact ⟨ht,ht.symm.trans (hqt.trans he.symm),he⟩

theorem signed_expectation_quantile_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hXi : Integrable X μ) {q : ℝ → ℝ}
    (hq : SelectionOn (tailQuantile (Measure.map X μ)) (Ioo (0 : ℝ) 1) q) :
    Integrable q unitUniform ∧ (∫ ω, X ω ∂μ) = ∫ p in Ioo (0 : ℝ) 1, q p := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection
    (Or.inr (tailQuantile_maximal (Measure.map X μ)).1) measurableSet_Ioo
    (fun p hp => tailQuantile_fiber_nonempty (Measure.map X μ) hp)
  have he : s =ᵐ[unitUniform] q :=
    decreasing_selections_ae_eq (tailQuantile_maximal (Measure.map X μ)).1 hs hq volume measurableSet_Ioo
  have hνi : Integrable (fun x : ℝ => x) (Measure.map X μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hX.aemeasurable).mpr hXi
  refine ⟨(quantile_selection_integrable (Measure.map X μ) hνi hsm hs).congr he,?_⟩
  have hm : (∫ x, x ∂Measure.map X μ) = ∫ ω, X ω ∂μ :=
    integral_map hX.aemeasurable measurable_id.aestronglyMeasurable
  rw [← hm,← quantile_selection_expectation (Measure.map X μ) hνi hsm hs]
  exact integral_congr_ae he

end ScalarMonotone.EndOfPaper
end
