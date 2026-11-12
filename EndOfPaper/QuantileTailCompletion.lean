import EndOfPaper.GeometricProduct
import EndOfPaper.QuantileMoments
import EndOfPaper.HardyVariational

/-!
Scalar strict-tail tests on an arbitrary selection
imply whole completed quantile comparison, including endpoints.
Only the countable output-quantile jump set is removed in the AE bridge.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem quantile_singleton_value_le_of_strict_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {p u t : ℝ} (hu : u ∈ tailQuantile (Measure.map X μ) p)
    (hsub : (tailQuantile (Measure.map X μ) p).Subsingleton)
    (hb : μ.real {ω | t < X ω} ≤ p) : u ≤ t := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  have ht : (Measure.map X μ).real (Ioi t) ≤ p := by
    simpa only [measureReal_def,Measure.map_apply hX measurableSet_Ioi,preimage_setOf_eq] using hb
  by_contra hut
  have htu : t < u := lt_of_not_ge hut
  have hpu : p ≤ (Measure.map X μ).real (Ici u) := hu.2
  have hpt : p ≤ (Measure.map X μ).real (Ioi t) := hpu.trans
    (measureReal_mono (show Ici u ⊆ Ioi t from fun x hx => htu.trans_le hx))
  have htm : t ∈ tailQuantile (Measure.map X μ) p :=
    ⟨ht,hpt.trans (measureReal_mono Ioi_subset_Ici_self)⟩
  exact (ne_of_lt htu) (hsub htm hu)

theorem quantile_selection_ae_le_of_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {s τ : ℝ → ℝ} (hs : SelectionOn (tailQuantile (Measure.map X μ)) (Ioo (0 : ℝ) 1) s)
    (hb : ∀ p ∈ Ioo (0 : ℝ) 1, μ.real {ω | τ p < X ω} ≤ p) :
    s ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] τ := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  have hQ := tailQuantile_maximal (Measure.map X μ)
  filter_upwards [(countable_jumpInputs hQ.1).ae_not_mem (volume.restrict (Ioo (0 : ℝ) 1)),
    ae_restrict_mem measurableSet_Ioo] with p hpJ hp
  apply quantile_singleton_value_le_of_strict_tail hX (hs p hp) _ (hb p hp)
  intro a ha b hb
  apply neg_injective
  apply fiber_subsingleton_off_jumps (negOut (tailQuantile (Measure.map X μ))) hpJ
  · simpa only [negOut,mem_setOf_eq,neg_neg] using ha
  · simpa only [negOut,mem_setOf_eq,neg_neg] using hb

theorem tailQuantile_decLE_of_profile_selection_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {q : Operator} (hq : MaximalDecreasing q) (hqi : interior (dom q) = Ioo (0 : ℝ) 1)
    {sq : ℝ → ℝ} (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    (hb : ∀ p ∈ Ioo (0 : ℝ) 1, μ.real {ω | sq p < X ω} ≤ p) :
    DecLE (tailQuantile (Measure.map X μ)) q := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨s,hm,hs⟩ := exists_global_measurable_selection
    (Or.inr (tailQuantile_maximal (Measure.map X μ)).1) measurableSet_Ioo
    (fun p hp => tailQuantile_fiber_nonempty (Measure.map X μ) hp)
  exact initial_decLE_of_selection_ae_le (by norm_num) (tailQuantile_maximal _) hq
    (tailQuantile_domain_interior _) hqi hs hsq (quantile_selection_ae_le_of_tail_bounds hX hs hb)

end ScalarMonotone.EndOfPaper
end
