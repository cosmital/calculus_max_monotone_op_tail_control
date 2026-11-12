import EndOfPaper.QuantileMoments
import EndOfPaper.HardyVariational
import MonotoneOperators.Order

/-!
Every nonnegative monotone expression transfers through
the actual marginal quantile comparison to an arbitrary selection
of the prescribed profile. Infinite integrals are retained.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem decLE_selections_ae_le {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g) (hfg : DecLE f g)
    (ν : Measure ℝ) [NoAtoms ν] {s t : ℝ → ℝ}
    (hs : ∀ᵐ x ∂ν, s x ∈ f x) (ht : ∀ᵐ x ∂ν, t x ∈ g x) : s ≤ᵐ[ν] t := by
  filter_upwards [(countable_jumpInputs hg.1).ae_not_mem ν,hs,ht] with x hx hsx htx
  have hsub : (g x).Subsingleton := by
    intro a ha b hb
    apply neg_injective
    apply fiber_subsingleton_off_jumps (negOut g) hx
    · simpa only [negOut,mem_setOf_eq,neg_neg] using ha
    · simpa only [negOut,mem_setOf_eq,neg_neg] using hb
  obtain ⟨v,hv,hsv⟩ := (decLE_fiber hf hg hfg ⟨s x,hsx⟩ ⟨t x,htx⟩).2
    (mem_lowerHull hsx)
  exact hsv.trans_eq (hsub hv htx)

theorem profile_selection_lintegral_mono {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g) (hfg : DecLE f g)
    (ν : Measure ℝ) [NoAtoms ν] {s t : ℝ → ℝ}
    (hs : ∀ᵐ x ∂ν, s x ∈ f x) (ht : ∀ᵐ x ∂ν, t x ∈ g x)
    {ψ : ℝ → ℝ≥0∞} (hψ : Monotone ψ) :
    (∫⁻ x, ψ (s x) ∂ν) ≤ ∫⁻ x, ψ (t x) ∂ν := by
  apply lintegral_mono_ae
  exact (decLE_selections_ae_le hf hg hfg ν hs ht).mono (fun _ hx => hψ hx)

theorem random_variable_profile_lintegral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {q : Operator} (hq : MaximalDecreasing q) (hqi : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {s : ℝ → ℝ} (hs : SelectionOn q (Ioo (0 : ℝ) 1) s)
    {ψ : ℝ → ℝ≥0∞} (hψm : Measurable ψ) (hψ : Monotone ψ) :
    (∫⁻ ω, ψ (X ω) ∂μ) ≤ ∫⁻ p in Ioo (0 : ℝ) 1, ψ (s p) := by
  letI : NoAtoms unitUniform := by unfold unitUniform; infer_instance
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨sX,hmX,hsX⟩ := exists_global_measurable_selection
    (Or.inr (tailQuantile_maximal (Measure.map X μ)).1) measurableSet_Ioo
    (fun p hp => tailQuantile_fiber_nonempty (Measure.map X μ) hp)
  rw [randomVariable_quantile_lintegral_comp μ hX hmX.aemeasurable hsX ψ hψm]
  apply profile_selection_lintegral_mono (tailQuantile_maximal _) hq hQ unitUniform
    (show ∀ᵐ p ∂unitUniform, sX p ∈ tailQuantile (Measure.map X μ) p from by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
      exact hsX p hp)
    (show ∀ᵐ p ∂unitUniform, s p ∈ q p from by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
      exact hs p hp) hψ

end ScalarMonotone.EndOfPaper
end
