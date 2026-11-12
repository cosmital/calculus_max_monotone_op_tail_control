import EndOfPaper.AdmissibleTailEnvelope
import EndOfPaper.ReplicatedHardyEnvelope

/-!
The whole survival bound by the inverse literal ordinary sum of marginal Hardy graphs, with original-space L1 derived from the envelopes.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hardy_sum_survival_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) μ) :
    MaximalDecreasing (inverse (finiteSum (fun i => quantileHardy (Measure.map (X i) μ)))) ∧
    DecLE (survival (Measure.map (fun ω => ∑ i, X i ω) μ))
      (inverse (finiteSum (fun i => quantileHardy (Measure.map (X i) μ)))) := by
  have hsum := signed_hardy_sum_operator_bound μ X hm hi
  have hYm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ (fun i _ => hm i)
  have hYi : Integrable (fun ω => ∑ i, X i ω) μ := integrable_finset_sum _ (fun i _ => hi i)
  let ν := Measure.map (fun ω => ∑ i, X i ω) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hYm.aemeasurable
  have hνi : Integrable (fun x : ℝ => x) ν :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hYm.aemeasurable).mpr hYi
  have hQH := tailQuantile_le_quantileHardy ν hνi
  have hQS := decLE_trans (tailQuantile_maximal ν) (quantileHardy_properties ν hνi).1
    hsum.1 hQH hsum.2
  refine ⟨inverse_maximal_decreasing hsum.1,?_⟩
  simpa only [tailQuantile,inverse_inverse] using (decLE_inverse_iff.mpr hQS)

theorem hardy_sum_survival_of_envelopes {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (h0 : ∀ i, 0 ≤ᵐ[μ] X i)
    {β : Fin n → Operator} (hβ : ∀ i, MaximalDecreasing (β i))
    (hβ1 : ∀ i, DecLE (β i) (ofFun (fun _ => (1 : ℝ))))
    (hz : ∀ i, IsGLB (ran (β i)) 0)
    (hS : ∀ i, DecLE (survival (Measure.map (X i) μ)) (β i))
    {b : Fin n → ℝ → ℝ}
    (hb : ∀ i, SelectionOn (inverse (β i)) (Ioo (0 : ℝ) 1) (b i))
    (hfinite : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b i p|) < ∞) :
    (∀ i, Integrable (X i) μ) ∧
    MaximalDecreasing (inverse (finiteSum (fun i => quantileHardy (Measure.map (X i) μ)))) ∧
    DecLE (survival (Measure.map (fun ω => ∑ i, X i ω) μ))
      (inverse (finiteSum (fun i => quantileHardy (Measure.map (X i) μ)))) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hi (i : Fin n) : Integrable (X i) μ :=
    (admissible_tail_integrability μ (hm i) (h0 i) (hβ i) (hβ1 i) (hz i) (hS i) (hb i) (hfinite i)).1
  exact ⟨hi,hardy_sum_survival_bound μ X hm hi⟩

end ScalarMonotone.EndOfPaper
end
