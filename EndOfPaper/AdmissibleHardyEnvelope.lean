import EndOfPaper.AdmissibleTailEnvelope
import EndOfPaper.ReplicatedHardyEnvelope

/-!
The whole Hardy envelope comparison, exact completed domains and scalar fibers, all derived from the original survival-envelope data.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem admissible_tail_hardy_data {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : 0 ≤ᵐ[μ] Y) {β : Operator} (hβ : MaximalDecreasing β)
    (hβ1 : DecLE β (ofFun (fun _ => (1 : ℝ)))) (hzero : IsGLB (ran β) 0)
    (hS : DecLE (survival (Measure.map Y μ)) β) {b : ℝ → ℝ}
    (hb : SelectionOn (inverse β) (Ioo (0 : ℝ) 1) b)
    (hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b p|) < ∞) :
    let H := hardyFamilyIntegral (interior (dom (inverse β))) (inverse β)
    Integrable Y μ ∧ MaximalDecreasing H ∧ interior (dom H) = Ioo (0 : ℝ) 1 ∧
      (dom H ⊆ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, H p = {hardyScalar b p}) ∧
      DecLE (quantileHardy (Measure.map Y μ)) H := by
  dsimp only
  let ν := Measure.map Y μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hY.aemeasurable
  have hν : ∀ᵐ x ∂ν, 0 ≤ x := (ae_map_iff hY.aemeasurable measurableSet_Ici).mpr hY0
  have hg := admissible_tail_inverse_geometry ν hν hβ hβ1 hzero hS
  obtain ⟨hYi,hbi⟩ := admissible_tail_integrability μ hY hY0 hβ hβ1 hzero hS hb hfinite
  have hbs : SelectionOn (inverse β) (interior (dom (inverse β))) b := by
    simpa only [hg.2.1] using hb
  have hbint : Integrable b (volume.restrict (interior (dom (inverse β)))) := by
    simpa only [hg.2.1,unitUniform] using hbi
  have hzq : IsGLB (dom (inverse β)) 0 := hzero
  have hpq : ∃ a ∈ dom (inverse β), 0 < a := ⟨1/2,hg.1 (by norm_num),by norm_num⟩
  have hH := hardyFamilyIntegral_of_integrable (inverse_maximal_decreasing hβ) hzq hpq hbs hbint
  have hνi : Integrable (fun x : ℝ => x) ν :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hY.aemeasurable).mpr hYi
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection (Or.inr (tailQuantile_maximal ν).1)
    measurableSet_Ioo (fun p hp => tailQuantile_fiber_nonempty ν hp)
  have hqs : SelectionOn (tailQuantile ν) (interior (dom (tailQuantile ν))) s := by
    simpa only [tailQuantile_domain_interior] using hs
  have hqint : Integrable s (volume.restrict (interior (dom (tailQuantile ν)))) := by
    simpa only [tailQuantile_domain_interior,unitUniform] using quantile_selection_integrable ν hνi hsm hs
  have hqd : dom (tailQuantile ν) ⊆ Icc (0 : ℝ) 1 := by
    rintro p ⟨x,hx⟩
    change ν.real (Ioi x) ≤ p ∧ p ≤ ν.real (Ici x) at hx
    exact ⟨measureReal_nonneg.trans hx.1,hx.2.trans measureReal_le_one⟩
  have hzQ : IsGLB (dom (tailQuantile ν)) 0 := by
    refine ⟨fun p hp => (hqd hp).1,?_⟩
    intro z hz
    exact (isGLB_Ioo (zero_lt_one : (0 : ℝ) < 1)).2
      (fun p hp => hz (tailQuantile_fiber_nonempty ν hp))
  have hpQ : ∃ a ∈ dom (tailQuantile ν), 0 < a :=
    ⟨1/2,tailQuantile_fiber_nonempty ν (by norm_num),by norm_num⟩
  have hcmp := hardyFamilyIntegral_mono (tailQuantile_maximal ν) (inverse_maximal_decreasing hβ)
    hzQ hpQ hzq hpq hqs hbs hqint hbint (decLE_inverse_iff.mpr hS)
  refine ⟨hYi,hH.1,?_,?_,?_,hcmp⟩
  · exact hH.2.1.trans hg.2.1
  · simpa only [hg.2.1,closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hH.2.2.1
  · intro p hp
    exact hH.2.2.2.1 p (by rwa [hg.2.1])

end ScalarMonotone.EndOfPaper
end
