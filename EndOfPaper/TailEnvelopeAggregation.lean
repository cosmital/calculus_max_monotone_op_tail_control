import EndOfPaper.AdmissibleHardyEnvelope
import EndOfPaper.MonotoneScalarAggregation
import EndOfPaper.GeometricProduct

/-!
The complete whole survival aggregation bound for arbitrary admissible envelopes, on the original probability space, retaining AE nonnegativity and all completed fibers.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem tail_envelope_aggregation_of_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {a | 0 ≤ a})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {β : Fin n → Operator} (hβ : ∀ i, MaximalDecreasing (β i))
    (hβ1 : ∀ i, DecLE (β i) (ofFun (fun _ => (1 : ℝ))))
    (hz : ∀ i, IsGLB (ran (β i)) 0)
    (hS : ∀ i, DecLE (survival (Measure.map (fun ω => X ω i) μ)) (β i))
    {b : Fin n → ℝ → ℝ}
    (hb : ∀ i, SelectionOn (inverse (β i)) (Ioo (0 : ℝ) 1) (b i))
    (hfinite : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b i p|) < ∞) :
    let A := aggregationOperator (superadditiveTransform F) (Ioo (0 : ℝ) 1)
      (fun i => hardyFamilyIntegral (interior (dom (inverse (β i)))) (inverse (β i)))
    MaximalDecreasing (inverse A) ∧
      DecLE (survival (Measure.map (fun ω => F (X ω)) μ)) (inverse A) := by
  dsimp only
  let H := fun i => hardyFamilyIntegral (interior (dom (inverse (β i)))) (inverse (β i))
  let B : ℝ → CoordinateVector n := fun p i => hardyScalar (b i) p
  let A := aggregationOperator (superadditiveTransform F) (Ioo (0 : ℝ) 1) H
  have hd (i : Fin n) := admissible_tail_hardy_data μ (measurable_pi_iff.mp hXm i)
    (Eventually.of_forall (fun ω => hX ω i)) (hβ i) (hβ1 i) (hz i) (hS i) (hb i) (hfinite i)
  have hi (i : Fin n) : Integrable (fun ω => X ω i) μ := (hd i).1
  have hH (i : Fin n) : MaximalDecreasing (H i) := (hd i).2.1
  have hHv (i : Fin n) : ∀ p ∈ Ioo (0 : ℝ) 1, H i p = {B p i} := (hd i).2.2.2.2.1
  have hcmp (i : Fin n) : DecLE (quantileHardy (Measure.map (fun ω => X ω i) μ)) (H i) :=
    (hd i).2.2.2.2.2
  have hBmem (i : Fin n) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : B p i ∈ H i p := by
    rw [hHv i p hp]
    rfl
  have hB0 (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : 0 ≤ B p := by
    intro i
    have hHi := quantileHardy_original_properties μ (measurable_pi_iff.mp hXm i) (hi i)
    have hip : p ∈ dom (quantileHardy (Measure.map (fun ω => X ω i) μ)) := by
      apply interior_subset
      rwa [hHi.2.1]
    obtain ⟨w,hw,hwle⟩ := (decLE_fiber hHi.1 (hH i) (hcmp i)
      hip ⟨_,hBmem i p hp⟩).1 (mem_upperHull (hBmem i p hp))
    exact (quantileHardy_nonnegative μ (measurable_pi_iff.mp hXm i) (hi i)
      (Eventually.of_forall (fun ω => hX ω i)) hp hw).trans hwle
  have hτanti : AntitoneOn (fun p => superadditiveTransform F (B p)) (Ioo (0 : ℝ) 1) := by
    intro p hp q hq hpq
    apply superadditiveTransform_mono hF (hB0 q hq)
    intro i
    rcases eq_or_lt_of_le hpq with he | hlt
    · rw [he]
    · exact Decreasing.le_of_lt (hH i).1 (hBmem i p hp) (hBmem i q hq) hlt
  have hA := aggregation_singleton_monotone_properties (superadditiveTransform F)
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr zero_lt_one)
    (fun p hp i => hHv i p hp) hτanti
  have hFm : Measurable (fun ω => F (X ω)) := by
    have he : (fun ω => F (fun i => max (X ω i) 0)) = fun ω => F (X ω) := by
      funext ω
      congr 1
      funext i
      exact max_eq_left (hX ω i)
    rw [← he]
    exact (aggregation_positiveExtension_continuous hFc).measurable.comp hXm
  have hFi := aggregation_composition_integrable hF hFc μ hXm hX hi
  let ν := Measure.map (fun ω => F (X ω)) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hFm.aemeasurable
  have hνi : Integrable (fun x : ℝ => x) ν :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hFm.aemeasurable).mpr hFi
  have hYH := quantileHardy_properties ν hνi
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection (Or.inr hYH.1.1) measurableSet_Ioo
    (fun p hp => interior_subset (show p ∈ interior (dom (quantileHardy ν)) from by rwa [hYH.2.1]))
  have hHA : DecLE (quantileHardy ν) A := by
    apply initial_decLE_of_selection_ae_le zero_lt_one hYH.1 hA.1 hYH.2.1 hA.2.1 hs hA.2.2.2
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    obtain ⟨a,v,ha,ham,hav,havb⟩ := hardy_tail_aggregation_ae hF hFc μ hXm
      (Eventually.of_forall hX) hi hp
    have hsv : s p = v := by
      have hh := hs p hp
      change s p ∈ hardyFamilyIntegral _ _ p at hh
      rw [hav] at hh
      exact hh
    have hab (i : Fin n) : a i ≤ B p i := by
      have hHi := quantileHardy_original_properties μ (measurable_pi_iff.mp hXm i) (hi i)
      have hip : p ∈ dom (quantileHardy (Measure.map (fun ω => X ω i) μ)) := by
        apply interior_subset
        rwa [hHi.2.1]
      obtain ⟨w,hw,hwle⟩ := (decLE_fiber hHi.1 (hH i) (hcmp i)
        hip ⟨_,hBmem i p hp⟩).1 (mem_upperHull (hBmem i p hp))
      change w ∈ hardyFamilyIntegral _ _ p at hw
      rw [ham i] at hw
      have he : w = a i := hw
      rwa [he] at hwle
    rw [hsv]
    exact havb.trans (superadditiveTransform_mono hF ha hab)
  have hQA := decLE_trans (tailQuantile_maximal ν) hYH.1 hA.1
    (tailQuantile_le_quantileHardy ν hνi) hHA
  refine ⟨inverse_maximal_decreasing hA.1,?_⟩
  simpa only [tailQuantile,inverse_inverse] using decLE_inverse_iff.mpr hQA

theorem tail_envelope_aggregation {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {a | 0 ≤ a})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hXm : Measurable X) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {β : Fin n → Operator} (hβ : ∀ i, MaximalDecreasing (β i))
    (hβ1 : ∀ i, DecLE (β i) (ofFun (fun _ => (1 : ℝ))))
    (hz : ∀ i, IsGLB (ran (β i)) 0)
    (hS : ∀ i, DecLE (survival (Measure.map (fun ω => X ω i) μ)) (β i))
    {b : Fin n → ℝ → ℝ}
    (hb : ∀ i, SelectionOn (inverse (β i)) (Ioo (0 : ℝ) 1) (b i))
    (hfinite : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b i p|) < ∞) :
    let A := aggregationOperator (superadditiveTransform F) (Ioo (0 : ℝ) 1)
      (fun i => hardyFamilyIntegral (interior (dom (inverse (β i)))) (inverse (β i)))
    MaximalDecreasing (inverse A) ∧
      DecLE (survival (Measure.map (fun ω => F (X ω)) μ)) (inverse A) := by
  let Xp : Ω → CoordinateVector n := fun ω i => max (X ω i) 0
  have hXpm : Measurable Xp := measurable_pi_iff.mpr (fun i =>
    (measurable_pi_iff.mp hXm i).max measurable_const)
  have hXp : ∀ ω, 0 ≤ Xp ω := fun ω i => le_max_right _ _
  have hS' (i : Fin n) : DecLE (survival (Measure.map (fun ω => Xp ω i) μ)) (β i) := by
    have he : (fun ω => Xp ω i) =ᵐ[μ] (fun ω => X ω i) :=
      hX.mono (fun ω hω => max_eq_left (hω i))
    rw [Measure.map_congr he]
    exact hS i
  have h := tail_envelope_aggregation_of_nonnegative hF hFc μ hXpm hXp hβ hβ1 hz hS' hb hfinite
  have heF : (fun ω => F (Xp ω)) =ᵐ[μ] (fun ω => F (X ω)) := by
    filter_upwards [hX] with ω hω
    congr 1
    funext i
    exact max_eq_left (hω i)
  rwa [Measure.map_congr heF] at h

end ScalarMonotone.EndOfPaper
end
