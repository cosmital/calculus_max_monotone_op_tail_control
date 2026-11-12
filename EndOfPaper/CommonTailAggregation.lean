import EndOfPaper.AdmissibleHardyEnvelope
import EndOfPaper.CompletedProfiles
import EndOfPaper.GeometricProduct

/-!
The exact positive sharp coefficient for a nonzero aggregation and the whole common-envelope quantile comparison without an extra F-sharp continuity assumption.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem sharp_one_positive_of_nonzero {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hnz : ¬ ∀ a, 0 ≤ a → F a = 0) :
    0 < superadditiveTransform F (fun _ => 1) := by
  push_neg at hnz
  obtain ⟨a,ha,hFa⟩ := hnz
  have hpos : 0 < F a := lt_of_le_of_ne (hF.nonneg a ha) (Ne.symm hFa)
  have h1pos : 0 < F (fun _ => 1) := by
    have h1 := hF.nonneg (fun _ => 1) (fun _ => zero_le_one)
    by_contra hn
    have he : F (fun _ => 1) = 0 := le_antisymm (le_of_not_gt hn) h1
    have hb := aggregation_linear_bound hF ha
    rw [he,zero_mul] at hb
    exact (not_lt_of_ge hb) hpos
  exact h1pos.trans_le (le_superadditiveTransform hF (fun _ => zero_le_one))

theorem common_envelope_quantile_bound_of_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {a | 0 ≤ a})
    (hC : 0 < superadditiveTransform F (fun _ => 1))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {β : Operator} (hβ : MaximalDecreasing β)
    (hβ1 : DecLE β (ofFun (fun _ => (1 : ℝ)))) (hz : IsGLB (ran β) 0)
    (hS : ∀ i, DecLE (survival (Measure.map (fun ω => X ω i) μ)) β)
    {b : ℝ → ℝ} (hb : SelectionOn (inverse β) (Ioo (0 : ℝ) 1) b)
    (hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b p|) < ∞) :
    DecLE (tailQuantile (Measure.map (fun ω => F (X ω)) μ))
      (outputScale (superadditiveTransform F (fun _ => 1))
        (hardyFamilyIntegral (interior (dom (inverse β))) (inverse β))) := by
  let H := hardyFamilyIntegral (interior (dom (inverse β))) (inverse β)
  let C := superadditiveTransform F (fun _ => 1)
  have hd (i : Fin n) := admissible_tail_hardy_data μ (measurable_pi_iff.mp hXm i)
    (Eventually.of_forall (fun ω => hX ω i)) hβ hβ1 hz (hS i) hb hfinite
  have hi (i : Fin n) : Integrable (fun ω => X ω i) μ := (hd i).1
  let i₀ : Fin n := ⟨0,hn⟩
  obtain ⟨_,hH,hHI,hHdom,hHv,_⟩ := hd i₀
  change ∀ p ∈ Ioo (0 : ℝ) 1, H p = {hardyScalar b p} at hHv
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
  have hT : MaximalDecreasing (outputScale C H) := outputScale_maximal_decreasing hC hH
  have hTI : interior (dom (outputScale C H)) = Ioo (0 : ℝ) 1 := by
    rw [dom_outputScale]
    exact hHI
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection (Or.inr hYH.1.1) measurableSet_Ioo
    (fun p hp => interior_subset (show p ∈ interior (dom (quantileHardy ν)) from by rwa [hYH.2.1]))
  have hτ : SelectionOn (outputScale C H) (Ioo (0 : ℝ) 1) (fun p => C*hardyScalar b p) := by
    intro p hp
    exact ⟨hardyScalar b p,by rw [hHv p hp]; rfl,rfl⟩
  have hcomp : DecLE (quantileHardy ν) (outputScale C H) := by
    apply initial_decLE_of_selection_ae_le zero_lt_one hYH.1 hT hYH.2.1 hTI hs hτ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    obtain ⟨a,v,ha,ham,hav,havb⟩ := hardy_tail_aggregation_ae hF hFc μ hXm
      (Eventually.of_forall hX) hi hp
    have hsv : s p = v := by
      have hh := hs p hp
      change s p ∈ hardyFamilyIntegral _ _ p at hh
      rw [hav] at hh
      exact hh
    have hab (i : Fin n) : a i ≤ hardyScalar b p := by
      have hHi := quantileHardy_original_properties μ (measurable_pi_iff.mp hXm i) (hi i)
      have hcmp := (hd i).2.2.2.2.2
      have hmem : hardyScalar b p ∈ H p := by rw [hHv p hp]; rfl
      have hip : p ∈ dom (quantileHardy (Measure.map (fun ω => X ω i) μ)) := by
        apply interior_subset
        rwa [hHi.2.1]
      obtain ⟨w,hw,hwle⟩ := (decLE_fiber hHi.1 hH hcmp
        hip ⟨_,hmem⟩).1 (mem_upperHull hmem)
      change w ∈ hardyFamilyIntegral _ _ p at hw
      rw [ham i] at hw
      have he : w = a i := hw
      rwa [he] at hwle
    have hb0 : 0 ≤ hardyScalar b p := (ha i₀).trans (hab i₀)
    calc
      s p = v := hsv
      _ ≤ superadditiveTransform F a := havb
      _ ≤ superadditiveTransform F (fun _ => hardyScalar b p) := superadditiveTransform_mono hF ha hab
      _ = hardyScalar b p*C := by
        change superadditiveTransform F (fun _ => hardyScalar b p) =
          hardyScalar b p*superadditiveTransform F (fun _ => 1)
        have he : (hardyScalar b p • (fun _ : Fin n => (1 : ℝ)) : CoordinateVector n) =
            fun _ => hardyScalar b p := by funext i; simp
        rw [← he]
        exact superadditiveTransform_smul hF (fun _ => zero_le_one) hb0
      _ = C*hardyScalar b p := mul_comm _ _
  exact decLE_trans (tailQuantile_maximal ν) hYH.1 hT
    (tailQuantile_le_quantileHardy ν hνi) hcomp

end ScalarMonotone.EndOfPaper
end
