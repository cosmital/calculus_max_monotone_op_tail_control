import EndOfPaper.ProfileOrder
import EndOfPaper.ProfilePrefixBounds

/-!
The complete general Hardy profile bounds from convex power
or logarithmic transformations. Prefix L1 and inverse/domain
properties are derived from the original profile hypotheses,
with extended range endpoints and full completed-graph order.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hardy_profiles_power {α : Operator} {a : ℝ → ℝ} {L : EReal} {κ : ℝ}
    (hα : MaximalDecreasing α) (ha : ∀ x ∈ dom α, α x = {a x})
    (hm : StrictAntiOn a (dom α)) (hL : 0 < L)
    (hrange : ran α = positiveInitialInterval L) (hκ : 1 < κ)
    (hc : ConvexOn ℝ (dom α) (fun x => (a x)^((-1 : ℝ)/κ))) :
    MaximalDecreasing (hardyTailTransform α) ∧
      DecLE (hardyTailTransform α) (outputScale ((κ/(κ-1))^κ) α) := by
  obtain ⟨q, hqm, hq, hprefix⟩ := hardy_profile_power_prefix hα ha hm hL hrange hκ hc
  have ho : IsOpen (ran α) := by rw [hrange]; exact (positiveInitialInterval_geometry hL).1
  have hz : IsGLB (ran α) 0 := by rw [hrange]; exact positiveInitialInterval_isGLB hL
  obtain ⟨p₀, hp₀⟩ := (positiveInitialInterval_geometry hL).2.2.1
  have hp₀r : p₀ ∈ ran α := hrange.symm ▸ hp₀
  have hp₀pos : 0 < p₀ := (positiveInitialInterval_geometry hL).2.2.2.1 _ hp₀
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  have hK : 1 < κ/(κ-1) := (lt_div_iff₀ (sub_pos.mpr hκ)).mpr (by linarith)
  have hK0 : 0 < κ/(κ-1) := zero_lt_one.trans hK
  have hb := hardyTailTransform_bound_of_scalar hα hz ⟨p₀, hp₀r, hp₀pos⟩
    (fun p hp => hq p (interior_subset hp))
    (fun p hp => (hprefix p (interior_subset hp)).1)
    (Real.rpow_pos_of_pos hK0 (-κ))
    (Real.rpow_le_one_of_one_le_of_nonpos hK.le (neg_nonpos.mpr hk0.le))
    (fun p hp => (hprefix p (interior_subset hp)).2)
  simpa only [Real.rpow_neg hK0.le, inv_inv] using hb

theorem hardy_profiles_exponential {α : Operator} {a : ℝ → ℝ} {L : EReal}
    (hα : MaximalDecreasing α) (ha : ∀ x ∈ dom α, α x = {a x})
    (hm : StrictAntiOn a (dom α)) (hL : 0 < L)
    (hrange : ran α = positiveInitialInterval L)
    (hc : ConvexOn ℝ (dom α) (fun x => -Real.log (a x))) :
    MaximalDecreasing (hardyTailTransform α) ∧
      DecLE (hardyTailTransform α) (outputScale (Real.exp 1) α) := by
  obtain ⟨q, hqm, hq, hprefix⟩ := hardy_profile_exponential_prefix hα ha hm hL hrange hc
  have hz : IsGLB (ran α) 0 := by rw [hrange]; exact positiveInitialInterval_isGLB hL
  obtain ⟨p₀, hp₀⟩ := (positiveInitialInterval_geometry hL).2.2.1
  have hp₀r : p₀ ∈ ran α := hrange.symm ▸ hp₀
  have hp₀pos : 0 < p₀ := (positiveInitialInterval_geometry hL).2.2.2.1 _ hp₀
  have hb := hardyTailTransform_bound_of_scalar hα hz ⟨p₀, hp₀r, hp₀pos⟩
    (fun p hp => hq p (interior_subset hp))
    (fun p hp => (hprefix p (interior_subset hp)).1)
    (Real.exp_pos (-1)) (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0))
    (fun p hp => (hprefix p (interior_subset hp)).2)
  simpa only [Real.exp_neg, inv_inv] using hb

end ScalarMonotone.EndOfPaper
end
