import EndOfPaper.ProfileInverseConcavity
import EndOfPaper.LocalHardy

/-!
Prefix scalar bounds extend to the entire completed Hardy graph,
including different upper domain endpoints. Inversion gives the
whole output-scale bound with all boundary fibers retained.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hardyFamilyIntegral_le_inputDilation {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ p ∈ dom f, 0 < p)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hbound : ∀ p ∈ interior (dom f), hardyScalar s p ≤ s (c*p)) :
    DecLE (hardyFamilyIntegral (interior (dom f)) f) (positiveInputDilation c f) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hH := hardyFamilyIntegral_of_locally_integrable hf hz hp hs hi
  have hG := positiveInputDilation_maximal hf hc
  have hcoverH : interior (dom f) ⊆ dom (hardyFamilyIntegral (interior (dom f)) f) := by
    intro p hpI
    exact ⟨hardyScalar s p, by rw [hH.2.2.2.1 p hpI]; exact mem_singleton _⟩
  have hcoverG : interior (dom f) ⊆ dom (positiveInputDilation c f) := by
    intro p hpI
    exact ⟨s (c*p), hs _ (hscale c ⟨hc, hc1⟩ p hpI)⟩
  have hGdom : dom (positiveInputDilation c f) ⊆ Ici (0 : ℝ) := by
    rintro x ⟨v, hv⟩
    have hcx : 0 ≤ c*x := hz.1 ⟨v, hv⟩
    exact nonneg_of_mul_nonneg_right hcx hc
  apply decLE_of_initial_interior hH.1.1 hG.1 isOpen_interior hord hne
    (zero_mem_closure_decreasing_domain_interior hf hz hne) hH.2.2.1 hGdom hcoverH hcoverG
  intro p hpI r hrI hrp u hu v hv
  rw [hH.2.2.2.1 p hpI] at hu
  rw [mem_singleton_iff.mp hu]
  have hvf : v ∈ f (c*r) := hv
  exact (hbound p hpI).trans
    (Decreasing.le_of_lt hf.1 hvf (hs _ (hscale c ⟨hc, hc1⟩ p hpI))
      (mul_lt_mul_of_pos_left hrp hc))

theorem hardyTailTransform_bound_of_scalar {α : Operator} (hα : MaximalDecreasing α)
    (hz : IsGLB (ran α) 0) (hp : ∃ p ∈ ran α, 0 < p)
    {q : ℝ → ℝ} (hq : SelectionOn (inverse α) (interior (ran α)) q)
    (hi : ∀ p ∈ interior (ran α), IntervalIntegrable q volume 0 p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hbound : ∀ p ∈ interior (ran α), hardyScalar q p ≤ q (c*p)) :
    MaximalDecreasing (hardyTailTransform α) ∧
      DecLE (hardyTailTransform α) (outputScale c⁻¹ α) := by
  have hH := hardyTailTransform_well_defined hα hz hp hq hi
  have hb := hardyFamilyIntegral_le_inputDilation (inverse_maximal_decreasing hα)
    hz hp hq hi hc hc1 hbound
  refine ⟨hH.1, ?_⟩
  have hinv := decLE_inverse_iff.mpr hb
  rw [inverse_positiveInputDilation hc.ne', inverse_inverse] at hinv
  exact hinv

end ScalarMonotone.EndOfPaper
end
