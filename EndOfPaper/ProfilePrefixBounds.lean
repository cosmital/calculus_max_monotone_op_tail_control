import EndOfPaper.ProfileGeometry
import EndOfPaper.ProfileInverseConcavity
import EndOfPaper.ProfileScalarJensen
import EndOfPaper.HardyOperatorAggregation

/-!
All prefix integrability and precise inverse-profile Hardy bounds
derived from the original convex forward-transform hypotheses. The
positive range endpoint is extended real, including infinity.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positiveInitialInterval_isGLB {L : EReal} (hL : 0 < L) :
    IsGLB (positiveInitialInterval L) 0 := by
  induction L with
  | bot => exact (not_lt_bot hL).elim
  | coe L =>
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have he : positiveInitialInterval (L : EReal) = Ioo (0 : ℝ) L := by
      ext p
      simp [positiveInitialInterval]
    rw [he]
    exact isGLB_Ioo hLr
  | top =>
    have he : positiveInitialInterval ⊤ = Ioi (0 : ℝ) := by
      ext p
      simp [positiveInitialInterval]
    rw [he]
    exact isGLB_Ioi

theorem prefix_congr_positive {f g : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hfg : ∀ t > 0, f t = g t) :
    (IntervalIntegrable f volume 0 p ↔ IntervalIntegrable g volume 0 p) ∧
      hardyScalar f p = hardyScalar g p := by
  have he : f =ᵐ[volume.restrict (Ι (0 : ℝ) p)] g := by
    apply (ae_restrict_mem measurableSet_uIoc).mono
    intro t ht
    rw [uIoc_of_le hp.le] at ht
    exact hfg t ht.1
  exact ⟨⟨fun h => h.congr he, fun h => h.congr he.symm⟩,
    congrArg (fun z => z/p) (intervalIntegral.integral_congr_ae_restrict he)⟩

theorem hardy_profile_power_prefix {α : Operator} {a : ℝ → ℝ} {L : EReal} {κ : ℝ}
    (hα : MaximalDecreasing α) (ha : ∀ x ∈ dom α, α x = {a x})
    (hm : StrictAntiOn a (dom α)) (hL : 0 < L)
    (hrange : ran α = positiveInitialInterval L) (hκ : 1 < κ)
    (hc : ConvexOn ℝ (dom α) (fun x => (a x)^((-1 : ℝ)/κ))) :
    ∃ q : ℝ → ℝ, Measurable q ∧ SelectionOn (inverse α) (ran α) q ∧
      ∀ p ∈ ran α, IntervalIntegrable q volume 0 p ∧
        hardyScalar q p ≤ q ((κ/(κ-1))^(-κ)*p) := by
  have ho : IsOpen (ran α) := by rw [hrange]; exact (positiveInitialInterval_geometry hL).1
  have hz : IsGLB (ran α) 0 := by rw [hrange]; exact positiveInitialInterval_isGLB hL
  obtain ⟨p₀, hp₀⟩ := (positiveInitialInterval_geometry hL).2.2.1
  have hp₀r : p₀ ∈ ran α := hrange.symm ▸ hp₀
  have hp₀pos : 0 < p₀ := (positiveInitialInterval_geometry hL).2.2.2.1 _ hp₀
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := profile_range_initial_geometry hα ho hz ⟨p₀, hp₀r, hp₀pos⟩
  obtain ⟨q, hqm, hq⟩ := exists_global_measurable_selection
    (Or.inr (inverse_maximal_decreasing hα).1) ho.measurableSet (by simp only [dom_inverse]; exact Subset.rfl)
  have haPos (x) (hx : x ∈ dom α) : 0 < a x :=
    hpos _ ⟨x, by rw [ha x hx]; exact mem_singleton _⟩
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  let U := powerSubstitutionDomain (ran α) κ
  let g : ℝ → ℝ := fun y => q (y^(-κ))
  have hUg := powerSubstitutionDomain_geometry ho hprefix hk0
  have hgMap : MapsTo g U (dom α) := fun y hy =>
    (inverse_selection_singleton_of_strictAnti ha hm hq hy.2).2.1
  have hgInv : ∀ y ∈ U, (a (g y))^((-1 : ℝ)/κ) = y := by
    intro y hy
    change (a (q (y^(-κ))))^((-1 : ℝ)/κ) = y
    rw [(inverse_selection_singleton_of_strictAnti ha hm hq hy.2).2.2,
      ← Real.rpow_mul hy.1.le,
      show (-κ)*((-1 : ℝ)/κ) = 1 by field_simp,
      Real.rpow_one]
  have hgConc : ConcaveOn ℝ U g := concaveOn_of_convexOn_right_inverse
    hc (power_transform_strictMono hm haPos hk0) hUg.2.1 hgMap hgInv
  have hgMono : MonotoneOn g U := monotoneOn_of_strictMonoOn_right_inverse
    (power_transform_strictMono hm haPos hk0) hgMap hgInv
  have hcomp (t : ℝ) (ht : 0 < t) : g (t^((-1 : ℝ)/κ)) = q t := by
    dsimp [g]
    rw [← Real.rpow_mul ht.le,
      show ((-1 : ℝ)/κ)*(-κ) = 1 by field_simp, Real.rpow_one]
  refine ⟨q, hqm, hq, ?_⟩
  intro p hp
  have hxp : p^((-1 : ℝ)/κ) ∈ U := powerSubstitutionDomain_point hk0 (hpos p hp) hp
  obtain ⟨hi, hJ⟩ := power_inverse_profile_jensen hgConc hgMono hUg.1 hκ (hpos p hp)
    hxp (hUg.2.2 _ hxp)
  have hcongr := prefix_congr_positive (hpos p hp) hcomp
  refine ⟨hcongr.1.mp hi, ?_⟩
  rw [hcongr.2] at hJ
  have hK : 0 < κ/(κ-1) := div_pos hk0 (sub_pos.mpr hκ)
  have he : g ((κ/(κ-1))*p^((-1 : ℝ)/κ)) = q ((κ/(κ-1))^(-κ)*p) := by
    dsimp [g]
    rw [Real.mul_rpow hK.le (Real.rpow_pos_of_pos (hpos p hp) _).le,
      ← Real.rpow_mul (hpos p hp).le,
      show ((-1 : ℝ)/κ)*(-κ) = 1 by field_simp, Real.rpow_one]
  exact he ▸ hJ

theorem hardy_profile_exponential_prefix {α : Operator} {a : ℝ → ℝ} {L : EReal}
    (hα : MaximalDecreasing α) (ha : ∀ x ∈ dom α, α x = {a x})
    (hm : StrictAntiOn a (dom α)) (hL : 0 < L)
    (hrange : ran α = positiveInitialInterval L)
    (hc : ConvexOn ℝ (dom α) (fun x => -Real.log (a x))) :
    ∃ q : ℝ → ℝ, Measurable q ∧ SelectionOn (inverse α) (ran α) q ∧
      ∀ p ∈ ran α, IntervalIntegrable q volume 0 p ∧
        hardyScalar q p ≤ q (Real.exp (-1)*p) := by
  have ho : IsOpen (ran α) := by rw [hrange]; exact (positiveInitialInterval_geometry hL).1
  have hz : IsGLB (ran α) 0 := by rw [hrange]; exact positiveInitialInterval_isGLB hL
  obtain ⟨p₀, hp₀⟩ := (positiveInitialInterval_geometry hL).2.2.1
  have hp₀r : p₀ ∈ ran α := hrange.symm ▸ hp₀
  have hp₀pos : 0 < p₀ := (positiveInitialInterval_geometry hL).2.2.2.1 _ hp₀
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := profile_range_initial_geometry hα ho hz ⟨p₀, hp₀r, hp₀pos⟩
  obtain ⟨q, hqm, hq⟩ := exists_global_measurable_selection
    (Or.inr (inverse_maximal_decreasing hα).1) ho.measurableSet (by simp only [dom_inverse]; exact Subset.rfl)
  have haPos (x) (hx : x ∈ dom α) : 0 < a x :=
    hpos _ ⟨x, by rw [ha x hx]; exact mem_singleton _⟩
  let U := exponentialSubstitutionDomain (ran α)
  let g : ℝ → ℝ := fun y => q (Real.exp (-y))
  have hUg := exponentialSubstitutionDomain_geometry ho hprefix
  have hgMap : MapsTo g U (dom α) := fun y hy =>
    (inverse_selection_singleton_of_strictAnti ha hm hq hy).2.1
  have hgInv : ∀ y ∈ U, -Real.log (a (g y)) = y := by
    intro y hy
    change -Real.log (a (q (Real.exp (-y)))) = y
    rw [(inverse_selection_singleton_of_strictAnti ha hm hq hy).2.2, Real.log_exp, neg_neg]
  have hgConc : ConcaveOn ℝ U g := concaveOn_of_convexOn_right_inverse
    hc (logarithmic_transform_strictMono hm haPos) hUg.2.1 hgMap hgInv
  have hgMono : MonotoneOn g U := monotoneOn_of_strictMonoOn_right_inverse
    (logarithmic_transform_strictMono hm haPos) hgMap hgInv
  have hcomp (t : ℝ) (ht : 0 < t) : g (-Real.log t) = q t := by
    dsimp [g]
    rw [neg_neg, Real.exp_log ht]
  refine ⟨q, hqm, hq, ?_⟩
  intro p hp
  have hxp : -Real.log p ∈ U := exponentialSubstitutionDomain_point (hpos p hp) hp
  obtain ⟨hi, hJ⟩ := exponential_inverse_profile_jensen hgConc hgMono hUg.1 (hpos p hp)
    hxp (hUg.2.2 _ hxp)
  have hcongr := prefix_congr_positive (hpos p hp) hcomp
  refine ⟨hcongr.1.mp hi, ?_⟩
  rw [hcongr.2] at hJ
  have he : g (1-Real.log p) = q (Real.exp (-1)*p) := by
    dsimp [g]
    rw [show -(1-Real.log p) = -1+Real.log p by ring,
      Real.exp_add, Real.exp_log (hpos p hp)]
  exact he ▸ hJ

end ScalarMonotone.EndOfPaper
end
