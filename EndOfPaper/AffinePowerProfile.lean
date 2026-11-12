import EndOfPaper.AffinePowerGeometric
import EndOfPaper.MonotoneScalarAggregation
import EndOfPaper.GeometricScalarCompletion
import EndOfPaper.ContinuousSelections
import EndOfPaper.GeometricProduct

/-!
The actual completed affine-power profile and whole geometric operator bound, without an arithmetic L1 assumption.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem affine_power_scalar_antitone {m c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α) :
    AntitoneOn (fun x : ℝ => m+c*x^(-α)) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx.1 hxy (neg_nonpos.mpr hα.le)) hc) m

def affinePowerProfile (m c α : ℝ) (hc : 0 ≤ c) (hα : 0 < α) : DecGraph :=
  ⟨completedDecreasingRestriction (Ioo (0 : ℝ) 1) (ofFun (fun x => m+c*x^(-α))),
    (antitone_scalar_completion_properties isOpen_Ioo ordConnected_Ioo
      (nonempty_Ioo.mpr zero_lt_one) (affine_power_scalar_antitone hc hα)).1⟩

theorem affine_power_profile_properties {m c α : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) :
    let q := affinePowerProfile m c α hc hα
    interior (dom q.val) = Ioo (0 : ℝ) 1 ∧
    (∀ p ∈ Ioo (0 : ℝ) 1, q.val p = {m+c*p^(-α)}) ∧
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val p, 0 ≤ v := by
  dsimp only
  have hR := antitone_scalar_completion_properties isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one) (affine_power_scalar_antitone (m := m) hc hα)
  have hdom : Ioo (0 : ℝ) 1 ⊆ dom (affinePowerProfile m c α hc hα).val :=
    fun p hp => ⟨m+c*p^(-α),hR.2.2.2 p hp⟩
  have hcont : ContinuousOn (fun x : ℝ => m+c*x^(-α)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')))
  have hval (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
      (affinePowerProfile m c α hc hα).val p = {m+c*p^(-α)} :=
    fiber_of_continuous_selection (Or.inr (affinePowerProfile m c α hc hα).property)
      isOpen_Ioo hdom hR.2.2.2 hcont hp
  refine ⟨hR.2.1,hval,?_⟩
  intro p hp v hv
  rw [hval p hp] at hv
  have he : v = m+c*p^(-α) := hv
  rw [he]
  exact add_nonneg hm (mul_nonneg hc (Real.rpow_nonneg hp.1.le _))

theorem affine_power_positive_log_area {m c α : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (m+c*x^(-α))) 0)) < ∞ := by
  by_cases hzero : m+c = 0
  · have hm0 : m = 0 := by linarith only [hm,hc,hzero]
    have hc0 : c = 0 := by linarith only [hm0,hzero]
    simp only [hm0,hc0,zero_mul,zero_add,Real.log_zero,max_self,ENNReal.ofReal_zero,lintegral_zero]
    exact ENNReal.zero_lt_top
  · have hpos : 0 < m+c := lt_of_le_of_ne (add_nonneg hm hc) (Ne.symm hzero)
    have hi := affine_power_prefix_log_integrable hm hc hα zero_lt_one
      (by simpa only [Real.one_rpow,mul_one] using hpos)
    have hi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mp hi
    have hNN : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        (fun x => max (Real.log (m+c*x^(-α))) 0) := Eventually.of_forall (fun _ => le_max_right _ _)
    exact (hasFiniteIntegral_iff_ofReal hNN).mp hi'.pos_part.hasFiniteIntegral

theorem affine_power_geometric_bound {m c α : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) :
    let q := affinePowerProfile m c α hc hα
    MaximalDecreasing (geometricHardyTransform 1 q) ∧
    DecLE (geometricHardyTransform 1 q) (outputScale (Real.exp α) q.val) ∧
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ geometricHardyTransform 1 q p,
      v ≤ Real.exp α*(m+c*p^(-α)) := by
  dsimp only
  let q := affinePowerProfile m c α hc hα
  have hq := affine_power_profile_properties hm hc hα
  have hs : SelectionOn q.val (Ioo (0 : ℝ) 1) (fun x => m+c*x^(-α)) := by
    intro p hp
    rw [hq.2.1 p hp]
    rfl
  have hmS : Measurable (fun x : ℝ => m+c*x^(-α)) := by fun_prop
  have hP := affine_power_positive_log_area hm hc hα
  have hG := geometricHardyTransform_well_defined zero_lt_one hq.1 hq.2.2 hmS hs hP
  have hGS := geometric_hardy_scalar_selection_measurable zero_lt_one hq.1 hq.2.2 hmS hs hP
  have hScale : MaximalDecreasing (outputScale (Real.exp α) q.val) :=
    outputScale_maximal_decreasing (Real.exp_pos α) q.property
  have hScaleI : interior (dom (outputScale (Real.exp α) q.val)) = Ioo (0 : ℝ) 1 := by
    rw [dom_outputScale]
    exact hq.1
  have hScaleS : SelectionOn (outputScale (Real.exp α) q.val) (Ioo (0 : ℝ) 1)
      (fun x => Real.exp α*(m+c*x^(-α))) :=
    fun x hx => ⟨_,hs x hx,rfl⟩
  have hOrd : DecLE (geometricHardyTransform 1 q) (outputScale (Real.exp α) q.val) := by
    apply initial_decLE_of_selection_ae_le zero_lt_one hG.1 hScale hG.2.1 hScaleI hGS hScaleS
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    exact geometricPrefixValue_affine_power_bound hm hc hα hp.1
  refine ⟨hG.1,hOrd,?_⟩
  intro p hp v hv
  obtain ⟨w,hw,hle⟩ := (decLE_fiber hG.1 hScale hOrd ⟨v,hv⟩ ⟨_,hScaleS p hp⟩).2
    (mem_lowerHull hv)
  obtain ⟨u,hu,rfl⟩ := hw
  rw [hq.2.1 p hp] at hu
  have he : u = m+c*p^(-α) := hu
  rwa [he] at hle

end ScalarMonotone.EndOfPaper
end
