import EndOfPaper.ReplicatedHardyValues
import EndOfPaper.ReplicatedHardyEnvelope

/-!
The whole completed original-space upper bound for every
replicated average. Coordinate L1 is derived from the prescribed
marginal laws; signs, atoms and arbitrary dependence are retained.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem replicated_average_operator_bound {Ω : Type*} [MeasurableSpace Ω]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Fin m → Ω → ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hLaw : ∀ i j, Measure.map (X i j) μ = laws i) :
    let Y := fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))
    MaximalDecreasing (replicatedHardyEnvelope laws) ∧
      DecLE (quantileHardy (Measure.map Y μ)) (replicatedHardyEnvelope laws) ∧
      DecLE (tailQuantile (Measure.map Y μ)) (replicatedHardyEnvelope laws) := by
  classical
  let Y := fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))
  have hXi (i : Fin n) (j : Fin m) : Integrable (X i j) μ := by
    have hid : Integrable (fun x : ℝ => x) (Measure.map (X i j) μ) := by
      rw [hLaw i j]
      exact hi i
    exact hid.comp_measurable (hXm i j)
  have hYm : Measurable Y := (Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => hXm i j))).div_const _
  have hYi : Integrable Y μ := (integrable_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hXi i j))).div_const _
  have hH := replicatedHardyEnvelope_properties hn laws hi
  have hY := quantileHardy_original_properties μ hYm hYi
  have hBound : DecLE (quantileHardy (Measure.map Y μ)) (replicatedHardyEnvelope laws) := by
    apply decLE_of_initial_interior hY.1.1 hH.1.1 isOpen_Ioo ordConnected_Ioo
      (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩)
      (by rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]; exact ⟨le_rfl, zero_le_one⟩)
      (by simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hY.2.2)
      (fun x hx => (hH.2.1 hx).1)
      (fun x hx => interior_subset (by rwa [hY.2.1])) hH.2.2
    intro p hp r hr hrp u hu v hv
    obtain ⟨a, b, ha, hb, hbound⟩ := replicated_average_hardy_values hn hm μ laws X hXm hXi hLaw hp
    have heH := replicatedHardyEnvelope_singletons laws ha
    have heu : u = b := by
      change u ∈ quantileHardy (Measure.map
        (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ) p at hu
      rw [hb] at hu
      exact mem_singleton_iff.mp hu
    have hmid : (∑ i, a i)/(n : ℝ) ∈ replicatedHardyEnvelope laws p := by
      rw [heH]
      rfl
    exact heu ▸ hbound.trans (Decreasing.le_of_lt hH.1.1 hv hmid hrp)
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hYm.aemeasurable
  have hid : Integrable (fun x : ℝ => x) (Measure.map Y μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hYm.aemeasurable).mpr hYi
  exact ⟨hH.1, hBound, decLE_trans (tailQuantile_maximal (Measure.map Y μ)) hY.1 hH.1
    (tailQuantile_le_quantileHardy (Measure.map Y μ) hid) hBound⟩

end ScalarMonotone.EndOfPaper
end
