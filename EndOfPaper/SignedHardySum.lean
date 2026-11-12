import EndOfPaper.HardyDomination
import MonotoneOperators.ProbabilityCore

/-!
Signed original-space Hardy sum inequalities, including the literal
ordinary finite graph sum and all completed boundary fibers. No
nonnegativity or independence of the random variables is assumed.
-/

open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem signed_hardy_sum_values {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : ι → ℝ, ∃ v : ℝ,
      (∀ i, quantileHardy (Measure.map (X i) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => ∑ i, X i ω) μ) p = {v} ∧
      v ≤ ∑ i, a i := by
  have hSm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ (fun i _ => hm i)
  have hSi : Integrable (fun ω => ∑ i, X i ω) μ := integrable_finset_sum _ (fun i _ => hi i)
  choose a ha hleast hdual hweighted hsup harg using
    (fun i => hardy_quantile_original_variational (hm i) (hi i) hp)
  obtain ⟨v, hv, _, hVdual, _, _, _⟩ := hardy_quantile_original_variational hSm hSi hp
  obtain ⟨W, hWm, hWb, hWp, hWv⟩ := hVdual.1
  have hbound (i : ι) : (∫ ω, X i ω*W ω ∂μ)/p ≤ a i :=
    (hdual i).2 ⟨W, hWm, hWb, hWp, rfl⟩
  refine ⟨a, v, ha, hv, ?_⟩
  rw [hWv]
  calc
    (∫ ω, (∑ i, X i ω)*W ω ∂μ)/p = (∫ ω, ∑ i, X i ω*W ω ∂μ)/p := by
      simp_rw [Finset.sum_mul]
    _ = (∑ i, ∫ ω, X i ω*W ω ∂μ)/p := by
      rw [integral_finset_sum _ (fun i _ => integrable_mul_unit_weight (hi i) hWm hWb)]
    _ = ∑ i, (∫ ω, X i ω*W ω ∂μ)/p := Finset.sum_div _ _ _
    _ ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => hbound i)

theorem finiteSum_singletons {ι : Type*} [Fintype ι] {f : ι → Operator}
    {p : ℝ} {a : ι → ℝ} (ha : ∀ i, f i p = {a i}) :
    finiteSum f p = {∑ i, a i} := by
  ext v
  constructor
  · rintro ⟨b, hb, hv⟩
    have he : b = a := funext (fun i => mem_singleton_iff.mp ((ha i) ▸ hb i))
    exact mem_singleton_iff.mpr (by simpa only [he] using hv)
  · intro hv
    exact ⟨a, fun i => by rw [ha i]; rfl, mem_singleton_iff.mp hv⟩

theorem signed_hardy_sum_operator_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) μ) :
    MaximalDecreasing (finiteSum (fun i => quantileHardy (Measure.map (X i) μ))) ∧
      DecLE (quantileHardy (Measure.map (fun ω => ∑ i, X i ω) μ))
        (finiteSum (fun i => quantileHardy (Measure.map (X i) μ))) := by
  classical
  let f : ι → Operator := fun i => quantileHardy (Measure.map (X i) μ)
  have hf (i) := quantileHardy_original_properties μ (hm i) (hi i)
  have hfi (i) : Ioo (0 : ℝ) 1 ⊆ dom (f i) := by
    intro p hp
    apply interior_subset
    change p ∈ interior (dom (quantileHardy (Measure.map (X i) μ)))
    rwa [(hf i).2.1]
  have hG : MaximalDecreasing (finiteSum f) := finiteSum_maximal_decreasing f
    (fun i => (hf i).1) ⟨1/2, fun i => hfi i (by norm_num)⟩
  have hGdom : dom (finiteSum f) ⊆ Icc (0 : ℝ) 1 := by
    rintro p ⟨v, a, ha, hv⟩
    let i₀ : ι := Classical.choice inferInstance
    exact (hf i₀).2.2 ⟨a i₀, ha i₀⟩
  have hGcover : Ioo (0 : ℝ) 1 ⊆ dom (finiteSum f) := by
    intro p hp
    choose a ha using (fun i => hfi i hp)
    exact ⟨∑ i, a i, a, ha, rfl⟩
  have hSm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ (fun i _ => hm i)
  have hSi : Integrable (fun ω => ∑ i, X i ω) μ := integrable_finset_sum _ (fun i _ => hi i)
  have hS := quantileHardy_original_properties μ hSm hSi
  refine ⟨hG, ?_⟩
  apply decLE_of_initial_interior hS.1.1 hG.1 isOpen_Ioo ordConnected_Ioo
    (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩)
    (by rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]; exact ⟨le_rfl, zero_le_one⟩)
    (by simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hS.2.2)
    (fun p hp => (hGdom hp).1)
    (fun p hp => interior_subset (by rwa [hS.2.1])) hGcover
  intro p hp r hr hrp u hu v hv
  obtain ⟨a, b, ha, hb, hbound⟩ := signed_hardy_sum_values μ X hm hi hp
  have hub : u = b := mem_singleton_iff.mp (hb ▸ hu)
  have hpoint : (∑ i, a i) ∈ finiteSum f p :=
    ⟨a, fun i => by change a i ∈ quantileHardy (Measure.map (X i) μ) p; rw [ha i]; rfl, rfl⟩
  rw [hub]
  exact hbound.trans (Decreasing.le_of_lt hG.1 hv hpoint hrp)

end ScalarMonotone.EndOfPaper
end
