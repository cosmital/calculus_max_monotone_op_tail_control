import EndOfPaper.SignedHardySum
import EndOfPaper.LocalHardy

/-!
The literal averaged ordinary finite sum of marginal Hardy
graphs, its maximality, completed domains and selection values,
and the whole comparison of any integrable quantile with its Hardy graph.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def replicatedHardyEnvelope {n : ℕ} (laws : Fin n → Measure ℝ) : Operator :=
  outputScale ((n : ℝ)⁻¹) (finiteSum (fun i => quantileHardy (laws i)))

theorem replicatedHardyEnvelope_properties {n : ℕ} (hn : 0 < n)
    (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    MaximalDecreasing (replicatedHardyEnvelope laws) ∧
      dom (replicatedHardyEnvelope laws) ⊆ Icc (0 : ℝ) 1 ∧
      Ioo (0 : ℝ) 1 ⊆ dom (replicatedHardyEnvelope laws) := by
  classical
  have hProp (i) := quantileHardy_properties (laws i) (hi i)
  have hCover (i : Fin n) : Ioo (0 : ℝ) 1 ⊆ dom (quantileHardy (laws i)) := by
    intro p hp
    apply interior_subset
    rwa [(hProp i).2.1]
  let f : Fin n → Operator := fun i => quantileHardy (laws i)
  have hSum := finiteSum_maximal_decreasing f (fun i => (hProp i).1)
    ⟨1/2, fun i => hCover i (by norm_num)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨outputScale_maximal_decreasing (inv_pos.mpr hn0) hSum, ?_, ?_⟩
  · rw [replicatedHardyEnvelope, dom_outputScale]
    rintro p ⟨v, a, ha, hv⟩
    let i₀ : Fin n := ⟨0, hn⟩
    exact (hProp i₀).2.2 ⟨a i₀, ha i₀⟩
  · rw [replicatedHardyEnvelope, dom_outputScale]
    intro p hp
    choose a ha using (fun i => hCover i hp)
    exact ⟨∑ i, a i, a, ha, rfl⟩

theorem replicatedHardyEnvelope_singletons {n : ℕ} (laws : Fin n → Measure ℝ)
    {p : ℝ} {a : Fin n → ℝ} (ha : ∀ i, quantileHardy (laws i) p = {a i}) :
    replicatedHardyEnvelope laws p = {(∑ i, a i)/(n : ℝ)} := by
  have hSum := finiteSum_singletons ha
  simp [replicatedHardyEnvelope, outputScale, hSum, div_eq_mul_inv, mul_comm]

theorem replicatedHardyEnvelope_selection_value {n : ℕ} (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i))
    {q : Fin n → ℝ → ℝ} (hm : ∀ i, Measurable (q i))
    (hs : ∀ i, ∀ u ∈ Ioo 0 1, q i u ∈ tailQuantile (laws i) u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    replicatedHardyEnvelope laws p = {(∑ i, hardyScalar (q i) p)/(n : ℝ)} := by
  apply replicatedHardyEnvelope_singletons
  intro i
  exact hardy_tailQuantile_fiber (laws i) (hi i) (hm i) (hs i) hp

theorem tailQuantile_le_quantileHardy (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun x : ℝ => x) ν) : DecLE (tailQuantile ν) (quantileHardy ν) := by
  have hCover : Ioo (0 : ℝ) 1 ⊆ dom (tailQuantile ν) :=
    fun p hp => tailQuantile_fiber_nonempty ν hp
  have hDom : dom (tailQuantile ν) ⊆ Icc (0 : ℝ) 1 := by
    rintro p ⟨a, ha⟩
    change ν.real (Ioi a) ≤ p ∧ p ≤ ν.real (Ici a) at ha
    exact ⟨measureReal_nonneg.trans ha.1, ha.2.trans measureReal_le_one⟩
  have hzero : IsGLB (dom (tailQuantile ν)) 0 := by
    refine ⟨fun p hp => (hDom hp).1, ?_⟩
    intro z hz
    exact (isGLB_Ioo (zero_lt_one : (0 : ℝ) < 1)).2
      (fun p hp => hz (hCover hp))
  obtain ⟨q, hqm, hs⟩ := exists_global_measurable_selection
    (Or.inr (tailQuantile_maximal ν).1) measurableSet_Ioo hCover
  have hsel : SelectionOn (tailQuantile ν) (interior (dom (tailQuantile ν))) q := by
    simpa only [tailQuantile_domain_interior] using hs
  have hqi : Integrable q (volume.restrict (interior (dom (tailQuantile ν)))) := by
    simpa only [tailQuantile_domain_interior, unitUniform] using
      quantile_selection_integrable ν hi hqm hs
  exact le_hardyFamilyIntegral (tailQuantile_maximal ν) hzero
    ⟨1/2, hCover (by norm_num), by norm_num⟩ hsel hqi

end ScalarMonotone.EndOfPaper
end
