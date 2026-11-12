import EndOfPaper.ReplicatedQuantileFamily
import MonotoneOperators.ExtremaComplete

/-!
The exact universal replicated quantile envelope as a whole
completed lattice supremum over arbitrary original probability
spaces and all couplings, with every lower witness constructed.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper
universe u

theorem replicatedQuantileFamily_near {n : ℕ} (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ a ∈ replicatedHardyEnvelope laws p, ∀ t < a,
      ∀ r ∈ Ioo (0 : ℝ) p,
        ∃ C ∈ replicatedQuantileFamily.{u} laws, ∃ z ∈ C r, t < z := by
  classical
  have hq (i : Fin n) : ∃ q : ℝ → ℝ, Measurable q ∧
      ∀ p ∈ Ioo (0 : ℝ) 1, q p ∈ tailQuantile (laws i) p :=
    exists_global_measurable_selection (Or.inr (tailQuantile_maximal (laws i)).1)
      measurableSet_Ioo (fun p hp => tailQuantile_fiber_nonempty (laws i) hp)
  choose q hqm hs using hq
  have hqi (i : Fin n) : Integrable (q i) unitUniform :=
    quantile_selection_integrable (laws i) (hi i) (hqm i) (hs i)
  intro p hp a ha t ht r hr
  have heH := replicatedHardyEnvelope_selection_value laws hi hqm hs hp
  have hea : a = (∑ i, hardyScalar (q i) p)/(n : ℝ) := by
    rw [heH] at ha
    exact mem_singleton_iff.mp ha
  obtain ⟨m, hm, hP⟩ := replicaAverage_near_mean hqm hqi hp (hea ▸ ht) hr
  letI : IsProbabilityMeasure iidUniformMeasure := iidUniformMeasure_probability
  let μ := twoBranchMeasure p iidUniformMeasure
  letI : IsProbabilityMeasure μ := twoBranchMeasure_probability iidUniformMeasure hp
  let X : Fin n → Fin m → (ℝ × (ℕ → ℝ)) → ℝ :=
    fun i j => quantileReplica q p i j.val
  have hXm (i : Fin n) (j : Fin m) : Measurable (X i j) :=
    quantileReplica_measurable hqm p i j.val
  have hLaw (i : Fin n) (j : Fin m) : Measure.map (X i j) μ = laws i :=
    (quantileReplica_law hqm hp i j.val).trans
      (tailQuantile_selection_law (laws i) (hqm i) (hs i))
  let Y := fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))
  have hYm : Measurable Y := (Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => hXm i j))).div_const _
  have hYrep : Y = replicaAverage q p m := by
    funext ω
    dsimp [Y, replicaAverage, X]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_range (fun j : ℕ => quantileReplica q p i j ω)]
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hYm.aemeasurable
  let C : DecGraph := ⟨tailQuantile (Measure.map Y μ), tailQuantile_maximal _⟩
  have hC : C ∈ replicatedQuantileFamily.{u} laws :=
    replicatedQuantileFamily_of_model (by omega) laws μ X hXm hLaw rfl
  have hTail : r < (Measure.map Y μ).real (Ioi t) := by
    rw [measureReal_def, Measure.map_apply hYm measurableSet_Ioi]
    change r < μ.real {ω | t < Y ω}
    rw [hYrep]
    exact hP
  obtain ⟨z, hz⟩ := tailQuantile_fiber_nonempty (Measure.map Y μ)
    (show r ∈ Ioo (0 : ℝ) 1 from ⟨hr.1, hr.2.trans hp.2⟩)
  exact ⟨C, hC, z, hz, tail_probability_lt_quantile (Measure.map Y μ) hTail hz⟩

theorem replicated_quantile_envelope_isLUB {n : ℕ} (hn : 0 < n)
    (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    IsLUB (replicatedQuantileFamily.{u} laws)
      (⟨replicatedHardyEnvelope laws, (replicatedHardyEnvelope_properties hn laws hi).1⟩ : DecGraph) := by
  have hH := replicatedHardyEnvelope_properties hn laws hi
  apply quantile_family_isLUB (replicatedQuantileFamily_nonempty laws)
    (replicatedQuantileFamily_domains laws) _ hH.2.1 hH.2.2
    (replicatedQuantileFamily_upper hn laws hi)
  exact replicatedQuantileFamily_near laws hi

theorem universal_replicated_quantile_envelope {n : ℕ} (hn : 0 < n)
    (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    (sSup (replicatedQuantileFamily.{u} laws)).val =
      outputScale ((n : ℝ)⁻¹) (finiteSum (fun i =>
        hardyFamilyIntegral (interior (dom (tailQuantile (laws i)))) (tailQuantile (laws i)))) := by
  have he := (replicated_quantile_envelope_isLUB.{u} hn laws hi).csSup_eq
    (replicatedQuantileFamily_nonempty laws)
  exact congrArg DecGraph.val he

end ScalarMonotone.EndOfPaper
end
