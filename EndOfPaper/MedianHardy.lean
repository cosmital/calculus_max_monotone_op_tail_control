import EndOfPaper.NormExamples
import EndOfPaper.MedianSharpness
import MonotoneOperators.ExtremaFinite

/-!
The full odd-median Hardy corollary. The right side is the literal
finite lattice infimum of positively scaled ordinary finite graph sums.
Whole comparisons retain all endpoint fibers; its exact scalar cut
minimum and both general/comonotone sharp suprema are identified.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def medianCutLinear (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (a : CoordinateVector (2*r+1)) : ℝ :=
  (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ)

theorem medianCutLinear_axioms (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ) :
    AggregationAxioms (medianCutLinear r ℓ J) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) (by positivity)
  · intro a b ha hab
    change (∑ i ∈ J.val, a i) / _ ≤ (∑ i ∈ J.val, b i) / _
    have hd : 0 ≤ (((ℓ.val+1 : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun i _ => hab i)) hd
  · intro c hc a ha
    simp only [medianCutLinear, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

theorem medianCutLinear_continuous (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ) :
    Continuous (medianCutLinear r ℓ J) :=
  (continuous_finset_sum J.val (fun i _ => continuous_apply i)).div_const _

def medianCutSum (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → Operator) : Operator :=
  outputScale (1 / ((ℓ.val+1 : ℕ) : ℝ))
    (finiteOperatorSum (fun i => if i ∈ J.val then f i else ofFun (fun _ => 0)))

theorem finiteOperatorSum_dom_component {n : ℕ} (f : Fin n → Operator) (i : Fin n) :
    dom (finiteOperatorSum f) ⊆ dom (f i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rintro x ⟨z, u, hu, v, hv, he⟩
      exact ⟨u, hu⟩
    · rintro x ⟨z, u, hu, v, hv, he⟩
      exact ih (fun j => f j.succ) j ⟨v, hv⟩

theorem medianCutSum_maximal (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → Operator) (hf : ∀ i, MaximalDecreasing (f i))
    (hd : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (f i)) : MaximalDecreasing (medianCutSum r ℓ J f) := by
  classical
  apply outputScale_maximal_decreasing (by positivity)
  apply (finiteOperatorSum_properties _ ?_
    (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩) ?_).1
  · intro i
    split_ifs with h
    · exact hf i
    · exact constant_maximal_decreasing 0
  · intro i x hx
    split_ifs with h
    · exact hd i hx
    · exact ⟨0, rfl⟩

theorem medianCutSum_dom_subset (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → Operator) (hc : ∀ i, dom (f i) ⊆ closure (Ioo (0 : ℝ) 1)) :
    dom (medianCutSum r ℓ J f) ⊆ closure (Ioo (0 : ℝ) 1) := by
  classical
  have hJ : J.val.Nonempty := Finset.card_pos.mp (by rw [J.property]; omega)
  obtain ⟨j, hj⟩ := hJ
  intro x hx
  change x ∈ dom (outputScale _ (finiteOperatorSum _)) at hx
  rw [dom_outputScale] at hx
  apply hc j
  simpa only [if_pos hj] using (finiteOperatorSum_dom_component _ j hx)

theorem medianCutSum_singleton (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → Operator) {p : ℝ} (a : CoordinateVector (2*r+1))
    (ha : ∀ i, f i p = {a i}) : medianCutSum r ℓ J f p = {medianCutLinear r ℓ J a} := by
  classical
  let b : Fin (2*r+1) → ℝ := fun i => if i ∈ J.val then a i else 0
  have hv (i) : (if i ∈ J.val then f i else ofFun (fun _ => 0)) p = {b i} := by
    by_cases hi : i ∈ J.val
    · simp [b, hi, ha i]
    · simp [b, hi, ofFun]
  have hb : (∑ i, b i) = ∑ i ∈ J.val, a i := by simp [b, Finset.sum_ite]
  rw [medianCutSum, outputScale_fiber_singleton _ (finiteOperatorSum_singleton _ b hv), hb]
  congr 1
  dsimp [medianCutLinear]
  ring

theorem medianCutSum_eq_aggregation (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → Operator) (hf : ∀ i, MaximalDecreasing (f i))
    (hd : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (f i))
    (hc : ∀ i, dom (f i) ⊆ closure (Ioo (0 : ℝ) 1))
    (hp : ∀ i, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ f i x, 0 ≤ v)
    (hv : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ a : Fin (2*r+1) → ℝ, ∀ i, f i x = {a i}) :
    medianCutSum r ℓ J f = aggregationOperator (medianCutLinear r ℓ J) (Ioo 0 1) f := by
  apply aggregationOperator_unique (medianCutLinear_axioms r ℓ J)
    (medianCutLinear_continuous r ℓ J).continuousOn isOpen_Ioo ordConnected_Ioo
    ⟨1/2, by norm_num⟩ hf hd hp (medianCutSum_maximal r ℓ J f hf hd)
    (medianCutSum_dom_subset r ℓ J f hc)
  intro x hx
  obtain ⟨a, ha⟩ := hv x hx
  rw [medianCutSum_singleton r ℓ J f a ha]
  simp only [ha, csInf_singleton, csSup_singleton, Icc_self]

def medianCutGraph (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → DecGraph) (hd : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (f i).val) : DecGraph :=
  ⟨medianCutSum r ℓ J (fun i => (f i).val),
    medianCutSum_maximal r ℓ J _ (fun i => (f i).property) hd⟩

def medianHardyBound {Ω : Type*} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → CoordinateVector (2*r+1))
    (hm : Measurable X) (hi : ∀ i, Integrable (fun ω => X ω i) μ) : DecGraph := by
  let f : Fin (2*r+1) → DecGraph := fun i =>
    ⟨quantileHardy (Measure.map (fun ω => X ω i) μ),
      (quantileHardy_original_properties μ (measurable_pi_iff.mp hm i) (hi i)).1⟩
  have hd (i) : Ioo (0 : ℝ) 1 ⊆ dom (f i).val := by
    intro p hp
    apply interior_subset
    rwa [(quantileHardy_original_properties μ (measurable_pi_iff.mp hm i) (hi i)).2.1]
  exact ⨅ ℓ : Fin (r+1), ⨅ J : medianCutSets r ℓ, medianCutGraph r ℓ J f hd

theorem hardy_tail_median_bound {Ω : Type*} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector (2*r+1)}
    (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : CoordinateVector (2*r+1), ∃ v : ℝ, 0 ≤ a ∧
      (∀ i, quantileHardy (Measure.map (fun ω => X ω i) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => scalarMedian r (X ω)) μ) p = {v} ∧
      v ≤ medianCutBound r a := by
  obtain ⟨a, v, ha, hMarg, hAgg, hb⟩ := hardy_tail_aggregation_ae
    (median_aggregation_axioms r) (scalarMedian_continuous r).continuousOn μ hm hx hi hp
  rw [median_transform_cut_formula r a ha] at hb
  exact ⟨a, v, ha, hMarg, hAgg, hb⟩

theorem hardy_tail_median_operator_bound {Ω : Type*} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector (2*r+1)}
    (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    DecLE (quantileHardy (Measure.map (fun ω => scalarMedian r (X ω)) μ))
      (medianHardyBound r μ X hm hi).val := by
  classical
  let f : Fin (2*r+1) → DecGraph := fun i =>
    ⟨quantileHardy (Measure.map (fun ω => X ω i) μ),
      (quantileHardy_original_properties μ (measurable_pi_iff.mp hm i) (hi i)).1⟩
  have hd (i) : Ioo (0 : ℝ) 1 ⊆ dom (f i).val := by
    intro p hp
    apply interior_subset
    rwa [(quantileHardy_original_properties μ (measurable_pi_iff.mp hm i) (hi i)).2.1]
  have hc (i) : dom (f i).val ⊆ closure (Ioo (0 : ℝ) 1) := by
    simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using
      (quantileHardy_original_properties μ (measurable_pi_iff.mp hm i) (hi i)).2.2
  have hpos (i) : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (f i).val p, 0 ≤ v := by
    intro p hp v hv
    exact quantileHardy_nonnegative μ (measurable_pi_iff.mp hm i) (hi i)
      (hx.mono (fun ω hω => hω i)) hp hv
  have hval : ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a : Fin (2*r+1) → ℝ, ∀ i, (f i).val p = {a i} := by
    intro p hp
    obtain ⟨a, v, ha, hMarg, hAgg, hb⟩ := hardy_tail_median_bound r μ hm hx hi hp
    exact ⟨a, hMarg⟩
  have hagg := aggregation_composition_integrable_ae (median_aggregation_axioms r)
    (scalarMedian_continuous r).continuousOn μ hm.aemeasurable hx hi
  let H : DecGraph :=
    ⟨quantileHardy (Measure.map (fun ω => scalarMedian r (X ω)) μ),
      (quantileHardy_original_properties μ ((scalarMedian_continuous r).measurable.comp hm) hagg).1⟩
  change H ≤ ⨅ ℓ : Fin (r+1), ⨅ J : medianCutSets r ℓ, medianCutGraph r ℓ J f hd
  letI (ℓ : Fin (r+1)) : Nonempty (medianCutSets r ℓ) := medianCutSets_nonempty r ℓ
  apply le_ciInf
  intro ℓ
  apply le_ciInf
  intro J
  change DecLE _ (medianCutSum r ℓ J (fun i => (f i).val))
  rw [medianCutSum_eq_aggregation r ℓ J _ (fun i => (f i).property) hd hc hpos hval]
  exact hardy_tail_operator_bound (median_aggregation_axioms r) (scalarMedian_continuous r)
    (medianCutLinear_axioms r ℓ J) (medianCutLinear_continuous r ℓ J).continuousOn
    (fun a ha => median_transform_subset_upper r (ℓ.val+1) (by omega) J.val J.property ha)
    μ hm hx hi

universe uMedianHardy

/-- Manuscript-facing full corollary: the ordinary sums and finite lattice
infima are retained as completed graphs, together with both exact sharp suprema. -/
theorem sharp_hardy_median {Ω : Type uMedianHardy} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector (2*r+1)}
    (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    DecLE (quantileHardy (Measure.map (fun ω => scalarMedian r (X ω)) μ))
        (medianHardyBound r μ X hm hi).val ∧
      ∀ p ∈ Ioo (0 : ℝ) 1, ∀ a : CoordinateVector (2*r+1), 0 ≤ a →
        sSup (hardyTailValues.{uMedianHardy} (scalarMedian r) p a) = medianCutBound r a ∧
          sSup (comonotoneHardyTailValues.{uMedianHardy} (scalarMedian r) p a) = medianCutBound r a :=
  ⟨hardy_tail_median_operator_bound r μ hm hx hi, fun p hp a ha => median_hardy_tail_sharp r hp ha⟩

theorem finite_decGraph_iInf_singleton {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → DecGraph) {p : ℝ} (a : ι → ℝ) (ha : ∀ i, (f i).val p = {a i}) :
    (⨅ i, f i).val p = {⨅ i, a i} := by
  rw [DecGraph.fiber_iInf f (fun i => ⟨a i, by rw [ha i]; rfl⟩)]
  simp_rw [ha]
  ext u
  simp only [intervalInf, mem_inter_iff, mem_iUnion, mem_iInter,
    upperHull, lowerHull, mem_setOf_eq, mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨⟨i, hi⟩, hu⟩
    exact le_antisymm (le_ciInf hu) ((ciInf_le (finite_range a).bddBelow i).trans hi)
  · rintro rfl
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := a)
    exact ⟨⟨i, hi.le⟩, fun j => ciInf_le (finite_range a).bddBelow j⟩

/-- The literal lattice right-hand side takes exactly the scalar cut minimum
at every interior level. This is separate from its whole-graph order proof. -/
theorem medianHardyBound_value {Ω : Type*} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector (2*r+1)}
    (hm : Measurable X) (hi : ∀ i, Integrable (fun ω => X ω i) μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) (a : CoordinateVector (2*r+1))
    (ha : ∀ i, quantileHardy (Measure.map (fun ω => X ω i) μ) p = {a i}) :
    (medianHardyBound r μ X hm hi).val p = {medianCutBound r a} := by
  classical
  letI (ℓ : Fin (r+1)) : Nonempty (medianCutSets r ℓ) := medianCutSets_nonempty r ℓ
  letI (ℓ : Fin (r+1)) : Finite (medianCutSets r ℓ) := medianCutSets_finite r ℓ
  unfold medianHardyBound
  apply finite_decGraph_iInf_singleton
  intro ℓ
  apply finite_decGraph_iInf_singleton
  intro J
  exact medianCutSum_singleton r ℓ J _ a ha

end ScalarMonotone.EndOfPaper
end
