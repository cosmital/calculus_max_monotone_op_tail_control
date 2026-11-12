import EndOfPaper.NormTransform
import EndOfPaper.HardyTailAggregation
import EndOfPaper.HardySharpness
import EndOfPaper.HardyCalculus

/-!
Actual Hardy norm bounds and exact sharp suprema for every exponent
from one through infinity. Almost-sure nonnegativity is allowed on
arbitrary original spaces. Whole completed graph comparisons,
ordinary finite sums and their common-interval completion are bridged
explicitly, and the Euclidean ones illustration is computed.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- The full original-space bound with almost-sure nonnegativity. Clipping
preserves all laws; nonnegative marginal Hardy values are also derived. -/
theorem hardy_tail_aggregation_ae {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {x | 0 ≤ x}) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → CoordinateVector n} (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : CoordinateVector n, ∃ v : ℝ, (∀ i, 0 ≤ a i) ∧
      (∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a i}) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => F (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => F (X ω)) μ)) p = {v} ∧
      v ≤ superadditiveTransform F a := by
  let Y : Ω → CoordinateVector n := fun ω i => max (X ω i) 0
  have hYm : Measurable Y := measurable_pi_iff.mpr
    (fun i => (measurable_pi_iff.mp hm i).max measurable_const)
  have hYn (ω) (i) : 0 ≤ Y ω i := le_max_right _ _
  have hYi (i) : Integrable (fun ω => Y ω i) μ := (hi i).pos_part
  have hXY : X =ᵐ[μ] Y := hx.mono
    (fun ω hω => funext (fun i => (max_eq_left (hω i)).symm))
  have hMargLaw (i) : Measure.map (fun ω => X ω i) μ = Measure.map (fun ω => Y ω i) μ :=
    Measure.map_congr (hXY.mono (fun ω he => congrArg (fun x => x i) he))
  have hAggLaw : Measure.map (fun ω => F (X ω)) μ = Measure.map (fun ω => F (Y ω)) μ :=
    Measure.map_congr (hXY.mono (fun ω he => congrArg F he))
  obtain ⟨a, v, hMarg, hAgg, hbound⟩ := hardy_tail_aggregation hF hFc μ hYm hYn hYi hp
  have hapos (i : Fin n) : 0 ≤ a i := by
    obtain ⟨b, hb, _, hdual, _, _, _⟩ :=
      hardy_quantile_original_variational (measurable_pi_iff.mp hYm i) (hYi i) hp
    have hba : b = a i := Set.singleton_injective (hb.symm.trans (hMarg i))
    have hc : (∫ ω, Y ω i*p ∂μ)/p ∈ dualCandidates μ (fun ω => Y ω i) p := by
      refine ⟨(fun _ => p), aemeasurable_const,
        Eventually.of_forall (fun _ => ⟨hp.1.le, hp.2.le⟩), ?_, rfl⟩
      simp
    have ht := hdual.2 hc
    rw [hba] at ht
    exact (div_nonneg (integral_nonneg (fun ω => mul_nonneg (hYn ω i) hp.1.le)) hp.1.le).trans ht
  refine ⟨a, v, hapos, ?_, ?_, hbound⟩
  · intro i
    rw [hMargLaw i]
    exact hMarg i
  · rw [hAggLaw]
    exact hAgg

theorem coordinateLpNorm_continuous (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Continuous (coordinateLpNorm n q) :=
  continuous_norm.comp (PiLp.continuous_equiv_symm q (fun _ : Fin n => ℝ))

theorem euclidean_norm_sharp_ones (n : ℕ) :
    @coordinateLpNorm n (2 : ℝ≥0∞) ⟨by norm_num⟩ (fun _ => 1) = Real.sqrt n ∧
      superadditiveTransform (@coordinateLpNorm n (2 : ℝ≥0∞) ⟨by norm_num⟩) (fun _ => 1) = n := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  constructor
  · change coordinateLpNorm n (2 : ℝ≥0∞) (fun _ => 1) = Real.sqrt n
    have hp0 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    rw [coordinateLpNorm, PiLp.norm_eq_sum hp0, Real.sqrt_eq_rpow]
    simp [WithLp.equiv_symm_pi_apply]
  · simpa using ellp_superadditive_transform n (2 : ℝ≥0∞)
      (a := fun _ => (1 : ℝ)) (fun _ => zero_le_one)

theorem hardy_tail_norm_bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → CoordinateVector n} (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : CoordinateVector n, ∃ v : ℝ,
      (∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a i}) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => coordinateLpNorm n q (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => coordinateLpNorm n q (X ω)) μ)) p = {v} ∧
      v ≤ ∑ i, a i := by
  obtain ⟨a, v, ha, hMarg, hAgg, hbound⟩ := hardy_tail_aggregation_ae
    (coordinateLpNorm_aggregation_axioms n q) (coordinateLpNorm_continuous n q).continuousOn μ hm hx hi hp
  refine ⟨a, v, hMarg, hAgg, ?_⟩
  simpa only [ellp_superadditive_transform n q ha] using hbound

universe uNormSharpness

/-- Both suprema use the literal classes of arbitrary probability spaces and
finite-valued comonotone tuples from the general sharpness theorem. -/
theorem ellp_hardy_tail_sharp (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    sSup (hardyTailValues.{uNormSharpness} (coordinateLpNorm n q) p a) = ∑ i, a i ∧
      sSup (comonotoneHardyTailValues.{uNormSharpness} (coordinateLpNorm n q) p a) = ∑ i, a i := by
  obtain ⟨hg, hc⟩ := hardy_tail_aggregation_sharp
    (coordinateLpNorm_aggregation_axioms n q) (coordinateLpNorm_continuous n q).continuousOn hp ha
  rw [ellp_superadditive_transform n q ha] at hg hc
  exact ⟨hg.symm, hc.symm⟩

theorem quantileHardy_properties (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun x : ℝ => x) ν) :
    MaximalDecreasing (quantileHardy ν) ∧
      interior (dom (quantileHardy ν)) = Ioo 0 1 ∧
      dom (quantileHardy ν) ⊆ Icc 0 1 := by
  have hd : Ioo (0 : ℝ) 1 ⊆ dom (tailQuantile ν) := by
    intro p hp
    apply interior_subset
    rwa [tailQuantile_domain_interior ν]
  obtain ⟨s, hsm, hs⟩ := exists_global_measurable_selection
    (Or.inr (tailQuantile_maximal ν).1) measurableSet_Ioo hd
  have h := hardyFamilyIntegral_well_defined (tailQuantile_maximal ν) isOpen_Ioo
    (ordConnected_Ioo) (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩)
    (by rw [tailQuantile_domain_interior ν])
    (fun p hp => hp.1) (by
      intro c hc p hp
      exact ⟨mul_pos hc.1 hp.1, (mul_le_mul_of_nonneg_right hc.2 hp.1.le).trans_lt (by simpa using hp.2)⟩)
    hs (fun p hp => quantile_selection_intervalIntegrable ν hi hsm hs hp)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [quantileHardy, tailQuantile_domain_interior] using h.1
  · simpa only [quantileHardy, tailQuantile_domain_interior] using h.2.1
  · simpa only [quantileHardy, tailQuantile_domain_interior,
      closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using h.2.2.1

theorem quantileHardy_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hm : Measurable Y) (hi : Integrable Y μ) (hn : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    {p v : ℝ} (hp : p ∈ Ioo 0 1)
    (hv : v ∈ quantileHardy (Measure.map Y μ) p) : 0 ≤ v := by
  obtain ⟨b, hb, _, hdual, _, _, _⟩ := hardy_quantile_original_variational hm hi hp
  have hval : v = b := by
    change v ∈ hardyFamilyIntegral _ _ p at hv
    rw [hb] at hv
    exact hv
  have hc : (∫ ω, Y ω*p ∂μ)/p ∈ dualCandidates μ Y p := by
    refine ⟨(fun _ => p), aemeasurable_const,
      Eventually.of_forall (fun _ => ⟨hp.1.le, hp.2.le⟩), ?_, rfl⟩
    simp
  have hnonneg : 0 ≤ (∫ ω, Y ω*p ∂μ)/p :=
    div_nonneg (integral_nonneg_of_ae (hn.mono (fun ω hω => mul_nonneg hω hp.1.le))) hp.1.le
  exact hval ▸ hnonneg.trans (hdual.2 hc)

theorem coordinateMass_aggregation_axioms (n : ℕ) :
    AggregationAxioms (@coordinateMass n) :=
  ⟨fun _ h => coordinateMass_nonneg h,
    fun _ h => coordinateMass_mono h,
    fun c _ x _ => coordinateMass_smul c x⟩

theorem coordinateMass_continuous (n : ℕ) : Continuous (@coordinateMass n) := by
  exact continuous_finset_sum Finset.univ (fun i _ => continuous_apply i)

/-- Interior scalar bounds extend to the whole completed graphs, including
all endpoint fibers. B is an auxiliary continuous aggregation majorant. -/
theorem hardy_tail_operator_bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {F B : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : Continuous F)
    (hB : AggregationAxioms B) (hBc : ContinuousOn B {x | 0 ≤ x})
    (hbound : ∀ a, 0 ≤ a → superadditiveTransform F a ≤ B a)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → CoordinateVector n} (hm : Measurable X)
    (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    DecLE (quantileHardy (Measure.map (fun ω => F (X ω)) μ))
      (aggregationOperator B (Ioo 0 1)
        (fun i => quantileHardy (Measure.map (fun ω => X ω i) μ))) := by
  let f : Fin n → Operator := fun i => quantileHardy (Measure.map (fun ω => X ω i) μ)
  let g : Operator := quantileHardy (Measure.map (fun ω => F (X ω)) μ)
  have hmi (i) := measurable_pi_iff.mp hm i
  have hprop (i) : MaximalDecreasing (f i) ∧ interior (dom (f i)) = Ioo 0 1 ∧ dom (f i) ⊆ Icc 0 1 := by
    letI : IsProbabilityMeasure (Measure.map (fun ω => X ω i) μ) := isProbabilityMeasure_map (hmi i).aemeasurable
    exact quantileHardy_properties _ ((integrable_map_measure measurable_id.aestronglyMeasurable
      (hmi i).aemeasurable).mpr (hi i))
  have hd (i) : Ioo (0 : ℝ) 1 ⊆ dom (f i) := by
    intro x hx
    exact interior_subset (by rwa [(hprop i).2.1])
  have hn (i) : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ f i x, 0 ≤ v := by
    intro x hx' v hv
    exact quantileHardy_nonnegative μ (hmi i) (hi i) (hx.mono (fun ω hω => hω i)) hx' hv
  have hfm : Measurable (fun ω => F (X ω)) := hFc.measurable.comp hm
  letI : IsProbabilityMeasure (Measure.map (fun ω => F (X ω)) μ) := isProbabilityMeasure_map hfm.aemeasurable
  have hgi := aggregation_composition_integrable_ae hF hFc.continuousOn μ hm.aemeasurable hx hi
  have hg := quantileHardy_properties (Measure.map (fun ω => F (X ω)) μ)
    ((integrable_map_measure measurable_id.aestronglyMeasurable hfm.aemeasurable).mpr hgi)
  have hA := aggregationOperator_properties hB hBc isOpen_Ioo ordConnected_Ioo
    (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩) (fun i => (hprop i).1) hd hn
  apply decLE_of_initial_interior hg.1.1 hA.1.1 isOpen_Ioo ordConnected_Ioo
    (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩)
    (by rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]; exact ⟨le_rfl, zero_le_one⟩)
    (by simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hg.2.2)
    (fun x hx' => (show x ∈ Icc (0 : ℝ) 1 from
      by simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hA.2.2.1 hx').1)
    (fun x hx' => interior_subset (by rwa [hg.2.1]))
    (fun x hx' => interior_subset (by rwa [hA.2.1]))
  intro p hp r hr hrp u hu v hv
  obtain ⟨a, t, ha, hMarg, hAgg, ht⟩ := hardy_tail_aggregation_ae hF hFc.continuousOn μ hm hx hi hp
  have hfp (i) : f i p = {a i} := hMarg i
  have hAp : aggregationOperator B (Ioo 0 1) f p = {B a} := by
    rw [hA.2.2.2 p hp]
    simp only [hfp, csInf_singleton, csSup_singleton, Icc_self]
  have hu' : u = t := by
    change u ∈ hardyFamilyIntegral _ _ p at hu
    rw [hAgg] at hu
    exact hu
  have hw : B a ∈ aggregationOperator B (Ioo 0 1) f p := by rw [hAp]; rfl
  exact hu' ▸ (ht.trans (hbound a ha)).trans (Decreasing.le_of_lt hA.1.1 hv hw hrp)

theorem hardy_tail_norm_operator_bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    DecLE (quantileHardy (Measure.map (fun ω => coordinateLpNorm n q (X ω)) μ))
      (aggregationOperator (@coordinateMass n) (Ioo 0 1)
        (fun i => quantileHardy (Measure.map (fun ω => X ω i) μ))) :=
  hardy_tail_operator_bound (coordinateLpNorm_aggregation_axioms n q)
    (coordinateLpNorm_continuous n q) (coordinateMass_aggregation_axioms n)
    (coordinateMass_continuous n).continuousOn
    (fun a ha => (ellp_superadditive_transform n q ha).le) μ hm hx hi

/-- The ordinary finite Minkowski sum of graphs. Its empty sum is the global
zero graph; restriction and completion are therefore explicit below. -/
def finiteOperatorSum : {n : ℕ} → (Fin n → Operator) → Operator
  | 0, _ => ofFun (fun _ => 0)
  | n+1, f => ScalarMonotone.add (f 0) (finiteOperatorSum (fun i : Fin n => f i.succ))

theorem finiteOperatorSum_singleton {n : ℕ} (f : Fin n → Operator)
    {p : ℝ} (a : Fin n → ℝ) (ha : ∀ i, f i p = {a i}) :
    finiteOperatorSum f p = {∑ i, a i} := by
  induction n with
  | zero => simp [finiteOperatorSum, ofFun]
  | succ n ih =>
    rw [finiteOperatorSum, add_fiber_singleton (ha 0)
      (ih (fun i => f i.succ) (fun i => a i.succ) (fun i => ha i.succ))]
    rw [Fin.sum_univ_succ]

theorem finiteOperatorSum_properties {n : ℕ} (f : Fin n → Operator)
    (hf : ∀ i, MaximalDecreasing (f i)) {I : Set ℝ} (hne : I.Nonempty)
    (hd : ∀ i, I ⊆ dom (f i)) :
    MaximalDecreasing (finiteOperatorSum f) ∧ I ⊆ dom (finiteOperatorSum f) := by
  induction n with
  | zero => exact ⟨constant_maximal_decreasing 0, fun x _ => ⟨0, rfl⟩⟩
  | succ n ih =>
    have ht := ih (fun i => f i.succ) (fun i => hf i.succ) (fun i => hd i.succ)
    have hc : (dom (f 0) ∩ dom (finiteOperatorSum (fun i : Fin n => f i.succ))).Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hd 0 hx, ht.2 hx⟩
    refine ⟨add_maximal_decreasing (hf 0) ht.1 hc, ?_⟩
    intro x hx
    obtain ⟨u, hu⟩ := hd 0 hx
    obtain ⟨v, hv⟩ := ht.2 hx
    exact ⟨u+v, u, hu, v, hv, rfl⟩

theorem finiteOperatorSum_dom_subset {n : ℕ} (hn : 0 < n) (f : Fin n → Operator)
    {I : Set ℝ} (hd : ∀ i, dom (f i) ⊆ I) : dom (finiteOperatorSum f) ⊆ I := by
  cases n with
  | zero => omega
  | succ n =>
    rintro x ⟨z, u, hu, v, hv, he⟩
    exact hd 0 ⟨u, hu⟩

/-- The aggregate mass graph is the completed restriction of the ordinary
finite graph sum, even for the empty family. This is equality of whole graphs. -/
theorem finiteOperatorSum_completed_aggregation {n : ℕ} (f : Fin n → Operator)
    (hf : ∀ i, MaximalDecreasing (f i)) {I : Set ℝ}
    (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hd : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ p ∈ I, ∀ v ∈ f i p, 0 ≤ v)
    (hval : ∀ p ∈ I, ∃ a : Fin n → ℝ, ∀ i, f i p = {a i}) :
    completedDecreasingRestriction I (finiteOperatorSum f) =
      aggregationOperator (@coordinateMass n) I f := by
  have hS := finiteOperatorSum_properties f hf hne hd
  apply aggregationOperator_unique (coordinateMass_aggregation_axioms n)
    (coordinateMass_continuous n).continuousOn hI hord hne hf hd hpos
    (completedDecreasingRestriction_maximal hS.1 hord hne hS.2)
    (completedDecreasingRestriction_domain hS.1 hI hord hne hS.2).2
  intro p hp
  obtain ⟨a, ha⟩ := hval p hp
  rw [completedDecreasingRestriction_value hS.1 hI hS.2 hp,
    finiteOperatorSum_singleton f a ha]
  simp only [ha, csInf_singleton, csSup_singleton, coordinateMass, Icc_self]

/-- For a nonempty family whose domains stay in the common closure, the
ordinary sum already has the correct completed endpoint fibers. -/
theorem finiteOperatorSum_eq_aggregation {n : ℕ} (hn : 0 < n) (f : Fin n → Operator)
    (hf : ∀ i, MaximalDecreasing (f i)) {I : Set ℝ}
    (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hd : ∀ i, I ⊆ dom (f i)) (hcl : ∀ i, dom (f i) ⊆ closure I)
    (hpos : ∀ i, ∀ p ∈ I, ∀ v ∈ f i p, 0 ≤ v)
    (hval : ∀ p ∈ I, ∃ a : Fin n → ℝ, ∀ i, f i p = {a i}) :
    finiteOperatorSum f = aggregationOperator (@coordinateMass n) I f := by
  apply aggregationOperator_unique (coordinateMass_aggregation_axioms n)
    (coordinateMass_continuous n).continuousOn hI hord hne hf hd hpos
    (finiteOperatorSum_properties f hf hne hd).1 (finiteOperatorSum_dom_subset hn f hcl)
  intro p hp
  obtain ⟨a, ha⟩ := hval p hp
  rw [finiteOperatorSum_singleton f a ha]
  simp only [ha, csInf_singleton, csSup_singleton, coordinateMass, Icc_self]

theorem quantileHardy_original_properties {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hm : Measurable Y) (hi : Integrable Y μ) :
    MaximalDecreasing (quantileHardy (Measure.map Y μ)) ∧
      interior (dom (quantileHardy (Measure.map Y μ))) = Ioo 0 1 ∧
      dom (quantileHardy (Measure.map Y μ)) ⊆ Icc 0 1 := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hm.aemeasurable
  exact quantileHardy_properties _
    ((integrable_map_measure measurable_id.aestronglyMeasurable hm.aemeasurable).mpr hi)

theorem quantileHardy_sum_graphs {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → CoordinateVector n} (hm : Measurable X)
    (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    let f : Fin n → Operator := fun i => quantileHardy (Measure.map (fun ω => X ω i) μ)
    completedDecreasingRestriction (Ioo 0 1) (finiteOperatorSum f) =
        aggregationOperator (@coordinateMass n) (Ioo 0 1) f ∧
      (0 < n → finiteOperatorSum f = aggregationOperator (@coordinateMass n) (Ioo 0 1) f) := by
  let f : Fin n → Operator := fun i => quantileHardy (Measure.map (fun ω => X ω i) μ)
  have hmi (i) := measurable_pi_iff.mp hm i
  have hprop (i) := quantileHardy_original_properties μ (hmi i) (hi i)
  have hd (i) : Ioo (0 : ℝ) 1 ⊆ dom (f i) := by
    intro p hp
    exact interior_subset (by rwa [(hprop i).2.1])
  have hpos (i) : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ f i p, 0 ≤ v := by
    intro p hp v hv
    exact quantileHardy_nonnegative μ (hmi i) (hi i) (hx.mono (fun ω hω => hω i)) hp hv
  have hval : ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a : Fin n → ℝ, ∀ i, f i p = {a i} := by
    intro p hp
    have hs (i) : ∃ a : ℝ, f i p = {a} := by
      obtain ⟨a, ha, _, _, _, _, _⟩ := hardy_quantile_original_variational (hmi i) (hi i) hp
      exact ⟨a, ha⟩
    choose a ha using hs
    exact ⟨a, ha⟩
  refine ⟨finiteOperatorSum_completed_aggregation f (fun i => (hprop i).1)
    isOpen_Ioo ordConnected_Ioo ⟨1/2, by norm_num⟩ hd hpos hval, ?_⟩
  intro hn
  exact finiteOperatorSum_eq_aggregation hn f (fun i => (hprop i).1)
    isOpen_Ioo ordConnected_Ioo ⟨1/2, by norm_num⟩ hd
    (fun i => by simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using (hprop i).2.2) hpos hval

/-- The sum in the manuscript is the ordinary sum of completed graphs for
every nonempty vector. The explicit completed restriction also covers n=0. -/
theorem hardy_tail_norm_sum_bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    let H := quantileHardy (Measure.map (fun ω => coordinateLpNorm n q (X ω)) μ)
    let S := finiteOperatorSum (fun i => quantileHardy (Measure.map (fun ω => X ω i) μ))
    DecLE H (completedDecreasingRestriction (Ioo 0 1) S) ∧ (0 < n → DecLE H S) := by
  have hbound := hardy_tail_norm_operator_bound q μ hm hx hi
  have heq := quantileHardy_sum_graphs μ hm hx hi
  refine ⟨?_, fun hn => ?_⟩
  · rwa [heq.1]
  · rwa [heq.2 hn]

end ScalarMonotone.EndOfPaper
end
