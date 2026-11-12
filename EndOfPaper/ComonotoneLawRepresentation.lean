import EndOfPaper.ComonotoneQuantiles
import EndOfPaper.IntegralAggregation

/-!
Comonotone representation in joint law on arbitrary original spaces,
including atomic spaces that carry no uniform random variable. AEMeasurable
pushforwards transfer the full joint representation, marginal laws and
aggregate law. Clipping derives profile nonnegativity from actual variables;
whole completed quantile aggregation and the fixed-fiber identity follow.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem antitone_profile_vector_aemeasurable {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1)) :
    AEMeasurable (fun u i => q i u) unitUniform := by
  have hm (i) : AEMeasurable (q i) unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo (hq i)
  let Q : ℝ → CoordinateVector n := fun u i => (hm i).mk (q i) u
  have hQ : Measurable Q := measurable_pi_iff.mpr (fun i => (hm i).measurable_mk)
  have he : (fun u i => q i u) =ᵐ[unitUniform] Q := by
    filter_upwards [ae_all_iff.mpr (fun i => (hm i).ae_eq_mk)] with u hu
    exact funext hu
  exact hQ.aemeasurable.congr he.symm

theorem joint_law_map {Ω E A B : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace A] [MeasurableSpace B] {μ : Measure Ω} {ν : Measure E}
    {X : Ω → A} {Y : E → A} (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (hlaw : Measure.map X μ = Measure.map Y ν) {f : A → B} (hf : Measurable f) :
    Measure.map (fun ω => f (X ω)) μ = Measure.map (fun u => f (Y u)) ν := by
  have he := congrArg (Measure.map f) hlaw
  rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hX,
    AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hY] at he
  exact he

theorem comonotone_joint_law_positive_profiles {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → CoordinateVector n} (hXm : AEMeasurable X μ)
    (hX : ∀ ω, 0 ≤ X ω) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hlaw : Measure.map X μ = Measure.map (fun u i => q i u) unitUniform) :
    ∃ r : Fin n → ℝ → ℝ, (∀ i, AntitoneOn (r i) (Ioo 0 1)) ∧
      (∀ i u, 0 ≤ r i u) ∧
      Measure.map X μ = Measure.map (fun u i => r i u) unitUniform := by
  let r : Fin n → ℝ → ℝ := fun i u => max (q i u) 0
  have hr (i) : AntitoneOn (r i) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact max_le_max (hq i hx hy hxy) le_rfl
  have hn (i) (u) : 0 ≤ r i u := le_max_right _ _
  refine ⟨r, hr, hn, ?_⟩
  have hclip : Measurable (fun x : CoordinateVector n => fun i => max (x i) 0) :=
    (continuous_pi (fun i => (continuous_apply i).max continuous_const)).measurable
  have ht := joint_law_map hXm (antitone_profile_vector_aemeasurable hq) hlaw hclip
  have heX : (fun ω i => max (X ω i) 0) = X := by
    funext ω i
    exact max_eq_left (hX ω i)
  change Measure.map (fun ω i => max (X ω i) 0) μ =
    Measure.map (fun u i => r i u) unitUniform at ht
  rwa [heX] at ht

theorem comonotone_joint_law_marginals_aggregate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → CoordinateVector n} (hXm : AEMeasurable X μ)
    (hX : ∀ ω, 0 ≤ X ω) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hlaw : Measure.map X μ = Measure.map (fun u i => q i u) unitUniform)
    {F : CoordinateVector n → ℝ} (hFc : ContinuousOn F {v | 0 ≤ v}) :
    ∃ r : Fin n → ℝ → ℝ, (∀ i, AntitoneOn (r i) (Ioo 0 1)) ∧
      (∀ i u, 0 ≤ r i u) ∧
      (∀ i, Measure.map (fun ω => X ω i) μ = Measure.map (r i) unitUniform) ∧
      Measure.map (fun ω => F (X ω)) μ =
        Measure.map (fun u => F (fun i => r i u)) unitUniform := by
  obtain ⟨r, hr, hn, hl⟩ := comonotone_joint_law_positive_profiles hXm hX hq hlaw
  have hrm := antitone_profile_vector_aemeasurable hr
  refine ⟨r, hr, hn, (fun i => joint_law_map hXm hrm hl (measurable_pi_apply i)), ?_⟩
  have hplus := (aggregation_positiveExtension_continuous hFc).measurable
  have ht := joint_law_map hXm hrm hl hplus
  have heX : (fun ω => F (fun i => max (X ω i) 0)) = (fun ω => F (X ω)) := by
    funext ω
    congr 1
    funext i
    exact max_eq_left (hX ω i)
  have heR : (fun u => F (fun i => max (r i u) 0)) = (fun u => F (fun i => r i u)) := by
    funext u
    congr 1
    funext i
    exact max_eq_left (hn i u)
  change Measure.map (fun ω => F (fun i => max (X ω i) 0)) μ =
    Measure.map (fun u => F (fun i => max (r i u) 0)) unitUniform at ht
  rwa [heX, heR] at ht

theorem comonotone_aggregation_quantile_joint_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → CoordinateVector n} (hXm : AEMeasurable X μ)
    (hX : ∀ ω, 0 ≤ X ω) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hlaw : Measure.map X μ = Measure.map (fun u i => q i u) unitUniform)
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) :
    tailQuantile (Measure.map (fun ω => F (X ω)) μ) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (fun ω => X ω i) μ)) := by
  obtain ⟨r, hr, hn, hMarg, hAgg⟩ :=
    comonotone_joint_law_marginals_aggregate hXm hX hq hlaw hFc
  rw [hAgg]
  simp_rw [hMarg]
  exact comonotone_aggregation_quantile hF hFc hr (fun i u _ => hn i u)

theorem comonotone_fixed_quantile_joint_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {X : Ω → CoordinateVector n} (hXm : AEMeasurable X μ)
    (hX : ∀ ω, 0 ≤ X ω) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hlaw : Measure.map X μ = Measure.map (fun u i => q i u) unitUniform)
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : CoordinateVector n}
    (hQa : ∀ i, tailQuantile (Measure.map (fun ω => X ω i) μ) p = {a i}) :
    tailQuantile (Measure.map (fun ω => F (X ω)) μ) p = {F a} := by
  obtain ⟨r, hr, hn, hMarg, hAgg⟩ :=
    comonotone_joint_law_marginals_aggregate hXm hX hq hlaw hFc
  have hsingle (i) : tailQuantile (Measure.map (r i) unitUniform) p = {a i} := by
    rw [← hMarg i]
    exact hQa i
  rw [hAgg]
  exact comonotone_quantile_fiber hF hFc hr (fun i u _ => hn i u) hp hsingle

end ScalarMonotone.EndOfPaper
end
