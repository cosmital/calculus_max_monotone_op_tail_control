import EndOfPaper.ReplicatedHardyUpper
import EndOfPaper.ReplicatedQuantileCoupling
import EndOfPaper.QuantileEnvelopeCriterion

/-!
The literal family of all prescribed-law replicated averages on
arbitrary original probability spaces in every universe, with
nonemptiness, exact universe lifts, domains and whole upper bounds.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper
universe u

def replicatedQuantileFamily {n : ℕ} (laws : Fin n → Measure ℝ) : Set DecGraph :=
  {C | ∃ m : ℕ, 0 < m ∧ ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∃ (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ) (X : Fin n → Fin m → Ω → ℝ),
      (∀ i j, Measurable (X i j)) ∧
      (∀ i j, Measure.map (X i j) μ = laws i) ∧
      C.val = tailQuantile (Measure.map
        (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ)}

theorem lift_probability_profile_law {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] (μ : Measure Ω) {f : Ω → A} (hf : Measurable f) :
    Measure.map (fun ω : ULift.{u} Ω => f ω.down)
      (Measure.map (ULift.up : Ω → ULift.{u} Ω) μ) = Measure.map f μ := by
  change Measure.map (f ∘ ULift.down) (Measure.map (ULift.up : Ω → ULift.{u} Ω) μ) = _
  rw [Measure.map_map (hf.comp measurable_down) measurable_up]
  rfl

theorem replicatedQuantileFamily_of_model {Ω : Type} [MeasurableSpace Ω]
    {n m : ℕ} (hm : 0 < m) (laws : Fin n → Measure ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Fin m → Ω → ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hLaw : ∀ i j, Measure.map (X i j) μ = laws i)
    {C : DecGraph} (hC : C.val = tailQuantile (Measure.map
      (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ)) :
    C ∈ replicatedQuantileFamily.{u} laws := by
  let Ω' := ULift.{u} Ω
  let μ' : Measure Ω' := Measure.map (ULift.up : Ω → Ω') μ
  have hμ' : IsProbabilityMeasure μ' := isProbabilityMeasure_map measurable_up.aemeasurable
  let X' : Fin n → Fin m → Ω' → ℝ := fun i j ω => X i j ω.down
  have hY : Measurable (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) :=
    (Finset.measurable_sum _ (fun i _ =>
      Finset.measurable_sum _ (fun j _ => hXm i j))).div_const _
  refine ⟨m, hm, Ω', inferInstance, μ', hμ', X',
    (fun i j => (hXm i j).comp measurable_down), ?_, ?_⟩
  · intro i j
    exact (lift_probability_profile_law μ (hXm i j)).trans (hLaw i j)
  · rw [hC]
    exact congrArg tailQuantile (lift_probability_profile_law μ hY).symm

theorem replicatedQuantileFamily_nonempty {n : ℕ} (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] :
    (replicatedQuantileFamily.{u} laws).Nonempty := by
  classical
  have hq (i : Fin n) : ∃ q : ℝ → ℝ, Measurable q ∧
      ∀ p ∈ Ioo (0 : ℝ) 1, q p ∈ tailQuantile (laws i) p :=
    exists_global_measurable_selection (Or.inr (tailQuantile_maximal (laws i)).1)
      measurableSet_Ioo (fun p hp => tailQuantile_fiber_nonempty (laws i) hp)
  choose q hqm hs using hq
  let X : Fin n → Fin 1 → ℝ → ℝ := fun i _ => q i
  have hXm (i : Fin n) (j : Fin 1) : Measurable (X i j) := hqm i
  have hLaw (i : Fin n) (j : Fin 1) : Measure.map (X i j) unitUniform = laws i :=
    tailQuantile_selection_law (laws i) (hqm i) (hs i)
  let Y := fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(1 : ℝ))
  have hYm : Measurable Y := (Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => hXm i j))).div_const _
  letI : IsProbabilityMeasure (Measure.map Y unitUniform) := isProbabilityMeasure_map hYm.aemeasurable
  let C : DecGraph := ⟨tailQuantile (Measure.map Y unitUniform), tailQuantile_maximal _⟩
  refine ⟨C, replicatedQuantileFamily_of_model (by norm_num) laws unitUniform X hXm hLaw ?_⟩
  change tailQuantile (Measure.map Y unitUniform) = _
  simp only [Y, Nat.cast_one]

theorem replicatedQuantileFamily_domains {n : ℕ} (laws : Fin n → Measure ℝ) :
    ∀ C ∈ replicatedQuantileFamily.{u} laws, dom C.val ⊆ Icc (0 : ℝ) 1 := by
  rintro C ⟨m, hm, Ω, mΩ, μ, hμ, X, hXm, hLaw, hC⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hμ
  let Y := fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))
  have hYm : Measurable Y := (Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => hXm i j))).div_const _
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hYm.aemeasurable
  rw [hC]
  rintro p ⟨a, ha⟩
  change (Measure.map Y μ).real (Ioi a) ≤ p ∧ p ≤ (Measure.map Y μ).real (Ici a) at ha
  exact ⟨measureReal_nonneg.trans ha.1, ha.2.trans measureReal_le_one⟩

theorem replicatedQuantileFamily_upper {n : ℕ} (hn : 0 < n)
    (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    ∀ C ∈ replicatedQuantileFamily.{u} laws,
      DecLE C.val (replicatedHardyEnvelope laws) := by
  rintro C ⟨m, hm, Ω, mΩ, μ, hμ, X, hXm, hLaw, hC⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hμ
  rw [hC]
  exact (replicated_average_operator_bound hn hm laws hi μ X hXm hLaw).2.2

end ScalarMonotone.EndOfPaper
end
