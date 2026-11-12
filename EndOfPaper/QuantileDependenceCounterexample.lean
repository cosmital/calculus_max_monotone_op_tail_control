import MonotoneOperators.CubicNested
import EndOfPaper.ContinuousSelections

/-!
The exact finite-valued counterexample when comonotonicity is
removed from pointwise quantile sharpness. On the same symmetric
Bernoulli law, complementary nonnegative indicators have marginal
quantiles zero at 3/4 and sum quantile one. All laws, finite ranges,
measurability and completed singleton fibers are proved.
-/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem tailQuantile_dirac_interior (c : ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    tailQuantile (Measure.dirac c) p = {c} := by
  ext x
  change p ∈ survival (Measure.dirac c) x ↔ x = c
  rcases lt_trichotomy x c with h | rfl | h
  · simp [survival_dirac_left h, hp.2.ne, h.ne]
  · simp [survival_dirac_at, hp.1.le, hp.2.le]
  · simp [survival_dirac_right h, hp.1.ne', h.ne']

theorem tailQuantile_constant_randomVariable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    tailQuantile (Measure.map (fun _ : Ω => c) μ) p = {c} := by
  rw [Measure.map_const, measure_univ, one_smul]
  exact tailQuantile_dirac_interior c hp

theorem tailQuantile_symmetricBernoulli_upper {p : ℝ} (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    tailQuantile symmetricBernoulli p = {0} := by
  have hs : SelectionOn (tailQuantile symmetricBernoulli) (Ioo (1/2 : ℝ) 1)
      (fun _ => 0) := by
    intro u hu
    change symmetricBernoulli.real (Ioi 0) ≤ u ∧ u ≤ symmetricBernoulli.real (Ici 0)
    have hstrict : symmetricBernoulli.real (Ioi 0) = 1/2 := by
      norm_num [symmetricBernoulli, measureReal_def, Measure.add_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator]
    have hweak : symmetricBernoulli.real (Ici 0) = 1 := by
      norm_num [symmetricBernoulli, measureReal_def, Measure.add_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator,
        ENNReal.inv_two_add_inv_two]
    rw [hstrict, hweak]
    exact ⟨hu.1.le, hu.2.le⟩
  exact fiber_of_continuous_selection (Or.inr (tailQuantile_maximal _)) isOpen_Ioo
    (fun u hu => ⟨0, hs u hu⟩) hs continuousOn_const hp

def bernoulliIndicator (ω : ℝ) : ℝ := if ω = 1 then 1 else 0

theorem bernoulliIndicator_measurable : Measurable bernoulliIndicator := by
  unfold bernoulliIndicator
  exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const

theorem bernoulliIndicator_finite_nonnegative :
    (∀ ω : ℝ, 0 ≤ bernoulliIndicator ω ∧ 0 ≤ 1-bernoulliIndicator ω) ∧
      (Set.range bernoulliIndicator).Finite ∧
      (Set.range (fun ω => 1-bernoulliIndicator ω)).Finite := by
  have hfin : ({(0 : ℝ), 1} : Set ℝ).Finite := (Set.finite_singleton 1).insert 0
  refine ⟨?_, hfin.subset ?_, hfin.subset ?_⟩
  · intro ω
    by_cases h : ω = 1 <;> norm_num [bernoulliIndicator, h]
  · rintro _ ⟨ω, rfl⟩
    by_cases h : ω = 1 <;> simp [bernoulliIndicator, h]
  · rintro _ ⟨ω, rfl⟩
    by_cases h : ω = 1 <;> simp [bernoulliIndicator, h]

theorem bernoulliIndicator_law :
    Measure.map bernoulliIndicator symmetricBernoulli = symmetricBernoulli := by
  unfold symmetricBernoulli
  rw [Measure.map_add _ _ bernoulliIndicator_measurable,
    Measure.map_smul, Measure.map_smul,
    Measure.map_dirac bernoulliIndicator_measurable,
    Measure.map_dirac bernoulliIndicator_measurable]
  norm_num [bernoulliIndicator]

theorem complementary_bernoulliIndicator_law :
    Measure.map (fun ω => 1-bernoulliIndicator ω) symmetricBernoulli = symmetricBernoulli := by
  have hm : Measurable (fun ω => 1-bernoulliIndicator ω) :=
    measurable_const.sub bernoulliIndicator_measurable
  unfold symmetricBernoulli
  rw [Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac hm, Measure.map_dirac hm]
  simp [bernoulliIndicator, add_comm]

theorem quantile_sharpness_fails_without_comonotonicity :
    ∃ X Y : ℝ → ℝ, Measurable X ∧ Measurable Y ∧
      (∀ ω, 0 ≤ X ω ∧ 0 ≤ Y ω) ∧ (Set.range X).Finite ∧ (Set.range Y).Finite ∧
      tailQuantile (Measure.map X symmetricBernoulli) (3/4) = {0} ∧
      tailQuantile (Measure.map Y symmetricBernoulli) (3/4) = {0} ∧
      tailQuantile (Measure.map (fun ω => X ω+Y ω) symmetricBernoulli) (3/4) = {1} ∧
      tailQuantile (Measure.map (fun ω => X ω+Y ω) symmetricBernoulli) (3/4) ≠ {(0 : ℝ)+0} := by
  have hsum : tailQuantile (Measure.map (fun ω => bernoulliIndicator ω+(1-bernoulliIndicator ω))
      symmetricBernoulli) (3/4) = {1} := by
    have he : (fun ω => bernoulliIndicator ω+(1-bernoulliIndicator ω)) =
        (fun _ : ℝ => (1 : ℝ)) := by funext ω; ring
    rw [he]
    exact tailQuantile_constant_randomVariable symmetricBernoulli 1 (by norm_num)
  refine ⟨bernoulliIndicator, (fun ω => 1-bernoulliIndicator ω),
    bernoulliIndicator_measurable, measurable_const.sub bernoulliIndicator_measurable,
    bernoulliIndicator_finite_nonnegative.1, bernoulliIndicator_finite_nonnegative.2.1,
    bernoulliIndicator_finite_nonnegative.2.2, ?_, ?_, hsum, ?_⟩
  · rw [bernoulliIndicator_law]
    exact tailQuantile_symmetricBernoulli_upper (by norm_num)
  · rw [complementary_bernoulliIndicator_law]
    exact tailQuantile_symmetricBernoulli_upper (by norm_num)
  · rw [hsum]
    norm_num

end ScalarMonotone.EndOfPaper
end
