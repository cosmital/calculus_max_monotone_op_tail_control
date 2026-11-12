import EndOfPaper.QuantileDependenceCounterexample
import EndOfPaper.FiniteStepProfiles
import EndOfPaper.ReplicatedHardyEnvelope

/-!
Replication is essential: every original-space coupling of
symmetric Bernoulli and a zero point mass has zero upper-level
quantile, while the actual averaged Hardy graph is strictly positive.
-/

open Set Filter MeasureTheory
open scoped BigOperators Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem tailQuantile_positive_smul (ν : Measure ℝ) {c : ℝ} (hc : 0 < c) :
    tailQuantile (Measure.map (fun x : ℝ => c*x) ν) = outputScale c (tailQuantile ν) := by
  ext p v
  rw [outputScale_mem_iff hc.ne']
  change ((Measure.map (fun x : ℝ => c*x) ν).real (Ioi v) ≤ p ∧
    p ≤ (Measure.map (fun x : ℝ => c*x) ν).real (Ici v)) ↔
      (ν.real (Ioi (v/c)) ≤ p ∧ p ≤ ν.real (Ici (v/c)))
  have hm : Measurable (fun x : ℝ => c*x) := by fun_prop
  have hstrict : (fun x : ℝ => c*x) ⁻¹' Ioi v = Ioi (v/c) := by
    ext x
    simp only [mem_preimage, mem_Ioi, div_lt_iff₀ hc, mul_comm]
  have hweak : (fun x : ℝ => c*x) ⁻¹' Ici v = Ici (v/c) := by
    ext x
    simp only [mem_preimage, mem_Ici, div_le_iff₀ hc, mul_comm]
  simp only [measureReal_def, Measure.map_apply hm measurableSet_Ioi,
    Measure.map_apply hm measurableSet_Ici, hstrict, hweak]

theorem bernoulli_quantile_step_selection :
    SelectionOn (tailQuantile symmetricBernoulli) (Ioo (0 : ℝ) 1)
      (hardyInitialStep (1/2) 1) := by
  intro u hu
  by_cases h : u ≤ 1/2
  · have hn : u ≤ (2 : ℝ)⁻¹ := by simpa only [one_div] using h
    have hq : hardyInitialStep (1/2) 1 u = 1 := by simp [hardyInitialStep, hn]
    rw [hq]
    change symmetricBernoulli.real (Ioi 1) ≤ u ∧ u ≤ symmetricBernoulli.real (Ici 1)
    have hstrict : symmetricBernoulli.real (Ioi 1) = 0 := by
      norm_num [symmetricBernoulli, measureReal_def, Measure.add_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator]
    have hweak : symmetricBernoulli.real (Ici 1) = 1/2 := by
      norm_num [symmetricBernoulli, measureReal_def, Measure.add_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator]
    rw [hstrict, hweak]
    exact ⟨hu.1.le, h⟩
  · have hn : ¬u ≤ (2 : ℝ)⁻¹ := by simpa only [one_div] using h
    have hq : hardyInitialStep (1/2) 1 u = 0 := by simp [hardyInitialStep, hn]
    rw [hq, tailQuantile_symmetricBernoulli_upper ⟨lt_of_not_ge h, hu.2⟩]
    rfl

theorem bernoulli_integrable : Integrable (fun x : ℝ => x) symmetricBernoulli := by
  have hq := hardyInitialStep_measurable (1/2 : ℝ) 1
  have hLaw := tailQuantile_selection_law symmetricBernoulli hq bernoulli_quantile_step_selection
  rw [← hLaw]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable hq.aemeasurable).mpr
    (hardyInitialStep_integrable (1/2) 1 unitUniform)

theorem bernoulli_hardy_value {p : ℝ} (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    quantileHardy symmetricBernoulli p = {1/(2*p)} := by
  have hp0 : p ∈ Ioo (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ) < 1/2).trans hp.1, hp.2⟩
  have h := hardy_tailQuantile_fiber symmetricBernoulli bernoulli_integrable
    (hardyInitialStep_measurable (1/2) 1) bernoulli_quantile_step_selection hp0
  have hscalar : hardyScalar (hardyInitialStep (1/2) 1) p = 1/(2*p) := by
    rw [hardyScalar, hardyInitialStep_integral 1 ⟨by norm_num, hp.1.le⟩]
    field_simp [hp0.1.ne']
    <;> ring
  rw [hscalar] at h
  exact h

theorem dirac_hardy_value (c : ℝ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    quantileHardy (Measure.dirac c) p = {c} := by
  have hLaw : Measure.map (fun _ : ℝ => c) unitUniform = Measure.dirac c := by
    rw [Measure.map_const, measure_univ, one_smul]
  have hi : Integrable (fun x : ℝ => x) (Measure.dirac c) := by
    rw [← hLaw]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_const.aemeasurable).mpr (integrable_const c)
  have hs : ∀ u ∈ Ioo (0 : ℝ) 1, c ∈ tailQuantile (Measure.dirac c) u := by
    intro u hu
    rw [tailQuantile_dirac_interior c hu]
    rfl
  have h := hardy_tailQuantile_fiber (Measure.dirac c) hi measurable_const hs hp
  rwa [hardyScalar_const c hp.1.ne'] at h

theorem fixed_pair_bernoulli_quantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : Measure.map X μ = symmetricBernoulli) (hY : Measure.map Y μ = Measure.dirac 0)
    {p : ℝ} (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    tailQuantile (Measure.map (fun ω => (X ω+Y ω)/2) μ) p = {0} := by
  have hzero : ∀ᵐ ω ∂μ, Y ω = 0 := by
    apply ae_iff.mpr
    have h := congrArg (fun ν : Measure ℝ => ν ({(0 : ℝ)}ᶜ)) hY
    change (Measure.map Y μ) ({(0 : ℝ)}ᶜ) = (Measure.dirac 0) ({(0 : ℝ)}ᶜ) at h
    rw [Measure.map_apply hYm (measurableSet_singleton (0 : ℝ)).compl] at h
    simpa [Measure.dirac_apply, Set.indicator] using h
  have heq : (fun ω => (X ω+Y ω)/2) =ᵐ[μ] (fun ω => (1/2 : ℝ)*X ω) :=
    hzero.mono (fun ω hω => by
      change (X ω+Y ω)/2 = (1/2 : ℝ)*X ω
      rw [hω]
      ring)
  rw [Measure.map_congr heq]
  change tailQuantile (Measure.map ((fun x : ℝ => (1/2 : ℝ)*x) ∘ X) μ) p = _
  rw [← Measure.map_map (by fun_prop) hXm, hX,
    tailQuantile_positive_smul symmetricBernoulli (by norm_num : (0 : ℝ) < 1/2)]
  simp [outputScale, tailQuantile_symmetricBernoulli_upper hp]

theorem replication_is_essential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : Measure.map X μ = symmetricBernoulli) (hY : Measure.map Y μ = Measure.dirac 0)
    {p : ℝ} (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    tailQuantile (Measure.map (fun ω => (X ω+Y ω)/2) μ) p = {0} ∧
      replicatedHardyEnvelope ![symmetricBernoulli, Measure.dirac 0] p = {1/(4*p)} ∧
      0 < 1/(4*p) := by
  have hp0 : p ∈ Ioo (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ) < 1/2).trans hp.1, hp.2⟩
  let laws : Fin 2 → Measure ℝ := ![symmetricBernoulli, Measure.dirac 0]
  let a : Fin 2 → ℝ := ![1/(2*p), 0]
  have ha (i : Fin 2) : quantileHardy (laws i) p = {a i} := by
    fin_cases i
    · exact bernoulli_hardy_value hp
    · exact dirac_hardy_value 0 hp0
  have hH := replicatedHardyEnvelope_singletons laws ha
  have hscalar : (∑ i, a i)/(2 : ℝ) = 1/(4*p) := by
    simp only [Fin.sum_univ_two, a, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    field_simp [hp0.1.ne']
    <;> ring
  norm_num only at hH
  rw [hscalar] at hH
  exact ⟨fixed_pair_bernoulli_quantile μ hXm hYm hX hY hp, hH,
    one_div_pos.mpr (mul_pos (by norm_num) hp0.1)⟩

theorem replication_counterexample_model :
    ∃ X Y : ℝ → ℝ, Measurable X ∧ Measurable Y ∧
      Integrable X symmetricBernoulli ∧ Integrable Y symmetricBernoulli ∧
      Measure.map X symmetricBernoulli = symmetricBernoulli ∧
      Measure.map Y symmetricBernoulli = Measure.dirac 0 := by
  refine ⟨id, (fun _ => 0), measurable_id, measurable_const, bernoulli_integrable,
    integrable_const 0, Measure.map_id, ?_⟩
  rw [Measure.map_const, measure_univ, one_smul]

end ScalarMonotone.EndOfPaper
end
