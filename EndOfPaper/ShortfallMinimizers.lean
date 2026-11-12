import EndOfPaper.Shortfall

/-!
# All expected-shortfall minimizers, including atoms and nonunique minimizers

The manuscript identifies the entire minimizer set with the completed quantile
fiber. Complementary slackness gives the converse without differentiating an
integral: equality in weak duality forces an optimal weight to be one above the
threshold and zero below it. The weight remains on the original probability space.
-/

open Set Filter MeasureTheory

noncomputable section
namespace ScalarMonotone.EndOfPaper

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tailQuantile_map_mem_iff {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) (a p : ℝ) :
    a ∈ tailQuantile (Measure.map X μ) p ↔
      μ.real {ω | a < X ω} ≤ p ∧ p ≤ μ.real {ω | a ≤ X ω} := by
  change ((Measure.map X μ).real (Ioi a) ≤ p ∧
    p ≤ (Measure.map X μ).real (Ici a)) ↔ _
  simp only [measureReal_def, Measure.map_apply hX measurableSet_Ioi,
    Measure.map_apply hX measurableSet_Ici]
  rfl

/-- Equality in weak duality forces the strict/weak tail brackets at the threshold. -/
theorem shortfall_equality_brackets {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Z : Ω → ℝ} {p a : ℝ} (hp : 0 < p) (hX : Integrable X μ)
    (hZ : AEMeasurable Z μ) (hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1)
    (hmean : (∫ ω, Z ω ∂μ) = p)
    (heq : (∫ ω, X ω * Z ω ∂μ) / p = shortfallObjective μ X p a)
    (hXm : Measurable X) :
    μ.real {ω | a < X ω} ≤ p ∧ p ≤ μ.real {ω | a ≤ X ω} := by
  classical
  have hZi := integrable_unit_weight hZ hz
  have hXZ := integrable_mul_unit_weight hX hZ hz
  have hprod := integrable_mul_unit_weight (hX.sub (integrable_const a)) hZ hz
  have hpos : Integrable (fun ω => max (X ω - a) 0) μ :=
    (hX.sub (integrable_const a)).pos_part
  have hle : (fun ω => (X ω - a) * Z ω) ≤ᵐ[μ] (fun ω => max (X ω - a) 0) :=
    hz.mono fun ω hω => weighted_excess_le (X ω) a (Z ω) hω.1 hω.2
  have hprodint : (∫ ω, (X ω - a) * Z ω ∂μ) =
      (∫ ω, X ω * Z ω ∂μ) - a * p := by
    simp_rw [sub_mul]
    rw [integral_sub hXZ (hZi.const_mul a), integral_const_mul, hmean]
  have hinteq : (∫ ω, (X ω - a) * Z ω ∂μ) = ∫ ω, max (X ω - a) 0 ∂μ := by
    rw [hprodint]
    unfold shortfallObjective at heq
    field_simp [hp.ne'] at heq
    linarith only [heq]
  have hpoint := (integral_eq_iff_of_ae_le hprod hpos hle).mp hinteq
  have hstrict : MeasurableSet {ω | a < X ω} := measurableSet_lt measurable_const hXm
  have hweak : MeasurableSet {ω | a ≤ X ω} := measurableSet_le measurable_const hXm
  have hstricti := (integrable_const (μ := μ) (1 : ℝ)).indicator hstrict
  have hweaki := (integrable_const (μ := μ) (1 : ℝ)).indicator hweak
  have hlower : {ω | a < X ω}.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ] Z := by
    filter_upwards [hz, hpoint] with ω hz he
    change (X ω - a) * Z ω = max (X ω - a) 0 at he
    by_cases ht : a < X ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | a < X ω} from ht)]
      rw [max_eq_left (sub_nonneg.mpr ht.le)] at he
      have hz1 : Z ω = 1 := (mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht)))
        (by simpa only [mul_one] using he)
      exact hz1.ge
    · rw [Set.indicator_of_not_mem (show ω ∉ {ω | a < X ω} from ht)]
      exact hz.1
  have hupper : Z ≤ᵐ[μ] {ω | a ≤ X ω}.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hz, hpoint] with ω hz he
    change (X ω - a) * Z ω = max (X ω - a) 0 at he
    by_cases ht : a ≤ X ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | a ≤ X ω} from ht)]
      exact hz.2
    · rw [Set.indicator_of_not_mem (show ω ∉ {ω | a ≤ X ω} from ht)]
      rw [max_eq_right (sub_nonpos.mpr (lt_of_not_ge ht).le)] at he
      have hz0 : Z ω = 0 := (mul_eq_zero.mp he).resolve_left
        (sub_ne_zero.mpr (ne_of_lt (lt_of_not_ge ht)))
      exact hz0.le
  constructor
  · have h := integral_mono_ae hstricti hZi hlower
    simpa only [integral_indicator hstrict, setIntegral_const, smul_eq_mul, mul_one,
      hmean] using h
  · have h := integral_mono_ae hZi hweaki hupper
    simpa only [integral_indicator hweak, setIntegral_const, smul_eq_mul, mul_one,
      hmean] using h

/-- The entire minimizer set, on an arbitrary original probability space. -/
theorem shortfall_minimizer_iff_quantile {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : Measurable X) (hXi : Integrable X μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) (a : ℝ) :
    (∀ b : ℝ, shortfallObjective μ X p a ≤ shortfallObjective μ X p b) ↔
      a ∈ tailQuantile (Measure.map X μ) p := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hXm.aemeasurable
  constructor
  · intro hmin
    obtain ⟨b, hb⟩ := tailQuantile_fiber_nonempty (Measure.map X μ) hp
    have hbr := (tailQuantile_map_mem_iff hXm b p).mp hb
    have hatt := shortfall_attainment hp.1 hXm hXi hbr.1 hbr.2
    obtain ⟨Z, hZm, hz, hmean, hval⟩ := hatt.1.1
    have hsame : shortfallObjective μ X p b = shortfallObjective μ X p a :=
      le_antisymm (hatt.2 a) (hmin b)
    exact (tailQuantile_map_mem_iff hXm a p).mpr
      (shortfall_equality_brackets hp.1 hXi hZm hz hmean (hval.symm.trans hsame) hXm)
  · intro ha
    have hbr := (tailQuantile_map_mem_iff hXm a p).mp ha
    exact (shortfall_attainment hp.1 hXm hXi hbr.1 hbr.2).2

theorem shortfall_minimizers_eq_tailQuantile {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : Measurable X) (hXi : Integrable X μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    {a | ∀ b : ℝ, shortfallObjective μ X p a ≤ shortfallObjective μ X p b} =
      tailQuantile (Measure.map X μ) p := by
  ext a
  exact shortfall_minimizer_iff_quantile hXm hXi hp a

end ScalarMonotone.EndOfPaper
end
