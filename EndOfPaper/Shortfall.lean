import MonotoneOperators.Survival
import EndOfPaper.Area

/-!
# Expected shortfall: weak duality and atom-aware attainment

Source: Lemma `hardyvariational`. The optimizer is constructed on the ORIGINAL
probability space; no independent randomizer and no atomlessness are assumed.

This module proves the optimization statements for a specified quantile
threshold. Identification with the Hardy integral, and the converse saying
that EVERY minimizer is a quantile, remain outside this module.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

variable {Ω : Type*} [MeasurableSpace Ω]

def shortfallObjective (μ : Measure Ω) (X : Ω → ℝ) (p a : ℝ) : ℝ :=
  a + (∫ ω, max (X ω-a) 0 ∂μ)/p

def dualCandidates (μ : Measure Ω) (X : Ω → ℝ) (p : ℝ) : Set ℝ :=
  {v | ∃ Z : Ω → ℝ, AEMeasurable Z μ ∧
    (∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) ∧
    (∫ ω, Z ω ∂μ) = p ∧ v = (∫ ω, X ω*Z ω ∂μ)/p}

/-- The deterministic inequality underlying expected-shortfall duality. -/
theorem weighted_excess_le (x a z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (x-a)*z ≤ max (x-a) 0 := by
  rcases le_total (x-a) 0 with hn | hp
  · rw [max_eq_right hn]
    exact mul_nonpos_of_nonpos_of_nonneg hn hz0
  · rw [max_eq_left hp]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hz1)]

/-- A bounded measurable weight is integrable on a probability space. -/
theorem integrable_unit_weight {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : AEMeasurable Z μ)
    (hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) : Integrable Z μ := by
  apply (integrable_const (1 : ℝ)).mono' hZ.aestronglyMeasurable
  filter_upwards [hz] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2

/-- Multiplication by a feasible weight preserves integrability. -/
theorem integrable_mul_unit_weight {μ : Measure Ω} {X Z : Ω → ℝ}
    (hX : Integrable X μ) (hZ : AEMeasurable Z μ)
    (hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) :
    Integrable (fun ω => X ω*Z ω) μ := by
  apply hX.mono (hX.aestronglyMeasurable.mul hZ.aestronglyMeasurable)
  filter_upwards [hz] with ω hω
  change ‖X ω * Z ω‖ ≤ ‖X ω‖
  rw [norm_mul, Real.norm_eq_abs (Z ω), abs_of_nonneg hω.1]
  nlinarith [norm_nonneg (X ω)]

/-- Weak duality at every threshold. -/
theorem shortfall_weak_duality {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Z : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hX : Integrable X μ)
    (hZ : AEMeasurable Z μ) (hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1)
    (hmean : (∫ ω, Z ω ∂μ) = p) (a : ℝ) :
    (∫ ω, X ω*Z ω ∂μ)/p ≤ shortfallObjective μ X p a := by
  have hZi := integrable_unit_weight hZ hz
  have hXZ := integrable_mul_unit_weight hX hZ hz
  have hpos : Integrable (fun ω => max (X ω-a) 0) μ :=
    (hX.sub (integrable_const a)).pos_part
  have hle : (∫ ω, X ω*Z ω ∂μ) ≤
      ∫ ω, a*Z ω+max (X ω-a) 0 ∂μ := by
    apply integral_mono_ae hXZ ((hZi.const_mul a).add hpos)
    filter_upwards [hz] with ω hω
    change X ω * Z ω ≤ a * Z ω + max (X ω - a) 0
    have := weighted_excess_le (X ω) a (Z ω) hω.1 hω.2
    nlinarith
  rw [integral_add (hZi.const_mul a) hpos, integral_const_mul, hmean] at hle
  unfold shortfallObjective
  apply (div_le_iff₀ hp).mpr
  have he : (a + (∫ ω, max (X ω-a) 0 ∂μ)/p)*p =
      a*p+(∫ ω, max (X ω-a) 0 ∂μ) := by
    field_simp [hp.ne'] <;> ring
  rw [he]
  exact hle

/-- Atoms require a fractional weight, not an auxiliary coin toss. -/
theorem exists_atom_fraction {A B p : ℝ} (hB : 0 ≤ B)
    (hlo : A ≤ p) (hhi : p ≤ A+B) :
    ∃ η : ℝ, 0 ≤ η ∧ η ≤ 1 ∧ A+η*B = p := by
  by_cases hB0 : B = 0
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simp only [zero_mul, add_zero]
    linarith
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    refine ⟨(p-A)/B, div_nonneg (sub_nonneg.mpr hlo) hB, ?_, ?_⟩
    · exact (div_le_one hBp).mpr (by linarith)
    · field_simp [hB0] <;> ring

def quantileWeight (X : Ω → ℝ) (a η : ℝ) : Ω → ℝ :=
  fun ω => ({ω | a < X ω}.indicator (fun _ => (1 : ℝ))) ω +
    η * ({ω | X ω = a}.indicator (fun _ => (1 : ℝ))) ω

theorem quantileWeight_bounds (X : Ω → ℝ) (a : ℝ) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ω : Ω) :
    0 ≤ quantileWeight X a η ω ∧ quantileWeight X a η ω ≤ 1 := by
  classical
  by_cases hlt : a < X ω
  · have heq : X ω ≠ a := ne_of_gt hlt
    simp [quantileWeight, Set.indicator, hlt, heq]
  · by_cases heq : X ω = a
    · simpa [quantileWeight, Set.indicator, hlt, heq] using And.intro hη0 hη1
    · simp [quantileWeight, Set.indicator, hlt, heq]

/-- Equality in the pointwise weak-duality inequality. -/
theorem quantileWeight_excess (X : Ω → ℝ) (a η : ℝ) (ω : Ω) :
    (X ω-a)*quantileWeight X a η ω = max (X ω-a) 0 := by
  classical
  by_cases hlt : a < X ω
  · have heq : X ω ≠ a := ne_of_gt hlt
    simp [quantileWeight, Set.indicator, hlt, heq,
      max_eq_left (sub_nonneg.mpr hlt.le)]
  · by_cases heq : X ω = a
    · simp [quantileWeight, Set.indicator, hlt, heq]
    · simp [quantileWeight, Set.indicator, hlt, heq,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hlt))]

theorem quantileWeight_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (a η : ℝ) :
    Integrable (quantileWeight X a η) μ := by
  exact ((integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const hX)).add
    (((integrable_const (1 : ℝ)).indicator (measurableSet_eq_fun hX measurable_const)).const_mul η)

theorem quantileWeight_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (a η : ℝ) :
    (∫ ω, quantileWeight X a η ω ∂μ) =
      μ.real {ω | a < X ω}+η*μ.real {ω | X ω = a} := by
  have hlt : MeasurableSet {ω | a < X ω} := measurableSet_lt measurable_const hX
  have heq : MeasurableSet {ω | X ω = a} := measurableSet_eq_fun hX measurable_const
  have hi := (integrable_const (μ := μ) (1 : ℝ)).indicator hlt
  have hj := (integrable_const (μ := μ) (1 : ℝ)).indicator heq
  unfold quantileWeight
  rw [integral_add hi (hj.const_mul η), integral_const_mul,
    integral_indicator hlt, integral_indicator heq]
  simp only [setIntegral_const, smul_eq_mul, mul_one]

/-- The weak-tail mass is the strict-tail mass plus the mass of its atom. -/
theorem weak_tail_mass {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    μ.real {ω | a ≤ X ω} = μ.real {ω | a < X ω}+μ.real {ω | X ω = a} := by
  have hset : {ω | a ≤ X ω} = {ω | a < X ω} ∪ {ω | X ω = a} := by
    ext ω
    simp only [mem_setOf_eq, mem_union]
    constructor
    · intro h
      rcases h.eq_or_lt with he | hl
      · exact Or.inr he.symm
      · exact Or.inl hl
    · rintro (h | h)
      · exact h.le
      · simp [h]
  have hd : Disjoint {ω | a < X ω} {ω | X ω = a} := by
    rw [Set.disjoint_left]
    intro ω hlt heq
    exact (ne_of_gt hlt) heq
  simp only [measureReal_def, hset,
    measure_union hd (measurableSet_eq_fun hX measurable_const),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

/-- Atom-aware attainment and primal optimality at every quantile threshold. -/
theorem shortfall_attainment {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p a : ℝ} (hp : 0 < p)
    (hXm : Measurable X) (hXi : Integrable X μ)
    (hlo : μ.real {ω | a < X ω} ≤ p)
    (hhi : p ≤ μ.real {ω | a ≤ X ω}) :
    IsGreatest (dualCandidates μ X p) (shortfallObjective μ X p a) ∧
      ∀ b : ℝ, shortfallObjective μ X p a ≤ shortfallObjective μ X p b := by
  rw [weak_tail_mass hXm a] at hhi
  obtain ⟨η, hη0, hη1, hη⟩ := exists_atom_fraction (measureReal_nonneg) hlo hhi
  let Z := quantileWeight X a η
  have hZi : Integrable Z μ := quantileWeight_integrable hXm a η
  have hZm : AEMeasurable Z μ := hZi.aestronglyMeasurable.aemeasurable
  have hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1 :=
    Eventually.of_forall (quantileWeight_bounds X a hη0 hη1)
  have hmean : (∫ ω, Z ω ∂μ) = p := (quantileWeight_integral hXm a η).trans hη
  have hpos : Integrable (fun ω => max (X ω-a) 0) μ :=
    (hXi.sub (integrable_const a)).pos_part
  have hprod : (∫ ω, X ω*Z ω ∂μ) = a*p+(∫ ω, max (X ω-a) 0 ∂μ) := by
    calc
      _ = ∫ ω, a*Z ω+max (X ω-a) 0 ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by
          have hh := quantileWeight_excess X a η ω
          dsimp [Z]
          nlinarith
      _ = _ := by rw [integral_add (hZi.const_mul a) hpos, integral_const_mul, hmean]
  have hval : (∫ ω, X ω*Z ω ∂μ)/p = shortfallObjective μ X p a := by
    rw [hprod, shortfallObjective]
    field_simp [hp.ne'] <;> ring
  have hbound : ∀ v ∈ dualCandidates μ X p, v ≤ shortfallObjective μ X p a := by
    rintro v ⟨W, hW, hw, hm, rfl⟩
    exact shortfall_weak_duality hp hXi hW hw hm a
  constructor
  · exact ⟨⟨Z, hZm, hz, hmean, hval.symm⟩, hbound⟩
  · intro b
    rw [← hval]
    exact shortfall_weak_duality hp hXi hZm hz hmean b

/-- A mean-pivot inequality, separated from the tail-area integrability step. -/
theorem mean_pivot_distance {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (c : ℝ) :
    |(∫ ω, X ω ∂μ)-c| ≤ ∫ ω, |X ω-c| ∂μ := by
  have he : (∫ ω, X ω ∂μ)-c = ∫ ω, X ω-c ∂μ := by
    rw [integral_sub hX (integrable_const c)]
    simp
  rw [he]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun ω => X ω-c)

theorem pointwise_mean_pivot (X : Ω → ℝ) (m c M : ℝ) (hmc : |m-c| ≤ M) (ω : Ω) :
    |X ω-m| ≤ |X ω-c|+M := by
  have ht := abs_add (X ω-c) (c-m)
  have he : |c-m| = |m-c| := abs_sub_comm c m
  have hx : X ω-c+(c-m) = X ω-m := by ring
  rw [hx, he] at ht
  linarith


/-- A separate scalar functional: NOT a definition of the operator Hardy
transform. Its identification with a quantile average is in QuantileArea. -/
def dualShortfall (μ : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ :=
  sSup (dualCandidates μ X p)

theorem dualCandidates_nonempty {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {p : ℝ} (hp : p ∈ Icc 0 1) :
    (dualCandidates μ X p).Nonempty := by
  refine ⟨(∫ ω, X ω*p ∂μ)/p, (fun _ => p), aemeasurable_const, ?_, ?_, rfl⟩
  · exact Filter.Eventually.of_forall fun _ => hp
  · simp

theorem dualCandidates_bddAbove {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hX : Integrable X μ) :
    BddAbove (dualCandidates μ X p) := by
  refine ⟨shortfallObjective μ X p 0, ?_⟩
  rintro z ⟨Z, hZ, hz, hm, rfl⟩
  exact shortfall_weak_duality hp hX hZ hz hm 0

/-- At a quantile threshold the dual supremum is attained. -/
theorem dualShortfall_eq_at_quantile {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p a : ℝ} (hp : 0 < p)
    (hXm : Measurable X) (hXi : Integrable X μ)
    (hlo : μ.real {ω | a < X ω} ≤ p)
    (hhi : p ≤ μ.real {ω | a ≤ X ω}) :
    dualShortfall μ X p = shortfallObjective μ X p a :=
  (shortfall_attainment hp hXm hXi hlo hhi).1.csSup_eq

/-- Subadditivity of expected shortfall for arbitrary dependence.
The theorem is stated for the separate dual functional, not for a full graph. -/
theorem dualShortfall_add_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {p : ℝ} (hp : p ∈ Ioo 0 1)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    dualShortfall μ (fun ω => X ω+Y ω) p ≤
      dualShortfall μ X p+dualShortfall μ Y p := by
  apply csSup_le (dualCandidates_nonempty _ ⟨hp.1.le, hp.2.le⟩)
  rintro v ⟨Z, hZ, hz, hm, rfl⟩
  have hXZ := integrable_mul_unit_weight hX hZ hz
  have hYZ := integrable_mul_unit_weight hY hZ hz
  have hx : (∫ ω, X ω*Z ω ∂μ)/p ≤ dualShortfall μ X p :=
    le_csSup (dualCandidates_bddAbove hp.1 hX) ⟨Z, hZ, hz, hm, rfl⟩
  have hy : (∫ ω, Y ω*Z ω ∂μ)/p ≤ dualShortfall μ Y p :=
    le_csSup (dualCandidates_bddAbove hp.1 hY) ⟨Z, hZ, hz, hm, rfl⟩
  have he : (fun ω => (X ω+Y ω)*Z ω) =
      (fun ω => X ω*Z ω+Y ω*Z ω) := by funext ω; ring
  rw [he, integral_add hXZ hYZ, add_div]
  exact add_le_add hx hy

end ScalarMonotone.EndOfPaper

end -- noncomputable section
