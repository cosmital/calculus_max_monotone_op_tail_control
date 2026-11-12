import MonotoneOperators.Survival

/-!
An explicit two-way shared-branch probability measure,
measurable branch observables, exact marginal and real-probability
formulas, and the lower bound furnished by its first branch.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

def twoBranchMeasure {Ω : Type*} [MeasurableSpace Ω] (p : ℝ) (μ : Measure Ω) :
    Measure (ℝ × Ω) :=
  ENNReal.ofReal p • Measure.map (fun ω => ((0 : ℝ), ω)) μ +
    ENNReal.ofReal (1-p) • Measure.map (fun ω => ((1 : ℝ), ω)) μ

def twoBranchFunction {Ω : Type*} (F G : Ω → ℝ) (z : ℝ × Ω) : ℝ :=
  if z.1 = 0 then F z.2 else G z.2

theorem twoBranchFunction_measurable {Ω : Type*} [MeasurableSpace Ω]
    {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (twoBranchFunction F G) := by
  exact Measurable.ite (measurable_fst (measurableSet_singleton (0 : ℝ)))
    (hF.comp measurable_snd) (hG.comp measurable_snd)

theorem twoBranchMeasure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : p ∈ Ioo 0 1) :
    IsProbabilityMeasure (twoBranchMeasure p μ) := by
  constructor
  have hp0 := hp.1.le
  have hq0 : 0 ≤ 1-p := by linarith [hp.2]
  have hm0 : Measurable (fun ω : Ω => ((0 : ℝ), ω)) := by fun_prop
  have hm1 : Measurable (fun ω : Ω => ((1 : ℝ), ω)) := by fun_prop
  simp only [twoBranchMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply hm0 MeasurableSet.univ, Measure.map_apply hm1 MeasurableSet.univ, preimage_univ,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 hq0]
  norm_num

theorem twoBranchFunction_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ) {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measure.map (twoBranchFunction F G) (twoBranchMeasure p μ) =
      ENNReal.ofReal p • Measure.map F μ +
        ENNReal.ofReal (1-p) • Measure.map G μ := by
  have hm := twoBranchFunction_measurable hF hG
  have hm0 : Measurable (fun ω : Ω => ((0 : ℝ), ω)) := by fun_prop
  have hm1 : Measurable (fun ω : Ω => ((1 : ℝ), ω)) := by fun_prop
  have heF : twoBranchFunction F G ∘ (fun ω : Ω => ((0 : ℝ), ω)) = F := by
    funext ω
    simp [Function.comp_def, twoBranchFunction]
  have heG : twoBranchFunction F G ∘ (fun ω : Ω => ((1 : ℝ), ω)) = G := by
    funext ω
    simp [Function.comp_def, twoBranchFunction]
  rw [twoBranchMeasure, Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.map_map hm hm0, Measure.map_map hm hm1, heF, heG]

theorem twoBranchMeasure_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : p ∈ Ioo 0 1)
    {S : Set (ℝ × Ω)} (hS : MeasurableSet S) :
    (twoBranchMeasure p μ).real S =
      p*μ.real {ω | ((0 : ℝ), ω) ∈ S} +
        (1-p)*μ.real {ω | ((1 : ℝ), ω) ∈ S} := by
  have hq0 : 0 ≤ 1-p := by linarith [hp.2]
  have hm0 : Measurable (fun ω : Ω => ((0 : ℝ), ω)) := by fun_prop
  have hm1 : Measurable (fun ω : Ω => ((1 : ℝ), ω)) := by fun_prop
  simp only [measureReal_def, twoBranchMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.map_apply hm0 hS, Measure.map_apply hm1 hS, smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.1.le,
    ENNReal.toReal_ofReal hq0]
  rfl

theorem twoBranchMeasure_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : p ∈ Ioo 0 1)
    {S : Set (ℝ × Ω)} (hS : MeasurableSet S) :
    p*μ.real {ω | ((0 : ℝ), ω) ∈ S} ≤ (twoBranchMeasure p μ).real S := by
  rw [twoBranchMeasure_real μ hp hS]
  exact le_add_of_nonneg_right (mul_nonneg (by linarith [hp.2]) measureReal_nonneg)

end ScalarMonotone.EndOfPaper
end
