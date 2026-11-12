import EndOfPaper.QuantileTailCompletion
import Mathlib.Topology.Order.Compact

/-!
Actual attained lower quantiles and optimization over
two positive probability levels, including equality in the budget.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem quantile_lower_endpoint_isLeast (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IsLeast (tailQuantile ν p) (sInf (tailQuantile ν p)) :=
  (tailQuantile_fiber_compact ν hp).isLeast_sInf (tailQuantile_fiber_nonempty ν hp)

theorem quantile_lower_endpoint_le_of_strict_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hb : μ.real {ω | t < X ω} ≤ p) :
    sInf (tailQuantile (Measure.map X μ) p) ≤ t := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  have hMin := quantile_lower_endpoint_isLeast (Measure.map X μ) hp
  by_contra hle
  have htm : t < sInf (tailQuantile (Measure.map X μ) p) := lt_of_not_ge hle
  have hTail : (Measure.map X μ).real (Ioi t) ≤ p := by
    simpa only [measureReal_def,Measure.map_apply hX measurableSet_Ioi,preimage_setOf_eq] using hb
  have hUpper : p ≤ (Measure.map X μ).real (Ici (sInf (tailQuantile (Measure.map X μ) p))) := hMin.1.2
  have hLower : p ≤ (Measure.map X μ).real (Ioi t) := hUpper.trans
    (measureReal_mono (fun x hx => htm.trans_le hx))
  have hmem : t ∈ tailQuantile (Measure.map X μ) p :=
    ⟨hTail,hLower.trans (measureReal_mono Ioi_subset_Ici_self)⟩
  exact (not_le_of_gt htm) (hMin.2 hmem)

theorem quantile_lower_endpoint_le_of_decLE (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {q : Operator} (hq : MaximalDecreasing q) (hcomp : DecLE (tailQuantile ν) q)
    {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : t ∈ q p) :
    sInf (tailQuantile ν p) ≤ t := by
  have hf := decLE_fiber (tailQuantile_maximal ν) hq hcomp
    (show p ∈ dom (tailQuantile ν) from tailQuantile_fiber_nonempty ν hp) ⟨t,ht⟩
  obtain ⟨u,hu,hut⟩ := hf.1 (show t ∈ upperHull (q p) from ⟨t,ht,le_rfl⟩)
  exact ((quantile_lower_endpoint_isLeast ν hp).2 hu).trans hut

def twoParameterThresholds (C : ℝ → ℝ → ℝ) (p : ℝ) : Set ℝ :=
  {t | ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 < b ∧ a+2*b ≤ p ∧ t = C a b}

theorem twoParameterThresholds_nonempty (C : ℝ → ℝ → ℝ) {p : ℝ} (hp : 0 < p) :
    (twoParameterThresholds C p).Nonempty := by
  refine ⟨C (p/3) (p/3),p/3,by linarith,p/3,by linarith,?_,rfl⟩
  linarith

theorem quantile_lower_endpoint_le_two_parameter_inf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {C : ℝ → ℝ → ℝ}
    (hb : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      μ.real {ω | C a b < X ω} ≤ a+2*b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    sInf (tailQuantile (Measure.map X μ) p) ≤ sInf (twoParameterThresholds C p) := by
  apply le_csInf (twoParameterThresholds_nonempty C hp.1)
  rintro t ⟨a,ha,b,hb0,hbudget,rfl⟩
  have haI : a ∈ Ioo (0 : ℝ) 1 := ⟨ha,by linarith [hp.2]⟩
  have hbI : b ∈ Ioo (0 : ℝ) 1 := ⟨hb0,by linarith [hp.2]⟩
  exact quantile_lower_endpoint_le_of_strict_tail hX hp ((hb a haI b hbI).trans hbudget)

end ScalarMonotone.EndOfPaper
end
