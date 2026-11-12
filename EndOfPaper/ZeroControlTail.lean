import EndOfPaper.EndpointSymmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The original modulus and a selected zero control cutoff
yield the direct two-copy 2b tail bound for every nonnegative
threshold, without logarithmic moments.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem randomized_control_zero_difference {ι E : Type*} [Fintype ι] [PseudoMetricSpace E]
    {h : E → ℝ} {Λ : ι → E → ℝ}
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (i : ι) {x y : E} (hx : Λ i x = 0) (hy : Λ i y = 0) : h x = h y := by
  classical
  have hp : (∏ j, max (Λ j x) (Λ j y)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hx,hy,max_self])
  have hb := hmod x y
  rw [hp,mul_zero] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

theorem randomized_two_copy_zero_control_tail {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hident : IdentDistrib Z Z' μ μ) {Λ : ι → E → ℝ}
    (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {h : E → ℝ} (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (i : ι) {b : ℝ} (hb : μ.real {ω | 0 < Λ i (Z ω)} ≤ b) :
    μ.real {ω | 0 < |h (Z ω)-h (Z' ω)|} ≤ 2*b := by
  let A : Set Ω := {ω | 0 < Λ i (Z ω)}
  let B : Set Ω := {ω | 0 < Λ i (Z' ω)}
  have hsub : {ω | 0 < |h (Z ω)-h (Z' ω)|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hA : 0 < Λ i (Z ω)
    · exact Or.inl hA
    by_cases hB : 0 < Λ i (Z' ω)
    · exact Or.inr hB
    have he := randomized_control_zero_difference hmod i
      (le_antisymm (le_of_not_gt hA) (hΛ0 i (Z ω)))
      (le_antisymm (le_of_not_gt hB) (hΛ0 i (Z' ω)))
    change 0 < |h (Z ω)-h (Z' ω)| at hω
    rw [he,sub_self,abs_zero] at hω
    exact (lt_irrefl (0 : ℝ) hω).elim
  have hAB : μ.real A = μ.real B := by
    exact congrArg ENNReal.toReal ((hident.comp (hΛm i)).measure_mem_eq measurableSet_Ioi)
  calc
    _ ≤ μ.real (A ∪ B) := measureReal_mono hsub
    _ ≤ μ.real A+μ.real B := measureReal_union_le A B
    _ = 2*μ.real A := by rw [← hAB,two_mul]
    _ ≤ 2*b := mul_le_mul_of_nonneg_left hb (by norm_num)

theorem randomized_zero_cutoff_tail {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E} (hZ : Measurable Z)
    (hident : IdentDistrib Z Z' μ μ) {Λ : ι → E → ℝ}
    (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {h : E → ℝ} (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (i : ι) {q : Operator} {b : ℝ}
    (hQ : DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) q)
    (hqb : (0 : ℝ) ∈ q b) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ < |h (Z ω)-h (Z' ω)|} ≤ 2*b := by
  have hb := quantile_comparison_strict_tail ((hΛm i).comp hZ) hQ hqb
  exact (measureReal_mono (show {ω | τ < |h (Z ω)-h (Z' ω)|} ⊆
      {ω | 0 < |h (Z ω)-h (Z' ω)|} from fun _ hω => hτ.trans_lt hω)).trans
    (randomized_two_copy_zero_control_tail hident hΛm hΛ0 hmod i hb)

end ScalarMonotone.EndOfPaper
end
