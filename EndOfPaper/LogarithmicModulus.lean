import EndOfPaper.LipschitzBrackets
import MonotoneOperators.ProbabilityBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
The actual finite product of local nonnegative controls
is bounded by a separated exponential logarithmic modulus.
The logarithmic control is proved measurable.
-/

open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem le_exp_log_positive_part {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.exp (max (Real.log x) 0) := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact (Real.exp_pos _).le
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log (lt_of_le_of_ne hx (Ne.symm hx0))).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_max_left _ _)

theorem logarithmic_two_endpoint_factor_bound {c x y : ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y ≤ c*Real.exp (max (Real.log (x/c)) 0+max (Real.log (y/c)) 0) := by
  have hbase (z : ℝ) (hz : 0 ≤ z) : z ≤ c*Real.exp (max (Real.log (z/c)) 0) := by
    have hb := le_exp_log_positive_part (div_nonneg hz hc.le)
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hb
  apply max_le
  · exact (hbase x hx).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (le_add_of_nonneg_right (le_max_right _ _))) hc.le)
  · exact (hbase y hy).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (le_add_of_nonneg_left (le_max_right _ _))) hc.le)

theorem logarithmic_product_bound {ι E : Type*} [Fintype ι]
    {c : ι → ℝ} {Λ : ι → E → ℝ} (hc : ∀ i, 0 < c i) (hΛ : ∀ i z, 0 ≤ Λ i z)
    (x y : E) :
    (∏ i, max (Λ i x) (Λ i y)) ≤ (∏ i, c i)*Real.exp
      ((∑ i, max (Real.log (Λ i x/c i)) 0)+(∑ i, max (Real.log (Λ i y/c i)) 0)) := by
  classical
  calc
    _ ≤ ∏ i, c i*Real.exp (max (Real.log (Λ i x/c i)) 0+max (Real.log (Λ i y/c i)) 0) :=
      Finset.prod_le_prod (fun i _ => (hΛ i x).trans (le_max_left _ _))
        (fun i _ => logarithmic_two_endpoint_factor_bound (hc i) (hΛ i x) (hΛ i y))
    _ = _ := by rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_add_distrib]

theorem logarithmic_control_measurable {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {Λ : ι → E → ℝ} (hΛ : ∀ i, Measurable (Λ i)) (c : ι → ℝ) :
    Measurable (fun z => ∑ i, max (Real.log (Λ i z/c i)) 0) := by
  classical
  fun_prop

theorem randomized_modulus_logarithmic_form {ι E : Type*} [Fintype ι] [PseudoMetricSpace E]
    {h : E → ℝ} {Λ : ι → E → ℝ} {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hΛ : ∀ i z, 0 ≤ Λ i z)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y))) :
    ∀ x y, |h x-h y| ≤ (∏ i, c i)*Real.exp
      ((∑ i, max (Real.log (Λ i x/c i)) 0)+(∑ i, max (Real.log (Λ i y/c i)) 0))*dist x y := by
  intro x y
  exact (hmod x y).trans (by
    simpa only [mul_comm (dist x y)] using
      mul_le_mul_of_nonneg_left (logarithmic_product_bound hc hΛ x y)
        (show 0 ≤ dist x y from dist_nonneg))

end ScalarMonotone.EndOfPaper
end
