import EndOfPaper.LocalHardy
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
The local geometric--arithmetic Hardy average inequality,
using the actual uniform dilation measure and the pinned
convex integral Jensen theorem. Prefix hypotheses are explicit.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem geometric_average_le_arithmetic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p)
    (hli : IntervalIntegrable (fun x => Real.log (f x)) volume 0 p)
    (hf : ∀ x ∈ Ioo (0 : ℝ) p, 0 < f x) :
    Real.exp (hardyScalar (fun x => Real.log (f x)) p) ≤ hardyScalar f p := by
  have hiD : Integrable (fun r => f (r*p)) unitUniform :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hardyScalar_dilation_integrable (f := f) hp hi)
  have hliD : Integrable (fun r => Real.log (f (r*p))) unitUniform :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hardyScalar_dilation_integrable (f := fun x : ℝ => Real.log (f x)) hp hli)
  have he : (fun r => Real.exp (Real.log (f (r*p)))) =ᵐ[unitUniform] (fun r => f (r*p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.exp_log (hf (r*p) ⟨mul_pos hr.1 hp,mul_lt_of_lt_one_left hp hr.2⟩)
  have hEi : Integrable (Real.exp ∘ fun r => Real.log (f (r*p))) unitUniform :=
    hiD.congr he.symm
  have hJ := ConvexOn.map_integral_le (μ := unitUniform)
    (f := fun r : ℝ => Real.log (f (r*p))) convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (Eventually.of_forall (fun r => mem_univ (Real.log (f (r*p))))) hliD hEi
  rw [integral_congr_ae he] at hJ
  rw [hardyScalar_dilation (fun x : ℝ => Real.log (f x)) hp,hardyScalar_dilation f hp]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,unitUniform] using hJ

end ScalarMonotone.EndOfPaper
end
