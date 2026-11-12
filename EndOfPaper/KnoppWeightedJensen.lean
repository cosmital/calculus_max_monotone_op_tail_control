import EndOfPaper.GeometricMeanJensen
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
The local weighted Jensen step and exact logarithmic
identity needed for Polya--Knopp. These are auxiliary local
lemmas; the full extended integral theorem remains separate.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem weighted_log_prefix_integrable {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < f x) :
    IntervalIntegrable (fun x => Real.log (x*f x)) volume 0 p := by
  have hi : IntervalIntegrable (fun x => Real.log x+Real.log (f x)) volume 0 p :=
    intervalIntegral.intervalIntegrable_log'.add hlog
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mp hi).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (Real.log_mul hx.1.ne' (hpos x hx).ne').symm

theorem weighted_log_hardy_identity {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < f x) :
    hardyScalar (fun x => Real.log (x*f x)) p =
      Real.log p-1+hardyScalar (fun x => Real.log (f x)) p := by
  have hInt : (∫ x in (0 : ℝ)..p, Real.log (x*f x)) =
      ∫ x in (0 : ℝ)..p, (Real.log x+Real.log (f x)) := by
    simp only [intervalIntegral.integral_of_le hp.le,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.log_mul hx.1.ne' (hpos x hx).ne'
  rw [hardyScalar,hInt,intervalIntegral.integral_add intervalIntegral.intervalIntegrable_log' hlog,
    integral_log]
  simp only [zero_mul,sub_zero,add_zero,hardyScalar]
  field_simp [hp.ne']
  <;> ring

theorem geometric_weighted_prefix_upper {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < f x) :
    Real.exp (hardyScalar (fun x => Real.log (f x)) p) ≤
      Real.exp 1/p^2*(∫ x in (0 : ℝ)..p, x*f x) := by
  have hgi : IntervalIntegrable (fun x => x*f x) volume 0 p :=
    hi.continuousOn_mul continuous_id.continuousOn
  have hJ := geometric_average_le_arithmetic hp hgi
    (weighted_log_prefix_integrable hp hlog hpos) (fun x hx => mul_pos hx.1 (hpos x hx))
  have he : Real.exp (hardyScalar (fun x => Real.log (f x)) p) =
      Real.exp 1/p*Real.exp (hardyScalar (fun x => Real.log (x*f x)) p) := by
    rw [weighted_log_hardy_identity hp hlog hpos,Real.exp_add,Real.exp_sub,Real.exp_log hp]
    field_simp [hp.ne',Real.exp_ne_zero (1 : ℝ)]
    <;> ring
  calc
    _ = Real.exp 1/p*Real.exp (hardyScalar (fun x => Real.log (x*f x)) p) := he
    _ ≤ Real.exp 1/p*hardyScalar (fun x => x*f x) p :=
      mul_le_mul_of_nonneg_left hJ (div_nonneg (Real.exp_pos 1).le hp.le)
    _ = _ := by
      rw [hardyScalar]
      simp only [div_eq_mul_inv,inv_pow]
      ring

end ScalarMonotone.EndOfPaper
end
