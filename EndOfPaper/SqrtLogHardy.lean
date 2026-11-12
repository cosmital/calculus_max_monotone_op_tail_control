import EndOfPaper.AffinePowerGeometric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
The exact square-root logarithmic Hardy estimate and derived prefix L1, used in the subgaussian example.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem sqrt_log_hardy_prefix {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt (Real.log 2-Real.log x)) volume 0 v ∧
      hardyScalar (fun x : ℝ => Real.sqrt (Real.log 2-Real.log x)) v ≤
        Real.sqrt (Real.log 2+1-Real.log v) := by
  let f := fun x : ℝ => Real.log 2-Real.log x
  let a := Real.sqrt (Real.log 2+1-Real.log v)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogv : Real.log v ≤ 0 := by
    simpa only [Real.log_one] using Real.log_le_log hv hv1
  have hA : 0 < Real.log 2+1-Real.log v := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr hA
  have hasq : a^2 = Real.log 2+1-Real.log v := Real.sq_sqrt hA.le
  have hf : IntervalIntegrable f volume 0 v :=
    intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
  have hf0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) v) : 0 ≤ f x := by
    have hh : Real.log x ≤ 0 := by
      simpa only [Real.log_one] using Real.log_le_log hx.1 (hx.2.le.trans hv1)
    dsimp only [f]
    linarith
  have ht (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) v) :
      Real.sqrt (f x) ≤ (f x+a^2)/(2*a) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) ha)).mpr
    nlinarith [Real.sq_sqrt (hf0 x hx),sq_nonneg (Real.sqrt (f x)-a)]
  have hdom : IntervalIntegrable (fun x => (f x+a^2)/(2*a)) volume 0 v :=
    (hf.add intervalIntegrable_const).div_const _
  have hgm : Measurable (fun x => Real.sqrt (f x)) := by dsimp only [f]; fun_prop
  have hgi : IntervalIntegrable (fun x => Real.sqrt (f x)) volume 0 v := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hv.le).mpr
    apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hv.le).mp hdom).mono' hgm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact ht x hx
  have hmean : hardyScalar f v = a^2 := by
    calc
      _ = Real.log 2+hardyScalar (fun x : ℝ => -Real.log x) v := by
        simpa only [one_mul,sub_eq_add_neg] using
          hardyScalar_affine hv intervalIntegral.intervalIntegrable_log'.neg (Real.log 2) 1
      _ = a^2 := by rw [hardyScalar_exponential_profile hv,hasq]; ring
  have hint : (∫ x in (0 : ℝ)..v, f x) = v*a^2 := by
    have hh : (∫ x in (0 : ℝ)..v, f x)/v = a^2 := hmean
    exact ((div_eq_iff hv.ne').mp hh).trans (mul_comm _ _)
  have hdomMean : hardyScalar (fun x => (f x+a^2)/(2*a)) v = a := by
    rw [hardyScalar,intervalIntegral.integral_div,
      intervalIntegral.integral_add hf intervalIntegrable_const,intervalIntegral.integral_const,hint]
    simp only [sub_zero,smul_eq_mul]
    field_simp [hv.ne',ha.ne']
    <;> ring
  exact ⟨hgi,(hardyScalar_mono hv hgi hdom ht).trans_eq hdomMean⟩

end ScalarMonotone.EndOfPaper
end
