import EndOfPaper.LogarithmicExpectations
import EndOfPaper.GeometricDilation

/-!
Affine nonnegative profiles inherit finite positive-log area from the single baseline; no ordinary profile L1 is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_log_affine_bound {m c x : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (hx : 0 ≤ x) :
    max (Real.log (m+c*x)) 0 ≤ Real.log (m+c+1)+max (Real.log x) 0 := by
  have hC : 1 ≤ m+c+1 := by linarith
  have hCpos : 0 < m+c+1 := zero_lt_one.trans_le hC
  have hM : 0 < max x 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hlogM : Real.log (max x 1) = max (Real.log x) 0 := by
    by_cases h : x ≤ 1
    · have hh := positive_log_part_monotoneOn_nonnegative hx (by norm_num : (0 : ℝ) ≤ 1) h
      have hz : max (Real.log x) 0 = 0 := le_antisymm (by simpa using hh) (le_max_right _ _)
      rw [max_eq_right h,Real.log_one,hz]
    · have h1 : 1 ≤ x := (lt_of_not_ge h).le
      rw [max_eq_left h1,max_eq_left (Real.log_nonneg h1)]
  have hbound : m+c*x ≤ (m+c+1)*max x 1 := by
    calc
      m+c*x ≤ m*max x 1+c*max x 1 :=
        add_le_add (by nlinarith [le_max_right x 1]) (mul_le_mul_of_nonneg_left (le_max_left x 1) hc)
      _ = (m+c)*max x 1 := by ring
      _ ≤ (m+c+1)*max x 1 := mul_le_mul_of_nonneg_right (by linarith) hM.le
  have hh := positive_log_part_monotoneOn_nonnegative (add_nonneg hm (mul_nonneg hc hx))
    (mul_nonneg hCpos.le hM.le) hbound
  change max (Real.log (m+c*x)) 0 ≤ max (Real.log ((m+c+1)*max x 1)) 0 at hh
  rw [Real.log_mul hCpos.ne' hM.ne',hlogM,
    max_eq_left (add_nonneg (Real.log_nonneg hC) (le_max_right _ _))] at hh
  exact hh

theorem positive_log_area_affine_finite {s : ℝ → ℝ} (hsm : Measurable s)
    (hs0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ s x)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (m+c*s x)) 0)) < ∞ := by
  have hbase := positive_log_integrable_of_lintegral hsm hP
  have hconst : IntegrableOn (fun _x : ℝ => Real.log (m+c+1)) (Ioo (0 : ℝ) 1) :=
    integrableOn_const.mpr (Or.inr (by simp))
  have hdom : IntegrableOn (fun x : ℝ => Real.log (m+c+1)+max (Real.log (s x)) 0)
      (Ioo (0 : ℝ) 1) := hconst.add hbase
  have htarget : IntegrableOn (fun x : ℝ => max (Real.log (m+c*s x)) 0) (Ioo (0 : ℝ) 1) := by
    have htm : Measurable (fun x : ℝ => max (Real.log (m+c*s x)) 0) := by fun_prop
    apply hdom.mono' htm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact positive_log_affine_bound hm hc (hs0 x hx)
  exact ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun x : ℝ => le_max_right (Real.log (m+c*s x)) 0))).mp htarget.2)

end ScalarMonotone.EndOfPaper
end
