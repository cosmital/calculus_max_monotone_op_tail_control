import EndOfPaper.ExtendedLogMean
import EndOfPaper.Profiles

/-!
The scalar affine-power geometric bound for every alpha>0, with derived logarithmic integrability and all zero cases.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem affine_power_prefix_log_bounds {m c α x v : ℝ}
    (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) (hx : 0 < x) (hv : 0 < v)
    (hxv : x ≤ v) (hsv : 0 < m+c*v^(-α)) :
    0 < m+c*x^(-α) ∧
      Real.log (m+c*v^(-α)) ≤ Real.log (m+c*x^(-α)) ∧
      Real.log (m+c*x^(-α)) ≤ Real.log (m+c*v^(-α))+α*(Real.log v-Real.log x) := by
  have hlow : m+c*v^(-α) ≤ m+c*x^(-α) :=
    add_le_add_left (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hxv (neg_nonpos.mpr hα.le)) hc) m
  have hsx : 0 < m+c*x^(-α) := hsv.trans_le hlow
  have ht : 1 ≤ (v/x)^α := Real.one_le_rpow ((one_le_div hx).mpr hxv) hα.le
  have hprod : v^(-α)*(v/x)^α = x^(-α) := by
    rw [Real.rpow_def_of_pos hv,Real.rpow_def_of_pos (div_pos hv hx),
      Real.rpow_def_of_pos hx,← Real.exp_add,Real.log_div hv.ne' hx.ne']
    congr 1
    ring
  have hup : m+c*x^(-α) ≤ (m+c*v^(-α))*(v/x)^α := by
    calc
      _ ≤ m*(v/x)^α+c*x^(-α) := add_le_add_right (by simpa using mul_le_mul_of_nonneg_left ht hm) _
      _ = _ := by rw [add_mul,mul_assoc,hprod]
  refine ⟨hsx,Real.log_le_log hsv hlow,?_⟩
  calc
    _ ≤ Real.log ((m+c*v^(-α))*(v/x)^α) := Real.log_le_log hsx hup
    _ = _ := by
      rw [Real.log_mul hsv.ne' (Real.rpow_pos_of_pos (div_pos hv hx) α).ne',
        Real.log_rpow (div_pos hv hx),Real.log_div hv.ne' hx.ne']

theorem affine_power_prefix_log_integrable {m c α v : ℝ}
    (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) (hv : 0 < v)
    (hsv : 0 < m+c*v^(-α)) :
    IntervalIntegrable (fun x : ℝ => Real.log (m+c*x^(-α))) volume 0 v := by
  have hlog : IntegrableOn Real.log (Ioo (0 : ℝ) v) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hv.le).mp intervalIntegral.intervalIntegrable_log'
  have hconst (a : ℝ) : IntegrableOn (fun _ : ℝ => a) (Ioo (0 : ℝ) v) volume :=
    integrableOn_const.mpr (Or.inr (by simp))
  have hbound : IntegrableOn (fun x => |Real.log (m+c*v^(-α))|+α*(Real.log v-Real.log x))
      (Ioo (0 : ℝ) v) volume := (hconst _).add (((hconst _).sub hlog).const_mul α)
  have hmeas : Measurable (fun x : ℝ => Real.log (m+c*x^(-α))) := by fun_prop
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hv.le).mpr
  apply hbound.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := affine_power_prefix_log_bounds hm hc hα hx.1 hv hx.2.le hsv
  have hd : 0 ≤ α*(Real.log v-Real.log x) :=
    mul_nonneg hα.le (sub_nonneg.mpr (Real.log_le_log hx.1 hx.2.le))
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith only [hb.2.1,neg_le_abs (Real.log (m+c*v^(-α))),hd]
  · linarith only [hb.2.2,le_abs_self (Real.log (m+c*v^(-α)))]

theorem hardyScalar_affine {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p) (a b : ℝ) :
    hardyScalar (fun x => a+b*f x) p = a+b*hardyScalar f p := by
  rw [hardyScalar,intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul b),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,hardyScalar]
  simp only [sub_zero,smul_eq_mul]
  field_simp [hp.ne']
  <;> ring

theorem geometricPrefixValue_zero {p : ℝ} (hp : 0 < p) :
    geometricPrefixValue (fun _ => (0 : ℝ)) p = 0 := by
  apply geometricPrefixValue_of_negative_area_top hp
  · simp only [Real.log_zero,ENNReal.ofReal_zero,lintegral_zero,ne_eq]
    exact ENNReal.zero_ne_top
  · exact negative_log_area_eq_top_of_zero_interval le_rfl hp le_rfl (fun _ _ => rfl)

theorem geometricPrefixValue_affine_power_bound {m c α v : ℝ}
    (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) (hv : 0 < v) :
    geometricPrefixValue (fun x => m+c*x^(-α)) v ≤ Real.exp α*(m+c*v^(-α)) := by
  have hsv0 : 0 ≤ m+c*v^(-α) := add_nonneg hm (mul_nonneg hc (Real.rpow_nonneg hv.le _))
  by_cases hsv : m+c*v^(-α) = 0
  · have hm0 : m = 0 := by nlinarith [mul_nonneg hc (Real.rpow_nonneg hv.le (-α))]
    have hc0 : c = 0 := by
      have he : c*v^(-α) = 0 := by linarith only [hsv,hm0]
      exact (mul_eq_zero.mp he).resolve_right (Real.rpow_pos_of_pos hv (-α)).ne'
    simp only [hm0,hc0,zero_mul,zero_add,mul_zero,geometricPrefixValue_zero hv,le_refl]
  · have hsvpos : 0 < m+c*v^(-α) := lt_of_le_of_ne hsv0 (Ne.symm hsv)
    have hlogi := affine_power_prefix_log_integrable hm hc hα hv hsvpos
    have hlogpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) v) : 0 < m+c*x^(-α) :=
      (affine_power_prefix_log_bounds hm hc hα hx.1 hv hx.2.le hsvpos).1
    let K := Real.log (m+c*v^(-α))
    have hi : IntervalIntegrable (fun x : ℝ => K+α*Real.log v+α*(-Real.log x)) volume 0 v :=
      intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_log'.neg.const_mul α)
    have hmean : hardyScalar (fun x => Real.log (m+c*x^(-α))) v ≤ K+α := by
      have hb := hardyScalar_mono hv hlogi hi (fun x hx => by
        have hh := (affine_power_prefix_log_bounds hm hc hα hx.1 hv hx.2.le hsvpos).2.2
        dsimp only [K]
        linarith only [hh])
      have he : hardyScalar (fun x : ℝ => K+α*Real.log v+α*(-Real.log x)) v = K+α := by
        rw [hardyScalar_affine (f := fun x : ℝ => -Real.log x) hv intervalIntegral.intervalIntegrable_log'.neg,
          hardyScalar_exponential_profile hv]
        ring
      exact hb.trans_eq he
    rw [geometricPrefixValue_of_integrable hv hlogi hlogpos]
    calc
      _ ≤ Real.exp (K+α) := Real.exp_le_exp.mpr hmean
      _ = _ := by rw [Real.exp_add,Real.exp_log hsvpos,mul_comm]

end ScalarMonotone.EndOfPaper
end
