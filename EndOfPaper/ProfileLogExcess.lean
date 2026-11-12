import EndOfPaper.LogGeometricDomain
import EndOfPaper.ExtendedLogMean

/-!
The exact positive-log excess area at a selected positive
cutoff, with prefix log L1 derived from the positive-log area.
Zero values after the cutoff are allowed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem profile_log_excess_integral {q : Operator} {sq : ℝ → ℝ} {B b c : ℝ}
    (hq : Decreasing q) (hm : Measurable sq)
    (hs : SelectionOn q (Ioo (0 : ℝ) B) sq)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, 0 ≤ v)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hb : b ∈ Ioo (0 : ℝ) B) (hc : 0 < c) (hcb : c ∈ q b) :
    IntegrableOn (fun x => max (Real.log (sq x/c)) 0) (Ioo (0 : ℝ) B) volume ∧
      (∫ x in Ioo (0 : ℝ) B, max (Real.log (sq x/c)) 0) =
        (∫ x in Ioo (0 : ℝ) b, Real.log (sq x))-b*Real.log c := by
  classical
  have hbLog : b ∈ dom (logOp q) := by
    refine ⟨Real.log c,?_⟩
    rw [logOp_mem_iff,Real.exp_log hc]
    exact hcb
  have hlog := logarithmic_prefix_integrable_of_positive_part hq hb.1 hb.2.le hm hs
    (positive_log_integrable_of_lintegral hm hP) hbLog
  have hlogOn := (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.1.le).mp hlog
  have hconst : IntegrableOn (fun _ : ℝ => Real.log c) (Ioo (0 : ℝ) b) volume :=
    integrableOn_const.mpr (Or.inr (by simp))
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo (0 : ℝ) B := fun x hx => ⟨hx.1,hx.2.trans hb.2⟩
  have he : (fun x => max (Real.log (sq x/c)) 0) =ᵐ[volume.restrict (Ioo (0 : ℝ) B)]
      (Ioo (0 : ℝ) b).indicator (fun x => Real.log (sq x)-Real.log c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      (Set.countable_singleton b).ae_not_mem (volume.restrict (Ioo (0 : ℝ) B))] with x hx hxb
    have hne : x ≠ b := by simpa only [mem_singleton_iff] using hxb
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcs : c ≤ sq x := Decreasing.le_of_lt hq (hs x hx) hcb hlt
      have hxp : 0 < sq x := hc.trans_le hcs
      rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) b from ⟨hx.1,hlt⟩),
        Real.log_div hxp.ne' hc.ne',max_eq_left (sub_nonneg.mpr (Real.log_le_log hc hcs))]
    · have hsc : sq x ≤ c := Decreasing.le_of_lt hq hcb (hs x hx) hgt
      have hratio : 0 ≤ sq x/c := div_nonneg (hq0 x hx (sq x) (hs x hx)) hc.le
      have hratio1 : sq x/c ≤ 1 := (div_le_one hc).mpr hsc
      rw [max_eq_right (Real.log_nonpos hratio hratio1),
        indicator_of_not_mem (show x ∉ Ioo (0 : ℝ) b from fun hxI => (not_lt_of_ge hgt.le) hxI.2)]
  have hDiff : IntegrableOn (fun x => Real.log (sq x)-Real.log c) (Ioo (0 : ℝ) b) volume :=
    hlogOn.sub hconst
  have hInd := (IntegrableOn.integrable_indicator hDiff measurableSet_Ioo).mono_measure
    (Measure.restrict_le_self (s := Ioo (0 : ℝ) B) (μ := volume))
  refine ⟨hInd.congr he.symm,?_⟩
  have hcint : (∫ _x in Ioo (0 : ℝ) b, Real.log c) = b*Real.log c := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.1.le,
      intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
  calc
    _ = ∫ x in Ioo (0 : ℝ) B, (Ioo (0 : ℝ) b).indicator
        (fun x => Real.log (sq x)-Real.log c) x := integral_congr_ae he
    _ = ∫ x in Ioo (0 : ℝ) b, Real.log (sq x)-Real.log c := by
      rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr hsub]
    _ = (∫ x in Ioo (0 : ℝ) b, Real.log (sq x))-(∫ _x in Ioo (0 : ℝ) b, Real.log c) :=
      integral_sub hlogOn hconst
    _ = _ := by rw [hcint]

end ScalarMonotone.EndOfPaper
end
