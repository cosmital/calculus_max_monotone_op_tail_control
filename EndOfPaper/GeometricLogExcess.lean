import EndOfPaper.ProfileLogExcess
import EndOfPaper.ExtendedLogMean

/-!
Exact geometric prefix normalization at a selected
positive cutoff. Prefix positivity and ordinary logarithmic
L1 are derived from the original profile data.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_cutoff_log_prefix_integrable {q : Operator} {sq : ℝ → ℝ} {B b c : ℝ}
    (hq : Decreasing q) (hm : Measurable sq) (hs : SelectionOn q (Ioo (0 : ℝ) B) sq)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hb : b ∈ Ioo (0 : ℝ) B) (hc : 0 < c) (hcb : c ∈ q b) :
    IntervalIntegrable (fun x => Real.log (sq x)) volume 0 b ∧
      ∀ x ∈ Ioo (0 : ℝ) b, 0 < sq x := by
  have hbLog : b ∈ dom (logOp q) := by
    refine ⟨Real.log c,?_⟩
    rw [logOp_mem_iff,Real.exp_log hc]
    exact hcb
  refine ⟨logarithmic_prefix_integrable_of_positive_part hq hb.1 hb.2.le hm hs
    (positive_log_integrable_of_lintegral hm hP) hbLog,?_⟩
  intro x hx
  exact hc.trans_le (Decreasing.le_of_lt hq (hs x ⟨hx.1,hx.2.trans hb.2⟩) hcb hx.2)

theorem geometricPrefixValue_log_excess {q : Operator} {sq : ℝ → ℝ} {B b c : ℝ}
    (hq : Decreasing q) (hm : Measurable sq) (hs : SelectionOn q (Ioo (0 : ℝ) B) sq)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, 0 ≤ v)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hb : b ∈ Ioo (0 : ℝ) B) (hc : 0 < c) (hcb : c ∈ q b) :
    geometricPrefixValue sq b = c*Real.exp ((∫ x in Ioo (0 : ℝ) B, max (Real.log (sq x/c)) 0)/b) := by
  have hpre := positive_cutoff_log_prefix_integrable hq hm hs hP hb hc hcb
  rw [geometricPrefixValue_of_integrable hb.1 hpre.1 hpre.2]
  have he := (profile_log_excess_integral hq hm hs hq0 hP hb hc hcb).2
  have hmean : hardyScalar (fun x => Real.log (sq x)) b = Real.log c+
      (∫ x in Ioo (0 : ℝ) B, max (Real.log (sq x/c)) 0)/b := by
    rw [hardyScalar,intervalIntegral.integral_of_le hb.1.le,integral_Ioc_eq_integral_Ioo,he]
    field_simp [hb.1.ne']
    <;> ring
  rw [hmean,Real.exp_add,Real.exp_log hc]

end ScalarMonotone.EndOfPaper
end
