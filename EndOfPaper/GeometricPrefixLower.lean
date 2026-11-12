import EndOfPaper.GeometricLogExcess
import EndOfPaper.GeometricScalarCompletion

/-!
Every selected profile value lies below its exact
extended geometric prefix mean. Arbitrary selections,
zeros and completed jump levels are included.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem geometricPrefixValue_nonnegative (s : ℝ → ℝ) (p : ℝ) : 0 ≤ geometricPrefixValue s p := by
  cases he : extendedLogIntegral s p <;> simp only [geometricPrefixValue,he]
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem profile_value_le_geometricPrefixValue {q : DecGraph} {s : ℝ → ℝ} {B p u : ℝ}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) (hu : u ∈ q.val p) : u ≤ geometricPrefixValue s p := by
  by_cases hupos : 0 < u
  · obtain ⟨t,hmt,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
    have hPt : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
      rw [harea]
      exact hP
    have he : t =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] s :=
      decreasing_selections_ae_eq q.property.1 hts hs volume measurableSet_Ioo
    rw [← geometricPrefixValue_congr_ae he hp.2.le,
      geometricPrefixValue_log_excess q.property.1 hmt hts hq0 hPt hp hupos hu]
    have hI0 : 0 ≤ (∫ x in Ioo (0 : ℝ) B, max (Real.log (t x/u)) 0)/p :=
      div_nonneg (integral_nonneg (fun x => le_max_right _ _)) hp.1.le
    have hexp : 1 ≤ Real.exp ((∫ x in Ioo (0 : ℝ) B, max (Real.log (t x/u)) 0)/p) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hI0
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hupos.le
  · exact (le_of_not_gt hupos).trans (geometricPrefixValue_nonnegative s p)

end ScalarMonotone.EndOfPaper
end
