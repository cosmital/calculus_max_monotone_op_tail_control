import EndOfPaper.LocalHardy

/-!
The explicit negative-infinite logarithm at zero.
Every positive-length interval of zeros has infinite negative
logarithmic area, including the zero-ramp example.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

def negativeLogWithZero (t : ℝ) : ℝ≥0∞ :=
  if t = 0 then ∞ else ENNReal.ofReal (-Real.log t)

theorem negativeLogWithZero_zero : negativeLogWithZero 0 = ∞ := by
  simp [negativeLogWithZero]

theorem negativeLogWithZero_of_pos {t : ℝ} (ht : 0 < t) :
    negativeLogWithZero t = ENNReal.ofReal (-Real.log t) := by
  simp only [negativeLogWithZero,if_neg ht.ne']

theorem negative_log_area_eq_top_of_zero_interval {f : ℝ → ℝ} {a b p : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbp : b ≤ p)
    (hz : ∀ x ∈ Ioo a b, f x = 0) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (f x)) = ∞ := by
  classical
  have hsub : Ioo a b ⊆ Ioo (0 : ℝ) p :=
    fun _ hx => ⟨ha.trans_lt hx.1,hx.2.trans_le hbp⟩
  have hA : ENNReal.ofReal (b-a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  have hconst :
      (∫⁻ x in Ioo (0 : ℝ) p, (Ioo a b).indicator (fun _ => (∞ : ℝ≥0∞)) x) = ∞ := by
    calc
      _ = (∞ : ℝ≥0∞)*(volume.restrict (Ioo (0 : ℝ) p)) (Ioo a b) := by
        simp [lintegral_indicator measurableSet_Ioo,lintegral_const]
      _ = ∞ := by
        rw [Measure.restrict_apply measurableSet_Ioo,inter_eq_left.mpr hsub]
        simp [ENNReal.top_mul,hA]
  apply top_unique
  rw [← hconst]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ Ioo a b
  · simp only [indicator_of_mem hx,hz x hx,negativeLogWithZero_zero,le_rfl]
  · simp only [indicator_of_not_mem hx]
    exact zero_le _

theorem zero_ramp_negative_log_after_half {p : ℝ} (hp : (1/2 : ℝ) < p) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (max (1-2*x) 0)) = ∞ := by
  apply negative_log_area_eq_top_of_zero_interval (a := (1/2 : ℝ)) (b := p)
    (by norm_num) hp le_rfl
  intro x hx
  exact max_eq_right (by linarith [hx.1])

end ScalarMonotone.EndOfPaper
end
