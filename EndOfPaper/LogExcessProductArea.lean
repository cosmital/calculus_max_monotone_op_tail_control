import EndOfPaper.ProfileExcessArbitrary

/-!
The exact finite product logarithmic prefix area at arbitrary positive graph-valued cutoffs, with individual L1 derived.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem finite_log_excess_product_area {ι : Type*} [Fintype ι]
    {q : ι → Operator} (hq : ∀ i, MaximalDecreasing (q i))
    {sq : ι → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i p, 0 ≤ v)
    (hP : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p)) 0)) < ∞)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hcb : ∀ i, c i ∈ q i b) :
    (∑ i, ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq i p/c i)) 0) =
      ∫ p in Ioo (0 : ℝ) b, Real.log ((∏ i, sq i p)/(∏ i, c i)) := by
  classical
  have hi (i : ι) := profile_log_excess_integrable_of_selection
    (hq i) (hsq i) (hq0 i) (hP i) hb (hc i) (hcb i)
  have he : (fun p => ∑ i, max (Real.log (sq i p/c i)) 0) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (Ioo (0 : ℝ) b).indicator (fun p => Real.log ((∏ i, sq i p)/(∏ i, c i))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      (Set.countable_singleton b).ae_not_mem (volume.restrict (Ioo (0 : ℝ) 1))]
      with p hp hne
    have hpb : p ≠ b := by simpa only [mem_singleton_iff] using hne
    rcases lt_or_gt_of_ne hpb with hlt | hgt
    · have hge (i : ι) : c i ≤ sq i p := Decreasing.le_of_lt (hq i).1 (hsq i p hp) (hcb i) hlt
      have hp0 (i : ι) : 0 < sq i p := (hc i).trans_le (hge i)
      rw [Set.indicator_of_mem (show p ∈ Ioo (0 : ℝ) b from ⟨hp.1,hlt⟩),
        ← Finset.prod_div_distrib,Real.log_prod Finset.univ (fun i => sq i p/c i)
          (fun i _ => (div_pos (hp0 i) (hc i)).ne')]
      apply Finset.sum_congr rfl
      intro i _
      exact max_eq_left (Real.log_nonneg ((one_le_div (hc i)).mpr (hge i)))
    · rw [Set.indicator_of_not_mem (show p ∉ Ioo (0 : ℝ) b from fun h => (not_lt_of_ge hgt.le) h.2)]
      apply Finset.sum_eq_zero
      intro i _
      have hle : sq i p ≤ c i := Decreasing.le_of_lt (hq i).1 (hcb i) (hsq i p hp) hgt
      exact max_eq_right (Real.log_nonpos
        (div_nonneg (hq0 i p hp (sq i p) (hsq i p hp)) (hc i).le)
        ((div_le_one (hc i)).mpr hle))
  calc
    _ = ∫ p in Ioo (0 : ℝ) 1, ∑ i, max (Real.log (sq i p/c i)) 0 :=
      (integral_finset_sum _ (fun i _ => hi i)).symm
    _ = ∫ p in Ioo (0 : ℝ) 1, (Ioo (0 : ℝ) b).indicator
        (fun p => Real.log ((∏ i, sq i p)/(∏ i, c i))) p := integral_congr_ae he
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr
        (show Ioo (0 : ℝ) b ⊆ Ioo (0 : ℝ) 1 from fun p hp => ⟨hp.1,hp.2.trans hb.2⟩)]

end ScalarMonotone.EndOfPaper
end
