import EndOfPaper.ProfileMomentComparison
import EndOfPaper.LogGeometricDomain

/-!
Actual marginal quantile comparison derives logarithmic
excess expectation bounds and L1 from finite profile area.
Arbitrary original spaces, atoms and selections are retained.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_log_part_monotoneOn_nonnegative :
    MonotoneOn (fun x : ℝ => max (Real.log x) 0) (Ici 0) := by
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · simpa only [hx0,Real.log_zero,max_self] using le_max_right (Real.log y) 0
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact max_le_max (Real.log_le_log hxp hxy) le_rfl

theorem clamped_log_excess_monotone {c : ℝ} (hc : 0 < c) :
    Monotone (fun x : ℝ => max (Real.log (max x 0/c)) 0) := by
  intro x y hxy
  apply positive_log_part_monotoneOn_nonnegative
  · exact div_nonneg (le_max_right _ _) hc.le
  · exact div_nonneg (le_max_right _ _) hc.le
  · exact div_le_div_of_nonneg_right (max_le_max hxy le_rfl) hc.le

theorem logarithmic_excess_lintegral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : 0 ≤ᵐ[μ] X) {q : Operator} (hq : MaximalDecreasing q)
    (hqi : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {sq : ℝ → ℝ} (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ ω, ENNReal.ofReal (max (Real.log (X ω/c)) 0) ∂μ) ≤
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p/c)) 0) := by
  have hψm : Measurable (fun x : ℝ => ENNReal.ofReal (max (Real.log (max x 0/c)) 0)) := by fun_prop
  have hψ : Monotone (fun x : ℝ => ENNReal.ofReal (max (Real.log (max x 0/c)) 0)) :=
    fun _ _ hxy => ENNReal.ofReal_le_ofReal (clamped_log_excess_monotone hc hxy)
  have hb := random_variable_profile_lintegral_bound μ hX hq hqi hQ hsq hψm hψ
  have hleft : (∫⁻ ω, ENNReal.ofReal (max (Real.log (max (X ω) 0/c)) 0) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (max (Real.log (X ω/c)) 0) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hX0] with ω hω
    change 0 ≤ X ω at hω
    rw [max_eq_left hω]
  have hright : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (max (sq p) 0/c)) 0)) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p/c)) 0) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    rw [max_eq_left (hq0 p hp (sq p) (hsq p hp))]
  rwa [hleft,hright] at hb

theorem logarithmic_excess_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : 0 ≤ᵐ[μ] X) {q : Operator} (hq : MaximalDecreasing q)
    (hqi : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {sq : ℝ → ℝ} (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    {c : ℝ} (hc : 0 < c)
    (hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p/c)) 0)) < ∞) :
    Integrable (fun ω => max (Real.log (X ω/c)) 0) μ := by
  have hm : Measurable (fun ω => max (Real.log (X ω/c)) 0) := by fun_prop
  refine ⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun ω => le_max_right (Real.log (X ω/c)) 0))).mpr ?_⟩
  exact (logarithmic_excess_lintegral_bound μ hX hX0 hq hqi hq0 hQ hsq hc).trans_lt hfinite

theorem logarithmic_excess_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : 0 ≤ᵐ[μ] X) {q : Operator} (hq : MaximalDecreasing q)
    (hqi : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {sq : ℝ → ℝ} (hsm : Measurable sq) (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    {c : ℝ} (hc : 0 < c)
    (hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p/c)) 0)) < ∞) :
    (∫ ω, max (Real.log (X ω/c)) 0 ∂μ) ≤
      ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq p/c)) 0 := by
  have hm : Measurable (fun ω => max (Real.log (X ω/c)) 0) := by fun_prop
  have hmp : Measurable (fun p => max (Real.log (sq p/c)) 0) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun ω => le_max_right (Real.log (X ω/c)) 0)) hm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun p => le_max_right (Real.log (sq p/c)) 0)) hmp.aestronglyMeasurable]
  exact ENNReal.toReal_mono hfinite.ne
    (logarithmic_excess_lintegral_bound μ hX hX0 hq hqi hq0 hQ hsq hc)

end ScalarMonotone.EndOfPaper
end
