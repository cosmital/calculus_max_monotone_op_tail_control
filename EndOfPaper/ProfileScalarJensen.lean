import EndOfPaper.ConcaveGrowth
import MonotoneOperators.Survival

/-!
Local Hardy Jensen bounds for concave inverse profiles. Prefix L1 of
the composition is a conclusion, without a sign or global integrability
assumption. Both power and exponential input averages are computed.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hardyScalar_concave_composition {g f : ℝ → ℝ} {U : Set ℝ}
    (hg : ConcaveOn ℝ U g) (hm : MonotoneOn g U) (ho : IsOpen U)
    {x₀ p : ℝ} (hx : x₀ ∈ U) (htail : Ici x₀ ⊆ U) (hp : 0 < p)
    (hf : IntervalIntegrable f volume 0 p)
    (hlower : ∀ t ∈ Ioo 0 p, x₀ ≤ f t) :
    IntervalIntegrable (fun t => g (f t)) volume 0 p ∧
      hardyScalar (fun t => g (f t)) p ≤ g (hardyScalar f p) := by
  obtain ⟨l, u, ⟨hlx, hxu⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hx)
  let a := (l+x₀)/2
  have ha : a ∈ U := hsub ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  have hax : a < x₀ := by dsimp [a]; linarith
  have hXi : Integrable (fun r => f (r*p)) unitUniform :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hardyScalar_dilation_integrable hp hf)
  have hX : ∀ᵐ r ∂unitUniform, x₀ ≤ f (r*p) := by
    apply (ae_restrict_mem measurableSet_Ioo).mono
    intro r hr
    exact hlower (r*p) ⟨mul_pos hr.1 hp, mul_lt_of_lt_one_left hp hr.2⟩
  obtain ⟨hGi, hJ⟩ := concave_monotone_jensen_derived_integrability
    hg hm (hg.continuousOn ho) ha hx hax htail hX hXi
  have hG01 : IntervalIntegrable (fun r => g (f (r*p))) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hGi
  refine ⟨?_, ?_⟩
  · simpa [hp.ne', mul_assoc] using hG01.comp_mul_right p⁻¹
  · rw [hardyScalar_dilation _ hp, hardyScalar_dilation f hp]
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, unitUniform] using hJ

theorem power_inverse_profile_jensen {g : ℝ → ℝ} {U : Set ℝ} {κ p : ℝ}
    (hg : ConcaveOn ℝ U g) (hm : MonotoneOn g U) (ho : IsOpen U)
    (hκ : 1 < κ) (hp : 0 < p) (hx : p^((-1 : ℝ)/κ) ∈ U)
    (htail : Ici (p^((-1 : ℝ)/κ)) ⊆ U) :
    IntervalIntegrable (fun t => g (t^((-1 : ℝ)/κ))) volume 0 p ∧
      hardyScalar (fun t => g (t^((-1 : ℝ)/κ))) p ≤
        g ((κ/(κ-1))*p^((-1 : ℝ)/κ)) := by
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  obtain ⟨hi, hJ⟩ := hardyScalar_concave_composition hg hm ho hx htail hp
    (power_quantile_intervalIntegrable hκ) (fun t ht =>
      Real.rpow_le_rpow_of_nonpos ht.1 ht.2.le (div_nonpos_of_nonpos_of_nonneg (by norm_num) hk0.le))
  exact ⟨hi, by simpa only [hardyScalar_power_profile hκ hp] using hJ⟩

theorem exponential_inverse_profile_jensen {g : ℝ → ℝ} {U : Set ℝ} {p : ℝ}
    (hg : ConcaveOn ℝ U g) (hm : MonotoneOn g U) (ho : IsOpen U)
    (hp : 0 < p) (hx : -Real.log p ∈ U) (htail : Ici (-Real.log p) ⊆ U) :
    IntervalIntegrable (fun t => g (-Real.log t)) volume 0 p ∧
      hardyScalar (fun t => g (-Real.log t)) p ≤ g (1-Real.log p) := by
  obtain ⟨hi, hJ⟩ := hardyScalar_concave_composition hg hm ho hx htail hp
    (exponential_quantile_intervalIntegrable p) (fun t ht =>
      neg_le_neg (Real.log_le_log ht.1 ht.2.le))
  exact ⟨hi, by simpa only [hardyScalar_exponential_profile hp] using hJ⟩

end ScalarMonotone.EndOfPaper
end
