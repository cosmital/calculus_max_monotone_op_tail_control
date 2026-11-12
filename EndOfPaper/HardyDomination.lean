import EndOfPaper.NormExamples

/-!
Original-space Hardy monotonicity under almost-sure domination, both
scalar and whole completed-graph forms; scalar nonnegative homogeneity
and the mean lower bound. Integrability is explicit and arbitrary atoms
are retained through the original-space attained variational formula.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem quantileHardy_mono_values {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y Z : Ω → ℝ}
    (hYm : Measurable Y) (hZm : Measurable Z) (hYi : Integrable Y μ) (hZi : Integrable Z μ)
    (hle : Y ≤ᵐ[μ] Z) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a b : ℝ, quantileHardy (Measure.map Y μ) p = {a} ∧
      quantileHardy (Measure.map Z μ) p = {b} ∧ a ≤ b := by
  obtain ⟨a, ha, _, hAd, _, _, _⟩ := hardy_quantile_original_variational hYm hYi hp
  obtain ⟨b, hb, _, hBd, _, _, _⟩ := hardy_quantile_original_variational hZm hZi hp
  obtain ⟨W, hWm, hWb, hWp, hWa⟩ := hAd.1
  have hprod : (∫ ω, Y ω*W ω ∂μ) ≤ ∫ ω, Z ω*W ω ∂μ := by
    apply integral_mono_ae (integrable_mul_unit_weight hYi hWm hWb)
      (integrable_mul_unit_weight hZi hWm hWb)
    filter_upwards [hle, hWb] with ω hω hWω
    exact mul_le_mul_of_nonneg_right hω hWω.1
  have hC : (∫ ω, Z ω*W ω ∂μ)/p ∈ dualCandidates μ Z p :=
    ⟨W, hWm, hWb, hWp, rfl⟩
  refine ⟨a, b, ha, hb, ?_⟩
  rw [hWa]
  apply le_trans _ (hBd.2 hC)
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr hp.1.le)

theorem quantileHardy_original_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y Z : Ω → ℝ}
    (hYm : Measurable Y) (hZm : Measurable Z) (hYi : Integrable Y μ) (hZi : Integrable Z μ)
    (hle : Y ≤ᵐ[μ] Z) : DecLE (quantileHardy (Measure.map Y μ)) (quantileHardy (Measure.map Z μ)) := by
  have hY := quantileHardy_original_properties μ hYm hYi
  have hZ := quantileHardy_original_properties μ hZm hZi
  apply decLE_of_initial_interior hY.1.1 hZ.1.1 isOpen_Ioo ordConnected_Ioo
    (show (Ioo (0 : ℝ) 1).Nonempty from ⟨1/2, by norm_num⟩)
    (by rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]; exact ⟨le_rfl, zero_le_one⟩)
    (by simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hY.2.2)
    (fun x hx => (hZ.2.2 hx).1)
    (fun x hx => interior_subset (by rwa [hY.2.1]))
    (fun x hx => interior_subset (by rwa [hZ.2.1]))
  intro p hp r hr hrp u hu v hv
  obtain ⟨a, b, ha, hb, hab⟩ := quantileHardy_mono_values μ hYm hZm hYi hZi hle hp
  have hua : u = a := by rw [ha] at hu; exact hu
  have hbp : b ∈ quantileHardy (Measure.map Z μ) p := by rw [hb]; rfl
  exact hua ▸ hab.trans (Decreasing.le_of_lt hZ.1.1 hv hbp hrp)

theorem quantileHardy_smul_value {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hm : Measurable Y) (hi : Integrable Y μ) {c : ℝ} (hc : 0 ≤ c)
    {p a : ℝ} (hp : p ∈ Ioo 0 1) (ha : quantileHardy (Measure.map Y μ) p = {a}) :
    quantileHardy (Measure.map (fun ω => c*Y ω) μ) p = {c*a} := by
  obtain ⟨a', ha', _, hAd, _, _, _⟩ := hardy_quantile_original_variational hm hi hp
  have he : a' = a := Set.singleton_injective (ha'.symm.trans ha)
  rw [he] at hAd
  obtain ⟨b, hb, _, hBd, _, _, _⟩ := hardy_quantile_original_variational
    (measurable_const.mul hm) (hi.const_mul c) hp
  have hscale (W : Ω → ℝ) : (∫ ω, (c*Y ω)*W ω ∂μ)/p = c*((∫ ω, Y ω*W ω ∂μ)/p) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  have hlo : c*a ≤ b := by
    obtain ⟨W, hWm, hWb, hWp, hWa⟩ := hAd.1
    apply hBd.2
    refine ⟨W, hWm, hWb, hWp, ?_⟩
    rw [hscale, ← hWa]
  have hhi : b ≤ c*a := by
    obtain ⟨W, hWm, hWb, hWp, hWv⟩ := hBd.1
    have hC : (∫ ω, Y ω*W ω ∂μ)/p ∈ dualCandidates μ Y p :=
      ⟨W, hWm, hWb, hWp, rfl⟩
    rw [hWv, hscale]
    exact mul_le_mul_of_nonneg_left (hAd.2 hC) hc
  rwa [le_antisymm hhi hlo] at hb

theorem quantileHardy_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hm : Measurable Y) (hi : Integrable Y μ) {p a : ℝ} (hp : p ∈ Ioo 0 1)
    (ha : quantileHardy (Measure.map Y μ) p = {a}) : (∫ ω, Y ω ∂μ) ≤ a := by
  obtain ⟨b, hb, _, hdual, _, _, _⟩ := hardy_quantile_original_variational hm hi hp
  have hba : b = a := Set.singleton_injective (hb.symm.trans ha)
  have hC : (∫ ω, Y ω*p ∂μ)/p ∈ dualCandidates μ Y p := by
    refine ⟨(fun _ => p), aemeasurable_const,
      Eventually.of_forall (fun _ => ⟨hp.1.le, hp.2.le⟩), ?_, rfl⟩
    simp
  have hv := hdual.2 hC
  rw [hba, integral_mul_const] at hv
  simpa only [mul_div_cancel_right₀ _ hp.1.ne'] using hv

end ScalarMonotone.EndOfPaper
end
