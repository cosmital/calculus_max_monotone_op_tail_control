import EndOfPaper.Area
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Nonnegative moments from a capped tail bound

Source: Corollary `moments`. The scalar tail bound is explicit; no assumption
of a finite moment is introduced. The integral lives in ENNReal throughout.
The bridge from the completed operator minimum to this scalar bound is not
asserted here.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- An explicit primitive, valid for every positive real exponent. -/
theorem moment_density_primitive {r : ℝ} (hr : 0 < r) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, r*t^(r-1)) = y^r := by
  have hexp : -1 < r-1 := by linarith
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hexp), sub_add_cancel,
    Real.zero_rpow hr.ne', sub_zero]
  field_simp [hr.ne'] <;> ring

/-- The full nonnegative moment-tail identity, including divergence. -/
theorem moment_tail_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (r*t^(r-1)) := by
  have hi : ∀ t > 0, IntervalIntegrable (fun u : ℝ => r*u^(r-1)) volume 0 t := by
    intro t ht
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r-1)).const_mul r
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ r*t^(r-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hr.le (Real.rpow_nonneg ht.le _)
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ hY0 hY hi hn
  simpa only [moment_density_primitive hr] using h

/-- Cap the supplied scalar envelope at probability one before integrating. -/
theorem moment_le_capped_tail_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {b : ℝ → ℝ≥0∞} (hY : AEMeasurable Y μ)
    (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r)
    (hb : ∀ t > 0, μ {ω | t < Y ω} ≤ b t) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), min (b t) 1 * ENNReal.ofReal (r*t^(r-1)) := by
  rw [moment_tail_area μ hY hY0 hr]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h1 : μ {ω | t < Y ω} ≤ 1 := by
    simpa using (measure_mono (subset_univ {ω | t < Y ω}) :
      μ {ω | t < Y ω} ≤ μ univ)
  exact mul_le_mul_right' (le_min (hb t ht) h1) _

/-- The centered version used in the paper, with an arbitrary real pivot. -/
theorem centered_moment_le_capped_tail_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (c : ℝ) {b : ℝ → ℝ≥0∞}
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ t > 0, μ {ω | t < |X ω-c|} ≤ b t) :
    (∫⁻ ω, ENNReal.ofReal (|X ω-c|^r) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), min (b t) 1 * ENNReal.ofReal (r*t^(r-1)) :=
  moment_le_capped_tail_area μ (hX.sub aemeasurable_const).abs
    (Eventually.of_forall fun ω => abs_nonneg _) hr hb

end ScalarMonotone.EndOfPaper

end -- noncomputable section
