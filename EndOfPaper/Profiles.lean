import EndOfPaper.HardyScalar
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Explicit scalar Hardy profiles

Source: equation `hardyprofileidentities` and the interior computations behind
`hardyregularizedprofiles`. These are exact scalar integral identities. They
do not assert equality of the full inverse completed graphs, or the general
convex-transformation bounds of Proposition `hardyprofiles`.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- The general integrable power average. -/
theorem hardyScalar_rpow {s p : ℝ} (hs : -1 < s) (hp : 0 < p) :
    hardyScalar (fun u => u ^ s) p = p ^ s/(s+1) := by
  have hs1 : s+1 ≠ 0 := ne_of_gt (by linarith : 0 < s+1)
  unfold hardyScalar
  rw [integral_rpow (Or.inl hs), Real.zero_rpow hs1,
    sub_zero, Real.rpow_add hp s 1, Real.rpow_one]
  field_simp [hp.ne', hs1] <;> ring

/-- Absolute integrability is proved before interpreting the power average. -/
theorem power_quantile_intervalIntegrable {κ p : ℝ} (hκ : 1 < κ) :
    IntervalIntegrable (fun u : ℝ => u ^ ((-1 : ℝ)/κ)) volume 0 p := by
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  have he : -1 < (-1 : ℝ)/κ := (lt_div_iff₀ hk0).mpr (by linarith)
  exact intervalIntegral.intervalIntegrable_rpow' he

/-- H(p ↦ p^(-1/κ))(p) = κ/(κ-1) p^(-1/κ), κ > 1. -/
theorem hardyScalar_power_profile {κ p : ℝ} (hκ : 1 < κ) (hp : 0 < p) :
    hardyScalar (fun u => u ^ ((-1 : ℝ)/κ)) p =
      (κ/(κ-1)) * p ^ ((-1 : ℝ)/κ) := by
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  have he : -1 < (-1 : ℝ)/κ := (lt_div_iff₀ hk0).mpr (by linarith)
  have heq : (-1 : ℝ)/κ+1 = (κ-1)/κ := by
    field_simp [hk0.ne'] <;> ring
  rw [hardyScalar_rpow he hp, heq]
  field_simp [hk0.ne', ne_of_gt (sub_pos.mpr hκ)] <;> ring

/-- The scalar scaled-power identity. Interpreting it as a survival-quantile
identity additionally requires C > 0. -/
theorem hardyScalar_scaled_power_profile {κ p : ℝ} (hκ : 1 < κ) (hp : 0 < p)
    (C : ℝ) :
    hardyScalar (fun u => C ^ (1/κ) * u ^ ((-1 : ℝ)/κ)) p =
      C ^ (1/κ) * (κ/(κ-1)) * p ^ ((-1 : ℝ)/κ) := by
  rw [hardyScalar_smul, hardyScalar_power_profile hκ hp]
  ring

/-- The exponential inverse profile is integrable at the origin. -/
theorem exponential_quantile_intervalIntegrable (p : ℝ) :
    IntervalIntegrable (fun u : ℝ => -Real.log u) volume 0 p :=
  intervalIntegral.intervalIntegrable_log'.neg

/-- H(-log)(p) = 1-log p. -/
theorem hardyScalar_exponential_profile {p : ℝ} (hp : 0 < p) :
    hardyScalar (fun u => -Real.log u) p = 1-Real.log p := by
  unfold hardyScalar
  rw [intervalIntegral.integral_neg, integral_log_from_zero]
  field_simp [hp.ne'] <;> ring

/-- A multiplicative survival constant becomes an additive quantile constant. -/
theorem hardyScalar_scaled_exponential_profile {p : ℝ} (hp : 0 < p) (C : ℝ) :
    hardyScalar (fun u => Real.log C-Real.log u) p =
      1+Real.log C-Real.log p := by
  have he : (fun u => Real.log C-Real.log u) =
      (fun u => Real.log C+(-Real.log u)) := by funext u; ring
  rw [he, hardyScalar_add intervalIntegrable_const
    (exponential_quantile_intervalIntegrable p), hardyScalar_const _ hp.ne',
    hardyScalar_exponential_profile hp]
  ring

/-- Interior exponential inversion yields the exact factor e. -/
theorem exponential_hardy_level_identity {C p : ℝ} (hC : 0 < C) (hp : 0 < p) :
    C * Real.exp 1 * Real.exp (-(1+Real.log C-Real.log p)) = p := by
  have he : -(1+Real.log C-Real.log p) = -1-Real.log C+Real.log p := by ring
  rw [he, Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log hC,
    Real.exp_log hp]
  field_simp [Real.exp_ne_zero (1 : ℝ), hC.ne'] <;> ring

/-- Jensen's concavity step, for a closed domain and explicitly integrable
composition. This is a helper, NOT Proposition `hardyprofiles`: the latter
must derive these integrability hypotheses from a supporting affine bound. -/
theorem concave_integral_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : ℝ → ℝ} {s : Set ℝ}
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hs : IsClosed s)
    {X : Ω → ℝ} (hXs : ∀ᵐ ω ∂μ, X ω ∈ s)
    (hXi : Integrable X μ) (hgi : Integrable (fun ω => g (X ω)) μ) :
    (∫ ω, g (X ω) ∂μ) ≤ g (∫ ω, X ω ∂μ) :=
  hg.le_map_integral hgc hs hXs hXi hgi

end ScalarMonotone.EndOfPaper

end -- noncomputable section
