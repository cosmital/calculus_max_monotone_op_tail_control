import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
Extended nonnegative moment inequalities imply the
actual eLpNorm bound for every real r>0. The finite input
MemLp hypothesis yields MemLp of the output.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem eLpNorm_nonnegative_eq_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X) {r : ℝ} (hr : 0 < r) :
    eLpNorm X (ENNReal.ofReal r) μ = (∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ)^(r⁻¹) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le,one_div]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hX0] with ω hω
  change 0 ≤ X ω at hω
  rw [Real.enorm_eq_ofReal hω,ENNReal.ofReal_rpow_of_nonneg hω hr.le]

theorem eLpNorm_le_of_nonnegative_moment_bound {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hY0 : 0 ≤ᵐ[ν] Y)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hb : (∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ) ≤
      ENNReal.ofReal C*(∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂ν)) :
    eLpNorm X (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (C^(r⁻¹))*eLpNorm Y (ENNReal.ofReal r) ν := by
  rw [eLpNorm_nonnegative_eq_moment hX0 hr,eLpNorm_nonnegative_eq_moment hY0 hr]
  have hp := ENNReal.rpow_le_rpow hb (inv_nonneg.mpr hr.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le),
    ENNReal.ofReal_rpow_of_nonneg hC (inv_nonneg.mpr hr.le)] at hp
  exact hp

theorem memLp_of_nonnegative_moment_bound {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hXm : Measurable X)
    (hX0 : 0 ≤ᵐ[μ] X) (hY0 : 0 ≤ᵐ[ν] Y) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hb : (∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ) ≤
      ENNReal.ofReal C*(∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂ν))
    (hY : MemLp Y (ENNReal.ofReal r) ν) : MemLp X (ENNReal.ofReal r) μ := by
  refine ⟨hXm.aestronglyMeasurable,?_⟩
  exact (eLpNorm_le_of_nonnegative_moment_bound hX0 hY0 hr hC hb).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hY.eLpNorm_lt_top)

end ScalarMonotone.EndOfPaper
end
