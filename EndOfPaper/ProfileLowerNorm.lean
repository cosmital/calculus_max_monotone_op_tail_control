import EndOfPaper.NonnegativeMomentNorm

/-!
An extended lower moment gives the actual Lr lower bound, including infinity.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem eLpNorm_ge_of_nonnegative_moment_bound {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hY0 : 0 ≤ᵐ[ν] Y)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hb : ENNReal.ofReal C*(∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂ν) ≤
      ∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ) :
    ENNReal.ofReal (C^(r⁻¹))*eLpNorm Y (ENNReal.ofReal r) ν ≤
      eLpNorm X (ENNReal.ofReal r) μ := by
  rw [eLpNorm_nonnegative_eq_moment hX0 hr,eLpNorm_nonnegative_eq_moment hY0 hr]
  have hp := ENNReal.rpow_le_rpow hb (inv_nonneg.mpr hr.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le),
    ENNReal.ofReal_rpow_of_nonneg hC (inv_nonneg.mpr hr.le)] at hp
  exact hp

end ScalarMonotone.EndOfPaper
end
