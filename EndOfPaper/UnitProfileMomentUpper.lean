import EndOfPaper.BoundedCopyMoment
import EndOfPaper.NonnegativeMomentNorm

/-!
The original constant-profile admissibility conditions imply the sharp one-half moment and 2^(-1/r) norm bounds for every r>=1.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem unit_profile_universal_moment_upper {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : ι → Operator}
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    (hq1 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → (1 : ℝ) ∈ q i p)
    {qΔ : Operator} (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    (hδ1 : ∀ p ∈ Ioo (0 : ℝ) 1, (1 : ℝ) ∈ qΔ p)
    {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hmod : ∀ x y, |Φ x-Φ y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (|Φ (Z ω)-Φ (Z' ω)|^r) ∂μ) ≤ ENNReal.ofReal (1/2 : ℝ) ∧
      eLpNorm (fun ω => Φ (Z ω)-Φ (Z' ω)) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal ((2 : ℝ)^(-1/r)) := by
  have hGap := unit_profile_modulus_copy_bound hZ hZ' he hΛm hΛ0 hQ hq1 hδ hδ1 hmod
  have hMoment := independent_copy_moment_le_half_of_gap (hΦ.comp hZ) (hΦ.comp hZ')
    (hi.comp hΦ hΦ) (he.comp hΦ) hGap hr
  refine ⟨hMoment,?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hAbs : eLpNorm (fun ω => Φ (Z ω)-Φ (Z' ω)) (ENNReal.ofReal r) μ =
      eLpNorm (fun ω => |Φ (Z ω)-Φ (Z' ω)|) (ENNReal.ofReal r) μ := by
    simpa only [Real.norm_eq_abs] using (eLpNorm_norm (p := ENNReal.ofReal r) (μ := μ)
      (fun ω => Φ (Z ω)-Φ (Z' ω))).symm
  have hNN : 0 ≤ᵐ[μ] (fun ω => |Φ (Z ω)-Φ (Z' ω)|) :=
    Eventually.of_forall (fun ω => abs_nonneg _)
  rw [hAbs,eLpNorm_nonnegative_eq_moment hNN hr0]
  have hb := ENNReal.rpow_le_rpow hMoment (inv_nonneg.mpr hr0.le)
  rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (inv_nonneg.mpr hr0.le)] at hb
  have hC : (1/2 : ℝ)^(r⁻¹) = (2 : ℝ)^(-1/r) := by
    rw [one_div,Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa only [hC] using hb

end ScalarMonotone.EndOfPaper
end
