import EndOfPaper.UnitProfileOptimality

/-!
Every larger coefficient is impossible for the prescribed unit profiles and arbitrary original admissible models.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem unit_profile_no_larger_coefficient {n : ℕ} (hn : 0 < n)
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) unitQuantileProfile.val)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) unitQuantileProfile.val)
    {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {r C : ℝ} (hr : 1 ≤ r) (hC : (2 : ℝ)^(-1/r) < C) :
    ¬ ENNReal.ofReal C ≤ eLpNorm (fun ω => Φ (Z ω)-Φ (Z' ω)) (ENNReal.ofReal r) μ := by
  have h := unit_profile_moment_optimality hn hZ hZ' hi he hΛm hΛ0 hQ hδ hΦ hmod hr
  intro hLarge
  have hLe : C ≤ (2 : ℝ)^(-1/r) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)).mp
      (hLarge.trans h.1.2)
  exact (not_le_of_gt hC) hLe

end ScalarMonotone.EndOfPaper
end
