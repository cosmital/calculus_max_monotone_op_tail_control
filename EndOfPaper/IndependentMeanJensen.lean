import EndOfPaper.NonnegativeMomentNorm
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.IdentDistrib

/-!
Actual Jensen and product-law comparison of
mean-centered and independent-copy moments on the original
probability space. Product integrability is derived.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem integral_sub_mean_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {r : ℝ}
    (hr : 1 ≤ r) (hX : MemLp X (ENNReal.ofReal r) μ) (c : ℝ) :
    |c-∫ ω, X ω ∂μ|^r ≤ ∫ ω, |c-X ω|^r ∂μ := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hp : 1 ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  have hXi : Integrable X μ := hX.integrable hp
  have hD : MemLp (fun ω => c-X ω) (ENNReal.ofReal r) μ := (memLp_const c).sub hX
  have hDi : Integrable (fun ω => c-X ω) μ := hD.integrable hp
  have hAbs : Integrable (fun ω => |c-X ω|) μ := by
    simpa only [Real.norm_eq_abs] using hDi.norm
  have hPow : Integrable (fun ω => |c-X ω|^r) μ := by
    simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hr0] using hD.integrable_norm_rpow'
  have he : (∫ ω, c-X ω ∂μ) = c-∫ ω, X ω ∂μ := by
    rw [integral_sub (integrable_const c) hXi]
    simp
  have hn : |c-∫ ω, X ω ∂μ| ≤ ∫ ω, |c-X ω| ∂μ := by
    simpa only [he,Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun ω => c-X ω)
  have hJ := ConvexOn.map_integral_le (μ := μ) (convexOn_rpow hr)
    (Real.continuous_rpow_const hr0).continuousOn isClosed_Ici
    (Eventually.of_forall (fun ω => (abs_nonneg (c-X ω) : |c-X ω| ∈ Ici (0 : ℝ)))) hAbs hPow
  exact (Real.rpow_le_rpow (abs_nonneg _) hn hr0).trans hJ

theorem law_mean_centered_moment_le_product (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 ≤ r) (hX : MemLp id (ENNReal.ofReal r) ν)
    (hJoint : Integrable (fun z : ℝ × ℝ => |z.1-z.2|^r) (ν.prod ν)) :
    (∫ v : ℝ, |v-∫ w : ℝ, w ∂ν|^r ∂ν) ≤ ∫ z : ℝ × ℝ, |z.1-z.2|^r ∂(ν.prod ν) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hC : MemLp (fun v : ℝ => v-∫ w : ℝ, w ∂ν) (ENNReal.ofReal r) ν :=
    hX.sub (memLp_const _)
  have hCi : Integrable (fun v : ℝ => |v-∫ w : ℝ, w ∂ν|^r) ν := by
    simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hr0] using hC.integrable_norm_rpow'
  rw [integral_prod _ hJoint]
  apply integral_mono hCi hJoint.integral_prod_left
  intro v
  exact integral_sub_mean_rpow_le hr hX v

theorem independent_copy_mean_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    {r : ℝ} (hr : 1 ≤ r) (hMem : MemLp X (ENNReal.ofReal r) μ)
    (hGap : MemLp (fun ω => |X ω-X' ω|) (ENNReal.ofReal r) μ) :
    (∫ ω, |X ω-∫ ω', X ω' ∂μ|^r ∂μ) ≤ ∫ ω, |X ω-X' ω|^r ∂μ := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  let ν := Measure.map X μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hId : MemLp id (ENNReal.ofReal r) ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hX.aemeasurable).mpr hMem
  have hPair := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hX'.aemeasurable).mp hi
  rw [← he.map_eq] at hPair
  have hDiffc : Continuous (fun z : ℝ × ℝ => z.1-z.2) := continuous_fst.sub continuous_snd
  have hFm : Measurable (fun z : ℝ × ℝ => |z.1-z.2|^r) :=
    ((Real.continuous_rpow_const hr0).comp hDiffc.abs).measurable
  have hGapI : Integrable (fun ω => |X ω-X' ω|^r) μ := by
    simpa only [Real.norm_eq_abs,abs_abs,ENNReal.toReal_ofReal hr0] using hGap.integrable_norm_rpow'
  have hJointMap : Integrable (fun z : ℝ × ℝ => |z.1-z.2|^r)
      (Measure.map (fun ω => (X ω,X' ω)) μ) :=
    (integrable_map_measure hFm.aestronglyMeasurable (hX.prodMk hX').aemeasurable).mpr hGapI
  have hJoint : Integrable (fun z : ℝ × ℝ => |z.1-z.2|^r) (ν.prod ν) := by
    rwa [hPair] at hJointMap
  have hb := law_mean_centered_moment_le_product ν hr hId hJoint
  have hMean : (∫ v : ℝ, v ∂ν) = ∫ ω, X ω ∂μ :=
    integral_map hX.aemeasurable measurable_id.aestronglyMeasurable
  have hSubc : Continuous (fun v : ℝ => v-∫ w : ℝ, w ∂ν) := continuous_id.sub continuous_const
  have hLm : Measurable (fun v : ℝ => |v-∫ w : ℝ, w ∂ν|^r) :=
    ((Real.continuous_rpow_const hr0).comp hSubc.abs).measurable
  have hLeft : (∫ v : ℝ, |v-∫ w : ℝ, w ∂ν|^r ∂ν) = ∫ ω, |X ω-∫ ω', X ω' ∂μ|^r ∂μ := by
    rw [show (∫ v : ℝ, |v-∫ w : ℝ, w ∂ν|^r ∂ν) =
      ∫ ω, |X ω-∫ w : ℝ, w ∂ν|^r ∂μ from integral_map hX.aemeasurable hLm.aestronglyMeasurable]
    rw [hMean]
  have hRight : (∫ z : ℝ × ℝ, |z.1-z.2|^r ∂(ν.prod ν)) = ∫ ω, |X ω-X' ω|^r ∂μ := by
    rw [← hPair]
    exact integral_map (hX.prodMk hX').aemeasurable hFm.aestronglyMeasurable
  rwa [hLeft,hRight] at hb

theorem independent_copy_mean_norm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    {r : ℝ} (hr : 1 ≤ r) (hMem : MemLp X (ENNReal.ofReal r) μ)
    (hGap : MemLp (fun ω => |X ω-X' ω|) (ENNReal.ofReal r) μ) :
    MemLp (fun ω => X ω-∫ ω', X ω' ∂μ) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => X ω-∫ ω', X ω' ∂μ) (ENNReal.ofReal r) μ ≤
        eLpNorm (fun ω => |X ω-X' ω|) (ENNReal.ofReal r) μ := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hC : MemLp (fun ω => X ω-∫ ω', X ω' ∂μ) (ENNReal.ofReal r) μ := hMem.sub (memLp_const _)
  refine ⟨hC,?_⟩
  have hb := independent_copy_mean_moment hX hX' hi he hr hMem hGap
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hr0)) ENNReal.ofReal_ne_top hC,
    MemLp.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hr0)) ENNReal.ofReal_ne_top hGap]
  simp only [ENNReal.toReal_ofReal hr0.le,Real.norm_eq_abs,abs_abs]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow _ hb (inv_nonneg.mpr hr0.le)
  exact integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)

end ScalarMonotone.EndOfPaper
end
