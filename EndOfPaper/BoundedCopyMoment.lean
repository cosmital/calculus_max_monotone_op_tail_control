import EndOfPaper.EssentialDiameter
import EndOfPaper.UnitIntervalCopyMoment
import EndOfPaper.UnitProfileAdmissibility

/-!
The one-half moment bound on the original independent-copy space, with essential boundedness derived.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem law_copy_moment_le_half_of_gap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hgap : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), |z.1-z.2| ≤ 1) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(ν.prod ν)) ≤ ENNReal.ofReal (1/2 : ℝ) := by
  obtain ⟨c,hc⟩ := law_essential_interval_of_copy_gap ν hgap
  let shift : ℝ → ℝ := fun x => x-c
  have hm : Measurable shift := measurable_id.sub measurable_const
  let τ := Measure.map shift ν
  letI : IsProbabilityMeasure τ := isProbabilityMeasure_map hm.aemeasurable
  have hτ : ∀ᵐ x ∂τ, x ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hm.aemeasurable measurableSet_Icc).mpr
    filter_upwards [hc] with x hx
    change 0 ≤ x-c ∧ x-c ≤ 1
    constructor <;> linarith [hx.1,hx.2]
  have hb := unit_interval_product_moment_le_half τ hτ hr
  have hDiff : Continuous (fun z : ℝ × ℝ => z.1-z.2) := continuous_fst.sub continuous_snd
  have hF : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (|z.1-z.2|^r)) :=
    ((Real.continuous_rpow_const (zero_le_one.trans hr)).comp hDiff.abs).measurable.ennreal_ofReal
  have he : (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(τ.prod τ)) =
      ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(ν.prod ν) := by
    change (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(Measure.map shift ν).prod (Measure.map shift ν)) = _
    rw [Measure.map_prod_map ν ν hm hm,lintegral_map hF (hm.prodMap hm)]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (|(z.1-c)-(z.2-c)|^r) = _
    rw [show (z.1-c)-(z.2-c) = z.1-z.2 by ring]
  rwa [he] at hb

theorem independent_copy_moment_le_half_of_gap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    (hgap : ∀ᵐ ω ∂μ, |X ω-X' ω| ≤ 1) {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (|X ω-X' ω|^r) ∂μ) ≤ ENNReal.ofReal (1/2 : ℝ) := by
  let ν := Measure.map X μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hPair := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hX'.aemeasurable).mp hi
  rw [← he.map_eq] at hPair
  have hDiff : Continuous (fun z : ℝ × ℝ => z.1-z.2) := continuous_fst.sub continuous_snd
  have hAbs : Measurable (fun z : ℝ × ℝ => |z.1-z.2|) := hDiff.abs.measurable
  have hNull : μ {ω | 1 < |X ω-X' ω|} = 0 := by simpa only [not_le] using ae_iff.mp hgap
  have hNullProd : (ν.prod ν) {z : ℝ × ℝ | 1 < |z.1-z.2|} = 0 := by
    rw [← hPair,Measure.map_apply (hX.prodMk hX') (measurableSet_lt measurable_const hAbs)]
    exact hNull
  have hGapProd : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), |z.1-z.2| ≤ 1 := by
    apply ae_iff.mpr
    simpa only [not_le] using hNullProd
  have hb := law_copy_moment_le_half_of_gap ν hGapProd hr
  have hF : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (|z.1-z.2|^r)) :=
    ((Real.continuous_rpow_const (zero_le_one.trans hr)).comp hDiff.abs).measurable.ennreal_ofReal
  have hInt : (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(ν.prod ν)) =
      ∫⁻ ω, ENNReal.ofReal (|X ω-X' ω|^r) ∂μ := by
    rw [← hPair]
    exact lintegral_map hF (hX.prodMk hX')
  rwa [hInt] at hb

end ScalarMonotone.EndOfPaper
end
