import EndOfPaper.QuantileZero
import EndOfPaper.BoundedControlExtensions
import Mathlib.Probability.IdentDistrib

/-!
The original constant-profile constraints give the copy-distance bound after a genuine full-measure-set Lipschitz extension.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem ae_le_constant_of_quantile_mem {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {q : Operator} (hQ : DecLE (tailQuantile (Measure.map X μ)) q) {c : ℝ}
    (hc : ∀ p ∈ Ioo (0 : ℝ) 1, c ∈ q p) : ∀ᵐ ω ∂μ, X ω ≤ c := by
  have hReal : μ.real {ω | c < X ω} = 0 :=
    eq_zero_of_nonnegative_unit_interval_bounds measureReal_nonneg
      (fun p hp => quantile_comparison_strict_tail hX hQ (hc p hp))
  have hNull : μ {ω | c < X ω} = 0 := (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hReal
  exact ae_iff.mpr (by simpa only [not_le] using hNull)

theorem unit_profile_modulus_copy_bound {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (hident : IdentDistrib Z Z' μ μ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : ι → Operator}
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    (hq1 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → (1 : ℝ) ∈ q i p)
    {qΔ : Operator} (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    (hδ1 : ∀ p ∈ Ioo (0 : ℝ) 1, (1 : ℝ) ∈ qΔ p)
    {Φ : E → ℝ} (hmod : ∀ x y, |Φ x-Φ y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y))) :
    ∀ᵐ ω ∂μ, |Φ (Z ω)-Φ (Z' ω)| ≤ 1 := by
  classical
  let A : Set E := {x | ∀ i, Λ i x ≤ 1}
  have hAZ : ∀ᵐ ω ∂μ, Z ω ∈ A := ae_all_iff.mpr
    (fun i => ae_le_constant_of_quantile_mem ((hΛm i).comp hZ) (hQ i) (hq1 i))
  have hAZ' : ∀ᵐ ω ∂μ, Z' ω ∈ A := by
    apply ae_all_iff.mpr
    intro i
    have hQ' : DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z' ω)) μ)) (q i) := by
      have hLaw : Measure.map (fun ω => Λ i (Z ω)) μ =
          Measure.map (fun ω => Λ i (Z' ω)) μ := (hident.comp (hΛm i)).map_eq
      rw [← hLaw]
      exact hQ i
    exact ae_le_constant_of_quantile_mem ((hΛm i).comp hZ') hQ' (hq1 i)
  have hA : A.Nonempty := by
    obtain ⟨ω,hω⟩ := hAZ.exists
    exact ⟨Z ω,hω⟩
  have hLip : LipschitzOnWith 1 Φ A := by
    simpa only [one_pow] using randomized_modulus_lipschitz_on_bounded_controls
      hΛ0 hmod (M := 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hExt := upperLipschitzExtension_properties hA hLip
  let f := upperLipschitzExtension A Φ (1 : ℝ≥0)
  have hf : LipschitzWith 1 f := hExt.1
  have hEq : EqOn Φ f A := hExt.2.1
  have hfm : Measurable f := hf.continuous.measurable
  have hCopy := ae_le_constant_of_quantile_mem
    ((hfm.comp hZ).sub (hfm.comp hZ')).abs (hδ f hf) hδ1
  filter_upwards [hAZ,hAZ',hCopy] with ω hz hz' hω
  rw [hEq hz,hEq hz']
  exact hω

end ScalarMonotone.EndOfPaper
end
