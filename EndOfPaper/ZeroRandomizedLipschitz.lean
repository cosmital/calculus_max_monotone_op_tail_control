import EndOfPaper.QuantileZero
import EndOfPaper.ZeroControlTail
import EndOfPaper.BoundedControlExtensions

/-!
Both original zero-input cases of randomized Lipschitz
control, including a globally zero baseline profile without
control moments or separability assumptions.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem zero_profile_mem {q : Operator} (hdom : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hz : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, v = 0) :
    ∀ p ∈ Ioo (0 : ℝ) 1, (0 : ℝ) ∈ q p := by
  intro p hp
  obtain ⟨v,hv⟩ := hdom hp
  simpa only [hz p hp v hv] using hv

theorem randomized_zero_baseline_difference {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') {q : Operator}
    (hcontrol : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    (hdom : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hz : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, v = 0)
    {h : E → ℝ} {Λ : ι → E → ℝ} (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y))) :
    (fun ω => h (Z ω)) =ᵐ[μ] (fun ω => h (Z' ω)) := by
  apply ae_difference_zero_of_bounded_control_extensions hΛ0 hmod
  intro K hK f hf
  exact lipschitz_difference_zero_of_quantile_zero hZ hZ' hcontrol
    (zero_profile_mem hdom hz) hK hf

theorem randomized_zero_marginal_difference {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (hident : IdentDistrib Z Z' μ μ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {h : E → ℝ} (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (i : ι) {q : Operator} (hQ : DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) q)
    (hdom : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hz : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, v = 0) :
    (fun ω => h (Z ω)) =ᵐ[μ] (fun ω => h (Z' ω)) := by
  have hQ' : DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z' ω)) μ)) q := by
    have heLaw : Measure.map (fun ω => Λ i (Z ω)) μ = Measure.map (fun ω => Λ i (Z' ω)) μ :=
      (hident.comp (hΛm i)).map_eq
    rw [← heLaw]
    exact hQ
  have hX := ae_nonpositive_of_quantile_zero ((hΛm i).comp hZ) hQ (zero_profile_mem hdom hz)
  have hX' := ae_nonpositive_of_quantile_zero ((hΛm i).comp hZ') hQ' (zero_profile_mem hdom hz)
  filter_upwards [hX,hX'] with ω hω hω'
  exact randomized_control_zero_difference hmod i
    (le_antisymm hω (hΛ0 i (Z ω))) (le_antisymm hω' (hΛ0 i (Z' ω)))

theorem randomized_lipschitz_zero_input {ι Ω E F : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (hident : IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    (hδdom : Ioo (0 : ℝ) 1 ⊆ dom qΔ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : ι → Operator} (hqdom : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (q i))
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    {Φ : E → F} (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (hz : (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q i p, v = 0)
    {g : F → ℝ} (hg : LipschitzWith 1 g) :
    (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) =ᵐ[μ] (fun _ => 0) := by
  have hscalar : ∀ x y, |g (Φ x)-g (Φ y)| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)) := by
    intro x y
    exact (show |g (Φ x)-g (Φ y)| ≤ dist (Φ x) (Φ y) from by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hg.dist_le_mul (Φ x) (Φ y)).trans (hmod x y)
  have he : (fun ω => g (Φ (Z ω))) =ᵐ[μ] (fun ω => g (Φ (Z' ω))) := by
    rcases hz with hδz | ⟨i,hiz⟩
    · exact randomized_zero_baseline_difference hZ hZ' hδ hδdom hδz hΛ0 hscalar
    · exact randomized_zero_marginal_difference hZ hZ' hident hΛm hΛ0 hscalar i (hQ i) (hqdom i) hiz
  filter_upwards [he] with ω hω
  simp only [hω,sub_self,abs_zero]

end ScalarMonotone.EndOfPaper
end
