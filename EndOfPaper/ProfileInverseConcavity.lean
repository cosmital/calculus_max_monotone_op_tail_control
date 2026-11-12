import EndOfPaper.ConcaveGrowth
import EndOfPaper.CompletedProfiles
import Mathlib.Analysis.Convex.Continuous

/-!
Restricted inverse concavity and monotonicity derived from a strictly
increasing convex forward transform; composition integrability before
Jensen, and the exact inverse of input dilation on the whole graph.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem monotoneOn_of_strictMonoOn_right_inverse {D U : Set ℝ} {φ ψ : ℝ → ℝ}
    (hφ : StrictMonoOn φ D) (hψ : MapsTo ψ U D)
    (hinv : ∀ y ∈ U, φ (ψ y) = y) : MonotoneOn ψ U := by
  intro x hx y hy hxy
  apply (hφ.le_iff_le (hψ hx) (hψ hy)).mp
  simpa only [hinv x hx, hinv y hy] using hxy

theorem concaveOn_of_convexOn_right_inverse {D U : Set ℝ} {φ ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ D φ) (hm : StrictMonoOn φ D) (hU : Convex ℝ U)
    (hψ : MapsTo ψ U D) (hinv : ∀ y ∈ U, φ (ψ y) = y) :
    ConcaveOn ℝ U ψ := by
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • ψ x+b • ψ y ∈ D := hc.1 (hψ hx) (hψ hy) ha hb hab
  have hz : a • x+b • y ∈ U := hU hx hy ha hb hab
  apply (hm.le_iff_le hxy (hψ hz)).mp
  calc
    φ (a • ψ x+b • ψ y) ≤ a • φ (ψ x)+b • φ (ψ y) := hc.2 (hψ hx) (hψ hy) ha hb hab
    _ = φ (ψ (a • x+b • y)) := by rw [hinv x hx, hinv y hy, hinv _ hz]

/-- Concavity and the supporting affine bound are derived from convexity of
the forward transform; neither composition L1 nor concavity is a premise. -/
theorem convex_inverse_jensen_derived_integrability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D U : Set ℝ} {φ ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ D φ) (hm : StrictMonoOn φ D) (hU : Convex ℝ U) (ho : IsOpen U)
    (hψ : MapsTo ψ U D) (hinv : ∀ y ∈ U, φ (ψ y) = y)
    {a x₀ : ℝ} (ha : a ∈ U) (hx : x₀ ∈ U) (hax : a < x₀)
    (htail : Ici x₀ ⊆ U) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, x₀ ≤ X ω) (hXi : Integrable X μ) :
    Integrable (fun ω => ψ (X ω)) μ ∧
      (∫ ω, ψ (X ω) ∂μ) ≤ ψ (∫ ω, X ω ∂μ) := by
  have hconc := concaveOn_of_convexOn_right_inverse hc hm hU hψ hinv
  exact concave_monotone_jensen_derived_integrability hconc
    (monotoneOn_of_strictMonoOn_right_inverse hm hψ hinv)
    (hconc.continuousOn ho) ha hx hax htail hX hXi

theorem inverse_positiveInputDilation {c : ℝ} (hc : c ≠ 0) (f : Operator) :
    inverse (positiveInputDilation c f) = outputScale c⁻¹ (inverse f) := by
  ext y x
  constructor
  · intro hx
    exact ⟨c*x, hx, by simp [hc]⟩
  · rintro ⟨z, hz, rfl⟩
    change y ∈ f (c*(c⁻¹*z))
    simpa [hc] using hz

end ScalarMonotone.EndOfPaper
end
