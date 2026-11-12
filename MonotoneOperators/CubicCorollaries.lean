import MonotoneOperators.CubicNested
import MonotoneOperators.Monomial

/-!
# The manuscript's cubic formulas in literal form

The nested probability bound and the three-term parallel identity are exposed
in one theorem. The monomial constituents are the positively completed root
composites identified by `monomialProfile_mem_iff`, with their zero fibers
verified in `Monomial`.
-/

open Set MeasureTheory ProbabilityTheory

namespace ScalarMonotone

/-- The full displayed cubic comparison and parallel identity, with coefficient
one and no independence assumption. -/
theorem cubic_parallel_transformation {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hmX : Measurable X)
    {α : Operator} (hα : MaximalDecreasing α) (hdom : dom α = Ici 0)
    (hbound : ∀ t > 0, α t ⊆ Icc 0 1)
    (hX : DecLE (survival (Measure.map X ν)) α)
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    DecLE (survival (Measure.map
      (fun ω => X ω * (σ₀ + X ω * (σ₁ + σ₂ * X ω))) ν))
      (parallelMul α (parallelAdd (positiveConstantProfile σ₀)
        (parallelMul α (parallelAdd (positiveConstantProfile σ₁) (inputDivide σ₂ α))))) ∧
      parallelMul α (parallelAdd (positiveConstantProfile σ₀)
        (parallelMul α (parallelAdd (positiveConstantProfile σ₁) (inputDivide σ₂ α)))) =
        parallelAdd (parallelAdd (inputDivide σ₀ α) (monomialProfile α σ₁ 2))
          (monomialProfile α σ₂ 3) := by
  constructor
  · simpa only [cubicPolynomial_nested, nestedCubicProfile] using
      survival_nested_cubic_comparison ν hmX hα hdom hbound hX hX₀ h₀ h₁ h₂
  · have h := nestedCubicProfile_eq_parallel_monomials hα hdom hbound h₀ h₁ h₂
    rw [monomialProfile_one h₀.ne'] at h
    exact h

/-- Maximality of the nested expression and all three completed root profiles.
The qualifications follow from the original positive-profile hypotheses. -/
theorem cubic_parallel_terms_maximal {α : Operator}
    (hα : MaximalDecreasing α) (hdom : dom α = Ici 0)
    (hbound : ∀ t > 0, α t ⊆ Icc 0 1) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    MaximalDecreasing (parallelMul α (parallelAdd (positiveConstantProfile σ₀)
      (parallelMul α (parallelAdd (positiveConstantProfile σ₁) (inputDivide σ₂ α))))) ∧
      MaximalDecreasing (inputDivide σ₀ α) ∧
      MaximalDecreasing (monomialProfile α σ₁ 2) ∧
      MaximalDecreasing (monomialProfile α σ₂ 3) := by
  have hα₀ : dom α ⊆ Ici 0 := by rw [hdom]
  refine ⟨nestedCubicProfile_maximal hα hdom hbound h₀ h₁ h₂, ?_,
    monomialProfile_maximal hα hα₀ h₁ (by norm_num),
    monomialProfile_maximal hα hα₀ h₂ (by norm_num)⟩
  rw [← monomialProfile_one h₀.ne']
  exact monomialProfile_maximal hα hα₀ h₀ (by norm_num)

/-- The explicit exponents and constants in the manuscript's multilevel bound.
The upper endpoint is included, so the conclusion also covers atoms. -/
theorem cubic_multilevel_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hmX : Measurable X)
    {α : Operator} (hX : DecLE (survival (Measure.map X ν)) α)
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω)
    (hgauss : ∀ r > 0, α r = {Real.exp (-(r ^ 2))})
    {t σ₀ σ₁ σ₂ u : ℝ} (ht : 0 < t)
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂)
    (hu : u ∈ survival (Measure.map
      (fun ω => X ω * (σ₀ + X ω * (σ₁ + σ₂ * X ω))) ν) t) :
    u ≤ Real.exp (-min (t ^ 2 / (9 * σ₀ ^ 2))
      (min (t / (3 * σ₁)) ((t / (3 * σ₂)) ^ (2 / 3 : ℝ)))) := by
  have hgaussmem : ∀ r > 0, Real.exp (-(r ^ 2)) ∈ α r := by
    intro r hr
    rw [hgauss r hr]
    rfl
  have hu' : u ∈ survival
      (Measure.map (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω)) ν) t := by
    simpa only [cubicPolynomial_nested] using hu
  exact cubic_gaussian_survival_bound_of_comparison ν hmX hX hX₀ hgaussmem
    ht h₀ h₁ h₂ hu'

end ScalarMonotone
