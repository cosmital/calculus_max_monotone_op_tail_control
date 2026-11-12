import MonotoneOperators.Completion
import MonotoneOperators.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Aumann integration of bounded interval fibers

These are the finite-interior-fiber statements from Definition `familyintegral`
and Theorem `familyintegral`. The exactness of the fibers AFTER maximal
completion is proved in `EndOfPaper.FamilyIntegral`, using actual finite interior
endpoints of maximal graphs. Endpoint measurability is part of that construction's
integrability hypotheses. See END_COVERAGE.md for remaining paper claims.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- The Aumann integral uses integrable selections on the original measure space. -/
def aumannIntegral {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (h : Θ → Set ℝ) : Set ℝ :=
  {v | ∃ s : Θ → ℝ, Integrable s μ ∧
    (∀ᵐ θ ∂μ, s θ ∈ h θ) ∧ v = ∫ θ, s θ ∂μ}

/-- Changing a multifunction on a null set leaves its Aumann integral unchanged. -/
theorem aumannIntegral_congr_ae {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {h k : Θ → Set ℝ} (hhk : h =ᵐ[μ] k) :
    aumannIntegral μ h = aumannIntegral μ k := by
  ext v
  constructor
  · rintro ⟨s, hs, hsel, hv⟩
    refine ⟨s, hs, ?_, hv⟩
    filter_upwards [hsel, hhk] with θ hθ heq
    rwa [← heq]
  · rintro ⟨s, hs, hsel, hv⟩
    refine ⟨s, hs, ?_, hv⟩
    filter_upwards [hsel, hhk] with θ hθ heq
    rwa [heq]

/-- Integrals of integrable almost-everywhere selections of an interval family. -/
def aumannInterval {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (l u : Θ → ℝ) : Set ℝ :=
  {v | ∃ s : Θ → ℝ, Integrable s μ ∧
    (∀ᵐ θ ∂μ, s θ ∈ Icc (l θ) (u θ)) ∧ v = ∫ θ, s θ ∂μ}

theorem aumannIntegral_interval {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (l u : Θ → ℝ) :
    aumannIntegral μ (fun θ => Icc (l θ) (u θ)) = aumannInterval μ l u := rfl

/-- Convex interpolation realizes every number between the two integrals. -/
theorem aumannInterval_eq {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {l u : Θ → ℝ}
    (hl : Integrable l μ) (hu : Integrable u μ) (hlu : l ≤ᵐ[μ] u) :
    aumannInterval μ l u = Icc (∫ θ, l θ ∂μ) (∫ θ, u θ ∂μ) := by
  ext v
  constructor
  · rintro ⟨s, hs, hsel, rfl⟩
    exact ⟨integral_mono_ae hl hs (hsel.mono fun θ h => h.1),
      integral_mono_ae hs hu (hsel.mono fun θ h => h.2)⟩
  · intro hv
    let L := ∫ θ, l θ ∂μ
    let U := ∫ θ, u θ ∂μ
    have hLU : L ≤ U := integral_mono_ae hl hu hlu
    rcases eq_or_lt_of_le hLU with heq | hlt
    · have hvL : v = L := by change L ≤ v ∧ v ≤ U at hv; linarith
      refine ⟨l, hl, ?_, hvL⟩
      filter_upwards [hlu] with θ hθ
      exact ⟨le_rfl, hθ⟩
    · let c : ℝ := (v-L)/(U-L)
      have hden : 0 < U-L := sub_pos.mpr hlt
      have hc0 : 0 ≤ c := div_nonneg (sub_nonneg.mpr hv.1) hden.le
      have hc1 : c ≤ 1 := (div_le_one hden).mpr (sub_le_sub_right hv.2 L)
      let s : Θ → ℝ := fun θ => (1-c)*l θ+c*u θ
      have hs : Integrable s μ := (hl.const_mul (1-c)).add (hu.const_mul c)
      refine ⟨s, hs, ?_, ?_⟩
      · filter_upwards [hlu] with θ hθ
        dsimp [s]
        constructor <;> nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hθ),
          mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hθ)]
      · change v = ∫ θ, (1-c)*l θ+c*u θ ∂μ
        rw [integral_add (hl.const_mul _) (hu.const_mul _),
          integral_const_mul, integral_const_mul]
        change v = (1-c)*L+c*U
        dsimp [c]
        field_simp [ne_of_gt hden] <;> ring

/-- Endpoint comparison implies interval-integral comparison. -/
theorem aumannInterval_mono {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {l₁ u₁ l₂ u₂ : Θ → ℝ}
    (hl₁ : Integrable l₁ μ) (hu₁ : Integrable u₁ μ)
    (hl₂ : Integrable l₂ μ) (hu₂ : Integrable u₂ μ)
    (h₁ : l₁ ≤ᵐ[μ] u₁) (h₂ : l₂ ≤ᵐ[μ] u₂)
    (hl : l₁ ≤ᵐ[μ] l₂) (hu : u₁ ≤ᵐ[μ] u₂) :
    (∫ θ, l₁ θ ∂μ) ≤ (∫ θ, l₂ θ ∂μ) ∧
    (∫ θ, u₁ θ ∂μ) ≤ (∫ θ, u₂ θ ∂μ) :=
  ⟨integral_mono_ae hl₁ hl₂ hl, integral_mono_ae hu₁ hu₂ hu⟩

/-- Additivity of the two endpoints. -/
theorem integrated_endpoints_add {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {l₁ u₁ l₂ u₂ : Θ → ℝ}
    (hl₁ : Integrable l₁ μ) (hu₁ : Integrable u₁ μ)
    (hl₂ : Integrable l₂ μ) (hu₂ : Integrable u₂ μ) :
    (∫ θ, l₁ θ+l₂ θ ∂μ) = (∫ θ, l₁ θ ∂μ)+(∫ θ, l₂ θ ∂μ) ∧
    (∫ θ, u₁ θ+u₂ θ ∂μ) = (∫ θ, u₁ θ ∂μ)+(∫ θ, u₂ θ ∂μ) :=
  ⟨integral_add hl₁ hl₂, integral_add hu₁ hu₂⟩

/-- Homogeneity of the endpoint integral, for every real scalar. -/
theorem integrated_endpoints_scale {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (l u : Θ → ℝ) (c : ℝ) :
    (∫ θ, c*l θ ∂μ) = c*(∫ θ, l θ ∂μ) ∧
    (∫ θ, c*u θ ∂μ) = c*(∫ θ, u θ ∂μ) :=
  ⟨integral_const_mul _ _, integral_const_mul _ _⟩

/-- The interior graph BEFORE its boundary/jump completion. -/
def integratedFiberGraph {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) (l u : Θ → ℝ → ℝ) : Operator := by
  classical
  exact fun x => if x ∈ I then Icc (∫ θ, l θ x ∂μ) (∫ θ, u θ x ∂μ) else ∅

/-- The proposed interior graph has exactly the common interior as domain. -/
theorem integratedFiberGraph_dom {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) (l u : Θ → ℝ → ℝ)
    (hl : ∀ x ∈ I, Integrable (fun θ => l θ x) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => u θ x) μ)
    (hlu : ∀ x ∈ I, ∀ᵐ θ ∂μ, l θ x ≤ u θ x) :
    dom (integratedFiberGraph μ I l u) = I := by
  ext x
  by_cases hx : x ∈ I
  · have hle := integral_mono_ae (hl x hx) (hu x hx) (hlu x hx)
    simp only [dom, integratedFiberGraph, hx, if_pos, mem_setOf_eq, iff_true]
    exact ⟨∫ θ, l θ x ∂μ, le_rfl, hle⟩
  · simp [dom, integratedFiberGraph, hx]

/-- Monotonicity of the interior graph follows by integrating separated fibers. -/
theorem integratedFiberGraph_increasing {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) (l u : Θ → ℝ → ℝ)
    (hl : ∀ x ∈ I, Integrable (fun θ => l θ x) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => u θ x) μ)
    (hsep : ∀ x ∈ I, ∀ y ∈ I, x < y → ∀ᵐ θ ∂μ, u θ x ≤ l θ y) :
    Increasing (integratedFiberGraph μ I l u) := by
  apply increasing_iff_order.mpr
  intro x a y b ha hb hxy
  have hx : x ∈ I := by
    by_contra hx
    simpa [integratedFiberGraph, hx] using ha
  have hy : y ∈ I := by
    by_contra hy
    simpa [integratedFiberGraph, hy] using hb
  have ha' : a ∈ Icc (∫ θ, l θ x ∂μ) (∫ θ, u θ x ∂μ) := by
    simpa [integratedFiberGraph, hx] using ha
  have hb' : b ∈ Icc (∫ θ, l θ y ∂μ) (∫ θ, u θ y ∂μ) := by
    simpa [integratedFiberGraph, hy] using hb
  exact ha'.2.trans ((integral_mono_ae (hu x hx) (hl y hy)
    (hsep x hx y hy hxy)).trans hb'.1)

/-- A maximal completion exists. This theorem deliberately does NOT assert
that completion leaves every interior fiber unchanged for arbitrary endpoint data.
`FamilyIntegral` proves this stronger conclusion for endpoints of maximal families,
using the manuscript's one-sided dominated-convergence argument. -/
theorem integratedFiberGraph_has_maximal_completion {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) (l u : Θ → ℝ → ℝ)
    (hI : I.OrdConnected) (hne : I.Nonempty)
    (hl : ∀ x ∈ I, Integrable (fun θ => l θ x) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => u θ x) μ)
    (hlu : ∀ x ∈ I, ∀ᵐ θ ∂μ, l θ x ≤ u θ x)
    (hsep : ∀ x ∈ I, ∀ y ∈ I, x < y → ∀ᵐ θ ∂μ, u θ x ≤ l θ y) :
    MaximalIncreasing (completion I (integratedFiberGraph μ I l u)) :=
  completion_maximal hI hne
    (integratedFiberGraph_increasing μ I l u hl hu hsep)
    (integratedFiberGraph_dom μ I l u hl hu hlu)

end ScalarMonotone.EndOfPaper

end -- noncomputable section
