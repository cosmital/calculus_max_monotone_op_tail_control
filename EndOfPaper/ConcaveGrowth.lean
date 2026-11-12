import EndOfPaper.Profiles
import Mathlib.Analysis.Convex.Slope

/-!
Supporting affine growth for monotone concave functions derives
absolute integrability of the composition before Jensen on a closed
half-line. These are genuine ingredients for the general Hardy-profile
bounds; their inverse/domain correspondences remain separately unfinished.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem concave_monotone_affine_bounds {g : ℝ → ℝ} {D : Set ℝ}
    (hg : ConcaveOn ℝ D g) (hm : MonotoneOn g D)
    {a x₀ : ℝ} (ha : a ∈ D) (hx : x₀ ∈ D) (hax : a < x₀)
    (htail : Ici x₀ ⊆ D) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ z ∈ Ici x₀,
      g x₀ ≤ g z ∧ g z ≤ g x₀+m*(z-x₀) := by
  let m : ℝ := (g x₀-g a)/(x₀-a)
  have hm0 : 0 ≤ m := div_nonneg (sub_nonneg.mpr (hm ha hx hax.le)) (sub_pos.mpr hax).le
  refine ⟨m, hm0, ?_⟩
  intro z hz
  refine ⟨hm hx (htail hz) hz, ?_⟩
  by_cases he : z = x₀
  · simp only [he, sub_self, mul_zero, add_zero, le_refl]
  · have hzx : x₀ < z := lt_of_le_of_ne hz (Ne.symm he)
    have hs := hg.slope_anti_adjacent ha (htail hz) hax hzx
    change (g z-g x₀)/(z-x₀) ≤ m at hs
    have hb := (div_le_iff₀ (sub_pos.mpr hzx)).mp hs
    linarith

theorem concave_monotone_comp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : ℝ → ℝ} {D : Set ℝ}
    (hg : ConcaveOn ℝ D g) (hm : MonotoneOn g D) (hc : ContinuousOn g D)
    {a x₀ : ℝ} (ha : a ∈ D) (hx : x₀ ∈ D) (hax : a < x₀)
    (htail : Ici x₀ ⊆ D) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, x₀ ≤ X ω) (hXi : Integrable X μ) :
    Integrable (fun ω => g (X ω)) μ := by
  obtain ⟨m, hm0, hb⟩ := concave_monotone_affine_bounds hg hm ha hx hax htail
  have hbound : Integrable (fun ω => |g x₀|+m*(X ω-x₀)) μ :=
    (integrable_const _).add ((hXi.sub (integrable_const _)).const_mul m)
  have hglob : Continuous (fun z => g (max z x₀)) :=
    hc.comp_continuous (continuous_id.max continuous_const) (fun z => htail (le_max_right z x₀))
  have he : (fun ω => g (max (X ω) x₀)) =ᵐ[μ] (fun ω => g (X ω)) :=
    hX.mono (fun ω hω => congrArg g (max_eq_left hω))
  have hgm : AEMeasurable (fun ω => g (X ω)) μ :=
    (hglob.measurable.comp_aemeasurable hXi.aemeasurable).congr he
  apply hbound.mono' hgm.aestronglyMeasurable
  filter_upwards [hX] with ω hω
  rw [Real.norm_eq_abs]
  have hbω := hb (X ω) hω
  have hmω : 0 ≤ m*(X ω-x₀) := mul_nonneg hm0 (sub_nonneg.mpr hω)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (g x₀)], by linarith [le_abs_self (g x₀)]⟩

/-- The composition's L1 premise is a conclusion. Jensen is applied on the
closed half-line above x₀, even when the original concavity domain is open. -/
theorem concave_monotone_jensen_derived_integrability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : ℝ → ℝ} {D : Set ℝ}
    (hg : ConcaveOn ℝ D g) (hm : MonotoneOn g D) (hc : ContinuousOn g D)
    {a x₀ : ℝ} (ha : a ∈ D) (hx : x₀ ∈ D) (hax : a < x₀)
    (htail : Ici x₀ ⊆ D) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, x₀ ≤ X ω) (hXi : Integrable X μ) :
    Integrable (fun ω => g (X ω)) μ ∧
      (∫ ω, g (X ω) ∂μ) ≤ g (∫ ω, X ω ∂μ) := by
  have hgi := concave_monotone_comp_integrable hg hm hc ha hx hax htail hX hXi
  exact ⟨hgi, (hg.subset htail (convex_Ici x₀)).le_map_integral
    (hc.mono htail) isClosed_Ici hX hXi hgi⟩

end ScalarMonotone.EndOfPaper
end
