import EndOfPaper.ShortfallMinimizers
import Mathlib.Analysis.Convex.Deriv
import EndOfPaper.Shortfall
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The full original-space shortfall calculus, including atoms: convexity,
left/weak and right/strict tail derivatives, the ordinary convex
subdifferential as the affine survival interval, and its exact quantile
zero condition. Difference quotients are uniformly dominated by one.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def excessSlope (x a b : ℝ) : ℝ := (max (x-b) 0-max (x-a) 0)/(b-a)

theorem excessSlope_abs_le_one (x a b : ℝ) : |excessSlope x a b| ≤ 1 := by
  by_cases hba : b-a = 0
  · simp [excessSlope, hba]
  · rw [excessSlope, abs_div, div_le_one (abs_pos.mpr hba)]
    have h := abs_max_sub_max_le_abs (x-b) (x-a) 0
    have he : (x-b)-(x-a) = -(b-a) := by ring
    simpa only [he, abs_neg] using h

theorem excessSlope_tendsto_right (x a : ℝ) :
    Tendsto (fun b => excessSlope x a b) (𝓝[>] a)
      (𝓝 (if a < x then (-1 : ℝ) else 0)) := by
  by_cases hax : a < x
  · rw [if_pos hax]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hax)] with b hab hbx
    change a < b at hab
    change b < x at hbx
    rw [excessSlope, max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp [sub_ne_zero.mpr (ne_of_gt hab)] <;> ring
  · rw [if_neg hax]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with b hab
    change a < b at hab
    have hxa := le_of_not_gt hax
    simp [excessSlope, max_eq_right (by linarith : x-b ≤ 0), max_eq_right (by linarith : x-a ≤ 0)]

theorem excessSlope_tendsto_left (x a : ℝ) :
    Tendsto (fun b => excessSlope x a b) (𝓝[<] a)
      (𝓝 (if a ≤ x then (-1 : ℝ) else 0)) := by
  by_cases hax : a ≤ x
  · rw [if_pos hax]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with b hba
    change b < a at hba
    rw [excessSlope, max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp [sub_ne_zero.mpr (ne_of_lt hba)] <;> ring
  · rw [if_neg hax]
    have hxa : x < a := lt_of_not_ge hax
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hxa)] with b hba hxb
    change b < a at hba
    change x < b at hxb
    simp [excessSlope, max_eq_right (by linarith : x-b ≤ 0), max_eq_right (by linarith : x-a ≤ 0)]

variable {Ω : Type*} [MeasurableSpace Ω]

theorem excessSlope_integral_right {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Tendsto (fun b => ∫ ω, excessSlope (X ω) a b ∂μ) (𝓝[>] a)
      (𝓝 (-μ.real {ω | a < X ω})) := by
  classical
  have ht : Tendsto (fun b => ∫ ω, excessSlope (X ω) a b ∂μ) (𝓝[>] a)
      (𝓝 (∫ ω, if a < X ω then (-1 : ℝ) else 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall (fun b => by
        unfold excessSlope
        exact (((hX.sub measurable_const).max measurable_const).sub
          ((hX.sub measurable_const).max measurable_const)).div_const _ |>.aestronglyMeasurable)
    · exact Eventually.of_forall (fun b => Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using excessSlope_abs_le_one (X ω) a b))
    · exact integrable_const _
    · exact Eventually.of_forall (fun ω => excessSlope_tendsto_right (X ω) a)
  have hs : MeasurableSet {ω | a < X ω} := measurableSet_lt measurable_const hX
  have he : (fun ω => if a < X ω then (-1 : ℝ) else 0) =
      {ω | a < X ω}.indicator (fun _ => (-1 : ℝ)) := by
    funext ω
    simp only [Set.indicator, mem_setOf_eq]
  simpa only [he, integral_indicator hs, setIntegral_const, smul_eq_mul, mul_neg_one] using ht

theorem excessSlope_integral_left {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Tendsto (fun b => ∫ ω, excessSlope (X ω) a b ∂μ) (𝓝[<] a)
      (𝓝 (-μ.real {ω | a ≤ X ω})) := by
  classical
  have ht : Tendsto (fun b => ∫ ω, excessSlope (X ω) a b ∂μ) (𝓝[<] a)
      (𝓝 (∫ ω, if a ≤ X ω then (-1 : ℝ) else 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall (fun b => by
        unfold excessSlope
        exact (((hX.sub measurable_const).max measurable_const).sub
          ((hX.sub measurable_const).max measurable_const)).div_const _ |>.aestronglyMeasurable)
    · exact Eventually.of_forall (fun b => Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using excessSlope_abs_le_one (X ω) a b))
    · exact integrable_const _
    · exact Eventually.of_forall (fun ω => excessSlope_tendsto_left (X ω) a)
  have hs : MeasurableSet {ω | a ≤ X ω} := measurableSet_le measurable_const hX
  have he : (fun ω => if a ≤ X ω then (-1 : ℝ) else 0) =
      {ω | a ≤ X ω}.indicator (fun _ => (-1 : ℝ)) := by
    funext ω
    simp only [Set.indicator, mem_setOf_eq]
  simpa only [he, integral_indicator hs, setIntegral_const, smul_eq_mul, mul_neg_one] using ht

theorem shortfall_slope_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hi : Integrable X μ) {p a b : ℝ} (hp : 0 < p) (hba : b ≠ a) :
    slope (shortfallObjective μ X p) a b =
      1+(∫ ω, excessSlope (X ω) a b ∂μ)/p := by
  have hia : Integrable (fun ω => max (X ω-a) 0) μ := (hi.sub (integrable_const a)).pos_part
  have hib : Integrable (fun ω => max (X ω-b) 0) μ := (hi.sub (integrable_const b)).pos_part
  have he : (∫ ω, excessSlope (X ω) a b ∂μ) =
      ((∫ ω, max (X ω-b) 0 ∂μ)-(∫ ω, max (X ω-a) 0 ∂μ))/(b-a) := by
    simp only [excessSlope, integral_div]
    rw [integral_sub hib hia]
  rw [slope_def_field, shortfallObjective, shortfallObjective, he]
  field_simp [hp.ne', sub_ne_zero.mpr hba] <;> ring

/-- The left derivative uses the weak tail and the right derivative the
strict tail, retaining atoms on the original probability space. -/
theorem shortfall_one_sided_derivatives {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ)
    {p : ℝ} (hp : 0 < p) (a : ℝ) :
    HasDerivWithinAt (shortfallObjective μ X p) (1-μ.real {ω | a ≤ X ω}/p) (Iio a) a ∧
      HasDerivWithinAt (shortfallObjective μ X p) (1-μ.real {ω | a < X ω}/p) (Ioi a) a := by
  constructor
  · apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Iio a)).mpr
    have hs : slope (shortfallObjective μ X p) a =ᶠ[𝓝[<] a]
        (fun b => 1+(∫ ω, excessSlope (X ω) a b ∂μ)/p) := by
      filter_upwards [self_mem_nhdsWithin] with b hb
      exact shortfall_slope_eq hi hp (ne_of_lt hb)
    apply (tendsto_congr' hs).mpr
    convert tendsto_const_nhds.add ((excessSlope_integral_left (μ := μ) hm a).div_const p) using 1 <;> ring
  · apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)).mpr
    have hs : slope (shortfallObjective μ X p) a =ᶠ[𝓝[>] a]
        (fun b => 1+(∫ ω, excessSlope (X ω) a b ∂μ)/p) := by
      filter_upwards [self_mem_nhdsWithin] with b hb
      exact shortfall_slope_eq hi hp (ne_of_gt hb)
    apply (tendsto_congr' hs).mpr
    convert tendsto_const_nhds.add ((excessSlope_integral_right (μ := μ) hm a).div_const p) using 1 <;> ring

/-- The ordinary real subdifferential, by its global supporting-line definition. -/
def realSubgradient (φ : ℝ → ℝ) (a : ℝ) : Set ℝ :=
  {d | ∀ b : ℝ, φ a+d*(b-a) ≤ φ b}

variable {Ω : Type*} [MeasurableSpace Ω]

theorem shortfallObjective_convex {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hi : Integrable X μ) {p : ℝ} (hp : 0 < p) :
    ConvexOn ℝ univ (shortfallObjective μ X p) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ c d hc hd hcd
  simp only [smul_eq_mul]
  have hia : Integrable (fun ω => max (X ω-a) 0) μ := (hi.sub (integrable_const a)).pos_part
  have hib : Integrable (fun ω => max (X ω-b) 0) μ := (hi.sub (integrable_const b)).pos_part
  have hic : Integrable (fun ω => max (X ω-(c*a+d*b)) 0) μ :=
    (hi.sub (integrable_const (c*a+d*b))).pos_part
  have hpoint (x : ℝ) : max (x-(c*a+d*b)) 0 ≤ c*max (x-a) 0+d*max (x-b) 0 := by
    apply max_le
    · have he : x-(c*a+d*b) = c*(x-a)+d*(x-b) := by
        calc
          x-(c*a+d*b) = (c+d)*x-(c*a+d*b) := by rw [hcd, one_mul]
          _ = _ := by ring
      rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hc)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hd)
    · exact add_nonneg (mul_nonneg hc (le_max_right _ _)) (mul_nonneg hd (le_max_right _ _))
  have hint : (∫ ω, max (X ω-(c*a+d*b)) 0 ∂μ) ≤
      c*(∫ ω, max (X ω-a) 0 ∂μ)+d*(∫ ω, max (X ω-b) 0 ∂μ) := by
    calc
      _ ≤ ∫ ω, c*max (X ω-a) 0+d*max (X ω-b) 0 ∂μ :=
        integral_mono_ae hic ((hia.const_mul c).add (hib.const_mul d))
          (Eventually.of_forall (fun ω => hpoint (X ω)))
      _ = _ := by rw [integral_add (hia.const_mul _) (hib.const_mul _), integral_const_mul, integral_const_mul]
  unfold shortfallObjective
  calc
    _ ≤ c*a+d*b+(c*(∫ ω, max (X ω-a) 0 ∂μ)+d*(∫ ω, max (X ω-b) 0 ∂μ))/p :=
      add_le_add_left (div_le_div_of_nonneg_right hint hp.le) _
    _ = _ := by ring

theorem realSubgradient_eq_Icc {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    {a dL dR : ℝ} (hL : HasDerivWithinAt φ dL (Iio a) a)
    (hR : HasDerivWithinAt φ dR (Ioi a) a) : realSubgradient φ a = Icc dL dR := by
  ext d
  constructor
  · intro hd
    constructor
    · apply le_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' not_mem_Iio_self).mp hL)
      filter_upwards [self_mem_nhdsWithin] with b hb
      rw [slope_def_field]
      apply (div_le_iff_of_neg (sub_neg.mpr hb)).mpr
      have h := hd b
      linarith
    · apply ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' not_mem_Ioi_self).mp hR)
      filter_upwards [self_mem_nhdsWithin] with b hb
      rw [slope_def_field]
      apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
      have h := hd b
      linarith
  · intro hd b
    rcases lt_trichotomy b a with hba | rfl | hab
    · have hs := (hφ.slope_le_of_hasDerivWithinAt_Iio (mem_univ b) (mem_univ a) hba hL).trans hd.1
      rw [slope_def_field] at hs
      have hmul := (div_le_iff₀ (sub_pos.mpr hba)).mp hs
      nlinarith
    · simp
    · have hs := hd.2.trans (hφ.le_slope_of_hasDerivWithinAt_Ioi (mem_univ a) (mem_univ b) hab hR)
      rw [slope_def_field] at hs
      have hmul := (le_div_iff₀ (sub_pos.mpr hab)).mp hs
      nlinarith

theorem shortfall_subgradient_interval {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ)
    {p : ℝ} (hp : 0 < p) (a : ℝ) :
    realSubgradient (shortfallObjective μ X p) a =
      Icc (1-μ.real {ω | a ≤ X ω}/p) (1-μ.real {ω | a < X ω}/p) :=
  realSubgradient_eq_Icc (shortfallObjective_convex hi hp)
    (shortfall_one_sided_derivatives hm hi hp a).1 (shortfall_one_sided_derivatives hm hi hp a).2

theorem shortfall_subgradient_survival {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ)
    {p : ℝ} (hp : 0 < p) (a : ℝ) :
    realSubgradient (shortfallObjective μ X p) a =
      (fun u => 1-u/p) '' survival (Measure.map X μ) a := by
  rw [shortfall_subgradient_interval hm hi hp a]
  ext d
  constructor
  · intro hd
    let u := p*(1-d)
    have hlo : μ.real {ω | a < X ω} ≤ u := by
      have hdiv : μ.real {ω | a < X ω}/p ≤ 1-d := by linarith [hd.2]
      have h := (div_le_iff₀ hp).mp hdiv
      dsimp [u]
      nlinarith
    have hhi : u ≤ μ.real {ω | a ≤ X ω} := by
      have hdiv : 1-d ≤ μ.real {ω | a ≤ X ω}/p := by linarith [hd.1]
      have h := (le_div_iff₀ hp).mp hdiv
      dsimp [u]
      nlinarith
    have hu : u ∈ survival (Measure.map X μ) a :=
      (tailQuantile_map_mem_iff hm a u).mpr ⟨hlo, hhi⟩
    refine ⟨u, hu, ?_⟩
    dsimp [u]
    field_simp [hp.ne'] <;> ring
  · rintro ⟨u, hu, rfl⟩
    have hbr := (tailQuantile_map_mem_iff hm a u).mp hu
    exact ⟨sub_le_sub_left (div_le_div_of_nonneg_right hbr.2 hp.le) 1,
      sub_le_sub_left (div_le_div_of_nonneg_right hbr.1 hp.le) 1⟩

theorem shortfall_zero_subgradient_iff_quantile {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ)
    {p : ℝ} (hp : 0 < p) (a : ℝ) :
    0 ∈ realSubgradient (shortfallObjective μ X p) a ↔
      a ∈ tailQuantile (Measure.map X μ) p := by
  rw [shortfall_subgradient_survival hm hi hp a]
  constructor
  · rintro ⟨u, hu, he⟩
    have hue : u = p := by field_simp [hp.ne'] at he; nlinarith
    simpa only [hue] using hu
  · intro ha
    exact ⟨p, ha, by simp [hp.ne']⟩

end ScalarMonotone.EndOfPaper
end
