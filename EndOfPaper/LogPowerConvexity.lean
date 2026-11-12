import Mathlib

/-!
The distinct appendix equivalence between logarithmic convexity and
limiting power convexity of positive profiles. The scaled pointwise
limit holds for every positive scalar; an arbitrary positive sequence
of exponents tending to infinity suffices for the converse.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem scaled_exponential_limit (t : ℝ) :
    Tendsto (fun κ : ℝ => κ*(Real.exp (t/κ)-1)) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · simpa only [ht, zero_div, Real.exp_zero, sub_self, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  · have harg0 : Tendsto (fun κ : ℝ => t/κ) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul t
    have harg : Tendsto (fun κ : ℝ => t/κ) atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨harg0,
        (eventually_gt_atTop (0 : ℝ)).mono (fun κ hκ => div_ne_zero ht hκ.ne')⟩
    have hs : Tendsto (slope Real.exp (0 : ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa only [Real.exp_zero] using
        (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp 0))
    have he : (fun κ : ℝ => t*slope Real.exp 0 (t/κ)) =ᶠ[atTop]
        (fun κ => κ*(Real.exp (t/κ)-1)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
      rw [slope_def_field, Real.exp_zero, sub_zero]
      field_simp [ht, hκ.ne'] <;> ring
    simpa only [mul_one] using ((hs.comp harg).const_mul t).congr' he

theorem scaled_power_log_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun κ : ℝ => κ*(a^((-1 : ℝ)/κ)-1)) atTop (𝓝 (-Real.log a)) := by
  have he (κ : ℝ) : a^((-1 : ℝ)/κ) = Real.exp ((-Real.log a)/κ) := by
    rw [Real.rpow_def_of_pos ha]
    congr 1
    ring
  simp_rw [he]
  exact scaled_exponential_limit (-Real.log a)

theorem log_convex_implies_all_power_convex {α : ℝ → ℝ} {D : Set ℝ}
    (hα : ∀ x ∈ D, 0 < α x) (hg : ConvexOn ℝ D (fun x => -Real.log (α x)))
    {κ : ℝ} (hκ : 0 < κ) : ConvexOn ℝ D (fun x => (α x)^((-1 : ℝ)/κ)) := by
  have hs : ConvexOn ℝ D (fun x => (1/κ)*(-Real.log (α x))) := by
    simpa only [smul_eq_mul] using ConvexOn.smul (one_div_pos.mpr hκ).le hg
  have he : ConvexOn ℝ D (fun x => Real.exp ((1/κ)*(-Real.log (α x)))) := by
    refine ⟨hg.1, ?_⟩
    intro x hx y hy c d hc hd hcd
    exact (Real.exp_le_exp.mpr (hs.2 hx hy hc hd hcd)).trans
      (convexOn_exp.2 (mem_univ _) (mem_univ _) hc hd hcd)
  apply he.congr
  intro x hx
  change Real.exp ((1/κ)*(-Real.log (α x))) = (α x)^((-1 : ℝ)/κ)
  rw [Real.rpow_def_of_pos (hα x hx)]
  congr 1
  ring

/-- Any positive sequence of exponents tending to infinity suffices. No
monotonicity of that sequence or continuity of α is added. -/
theorem limiting_power_convex_implies_log_convex {α : ℝ → ℝ} {D : Set ℝ}
    (hα : ∀ x ∈ D, 0 < α x) {κ : ℕ → ℝ} (hκpos : ∀ n, 0 < κ n)
    (hκ : Tendsto κ atTop atTop)
    (hc : ∀ n, ConvexOn ℝ D (fun x => (α x)^((-1 : ℝ)/κ n))) :
    ConvexOn ℝ D (fun x => -Real.log (α x)) := by
  have hscaled (n) : ConvexOn ℝ D (fun x => κ n*((α x)^((-1 : ℝ)/κ n)-1)) := by
    have ht := ConvexOn.smul (hκpos n).le ((hc n).add_const (-1))
    apply ht.congr
    intro x _
    change κ n*((α x)^((-1 : ℝ)/κ n)+(-1)) = κ n*((α x)^((-1 : ℝ)/κ n)-1)
    ring
  have hlim (x) (hx : x ∈ D) :
      Tendsto (fun n => κ n*((α x)^((-1 : ℝ)/κ n)-1)) atTop (𝓝 (-Real.log (α x))) :=
    (scaled_power_log_limit (hα x hx)).comp hκ
  refine ⟨(hc 0).1, ?_⟩
  intro x hx y hy c d hcn hdn hcd
  have hz : c • x+d • y ∈ D := (hc 0).1 hx hy hcn hdn hcd
  apply le_of_tendsto_of_tendsto (hlim _ hz)
    (((hlim x hx).const_mul c).add ((hlim y hy).const_mul d))
  exact Eventually.of_forall (fun n => (hscaled n).2 hx hy hcn hdn hcd)

end ScalarMonotone.EndOfPaper
end
