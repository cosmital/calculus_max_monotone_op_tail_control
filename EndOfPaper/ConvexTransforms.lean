import Mathlib

/-!
The full power/exponential convex-transformation proposition: both
forward implications and the converses under their exact monotonicity
directions. Pointwise convex limits are proved on expanding affine
domains. The exact Hardy power-envelope constant converges to exp(1).
-/

open Set Filter
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem eventually_positive_one_add_div (t : ℝ) :
    ∀ᶠ κ : ℝ in atTop, 0 < 1+t/κ := by
  have ht : Tendsto (fun κ : ℝ => 1+t/κ) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using (tendsto_inv_atTop_zero.const_mul t).const_add 1
  exact ht.eventually_const_lt zero_lt_one

theorem negative_power_exponential_limit (t : ℝ) :
    Tendsto (fun κ : ℝ => (1+t/κ)^(-κ)) atTop (𝓝 (Real.exp (-t))) := by
  rw [Real.exp_neg]
  apply ((tendsto_one_plus_div_rpow_exp t).inv₀ (Real.exp_ne_zero t)).congr'
  filter_upwards [eventually_positive_one_add_div t] with κ hκ
  exact (Real.rpow_neg hκ.le κ).symm

theorem continuous_power_exponential_limit {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioi 0)) (t : ℝ) :
    Tendsto (fun κ : ℝ => φ ((1+t/κ)^(-κ))) atTop (𝓝 (φ (Real.exp (-t)))) := by
  apply (hφ _ (Real.exp_pos (-t))).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨negative_power_exponential_limit t,
    (eventually_positive_one_add_div t).mono (fun κ hκ => Real.rpow_pos_of_pos hκ (-κ))⟩

theorem all_power_convex_implies_exponential_convex {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioi 0))
    (hp : ∀ κ : ℝ, 0 < κ → ConvexOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) :
    ConvexOn ℝ univ (fun x => φ (Real.exp (-x))) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d hc hd hcd
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto
    (continuous_power_exponential_limit hφ (c*x+d*y))
    (((continuous_power_exponential_limit hφ x).const_mul c).add
      ((continuous_power_exponential_limit hφ y).const_mul d))
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_positive_one_add_div x,
    eventually_positive_one_add_div y] with κ hκ hx hy
  have hi := (hp κ hκ).2 hx hy hc hd hcd
  have he : c*(1+x/κ)+d*(1+y/κ) = 1+(c*x+d*y)/κ := by
    calc
      _ = (c+d)+(c*x+d*y)/κ := by ring
      _ = _ := by rw [hcd]
  simpa only [smul_eq_mul, he] using hi

theorem exponential_convex_implies_power_convex {φ : ℝ → ℝ}
    (hm : MonotoneOn φ (Ioi 0)) (hg : ConvexOn ℝ univ (fun x => φ (Real.exp (-x))))
    {κ : ℝ} (hκ : 0 < κ) : ConvexOn ℝ (Ioi 0) (fun x => φ (x^(-κ))) := by
  let g : ℝ → ℝ := fun x => φ (Real.exp (-x))
  have hga : Antitone g := by
    intro x y hxy
    exact hm (Real.exp_pos (-y)) (Real.exp_pos (-x)) (Real.exp_le_exp.mpr (neg_le_neg hxy))
  have hl : ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x => κ*Real.log x) := by
    simpa only [smul_eq_mul] using ConcaveOn.smul hκ.le strictConcaveOn_log_Ioi.concaveOn
  have hcomp : ConvexOn ℝ (Ioi (0 : ℝ)) (fun x => g (κ*Real.log x)) := by
    refine ⟨convex_Ioi _, ?_⟩
    intro x hx y hy c d hc hd hcd
    exact (hga (hl.2 hx hy hc hd hcd)).trans (hg.2 (mem_univ _) (mem_univ _) hc hd hcd)
  apply hcomp.congr
  intro x hx
  change φ (Real.exp (-(κ*Real.log x))) = φ (x^(-κ))
  rw [Real.rpow_def_of_pos hx]
  congr 1
  congr 1
  ring

theorem all_power_concave_implies_exponential_concave {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioi 0))
    (hp : ∀ κ : ℝ, 0 < κ → ConcaveOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) :
    ConcaveOn ℝ univ (fun x => φ (Real.exp (-x))) := by
  have hn := all_power_convex_implies_exponential_convex hφ.neg (fun κ hκ => (hp κ hκ).neg)
  apply hn.neg.congr
  intro x _
  exact neg_neg _

theorem exponential_concave_implies_power_concave {φ : ℝ → ℝ}
    (hm : AntitoneOn φ (Ioi 0)) (hg : ConcaveOn ℝ univ (fun x => φ (Real.exp (-x))))
    {κ : ℝ} (hκ : 0 < κ) : ConcaveOn ℝ (Ioi 0) (fun x => φ (x^(-κ))) := by
  have hmn : MonotoneOn (fun x => -φ x) (Ioi 0) := by
    intro x hx y hy hxy
    exact neg_le_neg (hm hx hy hxy)
  have hn := exponential_convex_implies_power_convex hmn hg.neg hκ
  apply hn.neg.congr
  intro x _
  exact neg_neg _

/-- Every implication of prop:convextransforms, with the precise monotonicity
directions required only for the two converses. -/
theorem power_exponential_convex_transforms {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Ioi 0)) :
    ((∀ κ : ℝ, 0 < κ → ConvexOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) →
      ConvexOn ℝ univ (fun x => φ (Real.exp (-x)))) ∧
      (MonotoneOn φ (Ioi 0) → ConvexOn ℝ univ (fun x => φ (Real.exp (-x))) →
        ∀ κ : ℝ, 0 < κ → ConvexOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) ∧
      ((∀ κ : ℝ, 0 < κ → ConcaveOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) →
        ConcaveOn ℝ univ (fun x => φ (Real.exp (-x)))) ∧
      (AntitoneOn φ (Ioi 0) → ConcaveOn ℝ univ (fun x => φ (Real.exp (-x))) →
        ∀ κ : ℝ, 0 < κ → ConcaveOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) :=
  ⟨all_power_convex_implies_exponential_convex hφ,
   fun hm hg _ hκ => exponential_convex_implies_power_convex hm hg hκ,
   all_power_concave_implies_exponential_concave hφ,
   fun hm hg _ hκ => exponential_concave_implies_power_concave hm hg hκ⟩

/-- The exact Pareto-to-exponential constant limit asserted after
prop:hardyprofiles; the exponent and prefactor both vary with κ. -/
theorem hardy_power_constant_limit :
    Tendsto (fun κ : ℝ => (κ/(κ-1))^κ) atTop (𝓝 (Real.exp 1)) := by
  have ht : Tendsto (fun κ : ℝ => κ-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with κ hκ
    linarith
  have hp : Tendsto (fun κ : ℝ => (1+1/(κ-1))^(κ-1)) atTop (𝓝 (Real.exp 1)) :=
    (tendsto_one_plus_div_rpow_exp 1).comp ht
  have hb : Tendsto (fun κ : ℝ => 1+1/(κ-1)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, one_mul, add_zero] using
      (tendsto_inv_atTop_zero.comp ht).const_add 1
  have he : (fun κ : ℝ => (1+1/(κ-1))^(κ-1)*(1+1/(κ-1))) =ᶠ[atTop]
      (fun κ => (κ/(κ-1))^κ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with κ hκ
    have hk : κ-1 ≠ 0 := (sub_pos.mpr hκ).ne'
    have hpos : 0 < 1+1/(κ-1) := add_pos zero_lt_one (one_div_pos.mpr (sub_pos.mpr hκ))
    have hratio : κ/(κ-1) = 1+1/(κ-1) := by field_simp [hk] <;> ring
    rw [hratio]
    calc
      (1+1/(κ-1))^(κ-1)*(1+1/(κ-1)) =
          (1+1/(κ-1))^(κ-1)*(1+1/(κ-1))^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (1+1/(κ-1))^((κ-1)+1) := (Real.rpow_add hpos (κ-1) 1).symm
      _ = (1+1/(κ-1))^κ := by congr 1; ring
  simpa only [mul_one] using (hp.mul hb).congr' he

end ScalarMonotone.EndOfPaper
end
