import EndOfPaper.GeometricProduct

/-!
One finite positive-log area of a combined product
implies the individual areas on a common positive prefix.
The remaining part of the interval is bounded by antitonicity.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_log_le_log_product_add {x y c : ℝ}
    (hx : 0 ≤ x) (hc : 0 < c) (hcy : c ≤ y) :
    max (Real.log x) 0 ≤ max (Real.log (x*y)) 0+|Real.log c| := by
  by_cases hx0 : x = 0
  · simp only [hx0,zero_mul,Real.log_zero,max_self,zero_add]
    exact abs_nonneg _
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hyp : 0 < y := hc.trans_le hcy
    have hlog := Real.log_le_log hc hcy
    rw [Real.log_mul hxp.ne' hyp.ne']
    apply max_le
    · linarith [le_max_left (Real.log x+Real.log y) 0,neg_le_abs (Real.log c)]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)

theorem positive_log_area_factor_finite {f g : ℝ → ℝ} {B b : ℝ}
    (hmf : Measurable f) (hmg : Measurable g)
    (hf : AntitoneOn f (Ioo (0 : ℝ) B)) (hg : AntitoneOn g (Ioo (0 : ℝ) B))
    (hf0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ f x)
    (hb : b ∈ Ioo (0 : ℝ) B) (hgb : 0 < g b)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (f x*g x)) 0)) < ∞) :
    (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (f x)) 0)) < ∞ := by
  have hprod : IntegrableOn (fun x => max (Real.log (f x*g x)) 0) (Ioo (0 : ℝ) B) volume :=
    positive_log_integrable_of_lintegral (hmf.mul hmg) hP
  have hc : IntegrableOn (fun _ : ℝ => |Real.log (g b)|+max (Real.log (f b)) 0)
      (Ioo (0 : ℝ) B) volume := integrableOn_const.mpr (Or.inr (by simp))
  have hm : Measurable (fun x => max (Real.log (f x)) 0) := by fun_prop
  have hfi : IntegrableOn (fun x => max (Real.log (f x)) 0) (Ioo (0 : ℝ) B) volume := by
    apply (hprod.add hc).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    change max (Real.log (f x)) 0 ≤ max (Real.log (f x*g x)) 0+
      (|Real.log (g b)|+max (Real.log (f b)) 0)
    by_cases hxb : x < b
    · have hlow := positive_log_le_log_product_add (hf0 x hx) hgb (hg hx hb hxb.le)
      linarith [le_max_right (Real.log (f b)) 0]
    · have hfxb := hf hb hx (le_of_not_gt hxb)
      have hbound : max (Real.log (f x)) 0 ≤ max (Real.log (f b)) 0 := by
        by_cases hx0 : f x = 0
        · simpa only [hx0,Real.log_zero,max_self] using le_max_right (Real.log (f b)) 0
        · exact max_le_max (Real.log_le_log (lt_of_le_of_ne (hf0 x hx) (Ne.symm hx0)) hfxb) le_rfl
      linarith [le_max_right (Real.log (f x*g x)) 0,abs_nonneg (Real.log (g b))]
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    hm.aestronglyMeasurable (Eventually.of_forall (fun x => le_max_right (Real.log (f x)) 0))).mpr hfi)

theorem positive_log_areas_of_finite_product {ι : Type*} [Fintype ι]
    {s : ι → ℝ → ℝ} {B b : ℝ} (hm : ∀ i, Measurable (s i))
    (hanti : ∀ i, AntitoneOn (s i) (Ioo (0 : ℝ) B))
    (hs0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → 0 ≤ s i x)
    (hb : b ∈ Ioo (0 : ℝ) B) (hsb : ∀ i, 0 < s i b)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ i, s i x)) 0)) < ∞) :
    ∀ i, (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞ := by
  classical
  intro i
  let g := fun x => ∏ j ∈ Finset.univ.erase i, s j x
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hga : AntitoneOn g (Ioo (0 : ℝ) B) := by
    intro x hx y hy hxy
    exact Finset.prod_le_prod (fun j _ => hs0 j y hy) (fun j _ => hanti j hx hy hxy)
  have hgb : 0 < g b := Finset.prod_pos (fun j _ => hsb j)
  apply positive_log_area_factor_finite (hm i) hgm (hanti i) hga (hs0 i) hb hgb
  have hfact (x : ℝ) : s i x*g x = ∏ j, s j x :=
    Finset.mul_prod_erase Finset.univ (fun j => s j x) (Finset.mem_univ i)
  have he : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x*g x)) 0)) =
      ∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ j, s j x)) 0) := by
    apply lintegral_congr
    intro x
    rw [hfact]
  change (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x*g x)) 0)) < ∞
  rw [he]
  exact hP

end ScalarMonotone.EndOfPaper
end
