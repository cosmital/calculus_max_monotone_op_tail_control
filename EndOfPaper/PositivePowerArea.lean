import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
The full extended positive-power area substitution via the pinned Jacobian theorem; no finite integral or integrand measurability is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem lintegral_image_eq_abs_deriv_mul {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → ℝ≥0∞) :
    (∫⁻ x in f '' s, g x) = ∫⁻ x in s, ENNReal.ofReal |f' x| * g (f x) := by
  simpa only [ContinuousLinearMap.det_one_smulRight] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

theorem positive_power_area_substitution (g : ℝ → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioi (0 : ℝ), g (t^(1/r))) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1)) * g t := by
  have himage : (fun t : ℝ => t^r) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact Real.rpow_pos_of_pos ht r
    · intro hy
      refine ⟨y^r⁻¹,Real.rpow_pos_of_pos hy _,?_⟩
      exact Real.rpow_inv_rpow hy.le hr.ne'
  have hderiv (t : ℝ) (ht : t ∈ Ioi 0) :
      HasDerivWithinAt (fun x : ℝ => x^r) (r*t^(r-1)) (Ioi 0) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t^r) (Ioi 0) := by
    intro x hx y hy he
    exact (Real.rpow_left_inj hx.le hy.le hr.ne').mp he
  calc
    _ = ∫⁻ t in (fun t : ℝ => t^r) '' Ioi 0, g (t^(1/r)) := by rw [himage]
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal |r*t^(r-1)| * g ((t^r)^(1/r)) :=
      lintegral_image_eq_abs_deriv_mul measurableSet_Ioi hderiv hinj _
    _ = ENNReal.ofReal r * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1)) * g t := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [one_div,Real.rpow_rpow_inv ht.le hr.ne',
        abs_of_nonneg (mul_nonneg hr.le (Real.rpow_nonneg ht.le _)),ENNReal.ofReal_mul hr.le]
      exact mul_assoc _ _ _

end ScalarMonotone.EndOfPaper
end
