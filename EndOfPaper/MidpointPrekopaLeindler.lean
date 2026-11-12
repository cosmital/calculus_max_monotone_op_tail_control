import EndOfPaper.PositiveDensityMidpoint
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
A genuine one-dimensional midpoint Prekopa-Leindler inequality for positive continuous integrable densities, proved through actual CDF transport.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_sqrt_transport_bound {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hCompare : Real.sqrt (a*b) ≤ h) :
    a ≤ ((1+a/b)/2)*h := by
  let z := Real.sqrt (a*b)
  let r := Real.sqrt (a/b)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hrSq : r^2 = a/b := Real.sq_sqrt (div_nonneg ha.le hb.le)
  have hProd : z*r = a := by
    dsimp only [z,r]
    rw [← Real.sqrt_mul (mul_nonneg ha.le hb.le)]
    have he : (a*b)*(a/b) = a^2 := by field_simp [hb.ne'] <;> ring
    rw [he,Real.sqrt_sq_eq_abs,abs_of_pos ha]
  have hWeighted : z*r^2 = z*(a/b) := congrArg (fun t : ℝ => z*t) hrSq
  have hBound : z*r ≤ ((1+a/b)/2)*z := by
    have hn := mul_nonneg hz (sq_nonneg (r-1))
    nlinarith only [hn,hWeighted]
  calc
    a = z*r := hProd.symm
    _ ≤ ((1+a/b)/2)*z := hBound
    _ ≤ _ := mul_le_mul_of_nonneg_left hCompare
      (div_nonneg (add_nonneg zero_le_one (div_nonneg ha.le hb.le)) (by norm_num))

theorem midpoint_integral_unit_density {f g H : ℝ → ℝ}
    (hf : Continuous f) (hfp : ∀ x, 0 < f x) (hfi : Integrable f volume)
    (hfmass : (∫ x : ℝ, f x) = 1) (hg : Continuous g) (hgp : ∀ x, 0 < g x)
    (hgi : Integrable g volume) (hgmass : (∫ x : ℝ, g x) = 1) (hH : Integrable H volume)
    (hCompare : ∀ x y : ℝ, Real.sqrt (f x*g y) ≤ H ((x+y)/2)) :
    (1 : ℝ) ≤ ∫ x : ℝ, H x := by
  have hPull := density_midpoint_pullback_integrable hf hfp hfi hfmass hg hgp hgi hgmass hH
  have hPoint (x : ℝ) : f x ≤ densityMidpointJacobian f g x*H (densityMidpointTransport f g x) :=
    positive_sqrt_transport_bound (hfp x) (hgp _) (hCompare x (densityTransport f g x))
  calc
    (1 : ℝ) = ∫ x : ℝ, f x := hfmass.symm
    _ ≤ ∫ x : ℝ, densityMidpointJacobian f g x*H (densityMidpointTransport f g x) :=
      integral_mono hfi hPull hPoint
    _ = ∫ x : ℝ, H x := (density_midpoint_change_variables hf hfp hfi hfmass hg hgp hgi hgmass H).symm

theorem midpoint_prekopa_leindler_real {f g H : ℝ → ℝ}
    (hf : Continuous f) (hfp : ∀ x, 0 < f x) (hfi : Integrable f volume)
    (hg : Continuous g) (hgp : ∀ x, 0 < g x) (hgi : Integrable g volume) (hH : Integrable H volume)
    (hCompare : ∀ x y : ℝ, Real.sqrt (f x*g y) ≤ H ((x+y)/2)) :
    Real.sqrt ((∫ x : ℝ, f x)*(∫ x : ℝ, g x)) ≤ ∫ x : ℝ, H x := by
  let a := ∫ x : ℝ, f x
  let b := ∫ x : ℝ, g x
  let c := Real.sqrt (a*b)
  have ha : 0 < a := positive_density_mass_positive hf hfp hfi
  have hb : 0 < b := positive_density_mass_positive hg hgp hgi
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hf1 : (∫ x : ℝ, f x/a) = 1 := by rw [integral_div]; exact div_self ha.ne'
  have hg1 : (∫ x : ℝ, g x/b) = 1 := by rw [integral_div]; exact div_self hb.ne'
  have hNormCompare (x y : ℝ) : Real.sqrt ((f x/a)*(g y/b)) ≤ H ((x+y)/2)/c := by
    rw [div_mul_div_comm,Real.sqrt_div (mul_nonneg (hfp x).le (hgp y).le)]
    exact div_le_div_of_nonneg_right (hCompare x y) hc.le
  have hUnit := midpoint_integral_unit_density (hf.div_const a) (fun x => div_pos (hfp x) ha)
    (hfi.div_const a) hf1 (hg.div_const b) (fun x => div_pos (hgp x) hb)
    (hgi.div_const b) hg1 (hH.div_const c) hNormCompare
  rw [integral_div] at hUnit
  simpa only [one_mul] using (le_div_iff₀ hc).mp hUnit

end ScalarMonotone.EndOfPaper
end
