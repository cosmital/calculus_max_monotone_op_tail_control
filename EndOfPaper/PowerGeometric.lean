import Mathlib

/-!
The full weighted power--geometric limit, for arbitrary positive
a,b and every weight in the closed unit interval. The exact real
exponent tends to infinity. Positivity of every weighted base and
mean is proved, including the two endpoint weights.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def weightedPowerMean (κ w a b : ℝ) : ℝ :=
  (w*a^((-1 : ℝ)/κ)+(1-w)*b^((-1 : ℝ)/κ))^(-κ)

theorem weighted_power_base_positive {a b w κ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw : w ∈ Icc (0 : ℝ) 1) :
    0 < w*a^((-1 : ℝ)/κ)+(1-w)*b^((-1 : ℝ)/κ) := by
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul, sub_zero, one_mul, zero_add]
    exact Real.rpow_pos_of_pos hb _
  · have hp : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
    exact add_pos_of_pos_of_nonneg (mul_pos hp (Real.rpow_pos_of_pos ha _))
      (mul_nonneg (sub_nonneg.mpr hw.2) (Real.rpow_pos_of_pos hb _).le)

theorem weightedPowerMean_positive {a b w κ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw : w ∈ Icc (0 : ℝ) 1) :
    0 < weightedPowerMean κ w a b :=
  Real.rpow_pos_of_pos (weighted_power_base_positive ha hb hw) _

theorem weighted_power_geometric_limit {a b w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw : w ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun κ : ℝ => weightedPowerMean κ w a b) atTop
      (𝓝 (a^w*b^(1-w))) := by
  let f : ℝ → ℝ := fun h =>
    w*Real.exp ((-Real.log a)*h)+(1-w)*Real.exp ((-Real.log b)*h)
  have hf0 : f 0 = 1 := by dsimp [f]; simp
  have hA : HasDerivAt (fun h : ℝ => Real.exp ((-Real.log a)*h)) (-Real.log a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-Real.log a)).exp
  have hB : HasDerivAt (fun h : ℝ => Real.exp ((-Real.log b)*h)) (-Real.log b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-Real.log b)).exp
  have hf : HasDerivAt f (w*(-Real.log a)+(1-w)*(-Real.log b)) 0 :=
    (hA.const_mul w).add (hB.const_mul (1-w))
  have hg : HasDerivAt (fun h => Real.log (f h))
      (w*(-Real.log a)+(1-w)*(-Real.log b)) 0 := by
    simpa only [hf0, div_one] using hf.log (by rw [hf0]; norm_num)
  have hinv : Tendsto (fun κ : ℝ => 1/κ) atTop (𝓝[≠] (0 : ℝ)) := by
    simpa only [one_div] using
      tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE (0 : ℝ))
  have hs := ((hasDerivAt_iff_tendsto_slope.mp hg).comp hinv).neg
  have he : (fun κ : ℝ => -slope (fun h => Real.log (f h)) 0 (1/κ)) =ᶠ[atTop]
      (fun κ => (-κ)*Real.log (w*a^((-1 : ℝ)/κ)+(1-w)*b^((-1 : ℝ)/κ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
    have hpa : a^((-1 : ℝ)/κ) = Real.exp ((-Real.log a)*(1/κ)) := by
      rw [Real.rpow_def_of_pos ha]; congr 1; ring
    have hpb : b^((-1 : ℝ)/κ) = Real.exp ((-Real.log b)*(1/κ)) := by
      rw [Real.rpow_def_of_pos hb]; congr 1; ring
    rw [slope_def_field, hf0, Real.log_one, sub_zero, sub_zero, hpa, hpb]
    dsimp [f]
    field_simp [hκ.ne'] <;> ring
  have hlog : Tendsto
      (fun κ : ℝ => (-κ)*Real.log (w*a^((-1 : ℝ)/κ)+(1-w)*b^((-1 : ℝ)/κ)))
      atTop (𝓝 (w*Real.log a+(1-w)*Real.log b)) := by
    convert hs.congr' he using 1 <;> ring
  have hlim := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hmean (κ : ℝ) : weightedPowerMean κ w a b =
      Real.exp ((-κ)*Real.log (w*a^((-1 : ℝ)/κ)+(1-w)*b^((-1 : ℝ)/κ))) := by
    rw [weightedPowerMean, Real.rpow_def_of_pos (weighted_power_base_positive ha hb hw)]
    congr 1
    ring
  have hresult : Real.exp (w*Real.log a+(1-w)*Real.log b) = a^w*b^(1-w) := by
    rw [Real.exp_add, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
    congr 1 <;> congr 1 <;> ring
  simpa only [Function.comp_def, ← hmean, hresult] using hlim

end ScalarMonotone.EndOfPaper
end
