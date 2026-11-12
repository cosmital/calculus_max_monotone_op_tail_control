import EndOfPaper.NetworkEqualWidth

/-!
Uniform dimension constants when the batch-to-width ratio is bounded.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_depth_prefactor_uniform (L N : ℕ) {d : ℕ} (hd : 0 < d)
    {c : ℝ} (hRatio : (N : ℝ)/(d : ℝ) ≤ c) :
    Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ)) ≤ Real.sqrt (1+c*(L : ℝ)/2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.sqrt_le_sqrt
  calc
    _ = 1/(d : ℝ)+((N : ℝ)/(d : ℝ))*(L : ℝ)/2 := by
      field_simp [hdR.ne'] <;> ring <;> simp
    _ ≤ 1+c*(L : ℝ)/2 := add_le_add ((div_le_one hdR).mpr hd1)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg L)) (by norm_num))

theorem network_depth_threshold_uniform (L : ℕ) {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {c M m A r : ℝ} (hRatio : (N : ℝ)/(d : ℝ) ≤ c)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hA : 0 ≤ A) (hr : 0 ≤ r) :
    A*Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ))*r*
      (m+A*r/Real.sqrt (((d*min N 2 : ℕ) : ℝ)))^L ≤
    A*Real.sqrt (1+c*(L : ℝ)/2)*r*(M+A*r/Real.sqrt (d : ℝ))^L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdim : d ≤ d*min N 2 := by
    have hh := Nat.mul_le_mul_left d (show 1 ≤ min N 2 by omega)
    simpa only [Nat.mul_one] using hh
  have hden : Real.sqrt (d : ℝ) ≤ Real.sqrt (((d*min N 2 : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hdim)
  have hinner0 : 0 ≤ m+A*r/Real.sqrt (((d*min N 2 : ℕ) : ℝ)) :=
    add_nonneg hm (div_nonneg (mul_nonneg hA hr) (Real.sqrt_nonneg _))
  have hinner : m+A*r/Real.sqrt (((d*min N 2 : ℕ) : ℝ)) ≤ M+A*r/Real.sqrt (d : ℝ) :=
    add_le_add hmM (div_le_div_of_nonneg_left (mul_nonneg hA hr) (Real.sqrt_pos.mpr hdR) hden)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (network_depth_prefactor_uniform L N hd hRatio) hA) hr
  · exact pow_le_pow_left₀ hinner0 hinner L
  · exact pow_nonneg hinner0 L
  · exact mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) hr

end ScalarMonotone.EndOfPaper
end
