import EndOfPaper.GaussianNormMedian

/-!
The exact scalar normalization of the square Gaussian matrix median.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_matrix_median_normalization {d : ℝ} (hd : 0 < d) :
    (Real.sqrt 2+Real.sqrt (Real.log 2/d))*Real.sqrt (2*d) =
      Real.sqrt d+Real.sqrt d+Real.sqrt (2*Real.log 2) := by
  have hLog : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rw [add_mul,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_div hLog,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hdS : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  field_simp [hdS.ne']
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end ScalarMonotone.EndOfPaper
end
