import EndOfPaper.GaussianInterpolationDerivative

/-!
Explicit local velocity domination for the actual Gaussian comparison interpolation. All denominators are controlled inside the proved neighborhood.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianInterpolationVelocityMass {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (t : ℝ) : ℝ :=
  gaussianCoefficientMass A/(2*Real.sqrt (t/2))+
    gaussianCoefficientMass B/(2*Real.sqrt ((1-t)/2))

theorem gaussian_interpolation_velocity_mass_nonneg {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (t : ℝ) : 0 ≤ gaussianInterpolationVelocityMass A B t :=
  add_nonneg (div_nonneg (gaussian_coefficient_mass_nonneg A) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (div_nonneg (gaussian_coefficient_mass_nonneg B) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

theorem gaussian_interpolation_velocity_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hsA : t/2 ≤ s) (hsB : (1-t)/2 ≤ 1-s) (z : EuclideanSpace ℝ (Fin n)) (i : ι) :
    |gaussianInterpolationVelocity A B s z i| ≤ gaussianInterpolationVelocityMass A B t*‖z‖ := by
  have hDA : 0 < 2*Real.sqrt (t/2) := mul_pos (by norm_num) (Real.sqrt_pos.mpr (div_pos ht.1 (by norm_num)))
  have hDB : 0 < 2*Real.sqrt ((1-t)/2) :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr (div_pos (sub_pos.mpr ht.2) (by norm_num)))
  have hDAs : 2*Real.sqrt (t/2) ≤ 2*Real.sqrt s :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsA) (by norm_num)
  have hDBs : 2*Real.sqrt ((1-t)/2) ≤ 2*Real.sqrt (1-s) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsB) (by norm_num)
  have hA : |gaussianLinearProcess A z i| ≤ gaussianCoefficientMass A*‖z‖ :=
    (gaussian_linear_process_abs_le A z i).trans
      (mul_le_mul_of_nonneg_right (gaussian_coefficient_row_le A i) (norm_nonneg z))
  have hB : |gaussianLinearProcess B z i| ≤ gaussianCoefficientMass B*‖z‖ :=
    (gaussian_linear_process_abs_le B z i).trans
      (mul_le_mul_of_nonneg_right (gaussian_coefficient_row_le B i) (norm_nonneg z))
  have hQA : |gaussianLinearProcess A z i|/(2*Real.sqrt s) ≤
      (gaussianCoefficientMass A/(2*Real.sqrt (t/2)))*‖z‖ := by
    calc
      _ ≤ (gaussianCoefficientMass A*‖z‖)/(2*Real.sqrt s) :=
        div_le_div_of_nonneg_right hA (hDA.trans_le hDAs).le
      _ ≤ (gaussianCoefficientMass A*‖z‖)/(2*Real.sqrt (t/2)) :=
        div_le_div_of_nonneg_left (mul_nonneg (gaussian_coefficient_mass_nonneg A) (norm_nonneg z)) hDA hDAs
      _ = _ := by ring
  have hQB : |gaussianLinearProcess B z i|/(2*Real.sqrt (1-s)) ≤
      (gaussianCoefficientMass B/(2*Real.sqrt ((1-t)/2)))*‖z‖ := by
    calc
      _ ≤ (gaussianCoefficientMass B*‖z‖)/(2*Real.sqrt (1-s)) :=
        div_le_div_of_nonneg_right hB (hDB.trans_le hDBs).le
      _ ≤ (gaussianCoefficientMass B*‖z‖)/(2*Real.sqrt ((1-t)/2)) :=
        div_le_div_of_nonneg_left (mul_nonneg (gaussian_coefficient_mass_nonneg B) (norm_nonneg z)) hDB hDBs
      _ = _ := by ring
  calc
    _ ≤ |gaussianLinearProcess A z i/(2*Real.sqrt s)|+
        |gaussianLinearProcess B z i/(2*Real.sqrt (1-s))| := by
      simpa only [gaussianInterpolationVelocity,sub_eq_add_neg,abs_neg] using
        abs_add (gaussianLinearProcess A z i/(2*Real.sqrt s)) (-(gaussianLinearProcess B z i/(2*Real.sqrt (1-s))))
    _ = |gaussianLinearProcess A z i|/(2*Real.sqrt s)+
        |gaussianLinearProcess B z i|/(2*Real.sqrt (1-s)) := by
      rw [abs_div,abs_div,abs_of_nonneg (hDA.trans_le hDAs).le,abs_of_nonneg (hDB.trans_le hDBs).le]
    _ ≤ _ := by
      have hh := add_le_add hQA hQB
      simpa only [gaussianInterpolationVelocityMass,add_mul] using hh

end ScalarMonotone.EndOfPaper
end
