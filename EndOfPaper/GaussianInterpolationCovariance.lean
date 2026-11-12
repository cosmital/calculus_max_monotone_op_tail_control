import EndOfPaper.GaussianLinearProcess

/-!
Exact finite coefficient algebra in the Gaussian interpolation derivative. Orthogonality of the two input coefficient families removes every mixed term.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianInterpolationCovarianceWeight {ι : Type*} {n : ℕ} (A B : ι → Fin n → ℝ)
    (t : ℝ) (i j : ι) : ℝ :=
  (∑ k, A i k*(Real.sqrt t*A j k+Real.sqrt (1-t)*B j k))/(2*Real.sqrt t)-
    (∑ k, B i k*(Real.sqrt t*A j k+Real.sqrt (1-t)*B j k))/(2*Real.sqrt (1-t))

theorem gaussian_interpolation_covariance_weight {ι : Type*} {n : ℕ}
    (A B : ι → Fin n → ℝ) (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i j : ι) :
    gaussianInterpolationCovarianceWeight A B t i j =
      (gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)/2 := by
  have hBA : (∑ k, B i k*A j k) = 0 := by simpa only [mul_comm] using hCross j i
  have hA : (∑ k, A i k*(Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)) =
      Real.sqrt t*gaussianLinearCovariance A i j+Real.sqrt (1-t)*(∑ k, A i k*B j k) := by
    simp only [gaussianLinearCovariance,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hB : (∑ k, B i k*(Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)) =
      Real.sqrt t*(∑ k, B i k*A j k)+Real.sqrt (1-t)*gaussianLinearCovariance B i j := by
    simp only [gaussianLinearCovariance,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  unfold gaussianInterpolationCovarianceWeight
  simp only [hA,hB,hCross i j,hBA,mul_zero,add_zero,zero_add]
  have hT : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
  have hU : Real.sqrt (1-t) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr ht.2)).ne'
  field_simp [hT,hU]
  <;> ring

end ScalarMonotone.EndOfPaper
end
