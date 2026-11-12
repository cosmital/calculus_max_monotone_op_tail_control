import EndOfPaper.HSMatrixOperator

/-!
Actual coefficient arrays in the Gaussian matrix maximum comparison, with exact covariance difference and equal unit-pair variances.
-/

open Set
open scoped BigOperators InnerProductSpace
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianMatrixCoefficient {m n : Type*} (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    Option (m × n) → ℝ
  | none => 1
  | some p => u p.1*v p.2

def gaussianVectorComparisonCoefficient {m n : Type*} (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    m ⊕ n → ℝ := Sum.elim (fun i => u i) (fun j => v j)

theorem gaussian_real_euclidean_inner {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ ι) :
    ⟪u,v⟫_ℝ = ∑ i, u i*v i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gaussian_matrix_coefficient_covariance {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    (∑ k, gaussianMatrixCoefficient u v k*gaussianMatrixCoefficient u' v' k) =
      1+⟪u,u'⟫_ℝ * ⟪v,v'⟫_ℝ := by
  rw [gaussian_real_euclidean_inner,gaussian_real_euclidean_inner]
  calc
    _ = 1+∑ i, ∑ j, (u i*v j)*(u' i*v' j) := by
      simp only [Fintype.sum_option,Fintype.sum_prod_type,gaussianMatrixCoefficient,one_mul]
    _ = _ := by
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem gaussian_vector_comparison_covariance {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    (∑ k, gaussianVectorComparisonCoefficient u v k*gaussianVectorComparisonCoefficient u' v' k) =
      ⟪u,u'⟫_ℝ+⟪v,v'⟫_ℝ := by
  rw [gaussian_real_euclidean_inner,gaussian_real_euclidean_inner]
  simp only [Fintype.sum_sum_type,gaussianVectorComparisonCoefficient,Sum.elim_inl,Sum.elim_inr]

theorem gaussian_matrix_comparison_covariance_difference {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    (∑ k, gaussianMatrixCoefficient u v k*gaussianMatrixCoefficient u' v' k)-
      (∑ k, gaussianVectorComparisonCoefficient u v k*gaussianVectorComparisonCoefficient u' v' k) =
      (1-⟪u,u'⟫_ℝ)*(1-⟪v,v'⟫_ℝ) := by
  rw [gaussian_matrix_coefficient_covariance,gaussian_vector_comparison_covariance]
  ring

theorem gaussian_matrix_comparison_covariance_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    0 ≤ (∑ k, gaussianMatrixCoefficient u v k*gaussianMatrixCoefficient u' v' k)-
      (∑ k, gaussianVectorComparisonCoefficient u v k*gaussianVectorComparisonCoefficient u' v' k) := by
  rw [gaussian_matrix_comparison_covariance_difference]
  have hU : ⟪u,u'⟫_ℝ ≤ 1 := by simpa only [hu,hu',one_mul] using real_inner_le_norm u u'
  have hV : ⟪v,v'⟫_ℝ ≤ 1 := by simpa only [hv,hv',one_mul] using real_inner_le_norm v v'
  exact mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hV)

theorem gaussian_matrix_comparison_variances {m n : Type*} [Fintype m] [Fintype n]
    (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∑ k, (gaussianMatrixCoefficient u v k)^2) = 2 ∧
      (∑ k, (gaussianVectorComparisonCoefficient u v k)^2) = 2 := by
  have hU : ⟪u,u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have hV : ⟪v,v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,hv]; norm_num
  constructor
  · have hh := gaussian_matrix_coefficient_covariance u u v v
    norm_num only [hU,hV,one_mul] at hh
    simpa only [pow_two] using hh
  · have hh := gaussian_vector_comparison_covariance u u v v
    norm_num only [hU,hV] at hh
    simpa only [pow_two] using hh

end ScalarMonotone.EndOfPaper
end
