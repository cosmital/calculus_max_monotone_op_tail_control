import EndOfPaper.GaussianMatrixCovariance
import EndOfPaper.GaussianLinearProcess
import Mathlib.Data.Fintype.EquivFin

/-!
Actual disjoint Gaussian coordinate arrays for the matrix maximum comparison, reindexed to the canonical finite Gaussian input.
-/

open Set
open scoped BigOperators InnerProductSpace
noncomputable section
namespace ScalarMonotone.EndOfPaper

abbrev GaussianMatrixJointIndex (m n : Type*) := Option (m × n) ⊕ (m ⊕ n)

def gaussianMatrixJointDimension (m n : Type*) [Fintype m] [Fintype n] : ℕ :=
  Fintype.card m*Fintype.card n+Fintype.card m+Fintype.card n

def gaussianMatrixJointCoefficient {m n : Type*} (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    GaussianMatrixJointIndex m n → ℝ
  | Sum.inl k => gaussianMatrixCoefficient u v k
  | Sum.inr _ => 0

def gaussianVectorJointCoefficient {m n : Type*} (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    GaussianMatrixJointIndex m n → ℝ
  | Sum.inl _ => 0
  | Sum.inr k => gaussianVectorComparisonCoefficient u v k

theorem gaussian_matrix_joint_index_card (m n : Type*) [Fintype m] [Fintype n] :
    Fintype.card (GaussianMatrixJointIndex m n) = gaussianMatrixJointDimension m n+1 := by
  simp only [GaussianMatrixJointIndex,gaussianMatrixJointDimension,Fintype.card_sum,Fintype.card_option,Fintype.card_prod]
  ring

def gaussianMatrixJointIndexEquiv (m n : Type*) [Fintype m] [Fintype n] :
    GaussianMatrixJointIndex m n ≃ Fin (gaussianMatrixJointDimension m n+1) :=
  Fintype.equivFinOfCardEq (gaussian_matrix_joint_index_card m n)

theorem gaussian_matrix_joint_covariance {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    (∑ k, gaussianMatrixJointCoefficient u v k*gaussianMatrixJointCoefficient u' v' k) =
      1+⟪u,u'⟫_ℝ * ⟪v,v'⟫_ℝ := by
  simpa only [Fintype.sum_sum_type,gaussianMatrixJointCoefficient,zero_mul,Finset.sum_const_zero,add_zero] using
    gaussian_matrix_coefficient_covariance u u' v v'

theorem gaussian_vector_joint_covariance {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    (∑ k, gaussianVectorJointCoefficient u v k*gaussianVectorJointCoefficient u' v' k) =
      ⟪u,u'⟫_ℝ+⟪v,v'⟫_ℝ := by
  simpa only [Fintype.sum_sum_type,gaussianVectorJointCoefficient,zero_mul,Finset.sum_const_zero,zero_add] using
    gaussian_vector_comparison_covariance u u' v v'

theorem gaussian_matrix_vector_joint_cross {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n) :
    (∑ k, gaussianMatrixJointCoefficient u v k*gaussianVectorJointCoefficient u' v' k) = 0 := by
  simp only [Fintype.sum_sum_type,gaussianMatrixJointCoefficient,gaussianVectorJointCoefficient,
    mul_zero,zero_mul,Finset.sum_const_zero,add_zero]

def gaussianRelabelCoefficients {ι κ : Type*} {p : ℕ} (e : κ ≃ Fin p) (A : ι → κ → ℝ) :
    ι → Fin p → ℝ := fun i k => A i (e.symm k)

theorem gaussian_relabel_pairing {ι κ : Type*} [Fintype κ] {p : ℕ} (e : κ ≃ Fin p)
    (A B : ι → κ → ℝ) (i j : ι) :
    (∑ k, gaussianRelabelCoefficients e A i k*gaussianRelabelCoefficients e B j k) =
      ∑ k : κ, A i k*B j k := by
  change (∑ k : Fin p, A i (e.symm k)*B j (e.symm k)) = _
  exact Fintype.sum_equiv e.symm _ _ (fun k => rfl)

def gaussianMatrixComparisonArray {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n) :
    ι → Fin (gaussianMatrixJointDimension m n+1) → ℝ :=
  gaussianRelabelCoefficients (gaussianMatrixJointIndexEquiv m n) (fun i => gaussianMatrixJointCoefficient (u i) (v i))

def gaussianVectorComparisonArray {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n) :
    ι → Fin (gaussianMatrixJointDimension m n+1) → ℝ :=
  gaussianRelabelCoefficients (gaussianMatrixJointIndexEquiv m n) (fun i => gaussianVectorJointCoefficient (u i) (v i))

theorem gaussian_matrix_comparison_array_cross {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n) (i j : ι) :
    (∑ k, gaussianMatrixComparisonArray u v i k*gaussianVectorComparisonArray u v j k) = 0 := by
  unfold gaussianMatrixComparisonArray gaussianVectorComparisonArray
  rw [gaussian_relabel_pairing]
  exact gaussian_matrix_vector_joint_cross (u i) (u j) (v i) (v j)

theorem gaussian_matrix_comparison_array_covariance {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n) (i j : ι) :
    gaussianLinearCovariance (gaussianMatrixComparisonArray u v) i j =
      1+⟪u i,u j⟫_ℝ * ⟪v i,v j⟫_ℝ := by
  unfold gaussianLinearCovariance gaussianMatrixComparisonArray
  rw [gaussian_relabel_pairing]
  exact gaussian_matrix_joint_covariance (u i) (u j) (v i) (v j)

theorem gaussian_vector_comparison_array_covariance {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n) (i j : ι) :
    gaussianLinearCovariance (gaussianVectorComparisonArray u v) i j =
      ⟪u i,u j⟫_ℝ+⟪v i,v j⟫_ℝ := by
  unfold gaussianLinearCovariance gaussianVectorComparisonArray
  rw [gaussian_relabel_pairing]
  exact gaussian_vector_joint_covariance (u i) (u j) (v i) (v j)

theorem gaussian_matrix_comparison_array_diagonal {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (i : ι) :
    gaussianLinearCovariance (gaussianMatrixComparisonArray u v) i i =
      gaussianLinearCovariance (gaussianVectorComparisonArray u v) i i := by
  simp only [gaussian_matrix_comparison_array_covariance,gaussian_vector_comparison_array_covariance,
    real_inner_self_eq_norm_sq,hu i,hv i]
  norm_num

theorem gaussian_matrix_comparison_array_order {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (i j : ι) :
    gaussianLinearCovariance (gaussianVectorComparisonArray u v) i j ≤
      gaussianLinearCovariance (gaussianMatrixComparisonArray u v) i j := by
  rw [gaussian_matrix_comparison_array_covariance,gaussian_vector_comparison_array_covariance]
  have hh := gaussian_matrix_comparison_covariance_nonneg (u i) (u j) (v i) (v j) (hu i) (hu j) (hv i) (hv j)
  rw [gaussian_matrix_coefficient_covariance,gaussian_vector_comparison_covariance] at hh
  exact sub_nonneg.mp hh

end ScalarMonotone.EndOfPaper
end
