import EndOfPaper.GaussianMatrixFiniteComparison
import EndOfPaper.GaussianMatrixJointMoments

/-!
The finite family matrix exponential moment with the exact dimensional constant, using actual Gaussian blocks and proved independence.
-/

open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_matrix_finite_family_moment {ι m n : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, Real.exp (a*gaussianFiniteMaximum (fun i =>
      ⟪u i,hsMatrixOp (gaussianJointMatrix z) (v i)⟫_ℝ+gaussianJointScalar z))
      ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ≤
      Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2) := by
  have hFamily := gaussian_matrix_unit_family_maximum_comparison u v hu hv ha
  have hNormSum := gaussian_joint_vector_norm_sum_mgf (m := m) (n := n) ha
  have hExpB := gaussian_linear_finite_maximum_exp_integrable (gaussianVectorComparisonArray u v) ha
  have hCompare : gaussianFiniteMaxMoment (gaussianVectorComparisonArray u v) a ≤
      (∫ z, Real.exp (a*(‖gaussianJointLeftVector (m := m) (n := n) z‖+‖gaussianJointRightVector z‖))
        ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
    apply integral_mono hExpB hNormSum.1
    intro z
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ha
    apply gaussian_finite_maximum_le
    intro i
    rw [gaussian_joint_vector_process]
    have hLeft := real_inner_le_norm (gaussianJointLeftVector (m := m) (n := n) z) (u i)
    have hRight := real_inner_le_norm (gaussianJointRightVector (m := m) (n := n) z) (v i)
    simpa only [hu i,hv i,mul_one] using add_le_add hLeft hRight
  have hProcess (z) :
      gaussianLinearProcess (gaussianMatrixComparisonArray u v)
        (gaussianProductVector (gaussianMatrixJointDimension m n+1) z) =
      fun i => ⟪u i,hsMatrixOp (gaussianJointMatrix z) (v i)⟫_ℝ+gaussianJointScalar z :=
    funext (gaussian_joint_matrix_process u v z)
  have hMoment : (∫ z, Real.exp (a*gaussianFiniteMaximum (fun i =>
      ⟪u i,hsMatrixOp (gaussianJointMatrix z) (v i)⟫_ℝ+gaussianJointScalar z))
        ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) =
      gaussianFiniteMaxMoment (gaussianMatrixComparisonArray u v) a := by
    unfold gaussianFiniteMaxMoment
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hProcess]
  rw [hMoment]
  exact hFamily.trans (hCompare.trans hNormSum.2)

end ScalarMonotone.EndOfPaper
end
