import EndOfPaper.GaussianFiniteMaximumMoment
import EndOfPaper.GaussianMatrixJointCoefficients

/-!
The finite unit-pair Gaussian matrix moment comparison from actual disjoint coefficient arrays. All covariance assumptions are discharged from unit norms.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_matrix_unit_family_maximum_comparison {ι m n : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) {a : ℝ} (ha : 0 ≤ a) :
    gaussianFiniteMaxMoment (gaussianMatrixComparisonArray u v) a ≤
      gaussianFiniteMaxMoment (gaussianVectorComparisonArray u v) a := by
  exact gaussian_linear_finite_maximum_moment_comparison
    (gaussianMatrixComparisonArray u v) (gaussianVectorComparisonArray u v)
    (gaussian_matrix_comparison_array_cross u v) (gaussian_matrix_comparison_array_diagonal u v hu hv)
    (fun i j _ => gaussian_matrix_comparison_array_order u v hu hv i j) ha

end ScalarMonotone.EndOfPaper
end
