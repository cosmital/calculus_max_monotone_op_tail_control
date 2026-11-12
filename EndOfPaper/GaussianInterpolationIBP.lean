import EndOfPaper.GaussianInterpolationDomination
import EndOfPaper.GaussianCoordinateIBP

/-!
Actual coordinate Gaussian integration by parts for the smooth comparison gradient, with measurability and every L1 condition derived from the arrays.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_interpolated_gradient_measurable {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) (i : ι) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) => gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t z) i) := by
  unfold gaussianSoftmaxGradient gaussianSoftmaxMoment gaussianSoftmax gaussianSoftmaxWeight gaussianExpSum
    gaussianInterpolatedProcess gaussianLinearProcess
  fun_prop

theorem gaussian_interpolated_hessian_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) (i j : ι) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) => gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t z) i j) := by
  unfold gaussianSoftmaxHessian gaussianSoftmaxMoment gaussianSoftmax gaussianSoftmaxWeight gaussianExpSum
    gaussianInterpolatedProcess gaussianLinearProcess
  fun_prop

theorem gaussian_interpolated_gradient_integrable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (ht : t ∈ Icc (0 : ℝ) 1) (i : ι) :
    Integrable (fun z => gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i)
      (gaussianProductMeasure n) := by
  apply gaussian_product_exp_dominated_integrable (gaussian_interpolated_gradient_measurable A B a β t i)
    (C := a*Real.exp (a*Real.log (Fintype.card ι : ℝ)/β))
    (K := a*(gaussianCoefficientMass A+gaussianCoefficientMass B))
  intro z
  rw [Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left (gaussian_interpolated_softmax_bound A B ht ha hβ z) ha
  exact (gaussian_softmax_gradient_abs_bound ha β _ i).trans (by simpa only [mul_assoc] using hh)

theorem gaussian_interpolated_hessian_integrable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β)
    (ht : t ∈ Icc (0 : ℝ) 1) (i j : ι) :
    Integrable (fun z => gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i j)
      (gaussianProductMeasure n) := by
  apply gaussian_product_exp_dominated_integrable (gaussian_interpolated_hessian_measurable A B a β t i j)
    (C := (2*a*β)*Real.exp (a*Real.log (Fintype.card ι : ℝ)/β))
    (K := a*(gaussianCoefficientMass A+gaussianCoefficientMass B))
  intro z
  rw [Real.norm_eq_abs]
  have hCoeff : 0 ≤ 2*a*β := mul_nonneg (mul_nonneg (by norm_num) ha) hβ.le
  have hh := mul_le_mul_of_nonneg_left (gaussian_interpolated_softmax_bound A B ht ha hβ z) hCoeff
  exact (gaussian_softmax_hessian_abs_bound ha haβ _ i j).trans (by simpa only [mul_assoc] using hh)

theorem gaussian_interpolated_weighted_gradient_integrable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (ht : t ∈ Icc (0 : ℝ) 1)
    (i : ι) (k : Fin n) :
    Integrable (fun z => z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i)
      (gaussianProductMeasure n) := by
  have hDom := (gaussian_product_polynomial_exp_integrable n 1
    (a*(gaussianCoefficientMass A+gaussianCoefficientMass B))).const_mul
      (a*Real.exp (a*Real.log (Fintype.card ι : ℝ)/β))
  apply hDom.mono'
  · exact ((measurable_pi_apply k).mul
      ((gaussian_interpolated_gradient_measurable A B a β t i).comp
        (gaussian_product_vector_measurable n))).aestronglyMeasurable
  · refine ae_of_all _ (fun z => ?_)
    rw [Real.norm_eq_abs,abs_mul]
    have hCoord : |z k| ≤ ‖gaussianProductVector n z‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gaussianProductVector n z) k
    have hGrad := gaussian_softmax_gradient_abs_bound ha β
      (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i
    have hMoment := gaussian_interpolated_softmax_bound A B ht ha hβ (gaussianProductVector n z)
    calc
      _ ≤ ‖gaussianProductVector n z‖*
          (a*gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z))) :=
        mul_le_mul hCoord hGrad (abs_nonneg _) (norm_nonneg _)
      _ ≤ ‖gaussianProductVector n z‖*(a*(Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
          Real.exp ((a*(gaussianCoefficientMass A+gaussianCoefficientMass B))*‖gaussianProductVector n z‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMoment ha) (norm_nonneg _)
      _ = _ := by rw [pow_one]; ring

theorem gaussian_interpolation_gradient_coordinate_ibp {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ) {a β t : ℝ}
    (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) (ht : t ∈ Icc (0 : ℝ) 1) (i : ι) (k : Fin (n+1)) :
    (∫ z, z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i
      ∂gaussianProductMeasure (n+1)) =
      ∫ z, (∑ j, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i j*
        (Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)) ∂gaussianProductMeasure (n+1) := by
  have hDMeas : Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)) =>
      ∑ j, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t z) i j*
        (Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)) := by
    have hEach (j : ι) := gaussian_interpolated_hessian_measurable A B a β t i j
    fun_prop
  have hDInt : Integrable (fun z =>
      ∑ j, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i j*
        (Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)) (gaussianProductMeasure (n+1)) :=
    integrable_finset_sum Finset.univ (fun j _ =>
      (gaussian_interpolated_hessian_integrable A B ha hβ haβ ht i j).mul_const _)
  apply gaussian_product_coordinate_integration_by_parts k
    (gaussian_interpolated_gradient_measurable A B a β t i) hDMeas
  · intro z s
    exact gaussian_softmax_gradient_path_derivative
      (fun j => gaussian_interpolated_process_replace_derivative A B t z k j s) a hβ.ne' i
  · exact gaussian_interpolated_gradient_integrable A B ha hβ ht i
  · exact hDInt
  · exact gaussian_interpolated_weighted_gradient_integrable A B ha hβ ht i k

end ScalarMonotone.EndOfPaper
end
