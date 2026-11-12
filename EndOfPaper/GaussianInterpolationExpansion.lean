import EndOfPaper.GaussianInterpolationIBP
import EndOfPaper.GaussianInterpolationCovariance

/-!
Exact finite-sum expansion of the actual interpolation derivative integral. Every interchange uses the previously derived weighted-gradient integrability.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_interpolation_derivative_expansion {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    gaussianInterpolationDerivative A B a β t z =
      ∑ i, ∑ k, (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t z) i) := by
  unfold gaussianInterpolationDerivative gaussianInterpolationVelocity gaussianLinearProcess
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_div,mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem gaussian_interpolation_derivative_integral_expansion {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector n z) ∂gaussianProductMeasure n) =
      ∑ i, ∑ k, (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (∫ z, z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i
          ∂gaussianProductMeasure n) := by
  have hTerms (i : ι) (k : Fin n) : Integrable (fun z =>
      (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i))
      (gaussianProductMeasure n) :=
    (gaussian_interpolated_weighted_gradient_integrable A B ha hβ ht i k).const_mul _
  have hEach (i : ι) : Integrable (fun z => ∑ k,
      (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i))
      (gaussianProductMeasure n) := integrable_finset_sum Finset.univ (fun k _ => hTerms i k)
  calc
    _ = ∫ z, (∑ i, ∑ k, (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i))
        ∂gaussianProductMeasure n := by
      exact integral_congr_ae (ae_of_all _ (fun z => gaussian_interpolation_derivative_expansion A B a β t (gaussianProductVector n z)))
    _ = ∑ i, ∫ z, (∑ k, (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i))
        ∂gaussianProductMeasure n := integral_finset_sum Finset.univ (fun i _ => hEach i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum Finset.univ (fun k _ => hTerms i k)]
      simp only [integral_const_mul]

theorem gaussian_interpolation_gradient_coordinate_ibp_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ) {a β t : ℝ}
    (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) (ht : t ∈ Icc (0 : ℝ) 1) (i : ι) (k : Fin (n+1)) :
    (∫ z, z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i
      ∂gaussianProductMeasure (n+1)) =
      ∑ j, (Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)*
        (∫ z, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i j
          ∂gaussianProductMeasure (n+1)) := by
  rw [gaussian_interpolation_gradient_coordinate_ibp A B ha hβ haβ ht i k,
    integral_finset_sum Finset.univ (fun j _ =>
      (gaussian_interpolated_hessian_integrable A B ha hβ haβ ht i j).mul_const _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const]
  ring

theorem gaussian_interpolation_covariance_weight_eq_sum {ι : Type*} {n : ℕ}
    (A B : ι → Fin n → ℝ) (t : ℝ) (i j : ι) :
    gaussianInterpolationCovarianceWeight A B t i j =
      ∑ k, (A i k/(2*Real.sqrt t)-B i k/(2*Real.sqrt (1-t)))*
        (Real.sqrt t*A j k+Real.sqrt (1-t)*B j k) := by
  unfold gaussianInterpolationCovarianceWeight
  rw [Finset.sum_div,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem gaussian_interpolation_derivative_integral_covariance {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1)) =
      ∑ i, ∑ j, gaussianInterpolationCovarianceWeight A B t i j*
        (∫ z, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i j
          ∂gaussianProductMeasure (n+1)) := by
  rw [gaussian_interpolation_derivative_integral_expansion A B ha hβ ht]
  simp_rw [gaussian_interpolation_gradient_coordinate_ibp_sum A B ha hβ haβ ht]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [gaussian_interpolation_covariance_weight_eq_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem gaussian_interpolation_derivative_integral_orthogonal {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0) {a β t : ℝ}
    (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1)) =
      (1/2 : ℝ)*∑ i, ∑ j, (gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)*
        (∫ z, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i j
          ∂gaussianProductMeasure (n+1)) := by
  rw [gaussian_interpolation_derivative_integral_covariance A B ha hβ haβ ⟨ht.1.le,ht.2.le⟩]
  simp_rw [gaussian_interpolation_covariance_weight A B hCross ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end ScalarMonotone.EndOfPaper
end
