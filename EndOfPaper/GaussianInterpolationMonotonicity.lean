import EndOfPaper.GaussianInterpolationExpansion
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Genuine Gaussian interpolation monotonicity from the actual integral derivative and coordinate IBP, with all L1 conditions derived.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_interpolation_hessian_covariance_integral {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin n → ℝ)
    {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ z, (∑ i, ∑ j, (gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)*
      gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i j)
      ∂gaussianProductMeasure n) =
      ∑ i, ∑ j, (gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)*
        (∫ z, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i j
          ∂gaussianProductMeasure n) := by
  have hTerms (i j : ι) : Integrable (fun z => (gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)*
      gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) i j)
      (gaussianProductMeasure n) := (gaussian_interpolated_hessian_integrable A B ha hβ haβ ht i j).const_mul _
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hTerms i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum Finset.univ (fun j _ => hTerms i j)]
  simp only [integral_const_mul]

theorem gaussian_interpolation_derivative_integral_nonpos {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector (n+1) z)
      ∂gaussianProductMeasure (n+1)) ≤ 0 := by
  rw [gaussian_interpolation_derivative_integral_orthogonal A B hCross ha hβ haβ ht]
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← gaussian_interpolation_hessian_covariance_integral A B ha hβ haβ ⟨ht.1.le,ht.2.le⟩]
  apply integral_nonpos_of_ae
  exact ae_of_all _ (fun z => gaussian_softmax_covariance_contraction_nonpos ha haβ
    (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z))
    (fun i j => gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)
    (fun i => by
      change gaussianLinearCovariance A i i-gaussianLinearCovariance B i i = 0
      rw [hDiag i,sub_self]) (fun i j hij => sub_nonneg.mpr (hOff i j hij)))

theorem gaussian_interpolation_moment_antitoneOn {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) :
    AntitoneOn (gaussianInterpolationMoment A B a β) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
    (gaussian_interpolation_moment_continuousOn A B ha hβ)
    (f' := fun t => ∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector (n+1) z)
      ∂gaussianProductMeasure (n+1))
  · intro t ht
    have hti : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
    exact (gaussian_interpolation_moment_hasDerivAt A B ha hβ hti).2.hasDerivWithinAt
  · intro t ht
    have hti : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
    exact gaussian_interpolation_derivative_integral_nonpos A B hCross hDiag hOff ha hβ haβ hti

theorem gaussian_interpolated_process_at_zero {ι : Type*} {n : ℕ}
    (A B : ι → Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    gaussianInterpolatedProcess A B 0 z = gaussianLinearProcess B z := by
  funext i
  simp only [gaussianInterpolatedProcess,Real.sqrt_zero,sub_zero,Real.sqrt_one,zero_mul,one_mul,zero_add]

theorem gaussian_interpolated_process_at_one {ι : Type*} {n : ℕ}
    (A B : ι → Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    gaussianInterpolatedProcess A B 1 z = gaussianLinearProcess A z := by
  funext i
  simp only [gaussianInterpolatedProcess,Real.sqrt_one,sub_self,Real.sqrt_zero,one_mul,zero_mul,add_zero]

theorem gaussian_linear_softmax_moment_comparison {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) :
    (∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess A (gaussianProductVector (n+1) z))
      ∂gaussianProductMeasure (n+1)) ≤
      ∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess B (gaussianProductVector (n+1) z))
        ∂gaussianProductMeasure (n+1) := by
  have hAnti := gaussian_interpolation_moment_antitoneOn A B hCross hDiag hOff ha hβ haβ
  have hh : gaussianInterpolationMoment A B a β 1 ≤ gaussianInterpolationMoment A B a β 0 :=
    hAnti (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) (by norm_num)
  have hAtOne : gaussianInterpolationMoment A B a β 1 =
      ∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess A (gaussianProductVector (n+1) z))
        ∂gaussianProductMeasure (n+1) := by
    unfold gaussianInterpolationMoment
    apply integral_congr_ae
    exact ae_of_all _ (fun z => congrArg (gaussianSoftmaxMoment a β)
      (gaussian_interpolated_process_at_one A B (gaussianProductVector (n+1) z)))
  have hAtZero : gaussianInterpolationMoment A B a β 0 =
      ∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess B (gaussianProductVector (n+1) z))
        ∂gaussianProductMeasure (n+1) := by
    unfold gaussianInterpolationMoment
    apply integral_congr_ae
    exact ae_of_all _ (fun z => congrArg (gaussianSoftmaxMoment a β)
      (gaussian_interpolated_process_at_zero A B (gaussianProductVector (n+1) z)))
  rw [hAtOne,hAtZero] at hh
  exact hh

end ScalarMonotone.EndOfPaper
end
