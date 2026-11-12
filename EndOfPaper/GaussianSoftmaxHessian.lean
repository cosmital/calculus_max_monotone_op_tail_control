import EndOfPaper.GaussianSoftmax

/-!
The actual coordinate Hessian and the sign of its covariance contraction, needed for the Gaussian maximum interpolation.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianSoftmaxHessian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a β : ℝ) (z : ι → ℝ) (i j : ι) : ℝ :=
  a*β*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i*(if i = j then 1 else 0)+
    a*(a-β)*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i*gaussianSoftmaxWeight β z j

theorem gaussian_softmax_hessian_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (a : ℝ) {β : ℝ} (hβ : β ≠ 0) (z : ι → ℝ) (i j : ι) :
    HasDerivAt (fun t : ℝ => gaussianSoftmaxGradient a β
      (fun k => z k+t*(if k = j then 1 else 0)) i) (gaussianSoftmaxHessian a β z i j) 0 := by
  have hz (k : ι) : HasDerivAt (fun t : ℝ => z k+t*(if k = j then 1 else 0))
      (if k = j then 1 else 0) 0 := by
    simpa only [id_eq,one_mul] using
      ((hasDerivAt_id 0).mul_const (if k = j then (1 : ℝ) else 0)).const_add (z k)
  have hh := gaussian_softmax_gradient_hasDerivAt hz a hβ i
  simpa [gaussianSoftmaxHessian] using hh

theorem gaussian_softmax_hessian_off_diagonal_nonpos {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {a β : ℝ} (ha : 0 ≤ a) (haβ : a ≤ β)
    (z : ι → ℝ) {i j : ι} (hij : i ≠ j) : gaussianSoftmaxHessian a β z i j ≤ 0 := by
  simpa only [gaussianSoftmaxHessian,if_neg hij,mul_zero,zero_add] using
    gaussian_softmax_off_diagonal_nonpos ha haβ z i j

theorem gaussian_softmax_covariance_contraction_nonpos {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {a β : ℝ} (ha : 0 ≤ a) (haβ : a ≤ β)
    (z : ι → ℝ) (D : ι → ι → ℝ) (hDiag : ∀ i, D i i = 0)
    (hOff : ∀ i j, i ≠ j → 0 ≤ D i j) :
    (∑ i, ∑ j, D i j*gaussianSoftmaxHessian a β z i j) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  apply Finset.sum_nonpos
  intro j hj
  by_cases hij : i = j
  · subst j
    rw [hDiag i,zero_mul]
  · exact mul_nonpos_of_nonneg_of_nonpos (hOff i j hij)
      (gaussian_softmax_hessian_off_diagonal_nonpos ha haβ z hij)

end ScalarMonotone.EndOfPaper
end
