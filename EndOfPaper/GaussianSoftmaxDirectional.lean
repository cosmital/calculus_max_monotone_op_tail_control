import EndOfPaper.GaussianSoftmaxHessian

/-!
Explicit contractions of the actual gradient and Hessian along arbitrary coordinate paths.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_softmax_hessian_directional_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a β : ℝ) (z d : ι → ℝ) (i : ι) :
    (∑ j, gaussianSoftmaxHessian a β z i j*d j) =
      a*β*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i*d i+
        a*(a-β)*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i*
          (∑ j, gaussianSoftmaxWeight β z j*d j) := by
  simp only [gaussianSoftmaxHessian,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_pos]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem gaussian_softmax_moment_path_derivative {ι : Type*}
    [Fintype ι] [Nonempty ι] {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ}
    (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x) (a : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    HasDerivAt (fun t => gaussianSoftmaxMoment a β (z t))
      (∑ i, gaussianSoftmaxGradient a β (z x) i*d i) x := by
  have hh := gaussian_softmax_moment_hasDerivAt hz a hβ
  convert hh using 1
  simp only [gaussianSoftmaxGradient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gaussian_softmax_gradient_path_derivative {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ}
    (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x) (a : ℝ) {β : ℝ} (hβ : β ≠ 0) (i : ι) :
    HasDerivAt (fun t => gaussianSoftmaxGradient a β (z t) i)
      (∑ j, gaussianSoftmaxHessian a β (z x) i j*d j) x := by
  rw [gaussian_softmax_hessian_directional_sum]
  exact gaussian_softmax_gradient_hasDerivAt hz a hβ i

end ScalarMonotone.EndOfPaper
end
