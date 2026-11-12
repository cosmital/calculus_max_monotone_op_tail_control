import EndOfPaper.GaussianSoftmaxHessian

/-!
Explicit bounds for the actual smooth maximum derivatives, used to derive all domination and integrability in Gaussian interpolation.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_softmax_moment_positive {ι : Type*} [Fintype ι]
    (a β : ℝ) (z : ι → ℝ) : 0 < gaussianSoftmaxMoment a β z := Real.exp_pos _

theorem gaussian_softmax_weight_le_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (z : ι → ℝ) (i : ι) : gaussianSoftmaxWeight β z i ≤ 1 := by
  have hh := Finset.single_le_sum (s := Finset.univ) (f := gaussianSoftmaxWeight β z)
    (fun j _ => (gaussian_softmax_weight_positive β z j).le) (Finset.mem_univ i)
  rwa [gaussian_softmax_weight_sum] at hh

theorem gaussian_softmax_gradient_abs_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {a : ℝ} (ha : 0 ≤ a) (β : ℝ) (z : ι → ℝ) (i : ι) :
    |gaussianSoftmaxGradient a β z i| ≤ a*gaussianSoftmaxMoment a β z := by
  rw [gaussianSoftmaxGradient,abs_mul,abs_mul,abs_of_nonneg ha,
    abs_of_nonneg (gaussian_softmax_moment_positive a β z).le,
    abs_of_nonneg (gaussian_softmax_weight_positive β z i).le]
  exact mul_le_of_le_one_right (mul_nonneg ha (gaussian_softmax_moment_positive a β z).le)
    (gaussian_softmax_weight_le_one β z i)

theorem gaussian_softmax_hessian_abs_bound {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {a β : ℝ} (ha : 0 ≤ a) (haβ : a ≤ β)
    (z : ι → ℝ) (i j : ι) :
    |gaussianSoftmaxHessian a β z i j| ≤ 2*a*β*gaussianSoftmaxMoment a β z := by
  let H := gaussianSoftmaxMoment a β z
  let wi := gaussianSoftmaxWeight β z i
  let wj := gaussianSoftmaxWeight β z j
  have hH : 0 ≤ H := (gaussian_softmax_moment_positive a β z).le
  have hwi : 0 ≤ wi := (gaussian_softmax_weight_positive β z i).le
  have hwj : 0 ≤ wj := (gaussian_softmax_weight_positive β z j).le
  have hwi1 : wi ≤ 1 := gaussian_softmax_weight_le_one β z i
  have hwj1 : wj ≤ 1 := gaussian_softmax_weight_le_one β z j
  have hBase : 0 ≤ a*β*H := mul_nonneg (mul_nonneg ha (ha.trans haβ)) hH
  have hFirst : |a*β*H*wi*(if i = j then 1 else 0)| ≤ a*β*H := by
    by_cases hij : i = j
    · rw [if_pos hij,mul_one,abs_of_nonneg (mul_nonneg hBase hwi)]
      exact mul_le_of_le_one_right hBase hwi1
    · simpa only [if_neg hij,mul_zero,abs_zero] using hBase
  have hSecond : |a*(a-β)*H*wi*wj| ≤ a*β*H := by
    have hNeg : a*(a-β)*H*wi*wj ≤ 0 := gaussian_softmax_off_diagonal_nonpos ha haβ z i j
    rw [abs_of_nonpos hNeg]
    have hProd : wi*wj ≤ 1 := by
      calc
        _ ≤ 1*wj := mul_le_mul_of_nonneg_right hwi1 hwj
        _ ≤ 1 := by simpa only [one_mul] using hwj1
    have hCoeff : 0 ≤ a*(β-a)*H := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr haβ)) hH
    calc
      _ = (a*(β-a)*H)*(wi*wj) := by ring
      _ ≤ a*(β-a)*H := mul_le_of_le_one_right hCoeff hProd
      _ ≤ a*β*H := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_self β ha) ha) hH
  change |a*β*H*wi*(if i = j then 1 else 0)+a*(a-β)*H*wi*wj| ≤ 2*a*β*H
  calc
    _ ≤ |a*β*H*wi*(if i = j then 1 else 0)|+|a*(a-β)*H*wi*wj| := abs_add _ _
    _ ≤ a*β*H+a*β*H := add_le_add hFirst hSecond
    _ = _ := by ring

end ScalarMonotone.EndOfPaper
end
