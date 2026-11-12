import EndOfPaper.GaussianInterpolationMonotonicity
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Order.Field

/-!
Pass the proved smooth Gaussian comparison to actual finite maxima. The uniform finite softmax error permits an ordinary scalar limit; no interchange of this limit with an expectation is assumed.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianFiniteMaxMoment {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A : ι → Fin n → ℝ) (a : ℝ) : ℝ :=
  ∫ z, Real.exp (a*gaussianFiniteMaximum (gaussianLinearProcess A (gaussianProductVector n z)))
    ∂gaussianProductMeasure n

theorem gaussian_linear_finite_maximum_continuous {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A : ι → Fin n → ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) => gaussianFiniteMaximum (gaussianLinearProcess A z)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => gaussian_linear_process_continuous A i)

theorem gaussian_linear_finite_maximum_bound {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A : ι → Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    gaussianFiniteMaximum (gaussianLinearProcess A z) ≤ gaussianCoefficientMass A*‖z‖ :=
  gaussian_finite_maximum_le _ (fun i => (le_abs_self _).trans
    ((gaussian_linear_process_abs_le A z i).trans
      (mul_le_mul_of_nonneg_right (gaussian_coefficient_row_le A i) (norm_nonneg z))))

theorem gaussian_linear_finite_maximum_exp_integrable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A : ι → Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun z => Real.exp (a*gaussianFiniteMaximum (gaussianLinearProcess A (gaussianProductVector n z))))
      (gaussianProductMeasure n) := by
  apply gaussian_product_exp_dominated_integrable
    (Real.continuous_exp.comp (continuous_const.mul (gaussian_linear_finite_maximum_continuous A))).measurable
    (C := 1) (K := a*gaussianCoefficientMass A)
  intro z
  rw [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_linear_finite_maximum_bound A z) ha

theorem gaussian_linear_finite_maximum_comparison_with_error {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) :
    gaussianFiniteMaxMoment A a ≤ Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*gaussianFiniteMaxMoment B a := by
  have hAExp := gaussian_linear_finite_maximum_exp_integrable A ha
  have hBExp := gaussian_linear_finite_maximum_exp_integrable B ha
  have hAI : Integrable (fun z => gaussianSoftmaxMoment a β (gaussianLinearProcess A (gaussianProductVector (n+1) z)))
      (gaussianProductMeasure (n+1)) := by
    simpa only [gaussian_interpolated_process_at_one] using
      gaussian_interpolated_softmax_integrable A B (t := 1)
        (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ha hβ
  have hBI : Integrable (fun z => gaussianSoftmaxMoment a β (gaussianLinearProcess B (gaussianProductVector (n+1) z)))
      (gaussianProductMeasure (n+1)) := by
    simpa only [gaussian_interpolated_process_at_zero] using
      gaussian_interpolated_softmax_integrable A B (t := 0)
        (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ha hβ
  have hLeft : gaussianFiniteMaxMoment A a ≤
      ∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess A (gaussianProductVector (n+1) z))
        ∂gaussianProductMeasure (n+1) := by
    apply integral_mono hAExp hAI
    intro z
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (gaussian_finite_maximum_le_softmax (gaussianLinearProcess A (gaussianProductVector (n+1) z)) hβ) ha)
  have hRight : (∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess B (gaussianProductVector (n+1) z))
      ∂gaussianProductMeasure (n+1)) ≤
      Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*gaussianFiniteMaxMoment B a := by
    calc
      _ ≤ ∫ z, Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
          Real.exp (a*gaussianFiniteMaximum (gaussianLinearProcess B (gaussianProductVector (n+1) z)))
          ∂gaussianProductMeasure (n+1) :=
        integral_mono hBI (hBExp.const_mul _) (fun z => gaussian_softmax_moment_bound _ ha hβ)
      _ = _ := integral_const_mul _ _
  exact hLeft.trans ((gaussian_linear_softmax_moment_comparison A B hCross hDiag hOff ha hβ haβ).trans hRight)

theorem gaussian_linear_finite_maximum_moment_comparison {ι : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ} (A B : ι → Fin (n+1) → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a : ℝ} (ha : 0 ≤ a) : gaussianFiniteMaxMoment A a ≤ gaussianFiniteMaxMoment B a := by
  have hZero : Tendsto (fun β : ℝ => a*Real.log (Fintype.card ι : ℝ)/β) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop _
  have hExp := (Real.continuous_exp.tendsto 0).comp hZero
  have hLimit : Tendsto (fun β : ℝ => Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*gaussianFiniteMaxMoment B a)
      atTop (𝓝 (gaussianFiniteMaxMoment B a)) := by
    simpa only [Real.exp_zero,one_mul] using hExp.mul_const (gaussianFiniteMaxMoment B a)
  have hUpper : ∀ᶠ β : ℝ in atTop, gaussianFiniteMaxMoment A a ≤
      Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*gaussianFiniteMaxMoment B a := by
    filter_upwards [eventually_gt_atTop (max a 0)] with β hβ
    exact gaussian_linear_finite_maximum_comparison_with_error A B hCross hDiag hOff ha
      (lt_of_le_of_lt (le_max_right a 0) hβ) ((le_max_left a 0).trans hβ.le)
  exact ge_of_tendsto hLimit hUpper

end ScalarMonotone.EndOfPaper
end
