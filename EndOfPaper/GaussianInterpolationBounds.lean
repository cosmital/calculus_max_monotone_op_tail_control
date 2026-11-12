import EndOfPaper.GaussianLinearProcess
import EndOfPaper.GaussianSoftmaxBounds
import EndOfPaper.GaussianSoftmaxApprox
import EndOfPaper.GaussianGrowthIntegrability

/-!
Derived deterministic growth and actual Gaussian integrability for the smooth comparison interpolation, uniformly over its closed parameter interval.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianCoefficientMass {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ k, |A i k|

theorem gaussian_coefficient_mass_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → ℝ) :
    0 ≤ gaussianCoefficientMass A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => abs_nonneg (A i k)))

theorem gaussian_coefficient_row_le {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → ℝ) (i : ι) :
    (∑ k, |A i k|) ≤ gaussianCoefficientMass A :=
  Finset.single_le_sum (f := fun j => ∑ k, |A j k|)
    (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg (A j k))) (Finset.mem_univ i)

theorem gaussian_interpolated_process_abs_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (z : EuclideanSpace ℝ (Fin n)) (i : ι) :
    |gaussianInterpolatedProcess A B t z i| ≤ (gaussianCoefficientMass A+gaussianCoefficientMass B)*‖z‖ := by
  have hS : Real.sqrt t ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith only [ht.2]⟩
  have hT : Real.sqrt (1-t) ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith only [ht.1]⟩
  calc
    _ ≤ Real.sqrt t*|gaussianLinearProcess A z i| + Real.sqrt (1-t)*|gaussianLinearProcess B z i| := by
      simpa only [gaussianInterpolatedProcess,abs_mul,abs_of_nonneg (Real.sqrt_nonneg t),
        abs_of_nonneg (Real.sqrt_nonneg (1-t))] using
        abs_add (Real.sqrt t*gaussianLinearProcess A z i) (Real.sqrt (1-t)*gaussianLinearProcess B z i)
    _ ≤ |gaussianLinearProcess A z i| + |gaussianLinearProcess B z i| :=
      add_le_add (mul_le_of_le_one_left (abs_nonneg _) hS) (mul_le_of_le_one_left (abs_nonneg _) hT)
    _ ≤ (∑ k, |A i k|)*‖z‖+(∑ k, |B i k|)*‖z‖ :=
      add_le_add (gaussian_linear_process_abs_le A z i) (gaussian_linear_process_abs_le B z i)
    _ = ((∑ k, |A i k|)+(∑ k, |B i k|))*‖z‖ := (add_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add (gaussian_coefficient_row_le A i)
      (gaussian_coefficient_row_le B i)) (norm_nonneg z)

theorem gaussian_interpolated_softmax_bound {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {t a β : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) (hβ : 0 < β)
    (z : EuclideanSpace ℝ (Fin n)) :
    gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t z) ≤
      Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
        Real.exp ((a*(gaussianCoefficientMass A+gaussianCoefficientMass B))*‖z‖) := by
  have hMax : gaussianFiniteMaximum (gaussianInterpolatedProcess A B t z) ≤
      (gaussianCoefficientMass A+gaussianCoefficientMass B)*‖z‖ :=
    gaussian_finite_maximum_le _ (fun i => (le_abs_self _).trans (gaussian_interpolated_process_abs_bound A B ht z i))
  calc
    _ ≤ Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
        Real.exp (a*gaussianFiniteMaximum (gaussianInterpolatedProcess A B t z)) :=
      gaussian_softmax_moment_bound _ ha hβ
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hMax ha

theorem gaussian_interpolated_softmax_measurable {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (t a β : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t z)) := by
  have hEach (i : ι) : Measurable (fun z : EuclideanSpace ℝ (Fin n) => gaussianInterpolatedProcess A B t z i) :=
    ((gaussian_linear_process_continuous A i).measurable.const_mul (Real.sqrt t)).add
      ((gaussian_linear_process_continuous B i).measurable.const_mul (Real.sqrt (1-t)))
  unfold gaussianSoftmaxMoment gaussianSoftmax gaussianExpSum
  fun_prop

theorem gaussian_interpolated_softmax_integrable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {t a β : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) (hβ : 0 < β) :
    Integrable (fun z => gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z)))
      (gaussianProductMeasure n) := by
  apply gaussian_product_exp_dominated_integrable (gaussian_interpolated_softmax_measurable A B t a β)
    (C := Real.exp (a*Real.log (Fintype.card ι : ℝ)/β))
    (K := a*(gaussianCoefficientMass A+gaussianCoefficientMass B))
  intro z
  rw [Real.norm_eq_abs,abs_of_pos (gaussian_softmax_moment_positive _ _ _)]
  exact gaussian_interpolated_softmax_bound A B ht ha hβ z

end ScalarMonotone.EndOfPaper
end
