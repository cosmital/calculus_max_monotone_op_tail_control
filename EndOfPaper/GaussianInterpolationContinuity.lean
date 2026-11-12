import EndOfPaper.GaussianInterpolationBounds

/-!
Actual continuity of the Gaussian interpolation expectation, including both endpoints, with domination derived from the coefficient arrays.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianInterpolationMoment {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) : ℝ :=
  ∫ z, gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t (gaussianProductVector n z))
    ∂gaussianProductMeasure n

theorem gaussian_interpolated_softmax_continuous {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun t : ℝ => gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t z)) := by
  have hEach (i : ι) : Continuous (fun t : ℝ => gaussianInterpolatedProcess A B t z i) :=
    (Real.continuous_sqrt.mul continuous_const).add
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).mul continuous_const)
  have hSum : Continuous (fun t : ℝ => gaussianExpSum β (gaussianInterpolatedProcess A B t z)) := by
    unfold gaussianExpSum
    fun_prop
  have hLog := hSum.log (fun t => (gaussian_exp_sum_positive β (gaussianInterpolatedProcess A B t z)).ne')
  simpa only [gaussianSoftmaxMoment,gaussianSoftmax] using
    Real.continuous_exp.comp (continuous_const.mul (hLog.div_const β))

theorem gaussian_interpolation_moment_continuousOn {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    ContinuousOn (gaussianInterpolationMoment A B a β) (Icc (0 : ℝ) 1) := by
  let C := Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)
  let K := a*(gaussianCoefficientMass A+gaussianCoefficientMass B)
  apply continuousOn_of_dominated
    (bound := fun z => C*Real.exp (K*‖gaussianProductVector n z‖))
  · intro t ht
    exact ((gaussian_interpolated_softmax_measurable A B t a β).comp
      (gaussian_product_vector_measurable n)).aestronglyMeasurable
  · intro t ht
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_pos (gaussian_softmax_moment_positive _ _ _)]
      exact gaussian_interpolated_softmax_bound A B ht ha hβ (gaussianProductVector n z))
  · exact (gaussian_product_norm_exp_integrable n K).const_mul C
  · exact ae_of_all _ (fun z =>
      (gaussian_interpolated_softmax_continuous A B a β (gaussianProductVector n z)).continuousOn)

end ScalarMonotone.EndOfPaper
end
