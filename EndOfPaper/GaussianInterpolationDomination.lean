import EndOfPaper.GaussianInterpolationVelocity

/-!
A proved local integrable dominant for the actual interpolation derivative, and the resulting genuine differentiation-under-integral identity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianInterpolationDominant {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
    ((Fintype.card ι : ℝ)*a*gaussianInterpolationVelocityMass A B t))*
      (‖z‖*Real.exp ((a*(gaussianCoefficientMass A+gaussianCoefficientMass B))*‖z‖))

theorem gaussian_interpolation_derivative_measurable {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) :
    Measurable (gaussianInterpolationDerivative A B a β t) := by
  unfold gaussianInterpolationDerivative gaussianSoftmaxGradient gaussianSoftmaxMoment gaussianSoftmax
    gaussianSoftmaxWeight gaussianExpSum gaussianInterpolationVelocity gaussianInterpolatedProcess gaussianLinearProcess
  fun_prop

theorem gaussian_interpolation_dominant_integrable {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) :
    Integrable (fun z => gaussianInterpolationDominant A B a β t (gaussianProductVector n z))
      (gaussianProductMeasure n) := by
  have hh := (gaussian_product_polynomial_exp_integrable n 1
    (a*(gaussianCoefficientMass A+gaussianCoefficientMass B))).const_mul
      (Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
        ((Fintype.card ι : ℝ)*a*gaussianInterpolationVelocityMass A B t))
  simpa only [gaussianInterpolationDominant,pow_one] using hh

theorem gaussian_interpolation_derivative_local_bound {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β t s : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Metric.ball t (min (t/2) ((1-t)/2)))
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖gaussianInterpolationDerivative A B a β s z‖ ≤ gaussianInterpolationDominant A B a β t z := by
  have hS := (gaussian_interpolation_neighborhood ht).2 s hs
  have hH := gaussian_interpolated_softmax_bound A B ⟨hS.1.1.le,hS.1.2.le⟩ ha hβ z
  have hHpos := (gaussian_softmax_moment_positive a β (gaussianInterpolatedProcess A B s z)).le
  have hVel (i : ι) := gaussian_interpolation_velocity_bound A B ht hS.2.1 hS.2.2 z i
  have hEach (i : ι) :
      |gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B s z) i*
          gaussianInterpolationVelocity A B s z i| ≤
        (a*gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B s z))*
          (gaussianInterpolationVelocityMass A B t*‖z‖) := by
    rw [abs_mul]
    exact mul_le_mul (gaussian_softmax_gradient_abs_bound ha β _ i) (hVel i)
      (abs_nonneg _) (mul_nonneg ha hHpos)
  have hCoeff : 0 ≤ (Fintype.card ι : ℝ)*a*gaussianInterpolationVelocityMass A B t*‖z‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha)
      (gaussian_interpolation_velocity_mass_nonneg A B t)) (norm_nonneg z)
  rw [Real.norm_eq_abs,gaussianInterpolationDerivative]
  calc
    _ ≤ ∑ i, |gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B s z) i*
        gaussianInterpolationVelocity A B s z i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, (a*gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B s z))*
        (gaussianInterpolationVelocityMass A B t*‖z‖) := Finset.sum_le_sum (fun i _ => hEach i)
    _ = ((Fintype.card ι : ℝ)*a*gaussianInterpolationVelocityMass A B t*‖z‖)*
        gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B s z) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card ι : ℝ)*a*gaussianInterpolationVelocityMass A B t*‖z‖)*
        (Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
          Real.exp ((a*(gaussianCoefficientMass A+gaussianCoefficientMass B))*‖z‖)) :=
      mul_le_mul_of_nonneg_left hH hCoeff
    _ = _ := by unfold gaussianInterpolationDominant; ring

theorem gaussian_interpolation_moment_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun z => gaussianInterpolationDerivative A B a β t (gaussianProductVector n z))
        (gaussianProductMeasure n) ∧
      HasDerivAt (gaussianInterpolationMoment A B a β)
        (∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector n z) ∂gaussianProductMeasure n) t := by
  have hN := gaussian_interpolation_neighborhood ht
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianProductMeasure n) (x₀ := t) (ε := min (t/2) ((1-t)/2))
    (F := fun s z => gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B s (gaussianProductVector n z)))
    (F' := fun s z => gaussianInterpolationDerivative A B a β s (gaussianProductVector n z))
    (bound := fun z => gaussianInterpolationDominant A B a β t (gaussianProductVector n z)) hN.1
  · exact Filter.Eventually.of_forall (fun s =>
      ((gaussian_interpolated_softmax_measurable A B s a β).comp
        (gaussian_product_vector_measurable n)).aestronglyMeasurable)
  · exact gaussian_interpolated_softmax_integrable A B ⟨ht.1.le,ht.2.le⟩ ha hβ
  · exact ((gaussian_interpolation_derivative_measurable A B a β t).comp
      (gaussian_product_vector_measurable n)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => fun s hs => gaussian_interpolation_derivative_local_bound A B ha hβ ht hs
      (gaussianProductVector n z))
  · exact gaussian_interpolation_dominant_integrable A B a β t
  · exact ae_of_all _ (fun z => fun s hs => gaussian_interpolated_softmax_hasDerivAt A B a hβ.ne'
      (hN.2 s hs).1 (gaussianProductVector n z))

end ScalarMonotone.EndOfPaper
end
