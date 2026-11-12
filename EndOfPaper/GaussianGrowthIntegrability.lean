import EndOfPaper.GaussianFiniteMGF

/-!
Derived integrability for the actual exponential and polynomial growth appearing in Gaussian interpolation derivatives.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_norm_one_lipschitz {E : Type*} [SeminormedAddCommGroup E] :
    LipschitzWith 1 (fun x : E => ‖x‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using abs_norm_sub_norm_le x y

theorem gaussian_product_norm_exp_integrable (n : ℕ) (K : ℝ) :
    Integrable (fun z => Real.exp (K*‖gaussianProductVector n z‖)) (gaussianProductMeasure n) := by
  apply gaussian_product_exp_integrable (F := fun x : EuclideanSpace ℝ (Fin n) => K*‖x‖)
  exact gaussian_tilt_lipschitz (gaussian_norm_one_lipschitz (E := EuclideanSpace ℝ (Fin n))) K

theorem polynomial_times_norm_exponential_le (k : ℕ) (K : ℝ) {E : Type*}
    [SeminormedAddCommGroup E] (x : E) :
    ‖x‖^k*Real.exp (K*‖x‖) ≤ Real.exp ((K+(k : ℝ))*‖x‖) := by
  have hNorm : ‖x‖ ≤ Real.exp ‖x‖ := by linarith only [Real.add_one_le_exp ‖x‖]
  have hPow := pow_le_pow_left₀ (norm_nonneg x) hNorm k
  calc
    _ ≤ (Real.exp ‖x‖)^k*Real.exp (K*‖x‖) := mul_le_mul_of_nonneg_right hPow (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul,← Real.exp_add]; congr 1; ring

theorem gaussian_product_polynomial_exp_integrable (n k : ℕ) (K : ℝ) :
    Integrable (fun z => ‖gaussianProductVector n z‖^k*Real.exp (K*‖gaussianProductVector n z‖))
      (gaussianProductMeasure n) := by
  apply (gaussian_product_norm_exp_integrable n (K+(k : ℝ))).mono'
  · exact (((gaussian_product_vector_measurable n).norm.pow_const k).mul
      (((gaussian_product_vector_measurable n).norm.const_mul K).exp)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) k) (Real.exp_pos _).le)]
      exact polynomial_times_norm_exponential_le k K (gaussianProductVector n z))

theorem gaussian_product_exp_dominated_integrable {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Measurable g) {C K : ℝ}
    (hBound : ∀ x, ‖g x‖ ≤ C*Real.exp (K*‖x‖)) :
    Integrable (fun z => g (gaussianProductVector n z)) (gaussianProductMeasure n) := by
  apply ((gaussian_product_norm_exp_integrable n K).const_mul C).mono'
    (hg.comp (gaussian_product_vector_measurable n)).aestronglyMeasurable
  exact ae_of_all _ (fun z => hBound (gaussianProductVector n z))

end ScalarMonotone.EndOfPaper
end
