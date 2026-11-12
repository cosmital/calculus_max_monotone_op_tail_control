import EndOfPaper.GaussianSquareLaplace
import Mathlib.Probability.Integration

/-!
Actual independent Gaussian coordinate sums of squares, without assumed chi-square moment formulas or concentration bounds.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem independent_real_finset_product {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hInt : ∀ i, Integrable (X i) μ)
    (s : Finset ι) :
    Integrable (∏ i ∈ s, X i) μ ∧
      (∫ ω, (∏ i ∈ s, X i) ω ∂μ) = ∏ i ∈ s, ∫ ω, X i ω ∂μ := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨integrable_const (1 : ℝ),by simp⟩
  | cons j s hj ih =>
    have hInd := (hi.indepFun_finset_prod_of_not_mem hm hj).symm
    simp only [Finset.prod_cons]
    exact ⟨hInd.integrable_mul (hInt j) ih.1,
      (hInd.integral_mul_of_integrable (hInt j) ih.1).trans (congrArg ((∫ ω, X j ω ∂μ)*·) ih.2)⟩

theorem gaussian_square_sum_laplace {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 1) {t : ℝ} (ht : t < 1/2) :
    Integrable (fun ω => Real.exp (t*(∑ i, (X i ω)^2))) μ ∧
      (∫ ω, Real.exp (t*(∑ i, (X i ω)^2)) ∂μ) =
        ((Real.sqrt (1-2*t))⁻¹)^(Fintype.card ι) := by
  classical
  let f := fun x : ℝ => Real.exp (t*x^2)
  have hfm : Measurable f := by fun_prop
  have hfi (i : ι) : Integrable (f ∘ X i) μ := by
    have hh : Integrable f (Measure.map (X i) μ) := by
      rw [hLaw i]
      exact gaussian_square_exponential_integrable ht
    exact hh.comp_measurable (hm i)
  have hfI (i : ι) : (∫ ω, f (X i ω) ∂μ) = (Real.sqrt (1-2*t))⁻¹ := by
    calc
      _ = ∫ x : ℝ, f x ∂Measure.map (X i) μ := (integral_map (hm i).aemeasurable hfm.aestronglyMeasurable).symm
      _ = _ := by rw [hLaw i]; exact gaussian_square_laplace ht
  have hInd := hi.comp (fun _ => f) (fun _ => hfm)
  have hProd := independent_real_finset_product hInd (fun i => hfm.comp (hm i)) hfi Finset.univ
  have he : (fun ω => Real.exp (t*(∑ i, (X i ω)^2))) = (∏ i, f ∘ X i) := by
    funext ω
    simp only [Finset.prod_apply,Function.comp_apply]
    rw [Finset.mul_sum,Real.exp_sum]
  rw [he]
  refine ⟨hProd.1,?_⟩
  rw [hProd.2]
  simp only [Function.comp_apply,hfI,Finset.prod_const,Finset.card_univ]

end ScalarMonotone.EndOfPaper
end
