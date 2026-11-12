import EndOfPaper.GaussianFiniteMGF
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integrable
import Mathlib.Probability.Moments.SubGaussian

/-!
Transfer from the actual canonical Gaussian product to arbitrary original probability spaces and independent identical copies.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_vector_joint_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hi : iIndepFun (fun i ω => X ω i) μ) (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) :
    Measure.map (fun ω i => X ω i) μ = gaussianProductMeasure n := by
  simpa only [hLaw,gaussianProductMeasure] using
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).mp hi

theorem gaussian_vector_exp_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hi : iIndepFun (fun i ω => X ω i) μ) (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {K : ℝ≥0} {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : LipschitzWith K F) :
    (∫ ω, Real.exp (F (X ω)) ∂μ) = gaussianExpIntegral F := by
  unfold gaussianExpIntegral
  rw [← gaussian_vector_joint_law hi hm hLaw]
  have hh := integral_map (μ := μ) (φ := fun ω i => X ω i)
    (f := fun z => Real.exp (F (gaussianProductVector n z)))
    (measurable_pi_lambda _ hm).aemeasurable
    ((hF.continuous.measurable.comp (gaussian_product_vector_measurable n)).exp.aestronglyMeasurable)
  simpa only [Function.comp_apply] using hh.symm

theorem gaussian_lipschitz_copy_exp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X X' : Ω → EuclideanSpace ℝ (Fin n)}
    (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) :
    Integrable (fun ω => Real.exp (a*(f (X ω)-f (X' ω)))) μ ∧
      (∫ ω, Real.exp (a*(f (X ω)-f (X' ω))) ∂μ) ≤ Real.exp (a^2) := by
  have hF := gaussian_tilt_lipschitz hf a
  have hG := gaussian_tilt_lipschitz hf (-a)
  have hFI := gaussian_exp_integrable_lipschitz hX hi hm hLaw hF
  have hGI := gaussian_exp_integrable_lipschitz hX hi hm hLaw hG
  have hGD := hCopy.comp hG.continuous.measurable.exp
  have hG'I : Integrable (fun ω => Real.exp ((-a)*f (X' ω))) μ := hGD.integrable_iff.mp hGI
  have hEI := hInd.comp hF.continuous.measurable.exp hG.continuous.measurable.exp
  have hExp : (fun ω => Real.exp (a*(f (X ω)-f (X' ω)))) =
      fun ω => Real.exp (a*f (X ω))*Real.exp ((-a)*f (X' ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp]
  refine ⟨hEI.integrable_mul hFI hG'I,?_⟩
  have hFactor : (∫ ω, Real.exp (a*f (X ω))*Real.exp ((-a)*f (X' ω)) ∂μ) =
      (∫ ω, Real.exp (a*f (X ω)) ∂μ)*(∫ ω, Real.exp ((-a)*f (X' ω)) ∂μ) := by
    simpa only [Function.comp_apply,Pi.mul_apply] using hEI.integral_mul_of_integrable hFI hG'I
  have hCopyEq : (∫ ω, Real.exp ((-a)*f (X' ω)) ∂μ) = (∫ ω, Real.exp ((-a)*f (X ω)) ∂μ) :=
    hGD.integral_eq.symm
  rw [hFactor,hCopyEq,gaussian_vector_exp_integral hi hm hLaw hF,gaussian_vector_exp_integral hi hm hLaw hG]
  exact gaussian_finite_lipschitz_copy_mgf hf a

theorem gaussian_lipschitz_copy_subgaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X X' : Ω → EuclideanSpace ℝ (Fin n)}
    (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith 1 f) :
    HasSubgaussianMGF (fun ω => f (X ω)-f (X' ω)) 2 μ where
  integrable_exp_mul a := (gaussian_lipschitz_copy_exp hX hi hm hLaw hInd hCopy hf a).1
  mgf_le a := by
    simpa only [mgf,NNReal.coe_ofNat,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      (gaussian_lipschitz_copy_exp hX hi hm hLaw hInd hCopy hf a).2

end ScalarMonotone.EndOfPaper
end
