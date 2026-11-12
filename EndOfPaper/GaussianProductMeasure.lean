import EndOfPaper.GaussianLipschitzGeneral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
Actual finite products of standard Gaussian measures and their Euclidean coordinate vectors, including the empty product and every required integrability.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianProductMeasure (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

def gaussianProductVector (n : ℕ) (z : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 _).symm z

def gaussianExpIntegral {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ z : Fin n → ℝ, Real.exp (F (gaussianProductVector n z)) ∂gaussianProductMeasure n

theorem gaussian_product_vector_measurable (n : ℕ) : Measurable (gaussianProductVector n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.measurable

theorem gaussian_product_coordinate_law (n : ℕ) (i : Fin n) :
    Measure.map (fun z : Fin n → ℝ => z i) (gaussianProductMeasure n) = gaussianReal 0 1 := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have hSet : (fun z : Fin n → ℝ => z i) ⁻¹' s =
      Set.pi univ (fun j : Fin n => if j = i then s else univ) := by
    ext z
    simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies]
    constructor
    · intro hz j
      by_cases hji : j = i
      · subst j
        simpa using hz
      · simp [hji]
    · intro hz
      simpa using hz i
  rw [hSet,gaussianProductMeasure,Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem gaussian_product_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => fun z : Fin n → ℝ => z i) (gaussianProductMeasure n) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure n) := by unfold gaussianProductMeasure; infer_instance
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  change Measure.map (id : (Fin n → ℝ) → (Fin n → ℝ)) (gaussianProductMeasure n) =
    Measure.pi (fun i => Measure.map (fun z : Fin n → ℝ => z i) (gaussianProductMeasure n))
  rw [Measure.map_id]
  change Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
    Measure.pi (fun i => Measure.map (fun z : Fin n → ℝ => z i) (gaussianProductMeasure n))
  exact congrArg Measure.pi (funext (fun i => (gaussian_product_coordinate_law n i).symm))

theorem gaussian_product_exp_integrable {n : ℕ} {K : ℝ≥0}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : LipschitzWith K F) :
    Integrable (fun z => Real.exp (F (gaussianProductVector n z))) (gaussianProductMeasure n) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure n) := by unfold gaussianProductMeasure; infer_instance
  exact gaussian_exp_integrable_lipschitz (gaussian_product_vector_measurable n) (gaussian_product_independent n)
    (fun i => measurable_pi_apply i) (gaussian_product_coordinate_law n) hF

theorem gaussianExpIntegral_positive {n : ℕ} {K : ℝ≥0}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : LipschitzWith K F) : 0 < gaussianExpIntegral F := by
  letI : IsProbabilityMeasure (gaussianProductMeasure n) := by unfold gaussianProductMeasure; infer_instance
  exact integral_exp_pos (gaussian_product_exp_integrable hF)

theorem gaussianExpIntegral_zero (F : EuclideanSpace ℝ (Fin 0) → ℝ) :
    gaussianExpIntegral F = Real.exp (F 0) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure 0) := by unfold gaussianProductMeasure; infer_instance
  have hz (z : Fin 0 → ℝ) : gaussianProductVector 0 z = (0 : EuclideanSpace ℝ (Fin 0)) := by
    ext i
    exact Fin.elim0 i
  unfold gaussianExpIntegral
  simp only [hz]
  simp

end ScalarMonotone.EndOfPaper
end
