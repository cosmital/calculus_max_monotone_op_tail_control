import EndOfPaper.GaussianProductMeasure
import EndOfPaper.GaussianVectorSplit

/-!
Actual permutation invariance of finite product Gaussians and exact coordinate replacement, for transferring first-coordinate integration by parts.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianPermutation {n : ℕ} (e : Fin n ≃ Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

theorem gaussian_permutation_apply {n : ℕ} (e : Fin n ≃ Fin n)
    (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) : gaussianPermutation e z i = z (e.symm i) := rfl

theorem gaussian_permutation_vector {n : ℕ} (e : Fin n ≃ Fin n) (z : Fin n → ℝ) :
    gaussianPermutation e (gaussianProductVector n z) =
      gaussianProductVector n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e z) := by
  ext i
  obtain ⟨j,rfl⟩ := e.surjective i
  change z (e.symm (e j)) = (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e z) (e j)
  rw [e.symm_apply_apply,MeasurableEquiv.piCongrLeft_apply_apply]

theorem gaussian_permutation_measure_preserving {n : ℕ} (e : Fin n ≃ Fin n) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e)
      (gaussianProductMeasure n) (gaussianProductMeasure n) :=
  measurePreserving_piCongrLeft (fun _ : Fin n => gaussianReal 0 1) e

theorem gaussian_product_integral_permutation {n : ℕ} (e : Fin n ≃ Fin n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ z, g (gaussianPermutation e (gaussianProductVector n z)) ∂gaussianProductMeasure n) =
      ∫ z, g (gaussianProductVector n z) ∂gaussianProductMeasure n := by
  have hh := (gaussian_permutation_measure_preserving e).integral_comp'
    (fun z => g (gaussianProductVector n z))
  simpa only [gaussian_permutation_vector] using hh

theorem gaussian_product_integrable_permutation {n : ℕ} (e : Fin n ≃ Fin n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    Integrable (fun z => g (gaussianPermutation e (gaussianProductVector n z))) (gaussianProductMeasure n) ↔
      Integrable (fun z => g (gaussianProductVector n z)) (gaussianProductMeasure n) := by
  have hh := (gaussian_permutation_measure_preserving e).integrable_comp_emb
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).measurableEmbedding
    (g := fun z => g (gaussianProductVector n z))
  simpa only [Function.comp_apply,gaussian_permutation_vector] using hh

def gaussianReplace {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s : ℝ) :
    EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm (Function.update (fun j => z j) i s)

theorem gaussian_replace_apply {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i j : Fin n) (s : ℝ) :
    gaussianReplace z i s j = Function.update (fun k => z k) i s j := rfl

theorem gaussian_replace_self {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gaussianReplace z i (z i) = z := by
  ext j
  simp only [gaussian_replace_apply,Function.update_eq_self]

theorem gaussian_permutation_cons_replace {n : ℕ} (e : Fin (n+1) ≃ Fin (n+1))
    (s t : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    gaussianPermutation e (gaussianCons t u) =
      gaussianReplace (gaussianPermutation e (gaussianCons s u)) (e 0) t := by
  ext k
  obtain ⟨j,rfl⟩ := e.surjective k
  simp only [gaussian_permutation_apply,gaussian_replace_apply,e.symm_apply_apply]
  refine Fin.cases ?_ (fun q => ?_) j
  · simp only [Function.update_self]
    exact (congrArg (fun k => gaussianCons t u k) (e.symm_apply_apply 0)).trans rfl
  · have hq : e q.succ ≠ e 0 := fun h => Fin.succ_ne_zero q (e.injective h)
    simp only [Function.update_of_ne hq]
    have hT : gaussianCons t u (e.symm (e q.succ)) = u q :=
      (congrArg (fun k => gaussianCons t u k) (e.symm_apply_apply q.succ)).trans rfl
    have hS : gaussianCons s u (e.symm (e q.succ)) = u q :=
      (congrArg (fun k => gaussianCons s u k) (e.symm_apply_apply q.succ)).trans rfl
    exact hT.trans hS.symm

end ScalarMonotone.EndOfPaper
end
