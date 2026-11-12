import EndOfPaper.HSMatrixProduct
import EndOfPaper.GaussianLipschitzGeneral
import EndOfPaper.GaussianFiniteMGF

/-!
Exponential integrability of the actual Gaussian matrix operator norm, using the existing project Lipschitz theorem and actual entry laws.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_matrix_operator_exponential_integrable {Ω m n : Type*}
    [MeasurableSpace Ω] [Fintype m] [Fintype n] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → HSMatrix m n} (hX : Measurable X)
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (a : ℝ) :
    Integrable (fun ω => Real.exp (a*‖hsMatrixOp (X ω)‖)) μ := by
  have hLip : LipschitzWith 1 (fun A : HSMatrix m n => ‖hsMatrixOp A‖) :=
    hs_matrix_operator_norm_lipschitz
  have hTilt : LipschitzWith ⟨|a|,abs_nonneg a⟩ (fun A : HSMatrix m n => a*‖hsMatrixOp A‖) :=
    gaussian_tilt_lipschitz (f := fun A : HSMatrix m n => ‖hsMatrixOp A‖) hLip a
  exact gaussian_exp_integrable_lipschitz (X := X) (f := fun A : HSMatrix m n => a*‖hsMatrixOp A‖)
    hX hi hm hLaw hTilt

end ScalarMonotone.EndOfPaper
end
