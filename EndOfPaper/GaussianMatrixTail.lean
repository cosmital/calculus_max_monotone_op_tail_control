import EndOfPaper.GaussianMatrixOriginalLaw
import Mathlib.Probability.Moments.Basic

/-!
The sharp dimensional weak upper tail of the actual Gaussian matrix operator norm on every original probability space.
-/

open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_matrix_operator_norm_tail {Ω m n : Type*}
    [MeasurableSpace Ω] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+s ≤ ‖hsMatrixOp (X ω)‖} ≤
      Real.exp (-(s^2)/2) := by
  have hMoment := gaussian_matrix_operator_norm_mgf hi hm hLaw hs
  have hMarkov := measure_ge_le_exp_mul_mgf (X := fun ω => ‖hsMatrixOp (X ω)‖) (μ := μ)
    (Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+s) hs hMoment.1
  have hMGF : mgf (fun ω => ‖hsMatrixOp (X ω)‖) μ s ≤
      Real.exp (s*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+s^2/2) := hMoment.2
  calc
    _ ≤ Real.exp (-s*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+s))*
        mgf (fun ω => ‖hsMatrixOp (X ω)‖) μ s := hMarkov
    _ ≤ Real.exp (-s*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+s))*
        Real.exp (s*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+s^2/2) :=
      mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end ScalarMonotone.EndOfPaper
end
