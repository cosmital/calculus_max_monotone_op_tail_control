import EndOfPaper.GaussianMatrixDenseMoment
import Mathlib.Probability.IdentDistrib

/-!
Transfer of the actual matrix norm moment from the canonical construction to every original probability space with independent standard Gaussian entries.
-/

open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_matrix_joint_identDistrib {Ω m n : Type*}
    [MeasurableSpace Ω] [Fintype m] [Fintype n] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) :
    IdentDistrib X (gaussianJointMatrix (m := m) (n := n)) μ
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
    unfold gaussianProductMeasure
    infer_instance
  have hGInd := gaussian_joint_group_independent (m := m) (n := n)
    (fun p : m × n => Sum.inl (some p)) (fun _ _ h => Option.some.inj (Sum.inl.inj h))
  have hGMeas (i : m × n) : Measurable (fun z => gaussianJointMatrix (m := m) (n := n) z i) :=
    gaussian_joint_group_coordinate_measurable _ i
  have hGLaw (i : m × n) : Measure.map (fun z => gaussianJointMatrix (m := m) (n := n) z i)
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) = gaussianReal 0 1 :=
    gaussian_joint_group_coordinate_law _ i
  have hRawX := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).mp hi
  have hRawG := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hGMeas i).aemeasurable)).mp hGInd
  have hRaw : IdentDistrib (fun ω i => X ω i)
      (fun z i => gaussianJointMatrix (m := m) (n := n) z i) μ
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
    refine ⟨(measurable_pi_lambda _ hm).aemeasurable,
      (measurable_pi_lambda _ hGMeas).aemeasurable,?_⟩
    rw [hRawX,hRawG]
    simp only [hLaw,hGLaw]
  simpa only [Function.comp_apply] using
    hRaw.comp (EuclideanSpace.equiv (m × n) ℝ).symm.continuous.measurable

theorem gaussian_matrix_operator_norm_mgf {Ω m n : Type*}
    [MeasurableSpace Ω] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun ω => Real.exp (a*‖hsMatrixOp (X ω)‖)) μ ∧
      (∫ ω, Real.exp (a*‖hsMatrixOp (X ω)‖) ∂μ) ≤
      Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2/2) := by
  have hX : Measurable X := by
    simpa only [Function.comp_apply] using
      (EuclideanSpace.equiv (m × n) ℝ).symm.continuous.measurable.comp (measurable_pi_lambda _ hm)
  refine ⟨gaussian_matrix_operator_exponential_integrable hX hi hm hLaw a,?_⟩
  have hLip : LipschitzWith 1 (fun A : HSMatrix m n => ‖hsMatrixOp A‖) :=
    hs_matrix_operator_norm_lipschitz
  have hExp : Measurable (fun A : HSMatrix m n => Real.exp (a*‖hsMatrixOp A‖)) :=
    (Real.continuous_exp.comp (continuous_const.mul hLip.continuous)).measurable
  have hEq := ((gaussian_matrix_joint_identDistrib hi hm hLaw).comp hExp).integral_eq
  calc
    _ = (∫ z, Real.exp (a*‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖)
        ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
      simpa only [Function.comp_apply] using hEq
    _ ≤ _ := gaussian_joint_operator_norm_mgf ha

end ScalarMonotone.EndOfPaper
end
