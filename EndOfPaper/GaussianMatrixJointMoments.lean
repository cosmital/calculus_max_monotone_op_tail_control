import EndOfPaper.GaussianMatrixJointSample
import EndOfPaper.GaussianNormMGF
import EndOfPaper.GaussianMatrixOperatorIntegrability
import Mathlib.Probability.Independence.Integrable

/-!
Exact factorization and exponential moments of the constructed independent Gaussian blocks. Every independence and integrability condition is derived.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_joint_group_coordinate_law {m n κ : Type*} [Fintype m] [Fintype n]
    (f : κ → GaussianMatrixJointIndex m n) (i : κ) :
    Measure.map (fun z => gaussianJointGroup f z i)
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) = gaussianReal 0 1 :=
  gaussian_joint_coordinate_law (f i)

theorem gaussian_joint_group_coordinate_measurable {m n κ : Type*} [Fintype m] [Fintype n]
    (f : κ → GaussianMatrixJointIndex m n) (i : κ) :
    Measurable (fun z => gaussianJointGroup f z i) := gaussian_joint_coordinate_measurable (f i)

theorem gaussian_joint_vector_norm_sum_mgf {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun z => Real.exp (a*(‖gaussianJointLeftVector (m := m) (n := n) z‖+
        ‖gaussianJointRightVector z‖))) (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ∧
      (∫ z, Real.exp (a*(‖gaussianJointLeftVector (m := m) (n := n) z‖+
        ‖gaussianJointRightVector z‖)) ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ≤
        Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
    unfold gaussianProductMeasure
    infer_instance
  have hg := gaussian_euclidean_norm_mgf (X := gaussianJointLeftVector (m := m) (n := n))
    (gaussian_joint_group_measurable _) (gaussian_joint_group_independent _ (fun _ _ h => Sum.inl.inj (Sum.inr.inj h)))
    (gaussian_joint_group_coordinate_measurable _) (gaussian_joint_group_coordinate_law _) Fintype.card_pos ha
  have hh := gaussian_euclidean_norm_mgf (X := gaussianJointRightVector (m := m) (n := n))
    (gaussian_joint_group_measurable _) (gaussian_joint_group_independent _ (fun _ _ h => Sum.inr.inj (Sum.inr.inj h)))
    (gaussian_joint_group_coordinate_measurable _) (gaussian_joint_group_coordinate_law _) Fintype.card_pos ha
  have hInd : IndepFun (fun z => Real.exp (a*‖gaussianJointLeftVector (m := m) (n := n) z‖))
      (fun z => Real.exp (a*‖gaussianJointRightVector (m := m) (n := n) z‖))
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) :=
    (gaussian_joint_vector_independence (m := m) (n := n)).comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
  have hExp (z) : Real.exp (a*(‖gaussianJointLeftVector (m := m) (n := n) z‖+‖gaussianJointRightVector z‖)) =
      Real.exp (a*‖gaussianJointLeftVector z‖)*Real.exp (a*‖gaussianJointRightVector z‖) := by
    rw [mul_add,Real.exp_add]
  constructor
  · simpa only [hExp] using hInd.integrable_mul hg.1 hh.1
  · calc
      _ = (∫ z, Real.exp (a*‖gaussianJointLeftVector (m := m) (n := n) z‖)
            ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1))*
          (∫ z, Real.exp (a*‖gaussianJointRightVector (m := m) (n := n) z‖)
            ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
        simpa only [hExp,Function.comp_apply,Pi.mul_apply] using hInd.integral_mul_of_integrable hg.1 hh.1
      _ ≤ Real.exp (a*Real.sqrt (Fintype.card m : ℝ)+a^2/2)*
          Real.exp (a*Real.sqrt (Fintype.card n : ℝ)+a^2/2) :=
        mul_le_mul hg.2 hh.2 (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem gaussian_joint_scalar_exp_integral {m n : Type*} [Fintype m] [Fintype n] (a : ℝ) :
    Integrable (fun z => Real.exp (a*gaussianJointScalar (m := m) (n := n) z))
        (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ∧
      (∫ z, Real.exp (a*gaussianJointScalar (m := m) (n := n) z)
        ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) = Real.exp (a^2/2) := by
  have hLaw := gaussian_joint_coordinate_law (m := m) (n := n) (Sum.inl none)
  have hMGF : (∫ z, Real.exp (a*gaussianJointScalar (m := m) (n := n) z)
      ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) = Real.exp (a^2/2) := by
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using mgf_gaussianReal hLaw a
  refine ⟨?_,hMGF⟩
  by_contra hNot
  exact Real.exp_ne_zero _ (hMGF.symm.trans (integral_undef hNot))

theorem gaussian_joint_operator_scalar_exp_factor {m n : Type*} [Fintype m] [Fintype n] (a : ℝ) :
    Integrable (fun z => Real.exp (a*(‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖+
        gaussianJointScalar z))) (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ∧
      (∫ z, Real.exp (a*(‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖+gaussianJointScalar z))
        ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) =
      (∫ z, Real.exp (a*‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖)
        ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1))*Real.exp (a^2/2) := by
  letI : IsProbabilityMeasure (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
    unfold gaussianProductMeasure
    infer_instance
  have hMatrix := gaussian_matrix_operator_exponential_integrable
    (X := gaussianJointMatrix (m := m) (n := n)) (gaussian_joint_group_measurable _)
    (gaussian_joint_group_independent _ (fun _ _ h => Option.some.inj (Sum.inl.inj h)))
    (gaussian_joint_group_coordinate_measurable _) (gaussian_joint_group_coordinate_law _) a
  have hScalar := gaussian_joint_scalar_exp_integral (m := m) (n := n) a
  have hLip : LipschitzWith 1 (fun A : HSMatrix m n => ‖hsMatrixOp A‖) :=
    hs_matrix_operator_norm_lipschitz
  have hInd : IndepFun (fun z => Real.exp (a*‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖))
      (fun z => Real.exp (a*gaussianJointScalar (m := m) (n := n) z))
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) :=
    (gaussian_joint_matrix_scalar_independence (m := m) (n := n)).comp
    (Real.continuous_exp.comp (continuous_const.mul hLip.continuous)).measurable
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
  have hExp (z) : Real.exp (a*(‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖+gaussianJointScalar z)) =
      Real.exp (a*‖hsMatrixOp (gaussianJointMatrix z)‖)*Real.exp (a*gaussianJointScalar z) := by
    rw [mul_add,Real.exp_add]
  constructor
  · simpa only [hExp,Function.comp_apply] using hInd.integrable_mul hMatrix hScalar.1
  · have hFactor := hInd.integral_mul_of_integrable hMatrix hScalar.1
    simpa only [hExp,Function.comp_apply,Pi.mul_apply,hScalar.2] using hFactor

end ScalarMonotone.EndOfPaper
end
