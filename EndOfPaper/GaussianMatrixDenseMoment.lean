import EndOfPaper.GaussianMatrixFiniteMoment
import EndOfPaper.GaussianOperatorUnitPairs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The exact operator-norm exponential moment, obtained from the proved finite comparisons along a deterministic dense family, with derived L1.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_joint_operator_norm_mgf {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, Real.exp (a*‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖)
      ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ≤
    Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2/2) := by
  classical
  let q := gaussianUnitPairSequence m n
  let u (N : ℕ) (i : Fin (N+1)) : EuclideanSpace ℝ m := (q i.val).1.val
  let v (N : ℕ) (i : Fin (N+1)) : EuclideanSpace ℝ n := (q i.val).2.val
  let F (N : ℕ) (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) : ℝ :=
    Real.exp (a*gaussianFiniteMaximum (gaussianLinearProcess (gaussianMatrixComparisonArray (u N) (v N))
      (gaussianProductVector (gaussianMatrixJointDimension m n+1) z)))
  let f (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) : ℝ :=
    Real.exp (a*(‖hsMatrixOp (gaussianJointMatrix z)‖+gaussianJointScalar z))
  have hValues (N : ℕ) (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) :
      gaussianFiniteMaximum (gaussianLinearProcess (gaussianMatrixComparisonArray (u N) (v N))
        (gaussianProductVector (gaussianMatrixJointDimension m n+1) z)) =
      gaussianSequenceMaximum (gaussianUnitPairValue (hsMatrixOp (gaussianJointMatrix z)) ∘ q) N+
        gaussianJointScalar z := by
    have hProcess : gaussianLinearProcess (gaussianMatrixComparisonArray (u N) (v N))
        (gaussianProductVector (gaussianMatrixJointDimension m n+1) z) =
        fun i : Fin (N+1) => gaussianUnitPairValue (hsMatrixOp (gaussianJointMatrix z)) (q i.val)+
          gaussianJointScalar z := by
      funext i
      exact gaussian_joint_matrix_process (u N) (v N) z i
    rw [hProcess,gaussian_finite_maximum_add_constant]
    rfl
  have hMeas (N : ℕ) : AEStronglyMeasurable (F N)
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) :=
    ((Real.continuous_exp.comp (continuous_const.mul
      (gaussian_linear_finite_maximum_continuous (gaussianMatrixComparisonArray (u N) (v N))))).measurable.comp
        (gaussian_product_vector_measurable _)).aestronglyMeasurable
  have hFactor := gaussian_joint_operator_scalar_exp_factor (m := m) (n := n) a
  have hBound (N : ℕ) : ∀ᵐ z ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1),
      ‖F N z‖ ≤ f z := by
    filter_upwards [] with z
    change ‖Real.exp (a*_)‖ ≤ Real.exp (a*(_+_))
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hValues]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ha
    apply add_le_add_right
    exact gaussian_sequence_maximum_upper _
      (fun k => gaussian_unit_pair_value_le (hsMatrixOp (gaussianJointMatrix z)) (q k)) N
  have hLimit : ∀ᵐ z ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1),
      Tendsto (fun N => F N z) atTop (𝓝 (f z)) := by
    filter_upwards [] with z
    have hMax := gaussian_operator_dense_maximum_tendsto (hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z))
    have hExp := (Real.continuous_exp.tendsto _).comp
      ((hMax.add_const (gaussianJointScalar z)).const_mul a)
    simpa only [F,f,hValues,q] using hExp
  have hIntegralLimit := tendsto_integral_of_dominated_convergence f hMeas hFactor.1 hBound hLimit
  have hEach (N : ℕ) : (∫ z, F N z ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ≤
      Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2) := by
    have hFinite := gaussian_matrix_finite_family_moment (u N) (v N)
      (fun i => (q i.val).1.property) (fun i => (q i.val).2.property) ha
    have hProcess (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) :
        gaussianLinearProcess (gaussianMatrixComparisonArray (u N) (v N))
          (gaussianProductVector (gaussianMatrixJointDimension m n+1) z) =
        fun i => ⟪u N i,hsMatrixOp (gaussianJointMatrix z) (v N i)⟫_ℝ+gaussianJointScalar z :=
      funext (gaussian_joint_matrix_process (u N) (v N) z)
    simpa only [F,hProcess] using hFinite
  have hFinal := le_of_tendsto hIntegralLimit (Eventually.of_forall hEach)
  change (∫ z, Real.exp (a*(‖hsMatrixOp (gaussianJointMatrix (m := m) (n := n) z)‖+gaussianJointScalar z))
    ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ≤ _ at hFinal
  rw [hFactor.2] at hFinal
  have hExp : Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2) =
      Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2/2)*Real.exp (a^2/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp] at hFinal
  exact (mul_le_mul_right (Real.exp_pos _)).mp hFinal

end ScalarMonotone.EndOfPaper
end
