import EndOfPaper.GaussianMatrixJointCoefficients
import EndOfPaper.GaussianCoordinateGroups

/-!
Actual matrix, scalar and two vector samples on the single canonical Gaussian product used in the comparison arrays.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianJointCoordinate {m n : Type*} [Fintype m] [Fintype n]
    (k : GaussianMatrixJointIndex m n) (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) : ℝ :=
  z (gaussianMatrixJointIndexEquiv m n k)

def gaussianJointGroup {m n κ : Type*} [Fintype m] [Fintype n]
    (f : κ → GaussianMatrixJointIndex m n)
    (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) : EuclideanSpace ℝ κ :=
  (WithLp.equiv 2 _).symm (fun i => gaussianJointCoordinate (f i) z)

def gaussianJointMatrix {m n : Type*} [Fintype m] [Fintype n] :
    (Fin (gaussianMatrixJointDimension m n+1) → ℝ) → HSMatrix m n :=
  gaussianJointGroup (fun p => Sum.inl (some p))

def gaussianJointLeftVector {m n : Type*} [Fintype m] [Fintype n] :
    (Fin (gaussianMatrixJointDimension m n+1) → ℝ) → EuclideanSpace ℝ m :=
  gaussianJointGroup (fun i => Sum.inr (Sum.inl i))

def gaussianJointRightVector {m n : Type*} [Fintype m] [Fintype n] :
    (Fin (gaussianMatrixJointDimension m n+1) → ℝ) → EuclideanSpace ℝ n :=
  gaussianJointGroup (fun j => Sum.inr (Sum.inr j))

def gaussianJointScalar {m n : Type*} [Fintype m] [Fintype n] :
    (Fin (gaussianMatrixJointDimension m n+1) → ℝ) → ℝ :=
  gaussianJointCoordinate (Sum.inl none)

theorem gaussian_joint_coordinate_measurable {m n : Type*} [Fintype m] [Fintype n]
    (k : GaussianMatrixJointIndex m n) : Measurable (gaussianJointCoordinate k) :=
  measurable_pi_apply _

theorem gaussian_joint_coordinate_law {m n : Type*} [Fintype m] [Fintype n]
    (k : GaussianMatrixJointIndex m n) :
    Measure.map (gaussianJointCoordinate k) (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) =
      gaussianReal 0 1 := gaussian_product_coordinate_law _ _

theorem gaussian_joint_group_measurable {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (f : κ → GaussianMatrixJointIndex m n) : Measurable (gaussianJointGroup f) :=
  (EuclideanSpace.equiv κ ℝ).symm.continuous.measurable.comp
    (measurable_pi_lambda _ (fun i => gaussian_joint_coordinate_measurable (f i)))

theorem gaussian_joint_group_independent {m n κ : Type*} [Fintype m] [Fintype n]
    (f : κ → GaussianMatrixJointIndex m n) (hf : Function.Injective f) :
    iIndepFun (fun i => fun z => gaussianJointGroup f z i)
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) :=
  iIndepFun.precomp ((gaussianMatrixJointIndexEquiv m n).injective.comp hf) (gaussian_product_independent _)

theorem gaussian_joint_groups_independent {m n κ ρ : Type*}
    [Fintype m] [Fintype n] [Fintype κ] [Fintype ρ]
    (f : κ → GaussianMatrixJointIndex m n) (g : ρ → GaussianMatrixJointIndex m n)
    (hfg : ∀ i j, f i ≠ g j) :
    IndepFun (gaussianJointGroup f) (gaussianJointGroup g)
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
  have hh := gaussian_independent_coordinate_groups
    (fun (k : Fin (gaussianMatrixJointDimension m n+1)) (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) => z k)
    (gaussian_product_independent (gaussianMatrixJointDimension m n+1))
    (fun k => measurable_pi_apply k)
    (fun i => gaussianMatrixJointIndexEquiv m n (f i))
    (fun j => gaussianMatrixJointIndexEquiv m n (g j))
    (fun i j h => hfg i j ((gaussianMatrixJointIndexEquiv m n).injective h))
  exact hh.comp (EuclideanSpace.equiv κ ℝ).symm.continuous.measurable
    (EuclideanSpace.equiv ρ ℝ).symm.continuous.measurable

theorem gaussian_joint_vector_independence {m n : Type*} [Fintype m] [Fintype n] :
    IndepFun (gaussianJointLeftVector (m := m) (n := n)) gaussianJointRightVector
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
  apply gaussian_joint_groups_independent
  intro i j h
  exact Sum.noConfusion (Sum.inr.inj h)

theorem gaussian_joint_matrix_scalar_independence {m n : Type*} [Fintype m] [Fintype n] :
    IndepFun (gaussianJointMatrix (m := m) (n := n)) gaussianJointScalar
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) := by
  have hh := gaussian_independent_coordinate_groups
    (fun (k : Fin (gaussianMatrixJointDimension m n+1)) (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) => z k)
    (gaussian_product_independent (gaussianMatrixJointDimension m n+1))
    (fun k => measurable_pi_apply k)
    (fun p : m × n => gaussianMatrixJointIndexEquiv m n (Sum.inl (some p)))
    (fun _ : Unit => gaussianMatrixJointIndexEquiv m n (Sum.inl none)) (by
      intro p j h
      exact Option.noConfusion (Sum.inl.inj ((gaussianMatrixJointIndexEquiv m n).injective h)))
  exact hh.comp (EuclideanSpace.equiv (m × n) ℝ).symm.continuous.measurable
    (measurable_pi_apply ())

theorem gaussian_relabel_linear_process {ι κ : Type*} [Fintype κ] {p : ℕ}
    (e : κ ≃ Fin p) (A : ι → κ → ℝ) (z : Fin p → ℝ) (i : ι) :
    gaussianLinearProcess (gaussianRelabelCoefficients e A) (gaussianProductVector p z) i =
      ∑ k : κ, A i k*z (e k) := by
  change (∑ k : Fin p, A i (e.symm k)*z k) = _
  exact Fintype.sum_equiv e.symm _ _ (fun k => by rw [e.apply_symm_apply])

theorem gaussian_joint_matrix_process {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) (i : ι) :
    gaussianLinearProcess (gaussianMatrixComparisonArray u v)
      (gaussianProductVector (gaussianMatrixJointDimension m n+1) z) i =
      ⟪u i,hsMatrixOp (gaussianJointMatrix z) (v i)⟫_ℝ+gaussianJointScalar z := by
  unfold gaussianMatrixComparisonArray
  rw [gaussian_relabel_linear_process]
  simp only [Fintype.sum_sum_type,gaussianMatrixJointCoefficient,zero_mul,Finset.sum_const_zero,add_zero,
    Fintype.sum_option,gaussianMatrixCoefficient,one_mul,Fintype.sum_prod_type]
  rw [gaussian_real_euclidean_inner]
  simp only [hs_matrix_op_apply,hsMatrixToMatrix,Finset.mul_sum]
  dsimp only [gaussianJointMatrix,gaussianJointGroup,gaussianJointScalar,gaussianJointCoordinate]
  simp only [WithLp.equiv_symm_pi_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem gaussian_joint_vector_process {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) (i : ι) :
    gaussianLinearProcess (gaussianVectorComparisonArray u v)
      (gaussianProductVector (gaussianMatrixJointDimension m n+1) z) i =
      ⟪gaussianJointLeftVector z,u i⟫_ℝ+⟪gaussianJointRightVector z,v i⟫_ℝ := by
  unfold gaussianVectorComparisonArray
  rw [gaussian_relabel_linear_process]
  simp only [Fintype.sum_sum_type,gaussianVectorJointCoefficient,zero_mul,Finset.sum_const_zero,zero_add,
    gaussianVectorComparisonCoefficient,Sum.elim_inl,Sum.elim_inr]
  rw [gaussian_real_euclidean_inner,gaussian_real_euclidean_inner]
  dsimp only [gaussianJointLeftVector,gaussianJointRightVector,gaussianJointGroup,gaussianJointCoordinate]
  simp only [WithLp.equiv_symm_pi_apply]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring

end ScalarMonotone.EndOfPaper
end
