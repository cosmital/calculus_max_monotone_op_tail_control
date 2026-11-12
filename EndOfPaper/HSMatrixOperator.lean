import EndOfPaper.HSMatrixBasic

/-!
The actual matrix linear operator, its operator-norm bound by the Hilbert--Schmidt norm, and actual matrix multiplication.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def hsMatrixOp {m n : Type*} [Fintype m] [Fintype n] (A : HSMatrix m n) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m := by
  classical
  exact (Matrix.toEuclideanLin (hsMatrixToMatrix A)).toContinuousLinearMap

theorem hs_matrix_op_apply {m n : Type*} [Fintype m] [Fintype n]
    (A : HSMatrix m n) (x : EuclideanSpace ℝ n) (i : m) :
    hsMatrixOp A x i = ∑ j, hsMatrixToMatrix A i j*x j := rfl

theorem hs_matrix_op_norm_le {m n : Type*} [Fintype m] [Fintype n] (A : HSMatrix m n) :
    ‖hsMatrixOp A‖ ≤ ‖A‖ := by
  apply (hsMatrixOp A).opNorm_le_bound (norm_nonneg A)
  intro x
  have hrow (i : m) : (∑ j, hsMatrixToMatrix A i j*x j)^2 ≤
      (∑ j, (hsMatrixToMatrix A i j)^2)*(∑ j, (x j)^2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hsq : ‖hsMatrixOp A x‖^2 ≤ ‖A‖^2*‖x‖^2 := by
    calc
      _ = ∑ i, (∑ j, hsMatrixToMatrix A i j*x j)^2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [Real.norm_eq_abs,sq_abs,hs_matrix_op_apply]
      _ ≤ ∑ i, (∑ j, (hsMatrixToMatrix A i j)^2)*(∑ j, (x j)^2) :=
        Finset.sum_le_sum (fun i _ => hrow i)
      _ = (∑ i, ∑ j, (hsMatrixToMatrix A i j)^2)*(∑ j, (x j)^2) :=
        (Finset.sum_mul ..).symm
      _ = _ := by
        rw [hs_matrix_norm_sq,PiLp.norm_sq_eq_of_L2]
        simp only [Real.norm_eq_abs,sq_abs]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg x))).mp
  rwa [mul_pow]

def hsMatrixMul {m n k : Type*} [Fintype n] (A : HSMatrix m n) (B : HSMatrix n k) : HSMatrix m k :=
  hsMatrixOfMatrix (hsMatrixToMatrix A * hsMatrixToMatrix B)

theorem hs_matrix_mul_apply {m n k : Type*} [Fintype n]
    (A : HSMatrix m n) (B : HSMatrix n k) (i : m) (j : k) :
    hsMatrixMul A B (i,j) = ∑ l, hsMatrixToMatrix A i l*hsMatrixToMatrix B l j := rfl

end ScalarMonotone.EndOfPaper
end
