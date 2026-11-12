import EndOfPaper.HSMatrixOperator

/-!
The actual operator/HS matrix product norm bound and the one-Lipschitz operator norm in the HS metric.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def hsMatrixColumn {m n : Type*} (B : HSMatrix m n) (j : n) : EuclideanSpace ℝ m :=
  (WithLp.equiv 2 _).symm (fun i => hsMatrixToMatrix B i j)

theorem hs_matrix_norm_sq_columns {m n : Type*} [Fintype m] [Fintype n] (B : HSMatrix m n) :
    ‖B‖^2 = ∑ j, ‖hsMatrixColumn B j‖^2 := by
  rw [hs_matrix_norm_sq]
  simp only [PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]
  rw [Finset.sum_comm]
  rfl

theorem hs_matrix_mul_column {m n k : Type*} [Fintype m] [Fintype n]
    (A : HSMatrix m n) (B : HSMatrix n k) (j : k) :
    hsMatrixColumn (hsMatrixMul A B) j = hsMatrixOp A (hsMatrixColumn B j) := by
  ext i
  rfl

theorem hs_matrix_mul_norm_le {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (A : HSMatrix m n) (B : HSMatrix n k) :
    ‖hsMatrixMul A B‖ ≤ ‖hsMatrixOp A‖*‖B‖ := by
  have hcol (j : k) : ‖hsMatrixColumn (hsMatrixMul A B) j‖^2 ≤
      ‖hsMatrixOp A‖^2*‖hsMatrixColumn B j‖^2 := by
    rw [hs_matrix_mul_column]
    have hb := (hsMatrixOp A).le_opNorm (hsMatrixColumn B j)
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hb
  have hsq : ‖hsMatrixMul A B‖^2 ≤ ‖hsMatrixOp A‖^2*‖B‖^2 := by
    calc
      _ = ∑ j, ‖hsMatrixColumn (hsMatrixMul A B) j‖^2 := hs_matrix_norm_sq_columns _
      _ ≤ ∑ j, ‖hsMatrixOp A‖^2*‖hsMatrixColumn B j‖^2 := Finset.sum_le_sum (fun j _ => hcol j)
      _ = ‖hsMatrixOp A‖^2*(∑ j, ‖hsMatrixColumn B j‖^2) := (Finset.mul_sum ..).symm
      _ = _ := by rw [← hs_matrix_norm_sq_columns B]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow]

theorem hs_matrix_op_sub {m n : Type*} [Fintype m] [Fintype n] (A B : HSMatrix m n) :
    hsMatrixOp (A-B) = hsMatrixOp A-hsMatrixOp B := by
  ext x i
  rw [ContinuousLinearMap.sub_apply]
  simp only [hs_matrix_op_apply,hsMatrixToMatrix,PiLp.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hs_matrix_operator_norm_lipschitz {m n : Type*} [Fintype m] [Fintype n] :
    LipschitzWith 1 (fun A : HSMatrix m n => ‖hsMatrixOp A‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  have hop : ‖hsMatrixOp A-hsMatrixOp B‖ ≤ ‖A-B‖ := by
    rw [← hs_matrix_op_sub]
    exact hs_matrix_op_norm_le (A-B)
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul,dist_eq_norm] using
    (abs_norm_sub_norm_le (hsMatrixOp A) (hsMatrixOp B)).trans hop

end ScalarMonotone.EndOfPaper
end
