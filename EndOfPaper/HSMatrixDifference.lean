import EndOfPaper.HSMatrixProduct

/-!
The literal matrix product difference identity and its exact two-term norm bound.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hs_matrix_mul_difference {m n k : Type*} [Fintype n]
    (A A' : HSMatrix m n) (B B' : HSMatrix n k) :
    hsMatrixMul A B-hsMatrixMul A' B' =
      hsMatrixMul A (B-B')+hsMatrixMul (A-A') B' := by
  ext p
  obtain ⟨i,j⟩ := p
  simp only [PiLp.sub_apply,PiLp.add_apply,hs_matrix_mul_apply,hsMatrixToMatrix]
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem hs_matrix_mul_difference_norm_le {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (A A' : HSMatrix m n) (B B' : HSMatrix n k) :
    ‖hsMatrixMul A B-hsMatrixMul A' B'‖ ≤
      ‖hsMatrixOp A‖*‖B-B'‖+‖A-A'‖*‖B'‖ := by
  rw [hs_matrix_mul_difference]
  apply (norm_add_le _ _).trans
  exact add_le_add (hs_matrix_mul_norm_le A (B-B'))
    ((hs_matrix_mul_norm_le (A-A') B').trans
      (mul_le_mul_of_nonneg_right (hs_matrix_op_norm_le (A-A')) (norm_nonneg B')))

end ScalarMonotone.EndOfPaper
end
