import EndOfPaper.HSMatrixActivation
import EndOfPaper.HSMatrixDifference

/-!
The actual normalized network layer recursion and output, with derived one-layer norm and difference estimates.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkLayer {N : ℕ} (p : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (X : HSMatrix (Fin (p 0)) (Fin N))
    (W : (l : ℕ) → HSMatrix (Fin (p (l+1))) (Fin (p l))) :
    (l : ℕ) → HSMatrix (Fin (p l)) (Fin N)
  | 0 => X
  | l+1 => hsMatrixActivation (σ l)
      ((Real.sqrt ((p (l+1)+p l : ℕ) : ℝ))⁻¹ • hsMatrixMul (W l) (networkLayer p σ X W l))

def networkOutput {N : ℕ} (L : ℕ) (p : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (X : HSMatrix (Fin (p 0)) (Fin N))
    (W : (l : ℕ) → HSMatrix (Fin (p (l+1))) (Fin (p l))) :
    HSMatrix (Fin (p L)) (Fin N) :=
  (Real.sqrt (p L : ℝ))⁻¹ • networkLayer p σ X W L

theorem network_layer_norm_step {N : ℕ} (p : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    (X : HSMatrix (Fin (p 0)) (Fin N))
    (W : (l : ℕ) → HSMatrix (Fin (p (l+1))) (Fin (p l))) (l : ℕ) :
    ‖networkLayer p σ X W (l+1)‖ ≤
      (‖hsMatrixOp (W l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ))*‖networkLayer p σ X W l‖ := by
  rw [networkLayer]
  apply (hs_matrix_activation_norm_le (hσ l) (hσ0 l) _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hmul := mul_le_mul_of_nonneg_left
    (hs_matrix_mul_norm_le (W l) (networkLayer p σ X W l))
    (inv_nonneg.mpr (Real.sqrt_nonneg ((p (l+1)+p l : ℕ) : ℝ)))
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hmul

theorem network_layer_difference_step {N : ℕ} (p : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l))
    (X X' : HSMatrix (Fin (p 0)) (Fin N))
    (W W' : (l : ℕ) → HSMatrix (Fin (p (l+1))) (Fin (p l))) (l : ℕ) :
    ‖networkLayer p σ X W (l+1)-networkLayer p σ X' W' (l+1)‖ ≤
      (‖hsMatrixOp (W l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ))*
        ‖networkLayer p σ X W l-networkLayer p σ X' W' l‖+
      (‖W l-W' l‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ))*‖networkLayer p σ X' W' l‖ := by
  rw [networkLayer,networkLayer]
  apply (hs_matrix_activation_contraction (hσ l) _ _).trans
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hmul := mul_le_mul_of_nonneg_left
    (hs_matrix_mul_difference_norm_le (W l) (W' l)
      (networkLayer p σ X W l) (networkLayer p σ X' W' l))
    (inv_nonneg.mpr (Real.sqrt_nonneg ((p (l+1)+p l : ℕ) : ℝ)))
  simpa only [div_eq_mul_inv,mul_add,mul_assoc,mul_comm,mul_left_comm] using hmul

end ScalarMonotone.EndOfPaper
end
