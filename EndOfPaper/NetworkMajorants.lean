import EndOfPaper.NetworkControls

/-!
The symmetric max-controls majorize both copies and the normalized data, including zero controls.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkTwoPointControl {L N : ℕ} {p : ℕ → ℕ} (z w : NetworkParameters L N p) (l : ℕ) : ℝ :=
  if hl : l < L then max (networkControl ⟨l,hl⟩ z) (networkControl ⟨l,hl⟩ w)
  else max ‖networkData z‖ ‖networkData w‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)

theorem network_two_point_control_nonnegative {L N : ℕ} {p : ℕ → ℕ}
    (z w : NetworkParameters L N p) (l : ℕ) : 0 ≤ networkTwoPointControl z w l := by
  unfold networkTwoPointControl
  split_ifs with hl
  · exact (network_control_nonnegative ⟨l,hl⟩ z).trans (le_max_left _ _)
  · exact div_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (Real.sqrt_nonneg _)

theorem network_two_point_control_symmetric {L N : ℕ} {p : ℕ → ℕ}
    (z w : NetworkParameters L N p) (l : ℕ) :
    networkTwoPointControl z w l = networkTwoPointControl w z l := by
  unfold networkTwoPointControl
  split_ifs with hl
  · exact max_comm _ _
  · rw [max_comm ‖networkData z‖ ‖networkData w‖]

theorem network_two_point_control_input {L N : ℕ} {p : ℕ → ℕ}
    (z w : NetworkParameters L N p) (hK : 0 < Real.sqrt ((N*p 0 : ℕ) : ℝ)) (l : ℕ) :
    max ‖networkData z‖ ‖networkData w‖ ≤
      Real.sqrt ((N*p 0 : ℕ) : ℝ)*networkTwoPointControl z w l := by
  unfold networkTwoPointControl
  split_ifs with hl
  · have hz : ‖networkData z‖/Real.sqrt ((N*p 0 : ℕ) : ℝ) ≤
        max (networkControl ⟨l,hl⟩ z) (networkControl ⟨l,hl⟩ w) :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hw : ‖networkData w‖/Real.sqrt ((N*p 0 : ℕ) : ℝ) ≤
        max (networkControl ⟨l,hl⟩ z) (networkControl ⟨l,hl⟩ w) :=
      (le_max_left _ _).trans (le_max_right _ _)
    apply max_le
    · simpa only [mul_comm] using (div_le_iff₀ hK).mp hz
    · simpa only [mul_comm] using (div_le_iff₀ hK).mp hw
  · have he : Real.sqrt ((N*p 0 : ℕ) : ℝ)*
          (max ‖networkData z‖ ‖networkData w‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) =
        max ‖networkData z‖ ‖networkData w‖ := by
      rw [← mul_div_assoc]
      apply (div_eq_iff hK.ne').mpr
      ring
    rw [he]

theorem network_two_point_control_operator {L N : ℕ} {p : ℕ → ℕ}
    (z w : NetworkParameters L N p) (l : ℕ) :
    ‖hsMatrixOp (networkWeightsAt z l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ) ≤
      networkTwoPointControl z w l := by
  by_cases hl : l < L
  · simp only [networkWeightsAt,networkTwoPointControl,dif_pos hl]
    exact (le_max_right _ _).trans (le_max_left _ _)
  · have hzero : hsMatrixOp (0 : HSMatrix (Fin (p (l+1))) (Fin (p l))) = 0 := by
      ext x i
      simp [hs_matrix_op_apply,hsMatrixToMatrix]
    rw [networkWeightsAt,dif_neg hl,hzero,norm_zero,zero_div]
    exact network_two_point_control_nonnegative z w l

end ScalarMonotone.EndOfPaper
end
