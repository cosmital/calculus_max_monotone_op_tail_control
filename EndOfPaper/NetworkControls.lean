import EndOfPaper.NetworkParameters

/-!
The literal normalized max-controls, finite activation extension and actual finite network map.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkControl {L N : ℕ} {p : ℕ → ℕ} (l : Fin L) (z : NetworkParameters L N p) : ℝ :=
  max (‖networkData z‖/Real.sqrt ((N*p 0 : ℕ) : ℝ))
    (‖hsMatrixOp (networkWeight z l)‖/Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ))

theorem network_control_nonnegative {L N : ℕ} {p : ℕ → ℕ} (l : Fin L)
    (z : NetworkParameters L N p) : 0 ≤ networkControl l z :=
  (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)).trans (le_max_left _ _)

def networkActivationsAt {L : ℕ} (σ : Fin L → ℝ → ℝ) (l : ℕ) : ℝ → ℝ :=
  if hl : l < L then σ ⟨l,hl⟩ else id

theorem network_activations_lipschitz {L : ℕ} {σ : Fin L → ℝ → ℝ}
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (l : ℕ) : LipschitzWith 1 (networkActivationsAt σ l) := by
  unfold networkActivationsAt
  split_ifs with hl
  · exact hσ ⟨l,hl⟩
  · exact LipschitzWith.id

theorem network_activations_zero {L : ℕ} {σ : Fin L → ℝ → ℝ}
    (hσ0 : ∀ l, σ l 0 = 0) (l : ℕ) : networkActivationsAt σ l 0 = 0 := by
  unfold networkActivationsAt
  split_ifs with hl
  · exact hσ0 ⟨l,hl⟩
  · rfl

def finiteNetworkMap {L N : ℕ} {p : ℕ → ℕ} (σ : Fin L → ℝ → ℝ)
    (z : NetworkParameters L N p) : HSMatrix (Fin (p L)) (Fin N) :=
  networkMap (networkActivationsAt σ) z

end ScalarMonotone.EndOfPaper
end
