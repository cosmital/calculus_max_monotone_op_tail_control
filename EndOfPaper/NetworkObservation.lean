import EndOfPaper.NetworkContinuity

/-!
The exact positive D and the actual normalized network observation, with continuity and its product modulus derived.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_prefactor_pos {L N : ℕ} {p : ℕ → ℕ} (hpL : 0 < p L) :
    0 < networkPrefactor L N p := by
  apply mul_pos
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hpL))
  · apply Real.sqrt_pos.mpr
    have hh : 0 ≤ ((N*p 0 : ℕ) : ℝ)*
        (∑ l : Fin L, (((p (l.val+1)+p l.val : ℕ) : ℝ))⁻¹) :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun l _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    linarith

theorem normalized_network_observation_continuous {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N)
    (hp : ∀ l ≤ L, 0 < p l) (σ : Fin L → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    {g : HSMatrix (Fin (p L)) (Fin N) → ℝ} (hg : LipschitzWith 1 g) :
    Continuous (fun z : NetworkParameters L N p => g (finiteNetworkMap σ z)/networkPrefactor L N p) :=
  (hg.continuous.comp (finite_network_continuous hN hp σ hσ hσ0)).div_const _

theorem normalized_network_observation_modulus {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N)
    (hp : ∀ l ≤ L, 0 < p l) (σ : Fin L → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    {g : HSMatrix (Fin (p L)) (Fin N) → ℝ} (hg : LipschitzWith 1 g)
    (z w : NetworkParameters L N p) :
    dist (g (finiteNetworkMap σ z)/networkPrefactor L N p)
      (g (finiteNetworkMap σ w)/networkPrefactor L N p) ≤
      dist z w*(∏ l : Fin L, max (networkControl l z) (networkControl l w)) := by
  have hD := network_prefactor_pos (N := N) (hp L le_rfl)
  rw [Real.dist_eq,← sub_div,abs_div,abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  have hg' : |g (finiteNetworkMap σ z)-g (finiteNetworkMap σ w)| ≤
      ‖finiteNetworkMap σ z-finiteNetworkMap σ w‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using hg.dist_le_mul (finiteNetworkMap σ z) (finiteNetworkMap σ w)
  have hh := hg'.trans (network_two_point_bound hN hp σ hσ hσ0 z w)
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

end ScalarMonotone.EndOfPaper
end
