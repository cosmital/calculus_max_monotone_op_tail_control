import EndOfPaper.NetworkTwoPoint

/-!
Continuity of the actual controls and network, and derived Borel measurability of the finite network map.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_control_continuous {L N : ℕ} {p : ℕ → ℕ} (l : Fin L) :
    Continuous (fun z : NetworkParameters L N p => networkControl l z) := by
  exact ((continuous_norm.comp network_data_lipschitz.continuous).div_const _).max
    ((hs_matrix_operator_norm_lipschitz.continuous.comp (network_weight_lipschitz l).continuous).div_const _)

theorem finite_network_continuous {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N)
    (hp : ∀ l ≤ L, 0 < p l) (σ : Fin L → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0) :
    Continuous (@finiteNetworkMap L N p σ) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hc : Continuous (fun w : NetworkParameters L N p =>
      networkPrefactor L N p*dist w z*(∏ l : Fin L, max (networkControl l w) (networkControl l z))) :=
    (continuous_const.mul (continuous_id.dist continuous_const)).mul
      (continuous_finset_prod Finset.univ (fun l _ => (network_control_continuous l).max continuous_const))
  have ht : Tendsto (fun w : NetworkParameters L N p =>
      networkPrefactor L N p*dist w z*(∏ l : Fin L, max (networkControl l w) (networkControl l z)))
      (𝓝 z) (𝓝 (0 : ℝ)) := by
    simpa only [dist_self,mul_zero,zero_mul] using (hc.continuousAt (x := z)).tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun w => by simpa only [dist_eq_norm] using network_two_point_bound hN hp σ hσ hσ0 w z) ht

theorem finite_network_borel_measurable {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N)
    (hp : ∀ l ≤ L, 0 < p l) (σ : Fin L → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0) :
    @Measurable (NetworkParameters L N p) (HSMatrix (Fin (p L)) (Fin N))
      (borel _) (borel _) (finiteNetworkMap σ) := by
  letI : MeasurableSpace (NetworkParameters L N p) := borel _
  letI : BorelSpace (NetworkParameters L N p) := ⟨rfl⟩
  letI : MeasurableSpace (HSMatrix (Fin (p L)) (Fin N)) := borel _
  letI : BorelSpace (HSMatrix (Fin (p L)) (Fin N)) := ⟨rfl⟩
  exact (finite_network_continuous hN hp σ hσ hσ0).measurable

end ScalarMonotone.EndOfPaper
end
