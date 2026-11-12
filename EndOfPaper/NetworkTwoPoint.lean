import EndOfPaper.NetworkMajorants
import EndOfPaper.NetworkPrefixBounds

/-!
The exact manuscript D-times-Euclidean-distance-times-product two-point inequality.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkPrefactor (L N : ℕ) (p : ℕ → ℕ) : ℝ :=
  (Real.sqrt (p L : ℝ))⁻¹*Real.sqrt (1+((N*p 0 : ℕ) : ℝ)*
    (∑ l : Fin L, (((p (l.val+1)+p l.val : ℕ) : ℝ))⁻¹))

theorem network_two_point_bound {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N)
    (hp : ∀ l ≤ L, 0 < p l) (σ : Fin L → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    (z w : NetworkParameters L N p) :
    ‖finiteNetworkMap σ z-finiteNetworkMap σ w‖ ≤
      networkPrefactor L N p*dist z w*(∏ l : Fin L, max (networkControl l z) (networkControl l w)) := by
  let K := Real.sqrt ((N*p 0 : ℕ) : ℝ)
  let R := max ‖networkData z‖ ‖networkData w‖
  let B := networkTwoPointControl z w
  let S := networkActivationsAt σ
  let W := networkWeightsAt z
  let W' := networkWeightsAt w
  have hK : 0 < K := Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.mul_pos hN (hp 0 (Nat.zero_le L)))
  have hσS := network_activations_lipschitz hσ
  have hσS0 := network_activations_zero hσ0
  have hB (l : ℕ) : 0 ≤ B l := network_two_point_control_nonnegative z w l
  have hR (l : ℕ) : R ≤ K*B l := network_two_point_control_input z w hK l
  have hW (l : ℕ) : ‖hsMatrixOp (W l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ) ≤ B l :=
    network_two_point_control_operator z w l
  have hW' (l : ℕ) : ‖hsMatrixOp (W' l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ) ≤ B l := by
    rw [show B l = networkTwoPointControl w z l from network_two_point_control_symmetric z w l]
    exact network_two_point_control_operator w z l
  have hPrefix := network_prefix_error_from_majorants p S hσS hσS0
    (networkData z) (networkData w) W W' hB (le_max_right _ _) hR hW hW' L
  have hsum : (∑ l ∈ Finset.range L, ‖W l-W' l‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ)) =
      ∑ l : Fin L, ‖networkWeight z l-networkWeight w l‖/
        Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l _
    simp only [W,W',networkWeightsAt,dif_pos l.isLt]
  have hprod : (∏ l ∈ Finset.range L, B l) =
      ∏ l : Fin L, max (networkControl l z) (networkControl l w) := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro l _
    simp only [B,networkTwoPointControl,dif_pos l.isLt]
  rw [hsum,hprod] at hPrefix
  have hdim (l : Fin L) : 0 < ((p (l.val+1)+p l.val : ℕ) : ℝ) := by
    have hn : 0 < p (l.val+1)+p l.val := Nat.add_pos_left (hp (l.val+1) (by omega)) _
    exact_mod_cast hn
  have hcs := network_exact_cauchy_factor hK.le (norm_nonneg (networkData z-networkData w))
    (fun l : Fin L => norm_nonneg (networkWeight z l-networkWeight w l)) hdim
  have hsq : ‖z-w‖^2 = ‖networkData z-networkData w‖^2+
      ∑ l, ‖networkWeight z l-networkWeight w l‖^2 := by
    simpa only [network_data_sub,network_weight_sub] using network_parameter_norm_sq (z-w)
  have hnorm : Real.sqrt (‖networkData z-networkData w‖^2+
      ∑ l, ‖networkWeight z l-networkWeight w l‖^2) = ‖z-w‖ := by
    rw [← hsq,Real.sqrt_sq (norm_nonneg _)]
  have hKsq : K^2 = ((N*p 0 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  rw [hKsq,hnorm] at hcs
  have hprod0 : 0 ≤ ∏ l : Fin L, max (networkControl l z) (networkControl l w) :=
    Finset.prod_nonneg (fun l _ => (network_control_nonnegative l z).trans (le_max_left _ _))
  have hout : ‖finiteNetworkMap σ z-finiteNetworkMap σ w‖ =
      (Real.sqrt (p L : ℝ))⁻¹*‖networkLayer p S (networkData z) W L-
        networkLayer p S (networkData w) W' L‖ := by
    unfold finiteNetworkMap networkMap networkOutput
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [hout]
  apply (mul_le_mul_of_nonneg_left hPrefix (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcs hprod0)
    (inv_nonneg.mpr (Real.sqrt_nonneg (p L : ℝ)))
  simpa only [networkPrefactor,dist_eq_norm,mul_assoc] using hh

end ScalarMonotone.EndOfPaper
end
