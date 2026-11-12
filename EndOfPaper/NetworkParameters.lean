import EndOfPaper.NetworkLayers

/-!
The actual finite Euclidean parameter space, normalized network map, exact HS product norm and Lipschitz block projections.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

abbrev NetworkCoordinate (L N : ℕ) (p : ℕ → ℕ) :=
  (Fin (p 0) × Fin N) ⊕ (Σ l : Fin L, Fin (p (l.val+1)) × Fin (p l.val))

abbrev NetworkParameters (L N : ℕ) (p : ℕ → ℕ) := EuclideanSpace ℝ (NetworkCoordinate L N p)

def networkData {L N : ℕ} {p : ℕ → ℕ} (z : NetworkParameters L N p) :
    HSMatrix (Fin (p 0)) (Fin N) :=
  (WithLp.equiv 2 _).symm (fun ij => z (Sum.inl ij))

def networkWeight {L N : ℕ} {p : ℕ → ℕ} (z : NetworkParameters L N p) (l : Fin L) :
    HSMatrix (Fin (p (l.val+1))) (Fin (p l.val)) :=
  (WithLp.equiv 2 _).symm (fun ij => z (Sum.inr ⟨l,ij⟩))

theorem network_parameter_norm_sq {L N : ℕ} {p : ℕ → ℕ} (z : NetworkParameters L N p) :
    ‖z‖^2 = ‖networkData z‖^2+∑ l, ‖networkWeight z l‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2,Fintype.sum_sum_type,Fintype.sum_sigma]
  rfl

theorem network_data_sub {L N : ℕ} {p : ℕ → ℕ} (z w : NetworkParameters L N p) :
    networkData (z-w) = networkData z-networkData w := by ext ij; rfl

theorem network_weight_sub {L N : ℕ} {p : ℕ → ℕ} (z w : NetworkParameters L N p) (l : Fin L) :
    networkWeight (z-w) l = networkWeight z l-networkWeight w l := by ext ij; rfl

theorem network_data_norm_le {L N : ℕ} {p : ℕ → ℕ} (z : NetworkParameters L N p) :
    ‖networkData z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [network_parameter_norm_sq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun l _ => sq_nonneg ‖networkWeight z l‖))

theorem network_weight_norm_le {L N : ℕ} {p : ℕ → ℕ} (z : NetworkParameters L N p) (l : Fin L) :
    ‖networkWeight z l‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [network_parameter_norm_sq]
  have hsum : ‖networkWeight z l‖^2 ≤ ∑ j, ‖networkWeight z j‖^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖networkWeight z j‖) (Finset.mem_univ l)
  exact hsum.trans (le_add_of_nonneg_left (sq_nonneg ‖networkData z‖))

theorem network_data_lipschitz {L N : ℕ} {p : ℕ → ℕ} :
    LipschitzWith 1 (@networkData L N p) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,network_data_sub] using network_data_norm_le (z-w)

theorem network_weight_lipschitz {L N : ℕ} {p : ℕ → ℕ} (l : Fin L) :
    LipschitzWith 1 (fun z : NetworkParameters L N p => networkWeight z l) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,network_weight_sub] using network_weight_norm_le (z-w) l

def networkWeightsAt {L N : ℕ} {p : ℕ → ℕ} (z : NetworkParameters L N p) (l : ℕ) :
    HSMatrix (Fin (p (l+1))) (Fin (p l)) :=
  if hl : l < L then networkWeight z ⟨l,hl⟩ else 0

def networkMap {L N : ℕ} {p : ℕ → ℕ} (σ : ℕ → ℝ → ℝ) (z : NetworkParameters L N p) :
    HSMatrix (Fin (p L)) (Fin N) :=
  networkOutput L p σ (networkData z) (networkWeightsAt z)

end ScalarMonotone.EndOfPaper
end
