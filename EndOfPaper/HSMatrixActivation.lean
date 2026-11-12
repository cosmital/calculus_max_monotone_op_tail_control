import EndOfPaper.HSMatrixBasic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Entrywise one-Lipschitz activations are Hilbert--Schmidt contractions and preserve zero.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def hsMatrixActivation {m n : Type*} (σ : ℝ → ℝ) (A : HSMatrix m n) : HSMatrix m n :=
  (WithLp.equiv 2 _).symm (fun p => σ (A p))

theorem hs_matrix_activation_zero {m n : Type*} {σ : ℝ → ℝ} (hσ0 : σ 0 = 0) :
    hsMatrixActivation σ (0 : HSMatrix m n) = 0 := by
  ext p
  exact hσ0

theorem hs_matrix_activation_contraction {m n : Type*} [Fintype m] [Fintype n]
    {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ) (A B : HSMatrix m n) :
    ‖hsMatrixActivation σ A-hsMatrixActivation σ B‖ ≤ ‖A-B‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro p _
  have h := hσ.dist_le_mul (A p) (B p)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at h
  change ‖σ (A p)-σ (B p)‖^2 ≤ ‖A p-B p‖^2
  rw [Real.norm_eq_abs,Real.norm_eq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h

theorem hs_matrix_activation_lipschitz {m n : Type*} [Fintype m] [Fintype n]
    {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ) : LipschitzWith 1 (@hsMatrixActivation m n σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using hs_matrix_activation_contraction hσ A B

theorem hs_matrix_activation_norm_le {m n : Type*} [Fintype m] [Fintype n]
    {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ) (hσ0 : σ 0 = 0) (A : HSMatrix m n) :
    ‖hsMatrixActivation σ A‖ ≤ ‖A‖ := by
  simpa only [hs_matrix_activation_zero hσ0,sub_zero] using
    hs_matrix_activation_contraction hσ A 0

end ScalarMonotone.EndOfPaper
end
