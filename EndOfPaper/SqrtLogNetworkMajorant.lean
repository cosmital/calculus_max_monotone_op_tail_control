import EndOfPaper.SqrtLogGeometric
import EndOfPaper.GeometricPrefixLower

/-!
The exact confidence radius and product majorant in the depth example.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkDepthRadius (u : ℝ) : ℝ := Real.sqrt (Real.log (24*Real.exp 1/u))

theorem network_depth_radius_geometric {u : ℝ} (hu : 0 < u) :
    Real.sqrt (Real.log 2+1-Real.log (u/12)) = networkDepthRadius u := by
  have h24 : Real.log (24 : ℝ) = Real.log 2+Real.log 12 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (12 : ℝ) ≠ 0)]
    norm_num
  unfold networkDepthRadius
  rw [Real.log_div hu.ne' (by norm_num : (12 : ℝ) ≠ 0),
    Real.log_div (mul_ne_zero (by norm_num : (24 : ℝ) ≠ 0) (Real.exp_ne_zero _)) hu.ne',
    Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (Real.exp_ne_zero _),Real.log_exp,h24]
  congr 1
  ring

theorem network_depth_radius_baseline {u : ℝ} (hu : 0 < u) :
    sqrtLogScalar (u/6) ≤ networkDepthRadius u := by
  rw [← network_depth_radius_geometric hu]
  apply Real.sqrt_le_sqrt
  have hh : Real.log (u/12) ≤ Real.log (u/6) := Real.log_le_log (by linarith) (by linarith)
  linarith

theorem affine_geometricPrefix_sqrt_log_majorant {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {A : ℝ} (hA : 0 ≤ A) (hQ : DecLE q.val (affineSqrtLogProfile 0 A hA).val)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    geometricPrefixValue (fun x => m+c*s x) (u/12) ≤ m+c*A*networkDepthRadius u := by
  have hrdom := (completedProfileAffine_domain (m := m) (by norm_num) hqi hc).1
  have hr0 := completedProfileAffine_nonnegative (by norm_num) hqi hm hc hq0
  have hrs := completedProfileAffine_selection (m := m) (by norm_num) hqi hc hs
  have hrP := positive_log_area_affine_finite hsm (fun x hx => hq0 x hx _ (hs x hx))
    (positive_log_area_of_sqrt_log_control hq0 hs hA hQ) hm hc
  have hu12 : u/12 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hh := affine_geometric_sqrt_log_majorant hqi hq0 hsm hs hA hQ hm hc hu12
    (geometric_hardy_scalar_selection (by norm_num) hrdom hr0 hrs hrP _ hu12)
  rwa [network_depth_radius_geometric hu.1] at hh

theorem sqrt_log_network_selection_bound {L : ℕ} {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {D A M k : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hM : 0 ≤ M) (hk : 0 ≤ k)
    (hQ : DecLE q.val (affineSqrtLogProfile 0 A hA).val)
    {m κ : Fin L → ℝ} (hm : ∀ i, 0 ≤ m i) (hκ : ∀ i, 0 ≤ κ i)
    (hmM : ∀ i, m i ≤ M) (hκk : ∀ i, κ i ≤ k)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    D*s (u/6)*(∏ i, geometricPrefixValue (fun x => m i+κ i*s x) (u/12)) ≤
      D*A*networkDepthRadius u*(M+k*A*networkDepthRadius u)^L := by
  have hR : 0 ≤ networkDepthRadius u := Real.sqrt_nonneg _
  have hu6 : u/6 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hsB : s (u/6) ≤ A*networkDepthRadius u :=
    (sqrt_log_control_value_bound hA hQ _ hu6 _ (hs _ hu6)).trans
      (mul_le_mul_of_nonneg_left (network_depth_radius_baseline hu.1) hA)
  have hGB (i : Fin L) : geometricPrefixValue (fun x => m i+κ i*s x) (u/12) ≤
      M+k*A*networkDepthRadius u := by
    apply (affine_geometricPrefix_sqrt_log_majorant hqi hq0 hsm hs hA hQ (hm i) (hκ i) hu).trans
    exact add_le_add (hmM i) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hκk i) hA) hR)
  have hprod : (∏ i, geometricPrefixValue (fun x => m i+κ i*s x) (u/12)) ≤
      (M+k*A*networkDepthRadius u)^L := by
    have hh := Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) =>
      geometricPrefixValue_nonnegative (fun x => m i+κ i*s x) (u/12)) (fun i _ => hGB i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  apply mul_le_mul
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsB hD
  · exact hprod
  · exact Finset.prod_nonneg (fun i _ => geometricPrefixValue_nonnegative _ _)
  · exact mul_nonneg (mul_nonneg hD hA) hR

end ScalarMonotone.EndOfPaper
end
