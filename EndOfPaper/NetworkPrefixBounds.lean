import EndOfPaper.NetworkLayers
import EndOfPaper.NetworkProductRecursion

/-!
The actual matrix recursion yields its product modulus on every prefix, without positive-control assumptions.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_prefix_error_from_majorants {N : ℕ} (p : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    (X X' : HSMatrix (Fin (p 0)) (Fin N))
    (W W' : (l : ℕ) → HSMatrix (Fin (p (l+1))) (Fin (p l)))
    {B : ℕ → ℝ} {R K : ℝ} (hB : ∀ l, 0 ≤ B l) (hX' : ‖X'‖ ≤ R)
    (hR : ∀ l, R ≤ K*B l)
    (hW : ∀ l, ‖hsMatrixOp (W l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ) ≤ B l)
    (hW' : ∀ l, ‖hsMatrixOp (W' l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ) ≤ B l) (L : ℕ) :
    ‖networkLayer p σ X W L-networkLayer p σ X' W' L‖ ≤
      (‖X-X'‖+K*(∑ l ∈ Finset.range L, ‖W l-W' l‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ)))*
        (∏ l ∈ Finset.range L, B l) := by
  have hn' (l : ℕ) : ‖networkLayer p σ X' W' l‖ ≤ R*(∏ j ∈ Finset.range l, B j) := by
    induction l with
    | zero => simpa only [networkLayer,Finset.prod_range_zero,mul_one] using hX'
    | succ l ih =>
      calc
        _ ≤ (‖hsMatrixOp (W' l)‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ))*
            ‖networkLayer p σ X' W' l‖ := network_layer_norm_step p σ hσ hσ0 X' W' l
        _ ≤ B l*(R*(∏ j ∈ Finset.range l, B j)) :=
          mul_le_mul (hW' l) ih (norm_nonneg _) (hB l)
        _ = _ := by rw [Finset.prod_range_succ]; ring
  let d := fun l => ‖networkLayer p σ X W l-networkLayer p σ X' W' l‖
  let δ := fun l => ‖W l-W' l‖/Real.sqrt ((p (l+1)+p l : ℕ) : ℝ)
  have hδ (l : ℕ) : 0 ≤ δ l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hstep (l : ℕ) : d (l+1) ≤ B l*d l+δ l*R*(∏ j ∈ Finset.range l, B j) := by
    have hh := network_layer_difference_step p σ hσ X X' W W' l
    have hfirst := mul_le_mul_of_nonneg_right (hW l)
      (norm_nonneg (networkLayer p σ X W l-networkLayer p σ X' W' l))
    have hsecond := mul_le_mul_of_nonneg_left (hn' l) (hδ l)
    apply hh.trans
    simpa only [d,δ,mul_assoc] using add_le_add hfirst hsecond
  simpa only [d,δ,networkLayer] using network_product_error_prefix hB hδ hR hstep L

end ScalarMonotone.EndOfPaper
end
