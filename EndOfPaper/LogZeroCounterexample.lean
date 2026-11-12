import MonotoneOperators.ProductsDual
import MonotoneOperators.Interface

/-!
The globally zero maximal graph has empty logarithm.
This supplies the manuscript exception to logarithmic maximality.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem logarithm_of_zero_graph_empty :
    logOp (ofFun (fun _ : ℝ => (0 : ℝ))) = (fun _ : ℝ => (∅ : Set ℝ)) := by
  ext x t
  have ht : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  simp [logOp_mem_iff, ofFun, ht]

theorem logarithm_of_zero_graph_not_maximal :
    ¬ MaximalDecreasing (logOp (ofFun (fun _ : ℝ => (0 : ℝ)))) := by
  intro h
  have hnot : (0 : ℝ) ∉ logOp (ofFun (fun _ : ℝ => (0 : ℝ))) 0 := by
    rw [logarithm_of_zero_graph_empty]
    simp
  obtain ⟨y, v, hv, hbad⟩ :=
    (maximalDecreasing_iff_positive_witness.mp h).2 0 0 hnot
  simpa only [logarithm_of_zero_graph_empty, mem_empty_iff_false] using hv

theorem logarithmic_zero_exception :
    ∃ f : Operator, MaximalDecreasing f ∧ (∀ x : ℝ, f x = {0}) ∧
      logOp f = (fun _ : ℝ => (∅ : Set ℝ)) ∧ ¬ MaximalDecreasing (logOp f) := by
  have hn : negOut (ofFun (fun _ : ℝ => (0 : ℝ))) = ofFun (fun _ : ℝ => (0 : ℝ)) := by
    ext x u
    simp [negOut, ofFun]
  have hf : MaximalDecreasing (ofFun (fun _ : ℝ => (0 : ℝ))) := by
    change MaximalIncreasing (negOut (ofFun (fun _ : ℝ => (0 : ℝ))))
    rw [hn]
    exact constant_maximal 0
  exact ⟨ofFun (fun _ : ℝ => (0 : ℝ)), hf, fun _ => rfl,
    logarithm_of_zero_graph_empty, logarithm_of_zero_graph_not_maximal⟩

end ScalarMonotone.EndOfPaper
end
