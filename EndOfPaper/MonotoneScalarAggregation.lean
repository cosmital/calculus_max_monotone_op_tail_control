import EndOfPaper.AggregationOperator
import EndOfPaper.HardyIntegral

/-!
Exact completed singleton aggregation and maximality under monotonicity alone; no boundary continuity is assumed or needed.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem antitone_scalar_completion_properties {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) (hne : I.Nonempty) {s : ℝ → ℝ} (hs : AntitoneOn s I) :
    MaximalDecreasing (completedDecreasingRestriction I (ofFun s)) ∧
    interior (dom (completedDecreasingRestriction I (ofFun s))) = I ∧
    (dom (completedDecreasingRestriction I (ofFun s)) ⊆ closure I) ∧
    SelectionOn (completedDecreasingRestriction I (ofFun s)) I s := by
  let R := restrictOperator (negOut (ofFun s)) I
  have hR : Increasing R := by
    apply increasing_iff_order.mpr
    rintro x u y v ⟨hx,hu⟩ ⟨hy,hv⟩ hxy
    change -u = s x at hu
    change -v = s y at hv
    have h := hs hx hy hxy.le
    linarith only [hu,hv,h]
  have hRd : dom R = I := by
    apply dom_restrictOperator
    intro x _
    exact ⟨-s x,by simp [negOut,ofFun]⟩
  have hmax : MaximalDecreasing (completedDecreasingRestriction I (ofFun s)) := by
    change MaximalIncreasing (negOut (negOut (completion I R)))
    rw [negOut_negOut]
    exact completion_maximal hord hne hR hRd
  have hcl : dom (completedDecreasingRestriction I (ofFun s)) ⊆ closure I := by
    simpa only [completedDecreasingRestriction,dom_negOut] using completion_dom_subset I R
  have hsel : SelectionOn (completedDecreasingRestriction I (ofFun s)) I s := by
    intro x hx
    change -s x ∈ completion I R x
    apply le_completion hR hRd x
    exact ⟨hx,by simp [negOut,ofFun]⟩
  exact ⟨hmax,domain_interior_of_open_interval hI hord hne
    (fun x hx => ⟨s x,hsel x hx⟩) hcl,hcl,hsel⟩

theorem aggregation_singleton_completion {n : ℕ} (F : CoordinateVector n → ℝ)
    {I : Set ℝ} {f : Fin n → Operator} {a : ℝ → CoordinateVector n}
    (ha : ∀ p ∈ I, ∀ i, f i p = {a p i}) :
    aggregationOperator F I f = completedDecreasingRestriction I (ofFun (fun p => F (a p))) := by
  unfold aggregationOperator intervalCompletionI completedDecreasingRestriction
  apply congrArg negOut
  apply congrArg (completion I)
  ext p u
  by_cases hp : p ∈ I
  · simp only [intervalGraphOn,restrictOperator,negOut,ofFun,mem_setOf_eq]
    rw [if_pos hp]
    simp only [ha p hp,csSup_singleton,csInf_singleton,Icc_self,mem_singleton_iff,hp,true_and]
    constructor <;> intro h <;> linarith only [h]
  · simp only [intervalGraphOn,restrictOperator,mem_setOf_eq]
    rw [if_neg hp]
    simp only [not_mem_empty,hp,false_and]

theorem aggregation_singleton_monotone_properties {n : ℕ} (F : CoordinateVector n → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} {a : ℝ → CoordinateVector n}
    (ha : ∀ p ∈ I, ∀ i, f i p = {a p i})
    (hanti : AntitoneOn (fun p => F (a p)) I) :
    MaximalDecreasing (aggregationOperator F I f) ∧
    interior (dom (aggregationOperator F I f)) = I ∧
    (dom (aggregationOperator F I f) ⊆ closure I) ∧
    SelectionOn (aggregationOperator F I f) I (fun p => F (a p)) := by
  rw [aggregation_singleton_completion F ha]
  exact antitone_scalar_completion_properties hI hord hne hanti

end ScalarMonotone.EndOfPaper
end
