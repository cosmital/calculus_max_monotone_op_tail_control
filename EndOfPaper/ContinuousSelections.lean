import EndOfPaper.FamilyIntegral

/-!
# Continuous, convex and concave selections identify the whole interior fiber

This supplies the substantive assertion preceding Lemma `lem:hardyconvexity`.
Continuity, rather than a chosen point in each interval, removes every jump.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem increasing_fiber_of_continuous_selection {f : Operator}
    (hf : MaximalIncreasing f) {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) (hc : ContinuousOn s I)
    {x : ℝ} (hx : x ∈ I) : f x = {s x} := by
  have hsx : ContinuousAt s x := (hc x hx).continuousAt (hI.mem_nhds hx)
  have hl : sInf (f x) = s x := tendsto_nhds_unique
    (selection_tendsto_left hf hI hdom hs hx) (hsx.tendsto.mono_left nhdsWithin_le_nhds)
  have hu : sSup (f x) = s x := tendsto_nhds_unique
    (selection_tendsto_right hf hI hdom hs hx) (hsx.tendsto.mono_left nhdsWithin_le_nhds)
  rw [maximal_interior_fiber_eq_Icc hf (hI.subset_interior_iff.mpr hdom hx), hl, hu, Icc_self]

theorem fiber_of_continuous_selection {f : Operator}
    (hf : MaximalIncreasing f ∨ MaximalDecreasing f) {I : Set ℝ}
    (hI : IsOpen I) (hdom : I ⊆ dom f) {s : ℝ → ℝ}
    (hs : SelectionOn f I s) (hc : ContinuousOn s I)
    {x : ℝ} (hx : x ∈ I) : f x = {s x} := by
  rcases hf with hf | hf
  · exact increasing_fiber_of_continuous_selection hf hI hdom hs hc hx
  · have hnd : I ⊆ dom (negOut f) := by simpa only [dom_negOut] using hdom
    have hns : SelectionOn (negOut f) I (fun y => -s y) := by
      intro y hy
      simpa only [negOut, mem_setOf_eq, neg_neg] using hs y hy
    have he := increasing_fiber_of_continuous_selection hf hI hnd hns hc.neg hx
    ext v
    have hneg : v ∈ f x ↔ -v ∈ negOut f x := by simp only [negOut, mem_setOf_eq, neg_neg]
    rw [hneg, he]
    simp only [mem_singleton_iff, neg_inj]

theorem fiber_of_convex_selection {f : Operator}
    (hf : MaximalIncreasing f ∨ MaximalDecreasing f) {I : Set ℝ}
    (hI : IsOpen I) (hdom : I ⊆ dom f) {s : ℝ → ℝ}
    (hs : SelectionOn f I s) (hc : ConvexOn ℝ I s)
    {x : ℝ} (hx : x ∈ I) : f x = {s x} :=
  fiber_of_continuous_selection hf hI hdom hs (ConvexOn.continuousOn hI hc) hx

theorem fiber_of_concave_selection {f : Operator}
    (hf : MaximalIncreasing f ∨ MaximalDecreasing f) {I : Set ℝ}
    (hI : IsOpen I) (hdom : I ⊆ dom f) {s : ℝ → ℝ}
    (hs : SelectionOn f I s) (hc : ConcaveOn ℝ I s)
    {x : ℝ} (hx : x ∈ I) : f x = {s x} :=
  fiber_of_continuous_selection hf hI hdom hs (ConcaveOn.continuousOn hI hc) hx

end ScalarMonotone.EndOfPaper
end
