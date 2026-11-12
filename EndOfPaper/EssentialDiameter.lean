import Mathlib.Data.Real.Archimedean
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
An actual independent-copy bound forces an essential interval of length one, without prior boundedness or L1.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def nullRationalNeighborhoods (ν : Measure ℝ) : Set ℝ := by
  classical
  exact ⋃ q : ℚ × ℚ, if ν (Ioo (q.1 : ℝ) (q.2 : ℝ)) = 0 then Ioo (q.1 : ℝ) (q.2 : ℝ) else ∅

theorem nullRationalNeighborhoods_null (ν : Measure ℝ) : ν (nullRationalNeighborhoods ν) = 0 := by
  classical
  unfold nullRationalNeighborhoods
  apply measure_iUnion_null
  intro q
  split_ifs with h
  · exact h
  · exact measure_empty

theorem nullRationalNeighborhoods_measurable (ν : Measure ℝ) : MeasurableSet (nullRationalNeighborhoods ν) := by
  classical
  unfold nullRationalNeighborhoods
  apply MeasurableSet.iUnion
  intro q
  split_ifs
  · exact measurableSet_Ioo
  · exact MeasurableSet.empty

theorem positive_neighborhood_of_outside_null (ν : Measure ℝ) {x ε : ℝ}
    (hx : x ∉ nullRationalNeighborhoods ν) (hε : 0 < ε) :
    0 < ν (Ioo (x-ε) (x+ε)) := by
  classical
  apply pos_iff_ne_zero.mpr
  intro hzero
  obtain ⟨a,ha0,hax⟩ := exists_rat_btwn (show x-ε < x by linarith)
  obtain ⟨b,hxb,hb1⟩ := exists_rat_btwn (show x < x+ε by linarith)
  have hsub : Ioo (a : ℝ) (b : ℝ) ⊆ Ioo (x-ε) (x+ε) :=
    fun u hu => ⟨ha0.trans hu.1,hu.2.trans hb1⟩
  have hrat : ν (Ioo (a : ℝ) (b : ℝ)) = 0 := measure_mono_null hsub hzero
  apply hx
  unfold nullRationalNeighborhoods
  apply mem_iUnion.mpr
  refine ⟨(a,b),?_⟩
  rw [if_pos hrat]
  exact ⟨hax,hxb⟩

theorem copy_gap_support_sub_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hgap : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), |z.1-z.2| ≤ 1)
    {x y : ℝ} (hx : x ∉ nullRationalNeighborhoods ν) (hy : y ∉ nullRationalNeighborhoods ν) : x-y ≤ 1 := by
  by_contra hxy
  have hxy' : 1 < x-y := lt_of_not_ge hxy
  let ε := (x-y-1)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hnull : (ν.prod ν) {z : ℝ × ℝ | 1 < |z.1-z.2|} = 0 := by
    simpa only [not_le] using ae_iff.mp hgap
  have hsub : Ioo (x-ε) (x+ε) ×ˢ Ioo (y-ε) (y+ε) ⊆
      {z : ℝ × ℝ | 1 < |z.1-z.2|} := by
    intro z hz
    apply lt_of_lt_of_le _ (le_abs_self (z.1-z.2))
    dsimp [ε] at hz ⊢
    linarith [hz.1.1,hz.2.2]
  have hrect0 := measure_mono_null hsub hnull
  have hrect : 0 < (ν.prod ν) (Ioo (x-ε) (x+ε) ×ˢ Ioo (y-ε) (y+ε)) := by
    rw [Measure.prod_prod]
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (ne_of_gt (positive_neighborhood_of_outside_null ν hx hε))
      (ne_of_gt (positive_neighborhood_of_outside_null ν hy hε)))
  exact (ne_of_gt hrect) hrect0

theorem law_essential_interval_of_copy_gap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hgap : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), |z.1-z.2| ≤ 1) :
    ∃ c : ℝ, ∀ᵐ x ∂ν, x ∈ Icc c (c+1) := by
  have hAE : ∀ᵐ x ∂ν, x ∉ nullRationalNeighborhoods ν := by
    apply ae_iff.mpr
    simpa only [not_not] using nullRationalNeighborhoods_null ν
  obtain ⟨x0,hx0⟩ := hAE.exists
  let S : Set ℝ := {x | x ∉ nullRationalNeighborhoods ν}
  have hne : S.Nonempty := ⟨x0,hx0⟩
  have hb : BddBelow S := by
    refine ⟨x0-1,?_⟩
    intro x hx
    have h := copy_gap_support_sub_le_one ν hgap hx0 hx
    linarith
  refine ⟨sInf S,hAE.mono (fun x hx => ?_)⟩
  refine ⟨csInf_le hb hx,?_⟩
  have hlow : x-1 ≤ sInf S := by
    apply le_csInf hne
    intro y hy
    have h := copy_gap_support_sub_le_one ν hgap hx hy
    linarith
  linarith

theorem independent_copy_essential_interval {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    (hgap : ∀ᵐ ω ∂μ, |X ω-X' ω| ≤ 1) :
    ∃ c : ℝ, ∀ᵐ ω ∂μ, X ω ∈ Icc c (c+1) := by
  let ν := Measure.map X μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hPair := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hX'.aemeasurable).mp hi
  rw [← he.map_eq] at hPair
  have hnull : μ {ω | 1 < |X ω-X' ω|} = 0 := by
    simpa only [not_le] using ae_iff.mp hgap
  have hm : Measurable (fun z : ℝ × ℝ => |z.1-z.2|) :=
    (continuous_fst.sub continuous_snd).abs.measurable
  have hnullProd : (ν.prod ν) {z : ℝ × ℝ | 1 < |z.1-z.2|} = 0 := by
    rw [← hPair,Measure.map_apply (hX.prodMk hX') (measurableSet_lt measurable_const hm)]
    exact hnull
  have hgapProd : ∀ᵐ z : ℝ × ℝ ∂(ν.prod ν), |z.1-z.2| ≤ 1 := by
    apply ae_iff.mpr
    simpa only [not_le] using hnullProd
  obtain ⟨c,hc⟩ := law_essential_interval_of_copy_gap ν hgapProd
  exact ⟨c,ae_of_ae_map hX.aemeasurable hc⟩

end ScalarMonotone.EndOfPaper
end
