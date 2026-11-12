import EndOfPaper.PositiveProfileChain
import EndOfPaper.PositiveChainEmbedding
import EndOfPaper.PositiveCoordinateEstimates
import Mathlib.MeasureTheory.Constructions.Pi

/-!
The actual measurable prescribed-profile sample, including zeros and its exact product identity.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveProfileSampleVector {ι : Type*} (s : ι → ℝ → ℝ) (I : Set ℝ) (u : ℝ) : ι → ℝ := by
  classical
  exact if u ∈ I ∧ ∀ i, 0 < s i u then (fun i => s i u) else 0

theorem positiveProfileSampleVector_mem {ι : Type*} (s : ι → ℝ → ℝ) (I : Set ℝ) (u : ℝ) :
    positiveProfileSampleVector s I u ∈ positiveProfileChain s I := by
  classical
  unfold positiveProfileSampleVector
  split_ifs with h
  · exact Or.inr ⟨u,h.1,h.2,rfl⟩
  · exact positiveProfileChain_zero s I

def positiveProfileSampleSubtype {ι : Type*} (s : ι → ℝ → ℝ) (I : Set ℝ) (u : ℝ) :
    positiveProfileChain s I := ⟨positiveProfileSampleVector s I u,positiveProfileSampleVector_mem s I u⟩

theorem positiveProfileSampleVector_measurable {ι : Type*} [Fintype ι]
    {s : ι → ℝ → ℝ} (hs : ∀ i, Measurable (s i)) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable (positiveProfileSampleVector s I) := by
  classical
  have hset : MeasurableSet {u | u ∈ I ∧ ∀ i, 0 < s i u} := by
    have he : {u | u ∈ I ∧ ∀ i, 0 < s i u} = I ∩ ⋂ i, {u : ℝ | 0 < s i u} := by
      ext u
      simp only [mem_setOf_eq,mem_inter_iff,mem_iInter]
    rw [he]
    exact hI.inter (MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (hs i)))
  exact (measurable_pi_iff.mpr hs).piecewise hset measurable_const

theorem positiveProfileSampleSubtype_measurable {ι : Type*} [Fintype ι]
    {s : ι → ℝ → ℝ} (hs : ∀ i, Measurable (s i)) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable (positiveProfileSampleSubtype s I) :=
  (positiveProfileSampleVector_measurable hs hI).subtype_mk

theorem positiveProfileSampleVector_coordinate_le {ι : Type*} {s : ι → ℝ → ℝ} {I : Set ℝ}
    (h0 : ∀ i u, u ∈ I → 0 ≤ s i u) {u : ℝ} (hu : u ∈ I) (i : ι) :
    positiveProfileSampleVector s I u i ≤ s i u := by
  classical
  unfold positiveProfileSampleVector
  split_ifs
  · exact le_rfl
  · exact h0 i u hu

theorem positiveProfileSampleVector_product {ι : Type*} [Fintype ι] [Nonempty ι]
    {s : ι → ℝ → ℝ} {I : Set ℝ} (h0 : ∀ i u, u ∈ I → 0 ≤ s i u)
    {u : ℝ} (hu : u ∈ I) :
    (∏ i, positiveProfileSampleVector s I u i) = ∏ i, s i u := by
  classical
  unfold positiveProfileSampleVector
  by_cases h : u ∈ I ∧ ∀ i, 0 < s i u
  · simp only [if_pos h]
  · simp only [if_neg h,Pi.zero_apply]
    have hnot : ¬ ∀ i, 0 < s i u := fun hi => h ⟨hu,hi⟩
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    have hi0 : s i u = 0 := le_antisymm (le_of_not_gt hi) (h0 i u hu)
    have hright : (∏ j, s j u) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi0
    rw [hright]
    exact Finset.prod_eq_zero (Finset.mem_univ i) rfl

def positiveProfileChainMetric {n : ℕ} {s : Option (Fin n) → ℝ → ℝ} {I : Set ℝ}
    (hs : ∀ i, AntitoneOn (s i) I) : MetricSpace (PositiveProductPoint (positiveProfileChain s I)) :=
  positiveChainMetric (positiveProfileChain_properties hs).1
    (positiveProfileChain_properties hs).2.1 (positiveProfileChain_properties hs).2.2.1

def positiveProfilePointSample {n : ℕ} (s : Option (Fin n) → ℝ → ℝ) (I : Set ℝ) (u : ℝ) :
    PositiveProductPoint (positiveProfileChain s I) := positiveChainFromSubtype (positiveProfileSampleSubtype s I u)

theorem positiveProfilePointSample_measurable {n : ℕ} {s : Option (Fin n) → ℝ → ℝ} {I : Set ℝ}
    (hs : ∀ i, AntitoneOn (s i) I) (hsm : ∀ i, Measurable (s i)) (hI : MeasurableSet I) :
    letI := positiveProfileChainMetric hs
    @Measurable ℝ (PositiveProductPoint (positiveProfileChain s I)) _
      (borel (PositiveProductPoint (positiveProfileChain s I))) (positiveProfilePointSample s I) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace (PositiveProductPoint (positiveProfileChain s I)) :=
    borel (PositiveProductPoint (positiveProfileChain s I))
  exact (positiveChainMetric_fromSubtype_measurable (positiveProfileChain_properties hs).1
    (positiveProfileChain_properties hs).2.1 (positiveProfileChain_properties hs).2.2.1).comp
      (positiveProfileSampleSubtype_measurable hsm hI)

end ScalarMonotone.EndOfPaper
end
