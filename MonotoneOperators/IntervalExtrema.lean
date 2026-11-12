import MonotoneOperators.Order
import MonotoneOperators.ResolventEnvelopes

/-!
# Finite extrema of intervals

The hull formulas retain open and closed endpoints, including unbounded
intervals.  Finiteness and nonemptiness are required by the hull identities.
-/

namespace ScalarMonotone

open Set

variable {ι : Type*}

def intervalInf (I : ι → Set ℝ) : Set ℝ :=
  (⋃ i, upperHull (I i)) ∩ (⋂ i, lowerHull (I i))

def intervalSup (I : ι → Set ℝ) : Set ℝ :=
  (⋃ i, lowerHull (I i)) ∩ (⋂ i, upperHull (I i))

theorem intervalInf_ordConnected (I : ι → Set ℝ) : (intervalInf I).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  rcases mem_iUnion.mp hx.1 with ⟨i, a, ha, hax⟩
  refine ⟨mem_iUnion.mpr ⟨i, a, ha, hax.trans hz.1⟩, mem_iInter.mpr ?_⟩
  intro j
  rcases mem_iInter.mp hy.2 j with ⟨b, hb, hyb⟩
  exact ⟨b, hb, hz.2.trans hyb⟩

theorem intervalSup_ordConnected (I : ι → Set ℝ) : (intervalSup I).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  rcases mem_iUnion.mp hy.1 with ⟨i, a, ha, hya⟩
  refine ⟨mem_iUnion.mpr ⟨i, a, ha, hz.2.trans hya⟩, mem_iInter.mpr ?_⟩
  intro j
  rcases mem_iInter.mp hx.2 j with ⟨b, hb, hbx⟩
  exact ⟨b, hb, hbx.trans hz.1⟩

section Finite

variable [Finite ι] [Nonempty ι] (I : ι → Set ℝ)
variable (hI : ∀ i, (I i).Nonempty)

include hI

theorem intervalInf_nonempty : (intervalInf I).Nonempty := by
  classical
  choose a ha using hI
  obtain ⟨i, hi⟩ := finite_exists_min a
  refine ⟨a i, mem_iUnion.mpr ⟨i, a i, ha i, le_rfl⟩, mem_iInter.mpr ?_⟩
  intro j
  exact ⟨a j, ha j, hi j⟩

theorem intervalSup_nonempty : (intervalSup I).Nonempty := by
  classical
  choose a ha using hI
  obtain ⟨i, hi⟩ := finite_exists_max a
  refine ⟨a i, mem_iUnion.mpr ⟨i, a i, ha i, le_rfl⟩, mem_iInter.mpr ?_⟩
  intro j
  exact ⟨a j, ha j, hi j⟩

theorem upperHull_intervalInf : upperHull (intervalInf I) = ⋃ i, upperHull (I i) := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    rcases mem_iUnion.mp hy.1 with ⟨i, z, hz, hzy⟩
    exact mem_iUnion.mpr ⟨i, z, hz, hzy.trans hyx⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, z, hz, hzx⟩
    choose a ha using hI
    obtain ⟨j, hj⟩ := finite_exists_min a
    refine ⟨min z (a j), ?_, (min_le_left _ _).trans hzx⟩
    refine ⟨?_, mem_iInter.mpr (fun k => ⟨a k, ha k,
      (min_le_right _ _).trans (hj k)⟩)⟩
    rcases le_total z (a j) with h | h
    · exact mem_iUnion.mpr ⟨i, z, hz, by simpa [min_eq_left h]⟩
    · exact mem_iUnion.mpr ⟨j, a j, ha j, by simpa [min_eq_right h]⟩

theorem lowerHull_intervalInf : lowerHull (intervalInf I) = ⋂ i, lowerHull (I i) := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine mem_iInter.mpr ?_
    intro i
    rcases mem_iInter.mp hy.2 i with ⟨z, hz, hyz⟩
    exact ⟨z, hz, hxy.trans hyz⟩
  · intro hx
    have h : ∀ i, ∃ a ∈ I i, x ≤ a := fun i => mem_iInter.mp hx i
    choose a ha hxa using h
    obtain ⟨i, hi⟩ := finite_exists_min a
    refine ⟨a i, ⟨mem_iUnion.mpr ⟨i, a i, ha i, le_rfl⟩,
      mem_iInter.mpr (fun j => ⟨a j, ha j, hi j⟩)⟩, hxa i⟩

theorem upperHull_intervalSup : upperHull (intervalSup I) = ⋂ i, upperHull (I i) := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine mem_iInter.mpr ?_
    intro i
    rcases mem_iInter.mp hy.2 i with ⟨z, hz, hzy⟩
    exact ⟨z, hz, hzy.trans hyx⟩
  · intro hx
    have h : ∀ i, ∃ a ∈ I i, a ≤ x := fun i => mem_iInter.mp hx i
    choose a ha hax using h
    obtain ⟨i, hi⟩ := finite_exists_max a
    refine ⟨a i, ⟨mem_iUnion.mpr ⟨i, a i, ha i, le_rfl⟩,
      mem_iInter.mpr (fun j => ⟨a j, ha j, hi j⟩)⟩, hax i⟩

theorem lowerHull_intervalSup : lowerHull (intervalSup I) = ⋃ i, lowerHull (I i) := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases mem_iUnion.mp hy.1 with ⟨i, z, hz, hyz⟩
    exact mem_iUnion.mpr ⟨i, z, hz, hxy.trans hyz⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, z, hz, hxz⟩
    choose a ha using hI
    obtain ⟨j, hj⟩ := finite_exists_max a
    refine ⟨max z (a j), ?_, hxz.trans (le_max_left _ _)⟩
    refine ⟨?_, mem_iInter.mpr (fun k => ⟨a k, ha k,
      (hj k).trans (le_max_right _ _)⟩)⟩
    rcases le_total z (a j) with h | h
    · exact mem_iUnion.mpr ⟨j, a j, ha j, by simpa [max_eq_right h]⟩
    · exact mem_iUnion.mpr ⟨i, z, hz, by simpa [max_eq_left h]⟩

theorem intervalInf_le (i : ι) : IntervalLE (intervalInf I) (I i) := by
  rw [IntervalLE, upperHull_intervalInf I hI, lowerHull_intervalInf I hI]
  exact ⟨subset_iUnion_of_subset i Subset.rfl, iInter_subset _ i⟩

theorem le_intervalInf {J : Set ℝ} (h : ∀ i, IntervalLE J (I i)) :
    IntervalLE J (intervalInf I) := by
  rw [IntervalLE, upperHull_intervalInf I hI, lowerHull_intervalInf I hI]
  exact ⟨iUnion_subset (fun i => (h i).1), subset_iInter (fun i => (h i).2)⟩

theorem le_intervalSup (i : ι) : IntervalLE (I i) (intervalSup I) := by
  rw [IntervalLE, upperHull_intervalSup I hI, lowerHull_intervalSup I hI]
  exact ⟨iInter_subset _ i, subset_iUnion_of_subset i Subset.rfl⟩

theorem intervalSup_le {J : Set ℝ} (h : ∀ i, IntervalLE (I i) J) :
    IntervalLE (intervalSup I) J := by
  rw [IntervalLE, upperHull_intervalSup I hI, lowerHull_intervalSup I hI]
  exact ⟨subset_iInter (fun i => (h i).1), iUnion_subset (fun i => (h i).2)⟩

theorem intervalInf_universal {J : Set ℝ} :
    IntervalLE J (intervalInf I) ↔ ∀ i, IntervalLE J (I i) := by
  constructor
  · intro h i
    have hi := intervalInf_le I hI i
    exact ⟨hi.1.trans h.1, h.2.trans hi.2⟩
  · exact le_intervalInf I hI

theorem intervalSup_universal {J : Set ℝ} :
    IntervalLE (intervalSup I) J ↔ ∀ i, IntervalLE (I i) J := by
  constructor
  · intro h i
    have hi := le_intervalSup I hI i
    exact ⟨h.1.trans hi.1, hi.2.trans h.2⟩
  · exact intervalSup_le I hI

end Finite

theorem intervalInf_pair_eq_left_iff {I J : Set ℝ}
    (hIn : I.Nonempty) (hJn : J.Nonempty) (hIo : I.OrdConnected) :
    intervalInf (fun b : Bool => if b then I else J) = I ↔ IntervalLE I J := by
  let F : Bool → Set ℝ := fun b => if b then I else J
  have hn : ∀ b, (F b).Nonempty := by intro b; cases b <;> assumption
  constructor
  · intro h
    have hh := intervalInf_le F hn false
    simpa only [F, Bool.false_eq_true, if_false, h] using hh
  · intro h
    apply intervalLE_antisymm (intervalInf_ordConnected F) hIo
    · simpa only [F, if_true] using intervalInf_le F hn true
    · apply le_intervalInf F hn
      intro b
      cases b
      · exact h
      · exact intervalLE_refl I

theorem intervalSup_pair_eq_right_iff {I J : Set ℝ}
    (hIn : I.Nonempty) (hJn : J.Nonempty) (hJo : J.OrdConnected) :
    intervalSup (fun b : Bool => if b then I else J) = J ↔ IntervalLE I J := by
  let F : Bool → Set ℝ := fun b => if b then I else J
  have hn : ∀ b, (F b).Nonempty := by intro b; cases b <;> assumption
  constructor
  · intro h
    have hh := le_intervalSup F hn true
    simpa only [F, if_true, h] using hh
  · intro h
    apply intervalLE_antisymm (intervalSup_ordConnected F) hJo
    · apply intervalSup_le F hn
      intro b
      cases b
      · exact intervalLE_refl J
      · exact h
    · simpa only [F, Bool.false_eq_true, if_false] using le_intervalSup F hn false

theorem intervalLE_Icc_iff {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IntervalLE (Icc a b) (Icc c d) ↔ a ≤ c ∧ b ≤ d := by
  constructor
  · intro h
    obtain ⟨x, hx, hxc⟩ := h.1 (mem_upperHull (left_mem_Icc.mpr hcd))
    obtain ⟨y, hy, hby⟩ := h.2 (mem_lowerHull (right_mem_Icc.mpr hab))
    exact ⟨hx.1.trans hxc, hby.trans hy.2⟩
  · rintro ⟨hac, hbd⟩
    constructor
    · rintro x ⟨y, hy, hyx⟩
      exact ⟨a, left_mem_Icc.mpr hab, hac.trans (hy.1.trans hyx)⟩
    · rintro x ⟨y, hy, hxy⟩
      exact ⟨d, right_mem_Icc.mpr hcd, hxy.trans (hy.2.trans hbd)⟩

theorem intervalLE_Ico_Ioc : IntervalLE (Ico (0 : ℝ) 1) (Ioc 0 1) := by
  constructor
  · rintro x ⟨y, hy, hyx⟩
    exact ⟨0, by norm_num, hy.1.le.trans hyx⟩
  · rintro x ⟨y, hy, hxy⟩
    exact ⟨1, by norm_num, hxy.trans hy.2.le⟩

theorem interval_Ioo_Icc_incomparable :
    ¬ IntervalLE (Ioo (0 : ℝ) 1) (Icc 0 1) ∧
      ¬ IntervalLE (Icc (0 : ℝ) 1) (Ioo 0 1) := by
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := h.1 (mem_upperHull (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
    linarith [hx.1]
  · intro h
    obtain ⟨x, hx, h1x⟩ := h.2 (mem_lowerHull (show (1 : ℝ) ∈ Icc 0 1 by norm_num))
    linarith [hx.2]

end ScalarMonotone
