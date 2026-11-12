import MonotoneOperators.ExtremaFinite
import MonotoneOperators.IntervalIntersection

/-!
# Finite fibers with empty members omitted

The restriction to active indices is justified by connectedness of each
resolvent range.  It is valid at a point of the extremum's domain, and does not
assume that the original family has a common domain there.
-/

namespace ScalarMonotone

open Set

theorem range_le_of_not_mem {q : ℝ → ℝ} (ho : (range q).OrdConnected)
    {x s₀ : ℝ} (hx : x ∉ range q) (h₀ : q s₀ ≤ x) (s : ℝ) : q s ≤ x := by
  by_contra h
  exact hx (ho.out (mem_range_self s₀) (mem_range_self s) ⟨h₀, (lt_of_not_ge h).le⟩)

theorem range_ge_of_not_mem {q : ℝ → ℝ} (ho : (range q).OrdConnected)
    {x s₀ : ℝ} (hx : x ∉ range q) (h₀ : x ≤ q s₀) (s : ℝ) : x ≤ q s := by
  by_contra h
  exact hx (ho.out (mem_range_self s) (mem_range_self s₀) ⟨(lt_of_not_ge h).le, h₀⟩)

theorem IncGraph.J_le_of_not_mem_dom (f : IncGraph) {x s₀ : ℝ}
    (hx : x ∉ dom f.val) (h₀ : f.J s₀ ≤ x) (s : ℝ) : f.J s ≤ x :=
  range_le_of_not_mem (isPreconnected_range f.lipschitz_J.continuous).ordConnected
    (by simpa only [IncGraph.dom_eq_range_J] using hx) h₀ s

theorem IncGraph.J_ge_of_not_mem_dom (f : IncGraph) {x s₀ : ℝ}
    (hx : x ∉ dom f.val) (h₀ : x ≤ f.J s₀) (s : ℝ) : x ≤ f.J s :=
  range_ge_of_not_mem (isPreconnected_range f.lipschitz_J.continuous).ordConnected
    (by simpa only [IncGraph.dom_eq_range_J] using hx) h₀ s

theorem DecGraph.J_le_of_not_mem_dom (f : DecGraph) {x s₀ : ℝ}
    (hx : x ∉ dom f.val) (h₀ : f.J s₀ ≤ x) (s : ℝ) : f.J s ≤ x :=
  range_le_of_not_mem (isPreconnected_range f.lipschitz_J.continuous).ordConnected
    (by simpa only [DecGraph.dom_eq_range_J] using hx) h₀ s

theorem DecGraph.J_ge_of_not_mem_dom (f : DecGraph) {x s₀ : ℝ}
    (hx : x ∉ dom f.val) (h₀ : x ≤ f.J s₀) (s : ℝ) : x ≤ f.J s :=
  range_ge_of_not_mem (isPreconnected_range f.lipschitz_J.continuous).ordConnected
    (by simpa only [DecGraph.dom_eq_range_J] using hx) h₀ s

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem IncGraph.fiber_iInf_active (f : ι → IncGraph) {x : ℝ}
    (hx : x ∈ dom (⨅ i, f i).val) :
    (⨅ i, f i).val x = intervalInf
      (fun i : {i // x ∈ dom (f i).val} => (f i.val).val x) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hx
  have h₀ := (IncGraph.mem_iff_J _).mp hu₀
  rw [IncGraph.J_iInf_finite, finite_ciSup_eq_iff] at h₀
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_iInf_finite, finite_ciSup_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    have heq := le_antisymm (h i) hi
    have hix : x ∈ dom (f i).val := ⟨u, (IncGraph.mem_iff_J _).mpr heq⟩
    exact ⟨mem_iUnion.mpr ⟨⟨i, hix⟩,
      (resolvent_ge_iff_upperHull (f i).property hix).mp hi⟩,
      mem_iInter.mpr (fun j =>
        (resolvent_le_iff_lowerHull (f j.val).property j.property).mp (h j.val))⟩
  · rintro ⟨hu, hl⟩
    rcases mem_iUnion.mp hu with ⟨i, hi⟩
    refine ⟨?_, ⟨i.val, (resolvent_ge_iff_upperHull (f i.val).property i.property).mpr hi⟩⟩
    intro j
    by_cases hj : x ∈ dom (f j).val
    · exact (resolvent_le_iff_lowerHull (f j).property hj).mpr
        (mem_iInter.mp hl ⟨j, hj⟩)
    · exact (f j).J_le_of_not_mem_dom hj (h₀.1 j) (x + u)

theorem IncGraph.fiber_iSup_active (f : ι → IncGraph) {x : ℝ}
    (hx : x ∈ dom (⨆ i, f i).val) :
    (⨆ i, f i).val x = intervalSup
      (fun i : {i // x ∈ dom (f i).val} => (f i.val).val x) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hx
  have h₀ := (IncGraph.mem_iff_J _).mp hu₀
  rw [IncGraph.J_iSup_finite, finite_ciInf_eq_iff] at h₀
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_iSup_finite, finite_ciInf_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    have heq := le_antisymm hi (h i)
    have hix : x ∈ dom (f i).val := ⟨u, (IncGraph.mem_iff_J _).mpr heq⟩
    exact ⟨mem_iUnion.mpr ⟨⟨i, hix⟩,
      (resolvent_le_iff_lowerHull (f i).property hix).mp hi⟩,
      mem_iInter.mpr (fun j =>
        (resolvent_ge_iff_upperHull (f j.val).property j.property).mp (h j.val))⟩
  · rintro ⟨hl, hu⟩
    rcases mem_iUnion.mp hl with ⟨i, hi⟩
    refine ⟨?_, ⟨i.val, (resolvent_le_iff_lowerHull (f i.val).property i.property).mpr hi⟩⟩
    intro j
    by_cases hj : x ∈ dom (f j).val
    · exact (resolvent_ge_iff_upperHull (f j).property hj).mpr
        (mem_iInter.mp hu ⟨j, hj⟩)
    · exact (f j).J_ge_of_not_mem_dom hj (h₀.1 j) (x + u)

theorem DecGraph.fiber_iInf_active (f : ι → DecGraph) {x : ℝ}
    (hx : x ∈ dom (⨅ i, f i).val) :
    (⨅ i, f i).val x = intervalInf
      (fun i : {i // x ∈ dom (f i).val} => (f i.val).val x) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hx
  have h₀ := (DecGraph.mem_iff_J _).mp hu₀
  rw [DecGraph.J_iInf_finite, finite_ciInf_eq_iff] at h₀
  ext u
  rw [DecGraph.mem_iff_J, DecGraph.J_iInf_finite, finite_ciInf_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    have heq := le_antisymm hi (h i)
    have hix : x ∈ dom (f i).val := ⟨u, (DecGraph.mem_iff_J _).mpr heq⟩
    exact ⟨mem_iUnion.mpr ⟨⟨i, hix⟩,
      (decreasingResolvent_le_iff_upperHull (f i).property hix).mp hi⟩,
      mem_iInter.mpr (fun j =>
        (decreasingResolvent_ge_iff_lowerHull (f j.val).property j.property).mp (h j.val))⟩
  · rintro ⟨hu, hl⟩
    rcases mem_iUnion.mp hu with ⟨i, hi⟩
    refine ⟨?_, ⟨i.val,
      (decreasingResolvent_le_iff_upperHull (f i.val).property i.property).mpr hi⟩⟩
    intro j
    by_cases hj : x ∈ dom (f j).val
    · exact (decreasingResolvent_ge_iff_lowerHull (f j).property hj).mpr
        (mem_iInter.mp hl ⟨j, hj⟩)
    · exact (f j).J_ge_of_not_mem_dom hj (h₀.1 j) (x - u)

theorem DecGraph.fiber_iSup_active (f : ι → DecGraph) {x : ℝ}
    (hx : x ∈ dom (⨆ i, f i).val) :
    (⨆ i, f i).val x = intervalSup
      (fun i : {i // x ∈ dom (f i).val} => (f i.val).val x) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hx
  have h₀ := (DecGraph.mem_iff_J _).mp hu₀
  rw [DecGraph.J_iSup_finite, finite_ciSup_eq_iff] at h₀
  ext u
  rw [DecGraph.mem_iff_J, DecGraph.J_iSup_finite, finite_ciSup_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    have heq := le_antisymm (h i) hi
    have hix : x ∈ dom (f i).val := ⟨u, (DecGraph.mem_iff_J _).mpr heq⟩
    exact ⟨mem_iUnion.mpr ⟨⟨i, hix⟩,
      (decreasingResolvent_ge_iff_lowerHull (f i).property hix).mp hi⟩,
      mem_iInter.mpr (fun j =>
        (decreasingResolvent_le_iff_upperHull (f j.val).property j.property).mp (h j.val))⟩
  · rintro ⟨hl, hu⟩
    rcases mem_iUnion.mp hl with ⟨i, hi⟩
    refine ⟨?_, ⟨i.val,
      (decreasingResolvent_ge_iff_lowerHull (f i.val).property i.property).mpr hi⟩⟩
    intro j
    by_cases hj : x ∈ dom (f j).val
    · exact (decreasingResolvent_le_iff_upperHull (f j).property hj).mpr
        (mem_iInter.mp hu ⟨j, hj⟩)
    · exact (f j).J_le_of_not_mem_dom hj (h₀.1 j) (x - u)

end ScalarMonotone
