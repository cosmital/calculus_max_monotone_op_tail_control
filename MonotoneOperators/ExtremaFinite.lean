import MonotoneOperators.ExtremaComplete
import MonotoneOperators.IntervalEndpoints

/-!
# Finite domains, ranges, and fibers

Finite envelopes attain their scalar extrema.  Their range hulls can therefore
be computed exactly, and the common-domain fiber formulas retain all endpoint
information.
-/

namespace ScalarMonotone

open Set

noncomputable section

theorem IncGraph.mem_iff_J (f : IncGraph) {x u : ℝ} :
    u ∈ f.val x ↔ f.J (x + u) = x := (resolvent_eq_iff f.property).symm
theorem DecGraph.mem_iff_J (f : DecGraph) {x u : ℝ} :
    u ∈ f.val x ↔ f.J (x - u) = x := (decreasing_resolvent_eq_iff f.property).symm

theorem IncGraph.dom_eq_range_J (f : IncGraph) : dom f.val = range f.J :=
  dom_eq_range_resolvent f.property

theorem DecGraph.dom_eq_range_J (f : DecGraph) : dom f.val = range f.J := by
  ext x
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨x - u, (DecGraph.mem_iff_J f).mp hu⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, decreasing_resolvent_mem f.property s⟩

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem IncGraph.J_iInf_finite (f : ι → IncGraph) (s : ℝ) :
    (⨅ i, f i).J s = ⨆ i, (f i).J s := IncGraph.J_iInf f (finite_range f).bddBelow s
theorem IncGraph.J_iSup_finite (f : ι → IncGraph) (s : ℝ) :
    (⨆ i, f i).J s = ⨅ i, (f i).J s := IncGraph.J_iSup f (finite_range f).bddAbove s
theorem DecGraph.J_iInf_finite (f : ι → DecGraph) (s : ℝ) :
    (⨅ i, f i).J s = ⨅ i, (f i).J s := DecGraph.J_iInf f (finite_range f).bddBelow s
theorem DecGraph.J_iSup_finite (f : ι → DecGraph) (s : ℝ) :
    (⨆ i, f i).J s = ⨆ i, (f i).J s := DecGraph.J_iSup f (finite_range f).bddAbove s

theorem IncGraph.mem_iInf_imp_exists (f : ι → IncGraph) {x u : ℝ}
    (h : u ∈ (⨅ i, f i).val x) : ∃ i, u ∈ (f i).val x := by
  rw [IncGraph.mem_iff_J, IncGraph.J_iInf_finite] at h
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => (f i).J (x + u))
  exact ⟨i, (IncGraph.mem_iff_J _).mpr (hi.trans h)⟩

theorem IncGraph.mem_iSup_imp_exists (f : ι → IncGraph) {x u : ℝ}
    (h : u ∈ (⨆ i, f i).val x) : ∃ i, u ∈ (f i).val x := by
  rw [IncGraph.mem_iff_J, IncGraph.J_iSup_finite] at h
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => (f i).J (x + u))
  exact ⟨i, (IncGraph.mem_iff_J _).mpr (hi.trans h)⟩

theorem DecGraph.mem_iInf_imp_exists (f : ι → DecGraph) {x u : ℝ}
    (h : u ∈ (⨅ i, f i).val x) : ∃ i, u ∈ (f i).val x := by
  rw [DecGraph.mem_iff_J, DecGraph.J_iInf_finite] at h
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => (f i).J (x - u))
  exact ⟨i, (DecGraph.mem_iff_J _).mpr (hi.trans h)⟩

theorem DecGraph.mem_iSup_imp_exists (f : ι → DecGraph) {x u : ℝ}
    (h : u ∈ (⨆ i, f i).val x) : ∃ i, u ∈ (f i).val x := by
  rw [DecGraph.mem_iff_J, DecGraph.J_iSup_finite] at h
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => (f i).J (x - u))
  exact ⟨i, (DecGraph.mem_iff_J _).mpr (hi.trans h)⟩

theorem upperHull_range_ciInf (q : ι → ℝ → ℝ) :
    upperHull (range (fun s => ⨅ i, q i s)) = ⋃ i, upperHull (range (q i)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, rfl⟩, hyx⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => q i s)
    exact mem_iUnion.mpr ⟨i, q i s, mem_range_self s, hi ▸ hyx⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, y, ⟨s, rfl⟩, hyx⟩
    exact ⟨⨅ j, q j s, mem_range_self s,
      (ciInf_le (finite_range _).bddBelow i).trans hyx⟩

theorem lowerHull_range_ciInf (q : ι → ℝ → ℝ) (hm : ∀ i, Monotone (q i)) :
    lowerHull (range (fun s => ⨅ i, q i s)) = ⋂ i, lowerHull (range (q i)) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨s, rfl⟩, hxy⟩
    exact mem_iInter.mpr (fun i => ⟨q i s, mem_range_self s,
      hxy.trans (ciInf_le (finite_range _).bddBelow i)⟩)
  · intro hx
    have h : ∀ i, ∃ s, x ≤ q i s := by
      intro i
      rcases mem_iInter.mp hx i with ⟨y, ⟨s, rfl⟩, hxy⟩
      exact ⟨s, hxy⟩
    choose s hs using h
    obtain ⟨i, hi⟩ := finite_exists_max s
    exact ⟨⨅ j, q j (s i), mem_range_self (s i),
      le_ciInf (fun j => (hs j).trans (hm j (hi j)))⟩

theorem lowerHull_range_ciSup (q : ι → ℝ → ℝ) :
    lowerHull (range (fun s => ⨆ i, q i s)) = ⋃ i, lowerHull (range (q i)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, rfl⟩, hxy⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => q i s)
    exact mem_iUnion.mpr ⟨i, q i s, mem_range_self s, hi ▸ hxy⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, y, ⟨s, rfl⟩, hxy⟩
    exact ⟨⨆ j, q j s, mem_range_self s,
      hxy.trans (le_ciSup (finite_range (fun j => q j s)).bddAbove i)⟩

theorem upperHull_range_ciSup (q : ι → ℝ → ℝ) (hm : ∀ i, Monotone (q i)) :
    upperHull (range (fun s => ⨆ i, q i s)) = ⋂ i, upperHull (range (q i)) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨s, rfl⟩, hyx⟩
    exact mem_iInter.mpr (fun i => ⟨q i s, mem_range_self s,
      (le_ciSup (finite_range _).bddAbove i).trans hyx⟩)
  · intro hx
    have h : ∀ i, ∃ s, q i s ≤ x := by
      intro i
      rcases mem_iInter.mp hx i with ⟨y, ⟨s, rfl⟩, hyx⟩
      exact ⟨s, hyx⟩
    choose s hs using h
    obtain ⟨i, hi⟩ := finite_exists_min s
    exact ⟨⨆ j, q j (s i), mem_range_self (s i),
      ciSup_le (fun j => (hm j (hi j)).trans (hs j))⟩

theorem range_ciInf_eq_intervalInf (q : ι → ℝ → ℝ)
    (hm : ∀ i, Monotone (q i)) (hl : ∀ i, LipschitzWith 1 (q i)) :
    range (fun s => ⨅ i, q i s) = intervalInf (fun i => range (q i)) := by
  have hc := (lipschitz_ciInf hl (fun _ => (finite_range _).bddBelow)).continuous
  calc
    range (fun s => ⨅ i, q i s) =
        upperHull (range (fun s => ⨅ i, q i s)) ∩
        lowerHull (range (fun s => ⨅ i, q i s)) :=
      (hull_inter_eq (isPreconnected_range hc).ordConnected).symm
    _ = _ := by rw [upperHull_range_ciInf, lowerHull_range_ciInf q hm]; rfl

theorem range_ciSup_eq_intervalSup (q : ι → ℝ → ℝ)
    (hm : ∀ i, Monotone (q i)) (hl : ∀ i, LipschitzWith 1 (q i)) :
    range (fun s => ⨆ i, q i s) = intervalSup (fun i => range (q i)) := by
  have hc := (lipschitz_ciSup hl (fun _ => (finite_range _).bddAbove)).continuous
  calc
    range (fun s => ⨆ i, q i s) =
        upperHull (range (fun s => ⨆ i, q i s)) ∩
        lowerHull (range (fun s => ⨆ i, q i s)) :=
      (hull_inter_eq (isPreconnected_range hc).ordConnected).symm
    _ = _ := by
      rw [upperHull_range_ciSup q hm, lowerHull_range_ciSup, inter_comm]
      rfl

theorem IncGraph.dom_iInf (f : ι → IncGraph) :
    dom (⨅ i, f i).val = intervalSup (fun i => dom (f i).val) := by
  have hJ : (⨅ i, f i).J = fun s => ⨆ i, (f i).J s :=
    funext (IncGraph.J_iInf_finite f)
  simp only [IncGraph.dom_eq_range_J]
  rw [hJ]
  exact range_ciSup_eq_intervalSup (fun i => (f i).J)
    (fun i => (f i).monotone_J) (fun i => (f i).lipschitz_J)

theorem IncGraph.dom_iSup (f : ι → IncGraph) :
    dom (⨆ i, f i).val = intervalInf (fun i => dom (f i).val) := by
  have hJ : (⨆ i, f i).J = fun s => ⨅ i, (f i).J s :=
    funext (IncGraph.J_iSup_finite f)
  simp only [IncGraph.dom_eq_range_J]
  rw [hJ]
  exact range_ciInf_eq_intervalInf (fun i => (f i).J)
    (fun i => (f i).monotone_J) (fun i => (f i).lipschitz_J)

theorem DecGraph.dom_iInf (f : ι → DecGraph) :
    dom (⨅ i, f i).val = intervalInf (fun i => dom (f i).val) := by
  have hJ : (⨅ i, f i).J = fun s => ⨅ i, (f i).J s :=
    funext (DecGraph.J_iInf_finite f)
  simp only [DecGraph.dom_eq_range_J]
  rw [hJ]
  exact range_ciInf_eq_intervalInf (fun i => (f i).J)
    (fun i => (f i).monotone_J) (fun i => (f i).lipschitz_J)

theorem DecGraph.dom_iSup (f : ι → DecGraph) :
    dom (⨆ i, f i).val = intervalSup (fun i => dom (f i).val) := by
  have hJ : (⨆ i, f i).J = fun s => ⨆ i, (f i).J s :=
    funext (DecGraph.J_iSup_finite f)
  simp only [DecGraph.dom_eq_range_J]
  rw [hJ]
  exact range_ciSup_eq_intervalSup (fun i => (f i).J)
    (fun i => (f i).monotone_J) (fun i => (f i).lipschitz_J)

theorem IncGraph.ran_iInf (f : ι → IncGraph) :
    ran (⨅ i, f i).val = intervalInf (fun i => ran (f i).val) := by
  change dom (⨅ i, f i).inv.val = intervalInf (fun i => dom (f i).inv.val)
  rw [IncGraph.inv_iInf f (finite_range f).bddBelow, IncGraph.dom_iSup]

theorem IncGraph.ran_iSup (f : ι → IncGraph) :
    ran (⨆ i, f i).val = intervalSup (fun i => ran (f i).val) := by
  change dom (⨆ i, f i).inv.val = intervalSup (fun i => dom (f i).inv.val)
  rw [IncGraph.inv_iSup f (finite_range f).bddAbove, IncGraph.dom_iInf]

theorem DecGraph.ran_iInf (f : ι → DecGraph) :
    ran (⨅ i, f i).val = intervalInf (fun i => ran (f i).val) := by
  change dom (⨅ i, f i).inv.val = intervalInf (fun i => dom (f i).inv.val)
  rw [DecGraph.inv_iInf f (finite_range f).bddBelow, DecGraph.dom_iInf]

theorem DecGraph.ran_iSup (f : ι → DecGraph) :
    ran (⨆ i, f i).val = intervalSup (fun i => ran (f i).val) := by
  change dom (⨆ i, f i).inv.val = intervalSup (fun i => dom (f i).inv.val)
  rw [DecGraph.inv_iSup f (finite_range f).bddAbove, DecGraph.dom_iSup]

theorem finite_ciSup_eq_iff (a : ι → ℝ) (x : ℝ) :
    (⨆ i, a i) = x ↔ (∀ i, a i ≤ x) ∧ ∃ i, x ≤ a i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
    exact ⟨fun j => h ▸ le_ciSup (finite_range a).bddAbove j,
      ⟨i, le_of_eq (hi.trans h).symm⟩⟩
  · rintro ⟨h, i, hi⟩
    exact le_antisymm (ciSup_le h) (hi.trans (le_ciSup (finite_range a).bddAbove i))

theorem finite_ciInf_eq_iff (a : ι → ℝ) (x : ℝ) :
    (⨅ i, a i) = x ↔ (∀ i, x ≤ a i) ∧ ∃ i, a i ≤ x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := a)
    exact ⟨fun j => h ▸ ciInf_le (finite_range a).bddBelow j,
      ⟨i, le_of_eq (hi.trans h)⟩⟩
  · rintro ⟨h, i, hi⟩
    exact le_antisymm ((ciInf_le (finite_range a).bddBelow i).trans hi) (le_ciInf h)

theorem IncGraph.fiber_iInf (f : ι → IncGraph) {x : ℝ} (hx : ∀ i, x ∈ dom (f i).val) :
    (⨅ i, f i).val x = intervalInf (fun i => (f i).val x) := by
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_iInf_finite, finite_ciSup_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨mem_iUnion.mpr ⟨i, (resolvent_ge_iff_upperHull (f i).property (hx i)).mp hi⟩,
      mem_iInter.mpr (fun j => (resolvent_le_iff_lowerHull (f j).property (hx j)).mp (h j))⟩
  · rintro ⟨hu, hl⟩
    rcases mem_iUnion.mp hu with ⟨i, hi⟩
    exact ⟨fun j => (resolvent_le_iff_lowerHull (f j).property (hx j)).mpr
      (mem_iInter.mp hl j),
      ⟨i, (resolvent_ge_iff_upperHull (f i).property (hx i)).mpr hi⟩⟩

theorem IncGraph.fiber_iSup (f : ι → IncGraph) {x : ℝ} (hx : ∀ i, x ∈ dom (f i).val) :
    (⨆ i, f i).val x = intervalSup (fun i => (f i).val x) := by
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_iSup_finite, finite_ciInf_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨mem_iUnion.mpr ⟨i, (resolvent_le_iff_lowerHull (f i).property (hx i)).mp hi⟩,
      mem_iInter.mpr (fun j => (resolvent_ge_iff_upperHull (f j).property (hx j)).mp (h j))⟩
  · rintro ⟨hl, hu⟩
    rcases mem_iUnion.mp hl with ⟨i, hi⟩
    exact ⟨fun j => (resolvent_ge_iff_upperHull (f j).property (hx j)).mpr
      (mem_iInter.mp hu j),
      ⟨i, (resolvent_le_iff_lowerHull (f i).property (hx i)).mpr hi⟩⟩

theorem DecGraph.fiber_iInf (f : ι → DecGraph) {x : ℝ} (hx : ∀ i, x ∈ dom (f i).val) :
    (⨅ i, f i).val x = intervalInf (fun i => (f i).val x) := by
  ext u
  rw [DecGraph.mem_iff_J, DecGraph.J_iInf_finite, finite_ciInf_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨mem_iUnion.mpr ⟨i,
      (decreasingResolvent_le_iff_upperHull (f i).property (hx i)).mp hi⟩,
      mem_iInter.mpr (fun j =>
        (decreasingResolvent_ge_iff_lowerHull (f j).property (hx j)).mp (h j))⟩
  · rintro ⟨hu, hl⟩
    rcases mem_iUnion.mp hu with ⟨i, hi⟩
    exact ⟨fun j => (decreasingResolvent_ge_iff_lowerHull (f j).property (hx j)).mpr
      (mem_iInter.mp hl j),
      ⟨i, (decreasingResolvent_le_iff_upperHull (f i).property (hx i)).mpr hi⟩⟩

theorem DecGraph.fiber_iSup (f : ι → DecGraph) {x : ℝ} (hx : ∀ i, x ∈ dom (f i).val) :
    (⨆ i, f i).val x = intervalSup (fun i => (f i).val x) := by
  ext u
  rw [DecGraph.mem_iff_J, DecGraph.J_iSup_finite, finite_ciSup_eq_iff]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨mem_iUnion.mpr ⟨i,
      (decreasingResolvent_ge_iff_lowerHull (f i).property (hx i)).mp hi⟩,
      mem_iInter.mpr (fun j =>
        (decreasingResolvent_le_iff_upperHull (f j).property (hx j)).mp (h j))⟩
  · rintro ⟨hl, hu⟩
    rcases mem_iUnion.mp hl with ⟨i, hi⟩
    exact ⟨fun j => (decreasingResolvent_le_iff_upperHull (f j).property (hx j)).mpr
      (mem_iInter.mp hu j),
      ⟨i, (decreasingResolvent_ge_iff_lowerHull (f i).property (hx i)).mpr hi⟩⟩

theorem IncGraph.fiber_iInf_endpoints (f : ι → IncGraph) {x : ℝ}
    (hx : ∀ i, x ∈ dom (f i).val) :
    (⨅ i, f i).val x = {u : ℝ |
      (⨅ i, setLowerEndpoint ((f i).val x)) ≤ (u : EReal) ∧
      (u : EReal) ≤ ⨅ i, setUpperEndpoint ((f i).val x)} := by
  rw [IncGraph.fiber_iInf f hx]
  exact intervalInf_eq_endpoints _ hx (fun i => maximal_fiber_closed (f i).property x)

theorem IncGraph.fiber_iSup_endpoints (f : ι → IncGraph) {x : ℝ}
    (hx : ∀ i, x ∈ dom (f i).val) :
    (⨆ i, f i).val x = {u : ℝ |
      (⨆ i, setLowerEndpoint ((f i).val x)) ≤ (u : EReal) ∧
      (u : EReal) ≤ ⨆ i, setUpperEndpoint ((f i).val x)} := by
  rw [IncGraph.fiber_iSup f hx]
  exact intervalSup_eq_endpoints _ hx (fun i => maximal_fiber_closed (f i).property x)

theorem DecGraph.fiber_iInf_endpoints (f : ι → DecGraph) {x : ℝ}
    (hx : ∀ i, x ∈ dom (f i).val) :
    (⨅ i, f i).val x = {u : ℝ |
      (⨅ i, setLowerEndpoint ((f i).val x)) ≤ (u : EReal) ∧
      (u : EReal) ≤ ⨅ i, setUpperEndpoint ((f i).val x)} := by
  rw [DecGraph.fiber_iInf f hx]
  exact intervalInf_eq_endpoints _ hx (fun i => decreasing_fiber_closed (f i).property x)

theorem DecGraph.fiber_iSup_endpoints (f : ι → DecGraph) {x : ℝ}
    (hx : ∀ i, x ∈ dom (f i).val) :
    (⨆ i, f i).val x = {u : ℝ |
      (⨆ i, setLowerEndpoint ((f i).val x)) ≤ (u : EReal) ∧
      (u : EReal) ≤ ⨆ i, setUpperEndpoint ((f i).val x)} := by
  rw [DecGraph.fiber_iSup f hx]
  exact intervalSup_eq_endpoints _ hx (fun i => decreasing_fiber_closed (f i).property x)

end

end ScalarMonotone
