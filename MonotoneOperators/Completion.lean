import MonotoneOperators.Minty

/-!
# Maximal completion on a specified interval

The construction works for every nonempty interval. The manuscript uses it
only for nonempty open intervals. The closure restriction is essential for
uniqueness, and is included in the theorem statement.
-/

open Set

namespace ScalarMonotone

theorem closure_bounds {I : Set ℝ} {x : ℝ} (hx : x ∈ closure I) :
    (∀ a ∈ lowerBounds I, a ≤ x) ∧ (∀ b ∈ upperBounds I, x ≤ b) := by
  constructor
  · intro a ha
    exact (closure_minimal (show I ⊆ Ici a from ha) isClosed_Ici) hx
  · intro b hb
    exact (closure_minimal (show I ⊆ Iic b from hb) isClosed_Iic) hx

theorem mem_closure_of_bounds {I : Set ℝ} (hI : I.OrdConnected)
    {x : ℝ} (hx : (∀ a ∈ lowerBounds I, a ≤ x) ∧ (∀ b ∈ upperBounds I, x ≤ b)) :
    x ∈ closure I := by
  rw [Metric.mem_closure_iff]
  intro e he
  have ha : ∃ a ∈ I, a < x+e := by
    by_contra hn
    have hlow : x+e ∈ lowerBounds I := by
      intro a ha
      by_contra h
      exact hn ⟨a, ha, lt_of_not_ge h⟩
    have := hx.1 (x+e) hlow
    linarith
  have hb : ∃ b ∈ I, x-e < b := by
    by_contra hn
    have hupp : x-e ∈ upperBounds I := by
      intro b hb
      by_contra h
      exact hn ⟨b, hb, lt_of_not_ge h⟩
    have := hx.2 (x-e) hupp
    linarith
  obtain ⟨a, ha, hal⟩ := ha
  obtain ⟨b, hb, hbu⟩ := hb
  by_cases hax : x-e < a
  · exact ⟨a, ha, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith⟩
  · by_cases hbx : b < x+e
    · exact ⟨b, hb, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith⟩
    · have hxi : x ∈ I := hI.out ha hb ⟨by linarith, by linarith⟩
      exact ⟨x, hxi, by simpa using he⟩

theorem between_closure_mem {I : Set ℝ} (hI : I.OrdConnected)
    {x y z : ℝ} (hx : x ∈ closure I) (hy : y ∈ closure I)
    (hxz : x < z) (hzy : z < y) : z ∈ I := by
  have ha : ∃ a ∈ I, a < z := by
    by_contra hn
    have hlow : z ∈ lowerBounds I := by
      intro a ha
      by_contra h
      exact hn ⟨a, ha, lt_of_not_ge h⟩
    exact (not_le_of_gt hxz) ((closure_bounds hx).1 z hlow)
  have hb : ∃ b ∈ I, z < b := by
    by_contra hn
    have hupp : z ∈ upperBounds I := by
      intro b hb
      by_contra h
      exact hn ⟨b, hb, lt_of_not_ge h⟩
    exact (not_le_of_gt hzy) ((closure_bounds hy).2 z hupp)
  obtain ⟨a, ha, haz⟩ := ha
  obtain ⟨b, hb, hzb⟩ := hb
  exact hI.out ha hb ⟨haz.le, hzb.le⟩

def completion (I : Set ℝ) (f : Operator) : Operator :=
  fun x => {u | x ∈ closure I ∧ Compatible f x u}

theorem completion_increasing {I : Set ℝ} {f : Operator} (hI : I.OrdConnected)
    (hd : dom f = I) : Increasing (completion I f) := by
  apply increasing_iff_order.mpr
  rintro x u y v ⟨hx, hu⟩ ⟨hy, hv⟩ hxy
  have hz : (x+y)/2 ∈ dom f := by
    rw [hd]
    exact between_closure_mem hI hx hy (by linarith) (by linarith)
  obtain ⟨w, hw⟩ := hz
  have h₁ := (compatible_iff_bounds.mp hu).2 hw (by linarith : x < (x+y)/2)
  have h₂ := (compatible_iff_bounds.mp hv).1 hw (by linarith : (x+y)/2 < y)
  exact h₁.trans h₂

theorem completion_maximal {I : Set ℝ} {f : Operator}
    (hI : I.OrdConnected) (hne : I.Nonempty) (hf : Increasing f) (hd : dom f = I) :
    MaximalIncreasing (completion I f) := by
  apply maximal_of_minty (completion_increasing hI hd)
  intro s
  let L : Set ℝ := {l | ∃ y v, v ∈ f y ∧ l = min y (s-v)} ∪ lowerBounds I
  let U : Set ℝ := {u | ∃ y v, v ∈ f y ∧ u = max y (s-v)} ∪ upperBounds I
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ := (show a ∈ dom f by rw [hd]; exact ha)
  have hL : L.Nonempty := ⟨min a (s-b), Or.inl ⟨a, b, hb, rfl⟩⟩
  have hU : U.Nonempty := ⟨max a (s-b), Or.inl ⟨a, b, hb, rfl⟩⟩
  have hLU : ∀ l ∈ L, ∀ u ∈ U, l ≤ u := by
    intro l hl u hu
    rcases hl with ⟨y, v, hv, rfl⟩ | hl <;> rcases hu with ⟨z, w, hw, rfl⟩ | hu
    · by_contra hn
      have hh : max z (s-w) < min y (s-v) := lt_of_not_ge hn
      have hzy : z < y := (le_max_left _ _).trans_lt (hh.trans_le (min_le_left _ _))
      have hsw : s-w < s-v := (le_max_right _ _).trans_lt (hh.trans_le (min_le_right _ _))
      have := hf.le_of_lt hw hv hzy
      linarith
    · exact (min_le_left _ _).trans (hu (by rw [← hd]; exact ⟨v, hv⟩))
    · exact (hl (by rw [← hd]; exact ⟨w, hw⟩)).trans (le_max_left _ _)
    · exact (hl ha).trans (hu ha)
  obtain ⟨x, hxL, hxU⟩ := exists_between_of_forall_le hL hU hLU
  refine ⟨x, mem_closure_of_bounds hI ?_, ?_⟩
  · exact ⟨fun a ha => hxL (Or.inr ha), fun b hb => hxU (Or.inr hb)⟩
  · intro y v hv
    have hl : min y (s-v) ≤ x := hxL (Or.inl ⟨y, v, hv, rfl⟩)
    have hu : x ≤ max y (s-v) := hxU (Or.inl ⟨y, v, hv, rfl⟩)
    rcases le_total y (s-v) with h | h
    · rw [min_eq_left h] at hl
      rw [max_eq_right h] at hu
      exact mul_nonneg (by linarith) (by linarith)
    · rw [min_eq_right h] at hl
      rw [max_eq_left h] at hu
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

theorem le_completion {I : Set ℝ} {f : Operator} (hf : Increasing f) (hd : dom f = I) :
    f ≤ completion I f := by
  intro x u hu
  exact ⟨subset_closure (by rw [← hd]; exact ⟨u, hu⟩), hf.compatible hu⟩

theorem completion_dom_subset (I : Set ℝ) (f : Operator) : dom (completion I f) ⊆ closure I :=
  fun _ ⟨_, h⟩ => h.1

/-- The interval restriction on the domain makes the maximal completion unique. -/
theorem unique_maximal_completion {I : Set ℝ} {f : Operator}
    (hI : I.OrdConnected) (hne : I.Nonempty) (hf : Increasing f) (hd : dom f = I) :
    ∃! g : Operator, MaximalIncreasing g ∧ f ≤ g ∧ dom g ⊆ closure I := by
  refine ⟨completion I f,
    ⟨completion_maximal hI hne hf hd, le_completion hf hd, completion_dom_subset I f⟩, ?_⟩
  rintro g ⟨hg, hfg, hdom⟩
  apply hg.eq_of_le (completion_increasing hI hd)
  intro x u hu
  exact ⟨hdom ⟨u, hu⟩, fun {y v} hv => hg.1 hu (hfg _ hv)⟩

def restrictOperator (f : Operator) (I : Set ℝ) : Operator := fun x =>
  {u | x ∈ I ∧ u ∈ f x}

theorem restrictOperator_increasing {f : Operator} (hf : Increasing f) (I : Set ℝ) :
    Increasing (restrictOperator f I) := by
  intro x u y v hu hv
  exact hf hu.2 hv.2

theorem dom_restrictOperator {f : Operator} {I : Set ℝ} (hI : I ⊆ dom f) :
    dom (restrictOperator f I) = I := by
  ext x
  constructor
  · rintro ⟨u, hx, hu⟩
    exact hx
  · intro hx
    obtain ⟨u, hu⟩ := hI hx
    exact ⟨u, hx, hu⟩

/-- In particular, this applies to the specified open-interval restriction
of a maximal graph, as in the manuscript. -/
theorem unique_completed_restriction {f : Operator} (hf : MaximalIncreasing f)
    {I : Set ℝ} (hI : I.OrdConnected) (hne : I.Nonempty) (hdom : I ⊆ dom f) :
    ∃! g : Operator, MaximalIncreasing g ∧ restrictOperator f I ≤ g ∧ dom g ⊆ closure I :=
  unique_maximal_completion hI hne (restrictOperator_increasing hf.1 I) (dom_restrictOperator hdom)

theorem unique_completion_of_monotoneOn {φ : ℝ → ℝ} {I : Set ℝ}
    (hφ : MonotoneOn φ I) (hI : I.OrdConnected) (hne : I.Nonempty) :
    ∃! g : Operator, MaximalIncreasing g ∧ restrictOperator (ofFun φ) I ≤ g ∧
      dom g ⊆ closure I := by
  apply unique_maximal_completion hI hne
  · apply increasing_iff_order.mpr
    rintro x u y v ⟨hx, hu⟩ ⟨hy, hv⟩ hxy
    have hu' : u = φ x := hu
    have hv' : v = φ y := hv
    simpa [hu', hv'] using hφ hx hy hxy.le
  · apply dom_restrictOperator
    intro x _
    exact ⟨φ x, rfl⟩

/-- The completed fibers are exactly the one-sided extended-order intervals. -/
theorem completion_fiber_eq (I : Set ℝ) (f : Operator) (x : ℝ) :
    completion I f x = {u : ℝ | x ∈ closure I ∧
      lowerEndpoint f x ≤ (u : EReal) ∧ (u : EReal) ≤ upperEndpoint f x} := by
  ext u
  simp only [completion, mem_setOf_eq, compatible_iff_bounds, lowerEndpoint,
    upperEndpoint, iSup_le_iff, le_iInf_iff, EReal.coe_le_coe_iff]
  aesop

theorem completion_left_ray {I : Set ℝ} {f : Operator} {x a : ℝ}
    (hx : x ∈ closure I) (hl : lowerEndpoint f x = ⊥) (hu : upperEndpoint f x = (a : EReal)) :
    completion I f x = Iic a := by
  rw [completion_fiber_eq]
  ext u
  simp [hx, hl, hu, EReal.coe_le_coe_iff]

theorem completion_right_ray {I : Set ℝ} {f : Operator} {x a : ℝ}
    (hx : x ∈ closure I) (hl : lowerEndpoint f x = (a : EReal)) (hu : upperEndpoint f x = ⊤) :
    completion I f x = Ici a := by
  rw [completion_fiber_eq]
  ext u
  simp [hx, hl, hu, EReal.coe_le_coe_iff]

theorem completion_empty_of_upper_bot {I : Set ℝ} {f : Operator} {x : ℝ}
    (hu : upperEndpoint f x = ⊥) : completion I f x = ∅ := by
  rw [completion_fiber_eq]
  ext u
  simp [hu]

theorem completion_empty_of_lower_top {I : Set ℝ} {f : Operator} {x : ℝ}
    (hl : lowerEndpoint f x = ⊤) : completion I f x = ∅ := by
  rw [completion_fiber_eq]
  ext u
  simp [hl]

/-- The same uniqueness convention for nonincreasing graphs. -/
theorem unique_maximal_decreasing_completion {I : Set ℝ} {f : Operator}
    (hI : I.OrdConnected) (hne : I.Nonempty) (hf : Decreasing f) (hd : dom f = I) :
    ∃! g : Operator, MaximalDecreasing g ∧ f ≤ g ∧ dom g ⊆ closure I := by
  have hnegdom : dom (negOut f) = I := by
    rw [← hd]
    ext x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨-u, hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨-u, by simpa [negOut] using hu⟩
  obtain ⟨g, hg, huniq⟩ := unique_maximal_completion hI hne hf hnegdom
  refine ⟨negOut g, ⟨?_, ?_, ?_⟩, ?_⟩
  · change MaximalIncreasing (negOut (negOut g))
    simpa using hg.1
  · intro x u hu
    have hp := hg.2.1 x (show -u ∈ negOut f x by simpa [negOut] using hu)
    simpa [negOut] using hp
  · rintro x ⟨u, hu⟩
    exact hg.2.2 ⟨-u, hu⟩
  · rintro h ⟨hh, hfh, hdom⟩
    have heq : negOut h = g := huniq (negOut h) ⟨hh,
      (by intro x u hu; exact hfh x hu), (by rintro x ⟨u, hu⟩; exact hdom ⟨-u, hu⟩)⟩
    have := congrArg negOut heq
    simpa using this

end ScalarMonotone
