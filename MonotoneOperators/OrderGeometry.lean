import MonotoneOperators.Order

/-! # Domains, ranges, elementary examples, and scale independence -/

open Set Filter
open scoped Topology

namespace ScalarMonotone

theorem intervalLE_range_of_le {q r : ℝ → ℝ} (h : ∀ s, q s ≤ r s) :
    IntervalLE (Set.range q) (Set.range r) := by
  constructor
  · rintro u ⟨v, ⟨s, rfl⟩, hv⟩
    exact ⟨q s, ⟨s, rfl⟩, (h s).trans hv⟩
  · rintro u ⟨v, ⟨s, rfl⟩, hv⟩
    exact ⟨r s, ⟨s, rfl⟩, hv.trans (h s)⟩

theorem incLE_domains {f g : Operator} (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : IncLE f g) : IntervalLE (dom g) (dom f) := by
  rw [dom_eq_range_resolvent hf, dom_eq_range_resolvent hg]
  exact intervalLE_range_of_le ((incLE_iff_resolvent hf hg).1 hfg)

theorem incLE_ranges {f g : Operator} (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : IncLE f g) : IntervalLE (ran f) (ran g) := by
  rw [ran_eq_range_resolvent_complement hf, ran_eq_range_resolvent_complement hg]
  apply intervalLE_range_of_le
  intro s
  exact sub_le_sub_left ((incLE_iff_resolvent hf hg).1 hfg s) s

theorem decreasing_dom_eq_range_resolvent {f : Operator} (hf : MaximalDecreasing f) :
    dom f = Set.range (decreasingResolvent f hf) := by
  ext x
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨x-u, (decreasing_resolvent_eq_iff hf).2 hu⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, decreasing_resolvent_mem hf s⟩

theorem decreasing_ran_eq_range_resolvent {f : Operator} (hf : MaximalDecreasing f) :
    ran f = Set.range (fun s => decreasingResolvent f hf s - s) := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x-u, ?_⟩
    dsimp
    rw [(decreasing_resolvent_eq_iff hf).2 hx]
    ring
  · rintro ⟨s, rfl⟩
    exact ⟨_, decreasing_resolvent_mem hf s⟩

theorem decLE_domains {f g : Operator} (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : DecLE f g) : IntervalLE (dom f) (dom g) := by
  rw [decreasing_dom_eq_range_resolvent hf, decreasing_dom_eq_range_resolvent hg]
  exact intervalLE_range_of_le ((decLE_iff_resolvent hf hg).1 hfg)

theorem decLE_ranges {f g : Operator} (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : DecLE f g) : IntervalLE (ran f) (ran g) := by
  rw [decreasing_ran_eq_range_resolvent hf, decreasing_ran_eq_range_resolvent hg]
  apply intervalLE_range_of_le
  intro s
  exact sub_le_sub_right ((decLE_iff_resolvent hf hg).1 hfg s) s

theorem incLE_iff_fibers_of_dom_eq {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g) (hd : dom f = dom g) :
    IncLE f g ↔ ∀ x ∈ dom f, IntervalLE (f x) (g x) := by
  constructor
  · intro h x hx
    exact incLE_fiber hf hg h hx (hd ▸ hx)
  · intro h x u y v hu hv hxy
    obtain ⟨w, hw, huw⟩ := (h x ⟨u, hu⟩).2 (mem_lowerHull hu)
    exact huw.trans (hg.1.le_of_lt hw hv hxy)

theorem decLE_iff_fibers_of_dom_eq {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g) (hd : dom f = dom g) :
    DecLE f g ↔ ∀ x ∈ dom f, IntervalLE (f x) (g x) := by
  constructor
  · intro h x hx
    exact decLE_fiber hf hg h hx (hd ▸ hx)
  · intro h x u y v hu hv hyx
    obtain ⟨w, hw, huw⟩ := (h x ⟨u, hu⟩).2 (mem_lowerHull hu)
    exact huw.trans (Decreasing.le_of_lt hg.1 hv hw hyx)

theorem outputScale_one (f : Operator) : outputScale 1 f = f := by
  ext x u
  simp [outputScale]

theorem outputScale_outputScale (c d : ℝ) (f : Operator) :
    outputScale c (outputScale d f) = outputScale (c*d) f := by
  ext x u
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by ring⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨d*w, ⟨w, hw, rfl⟩, by ring⟩

/-- Positive scaling is an isomorphism for the increasing comparison order. -/
def IncGraph.scaleOrderIso (c : ℝ) (hc : 0 < c) : IncGraph ≃o IncGraph where
  toFun f := ⟨outputScale c f.val, outputScale_maximal hc f.property⟩
  invFun f := ⟨outputScale c⁻¹ f.val, outputScale_maximal (inv_pos.2 hc) f.property⟩
  left_inv f := by
    apply IncGraph.ext_val
    simp [outputScale_outputScale, hc.ne', outputScale_one]
  right_inv f := by
    apply IncGraph.ext_val
    simp [outputScale_outputScale, hc.ne', outputScale_one]
  map_rel_iff' := incLE_outputScale_iff hc

/-- Positive scaling is an isomorphism for the decreasing comparison order. -/
def DecGraph.scaleOrderIso (c : ℝ) (hc : 0 < c) : DecGraph ≃o DecGraph where
  toFun f := ⟨outputScale c f.val, outputScale_maximal_decreasing hc f.property⟩
  invFun f := ⟨outputScale c⁻¹ f.val,
    outputScale_maximal_decreasing (inv_pos.2 hc) f.property⟩
  left_inv f := by
    apply DecGraph.ext_val
    simp [outputScale_outputScale, hc.ne', outputScale_one]
  right_inv f := by
    apply DecGraph.ext_val
    simp [outputScale_outputScale, hc.ne', outputScale_one]
  map_rel_iff' := decLE_outputScale_iff hc

theorem incLE_vertical_iff (a b : ℝ) : IncLE (vertical a) (vertical b) ↔ b ≤ a := by
  constructor
  · intro h
    by_contra hn
    have := h (show (1:ℝ) ∈ vertical a a from rfl)
      (show (0:ℝ) ∈ vertical b b from rfl) (lt_of_not_ge hn)
    norm_num at this
  · intro h x u y v hx hy hxy
    change x = a at hx
    change y = b at hy
    subst x
    subst y
    exact False.elim ((not_lt_of_ge h) hxy)

theorem decLE_vertical_iff (a b : ℝ) : DecLE (vertical a) (vertical b) ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    have := h (show (1:ℝ) ∈ vertical a a from rfl)
      (show (0:ℝ) ∈ vertical b b from rfl) (lt_of_not_ge hn)
    norm_num at this
  · intro h x u y v hx hy hyx
    change x = a at hx
    change y = b at hy
    subst x
    subst y
    exact False.elim ((not_lt_of_ge h) hyx)

theorem incLE_constant_iff (a b : ℝ) :
    IncLE (ofFun (fun _ => a)) (ofFun (fun _ => b)) ↔ a ≤ b := by
  constructor
  · intro h
    exact h (x := 0) (y := 1) rfl rfl (by norm_num)
  · intro h x u y v hu hv _
    have hu' : u = a := hu
    have hv' : v = b := hv
    simpa [hu', hv'] using h

theorem decLE_constant_iff (a b : ℝ) :
    DecLE (ofFun (fun _ => a)) (ofFun (fun _ => b)) ↔ a ≤ b := by
  constructor
  · intro h
    exact h (x := 1) (y := 0) rfl rfl (by norm_num)
  · intro h x u y v hu hv _
    have hu' : u = a := hu
    have hv' : v = b := hv
    simpa [hu', hv'] using h

/-- The two orientation conventions cannot be the restrictions of one relation. -/
theorem no_orientation_independent_order :
    ¬ ∃ R : Operator → Operator → Prop,
      (∀ f g, MaximalIncreasing f → MaximalIncreasing g → (R f g ↔ IncLE f g)) ∧
      (∀ f g, MaximalDecreasing f → MaximalDecreasing g → (R f g ↔ DecLE f g)) := by
  rintro ⟨R, hi, hd⟩
  have hr := (hd (vertical 0) (vertical 1)
    (vertical_maximal_decreasing 0) (vertical_maximal_decreasing 1)).2
    ((decLE_vertical_iff 0 1).2 (by norm_num))
  have hh := (hi (vertical 0) (vertical 1) (vertical_maximal 0) (vertical_maximal 1)).1 hr
  have := (incLE_vertical_iff 0 1).1 hh
  norm_num at this

theorem ofFun_maximal_of_continuous {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) :
    MaximalIncreasing (ofFun φ) := by
  refine ⟨increasing_iff_order.2 ?_, ?_⟩
  · intro x u y v hu hv hxy
    have hu' : u = φ x := hu
    have hv' : v = φ y := hv
    simpa [hu', hv'] using hm hxy.le
  · intro x u hu
    have hlimL : Tendsto φ (𝓝[<] x) (𝓝 (φ x)) := hc.continuousAt.tendsto.mono_left inf_le_left
    have hlimR : Tendsto φ (𝓝[>] x) (𝓝 (φ x)) := hc.continuousAt.tendsto.mono_left inf_le_left
    have hlo : φ x ≤ u := le_of_tendsto hlimL (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (compatible_iff_bounds.1 hu).1 (show φ y ∈ ofFun φ y from rfl) hy)
    have hhi : u ≤ φ x := ge_of_tendsto hlimR (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (compatible_iff_bounds.1 hu).2 (show φ y ∈ ofFun φ y from rfl) hy)
    exact le_antisymm hhi hlo

theorem incLE_ofFun_iff {φ ψ : ℝ → ℝ}
    (hf : MaximalIncreasing (ofFun φ)) (hg : MaximalIncreasing (ofFun ψ)) :
    IncLE (ofFun φ) (ofFun ψ) ↔ ∀ x, φ x ≤ ψ x := by
  constructor
  · intro h x
    obtain ⟨u, hu, huψ⟩ := (incLE_fiber hf hg h
      (show x ∈ dom (ofFun φ) from ⟨φ x, rfl⟩)
      (show x ∈ dom (ofFun ψ) from ⟨ψ x, rfl⟩)).1 (mem_upperHull rfl)
    have hu' : u = φ x := hu
    simpa [hu'] using huψ
  · intro h x u y v hu hv hxy
    have hu' : u = φ x := hu
    exact hu' ▸ ((h x).trans (hg.1.le_of_lt (show ψ x ∈ ofFun ψ x from rfl) hv hxy))

theorem decLE_ofFun_iff {φ ψ : ℝ → ℝ}
    (hf : MaximalDecreasing (ofFun φ)) (hg : MaximalDecreasing (ofFun ψ)) :
    DecLE (ofFun φ) (ofFun ψ) ↔ ∀ x, φ x ≤ ψ x := by
  constructor
  · intro h x
    obtain ⟨u, hu, huψ⟩ := (decLE_fiber hf hg h
      (show x ∈ dom (ofFun φ) from ⟨φ x, rfl⟩)
      (show x ∈ dom (ofFun ψ) from ⟨ψ x, rfl⟩)).1 (mem_upperHull rfl)
    have hu' : u = φ x := hu
    simpa [hu'] using huψ
  · intro h x u y v hu hv hyx
    have hu' : u = φ x := hu
    exact hu' ▸ ((h x).trans
      (Decreasing.le_of_lt hg.1 hv (show ψ x ∈ ofFun ψ x from rfl) hyx))

end ScalarMonotone
