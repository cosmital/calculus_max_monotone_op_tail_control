import MonotoneOperators.Sums
import MonotoneOperators.Algebra

/-!
# Nonnegative products and logarithms

The proofs make explicit two facts used in the manuscript: nonnegative
maximal increasing graphs have lower-set domains, and their zero fibers
are closed. Neither product nonemptiness nor maximality is assumed silently.
-/

open Set

namespace ScalarMonotone

variable {f g : Operator}

theorem nonnegative_dom_below (hf : MaximalIncreasing f) (hf₀ : Nonnegative f)
    (a : ℝ) : ∃ x ∈ dom f, x < a := by
  obtain ⟨x, hx⟩ := minty_surjective hf (a - 1)
  exact ⟨x, ⟨a - 1 - x, hx⟩, by have := hf₀ hx; linarith⟩

theorem nonnegative_dom_lower (hf : MaximalIncreasing f) (hf₀ : Nonnegative f)
    {a b : ℝ} (hb : b ∈ dom f) (hab : a ≤ b) : a ∈ dom f := by
  obtain ⟨x, hx, hxa⟩ := nonnegative_dom_below hf hf₀ a
  exact (dom_ordConnected hf).out hx hb ⟨hxa.le, hab⟩

theorem nonnegative_common_domain (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) : (dom f ∩ dom g).Nonempty := by
  obtain ⟨a, u, hu⟩ := maximal_nonempty hf
  obtain ⟨b, v, hv⟩ := maximal_nonempty hg
  exact ⟨min a b, nonnegative_dom_lower hf hf₀ ⟨u, hu⟩ (min_le_left _ _),
    nonnegative_dom_lower hg hg₀ ⟨v, hv⟩ (min_le_right _ _)⟩

theorem logOp_mem_iff {x t : ℝ} : t ∈ logOp f x ↔ Real.exp t ∈ f x := by
  constructor
  · rintro ⟨u, hu, hpos, rfl⟩
    simpa [Real.exp_log hpos] using hu
  · intro h
    exact ⟨Real.exp t, h, Real.exp_pos t, Real.log_exp t⟩

theorem logOp_increasing (hf : Increasing f) : Increasing (logOp f) := by
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  exact Real.exp_le_exp.mp (hf.le_of_lt (logOp_mem_iff.mp hu) (logOp_mem_iff.mp hv) hxy)

/-- Taking logarithms preserves maximality when there is a positive range value. -/
theorem logOp_maximal (hf : MaximalIncreasing f) (hf₀ : Nonnegative f)
    (hpos : ∃ c ∈ ran f, 0 < c) : MaximalIncreasing (logOp f) := by
  refine ⟨logOp_increasing hf.1, ?_⟩
  intro x t hc
  rw [logOp_mem_iff]
  apply hf.2
  rw [compatible_iff_bounds]
  have hb := compatible_iff_bounds.mp hc
  constructor
  · intro y v hv hyx
    rcases (hf₀ hv).eq_or_lt with hvzero | hvpos
    · rw [← hvzero]
      exact (Real.exp_pos t).le
    · have hl := hb.1 (show Real.log v ∈ logOp f y from ⟨v, hv, hvpos, rfl⟩) hyx
      exact (Real.log_le_iff_le_exp hvpos).mp hl
  · intro y v hv hxy
    rcases (hf₀ hv).eq_or_lt with hvzero | hvpos
    · have hv0 : v = 0 := hvzero.symm
      obtain ⟨c, ⟨z, hz⟩, hcpos⟩ := hpos
      let e := min c (Real.exp t) / 2
      have he0 : 0 < e := by dsimp [e]; positivity
      have hec : e ≤ c := by
        have := min_le_left c (Real.exp t)
        dsimp [e]; linarith [le_of_lt he0]
      have het : e < Real.exp t := by
        have := min_le_right c (Real.exp t)
        dsimp [e]; linarith [Real.exp_pos t]
      have her : e ∈ ran f := (ran_ordConnected hf).out
        (show 0 ∈ ran f from ⟨y, hv0 ▸ hv⟩) ⟨z, hz⟩ ⟨he0.le, hec⟩
      obtain ⟨a, ha⟩ := her
      have hya : y ≤ a := by
        by_contra hn
        have hle := hf.1.le_of_lt ha hv (lt_of_not_ge hn)
        linarith
      have hl := hb.2 (show Real.log e ∈ logOp f a from ⟨e, ha, he0, rfl⟩)
        (hxy.trans_le hya)
      have hle := (Real.le_log_iff_exp_le he0).mp hl
      linarith
    · have hl := hb.2 (show Real.log v ∈ logOp f y from ⟨v, hv, hvpos, rfl⟩) hxy
      exact (Real.le_log_iff_exp_le hvpos).mp hl

theorem logOp_mul (_hf₀ : Nonnegative f) (hg₀ : Nonnegative g) :
    logOp (mul f g) = add (logOp f) (logOp g) := by
  funext x
  ext t
  constructor
  · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, hw, hlog⟩
    have hu0 : 0 < u := by nlinarith [_hf₀ hu, hg₀ hv]
    have hv0 : 0 < v := by nlinarith [_hf₀ hu, hg₀ hv]
    exact ⟨Real.log u, ⟨u, hu, hu0, rfl⟩,
      Real.log v, ⟨v, hv, hv0, rfl⟩, by rw [← hlog, Real.log_mul hu0.ne' hv0.ne']⟩
  · rintro ⟨a, ⟨u, hu, hu0, rfl⟩, b, ⟨v, hv, hv0, rfl⟩, rfl⟩
    exact ⟨u*v, ⟨u, hu, v, hv, rfl⟩, mul_pos hu0 hv0,
      Real.log_mul hu0.ne' hv0.ne'⟩

theorem zero_fiber_below_positive (hf : Increasing f) {x c u : ℝ}
    (hx : 0 ∈ f x) (hc : u ∈ f c) (hu : 0 < u) : x ≤ c := by
  by_contra h
  have := hf.le_of_lt hc hx (lt_of_not_ge h)
  linarith

theorem product_zero_fiber (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g)
    {c u v : ℝ} (hu : u ∈ f c) (hv : v ∈ g c) (hu0 : 0 < u) (hv0 : 0 < v) :
    inverse (mul f g) 0 = inverse f 0 ∪ inverse g 0 := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases mul_eq_zero.mp hab.symm with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (h ▸ hb)
  · rintro (hx | hx)
    · have hxc := zero_fiber_below_positive hf.1 hx hu hu0
      obtain ⟨b, hb⟩ := nonnegative_dom_lower hg hg₀ ⟨v, hv⟩ hxc
      exact ⟨0, hx, b, hb, by simp⟩
    · have hxc := zero_fiber_below_positive hg.1 hx hv hv0
      obtain ⟨a, ha⟩ := nonnegative_dom_lower hf hf₀ ⟨u, hu⟩ hxc
      exact ⟨a, ha, 0, hx, by simp⟩

theorem product_maximal_of_positive (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g)
    (hpos : ∃ c w, w ∈ mul f g c ∧ 0 < w) : MaximalIncreasing (mul f g) := by
  obtain ⟨c, w, ⟨u, hu, v, hv, rfl⟩, hw⟩ := hpos
  have hu0 : 0 < u := by nlinarith [hf₀ hu, hg₀ hv]
  have hv0 : 0 < v := by nlinarith [hf₀ hu, hg₀ hv]
  have hlf := logOp_maximal hf hf₀ ⟨u, ⟨c, hu⟩, hu0⟩
  have hlg := logOp_maximal hg hg₀ ⟨v, ⟨c, hv⟩, hv0⟩
  have hcommon : (dom (logOp f) ∩ dom (logOp g)).Nonempty :=
    ⟨c, ⟨Real.log u, ⟨u, hu, hu0, rfl⟩⟩, ⟨Real.log v, ⟨v, hv, hv0, rfl⟩⟩⟩
  have hlog : MaximalIncreasing (logOp (mul f g)) := by
    rw [logOp_mul hf₀ hg₀]
    exact add_maximal hlf hlg hcommon
  have hzclosed : IsClosed (inverse (mul f g) 0) := by
    rw [product_zero_fiber hf hg hf₀ hg₀ hu hv hu0 hv0]
    exact (maximal_fiber_closed (inverse_maximal hf) 0).union
      (maximal_fiber_closed (inverse_maximal hg) 0)
  refine ⟨hf.1.mul hg.1 hf₀ hg₀, ?_⟩
  intro x t hc
  have hb := compatible_iff_bounds.mp hc
  have ht0 : 0 ≤ t := by
    obtain ⟨y, hy, hyx⟩ := nonnegative_dom_below hf hf₀ (min x c)
    have hyc : y ≤ c := hyx.le.trans (min_le_right _ _)
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb'⟩ := nonnegative_dom_lower hg hg₀ ⟨v, hv⟩ hyc
    exact (mul_nonneg (hf₀ ha) (hg₀ hb')).trans
      (hb.1 ⟨a, ha, b, hb', rfl⟩ (hyx.trans_le (min_le_left _ _)))
  rcases ht0.eq_or_lt with htzero | htpos
  · have htx : t = 0 := htzero.symm
    subst t
    have hxc : x ≤ c := by
      by_contra hn
      have := hb.1 (show u*v ∈ mul f g c from ⟨u, hu, v, hv, rfl⟩) (lt_of_not_ge hn)
      linarith
    have hsub : Iio x ⊆ inverse (mul f g) 0 := by
      intro y hy
      have hyc : y ≤ c := hy.le.trans hxc
      obtain ⟨a, ha⟩ := nonnegative_dom_lower hf hf₀ ⟨u, hu⟩ hyc
      obtain ⟨b, hb'⟩ := nonnegative_dom_lower hg hg₀ ⟨v, hv⟩ hyc
      have hval : a*b ∈ mul f g y := ⟨a, ha, b, hb', rfl⟩
      have hz : a*b = 0 := le_antisymm (hb.1 hval hy) (mul_nonneg (hf₀ ha) (hg₀ hb'))
      exact hz ▸ hval
    have hcl := closure_minimal hsub hzclosed
    rw [closure_Iio] at hcl
    exact hcl (by simp)
  · have hl : Real.log t ∈ logOp (mul f g) x := hlog.2 (by
      rw [compatible_iff_bounds]
      constructor
      · intro y s hs hyx
        have hh := hb.1 (logOp_mem_iff.mp hs) hyx
        have := Real.log_le_log (Real.exp_pos s) hh
        simpa using this
      · intro y s hs hxy
        have hh := hb.2 (logOp_mem_iff.mp hs) hxy
        have := Real.log_le_log htpos hh
        simpa using this)
    simpa [Real.exp_log htpos] using logOp_mem_iff.mp hl

theorem constant_maximal (c : ℝ) : MaximalIncreasing (ofFun (fun _ => c)) := by
  apply maximal_of_minty
  · intro x u y v hu hv
    simp only [ofFun, mem_singleton_iff] at hu hv
    simp [hu, hv]
  · intro s
    exact ⟨s-c, by simp [ofFun]⟩

theorem maximal_zero_range_dom (hF : MaximalIncreasing f) (hr : ran f = {0}) : dom f = univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine ⟨0, hF.2 ?_⟩
  intro y v hv
  have hv0 : v = 0 := by
    have : v ∈ ran f := ⟨y, hv⟩
    rw [hr] at this
    exact this
  simp [hv0]

theorem product_has_positive_or_zero_range (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) :
    (∃ c w, w ∈ mul f g c ∧ 0 < w) ∨ ran (mul f g) = {0} := by
  by_cases hp : ∃ c w, w ∈ mul f g c ∧ 0 < w
  · exact Or.inl hp
  · right
    have hzero : ∀ x w, w ∈ mul f g x → w = 0 := by
      intro x w hw
      apply le_antisymm
      · by_contra hn
        exact hp ⟨x, w, hw, lt_of_not_ge hn⟩
      · exact (hf₀.mul hg₀) hw
    obtain ⟨c, ⟨a, ha⟩, ⟨b, hb⟩⟩ := nonnegative_common_domain hf hg hf₀ hg₀
    ext w
    constructor
    · rintro ⟨x, hx⟩
      exact hzero x w hx
    · intro hw
      have hval : a*b ∈ mul f g c := ⟨a, ha, b, hb, rfl⟩
      have h0 := hzero c (a*b) hval
      refine ⟨c, ?_⟩
      simp only [mem_singleton_iff] at hw
      simpa [hw, h0] using hval

/-- Exact zero-degeneracy criterion for nonnegative products. -/
theorem mul_maximal_iff (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) :
    MaximalIncreasing (mul f g) ↔ dom f ∩ dom g = univ ∨ ran (mul f g) ≠ {0} := by
  constructor
  · intro hm
    by_cases hr : ran (mul f g) = {0}
    · exact Or.inl (by simpa only [dom_mul] using maximal_zero_range_dom hm hr)
    · exact Or.inr hr
  · intro h
    rcases product_has_positive_or_zero_range hf hg hf₀ hg₀ with hp | hr
    · exact product_maximal_of_positive hf hg hf₀ hg₀ hp
    · have hd : dom (mul f g) = univ := by
        rw [dom_mul]
        exact h.resolve_right (not_not.mpr hr)
      have heq : mul f g = ofFun (fun _ => 0) := by
        funext x
        ext w
        constructor
        · intro hw
          have : w ∈ ran (mul f g) := ⟨x, hw⟩
          simpa [hr, ofFun] using this
        · intro hw
          have hw0 : w = 0 := hw
          obtain ⟨v, hv⟩ := (Set.eq_univ_iff_forall.mp hd) x
          have hv0 : v = 0 := by
            have : v ∈ ran (mul f g) := ⟨x, hv⟩
            simpa [hr] using this
          simpa [hw0, hv0] using hv
      rw [heq]
      exact constant_maximal 0

/-- The exact product range when the product is maximal. -/
theorem ran_mul_eq (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) (hm : MaximalIncreasing (mul f g)) :
    ran (mul f g) = setMul (ran f) (ran g) := by
  apply Set.Subset.antisymm
  · rintro w ⟨x, u, hu, v, hv, rfl⟩
    exact ⟨u, ⟨x, hu⟩, v, ⟨x, hv⟩, rfl⟩
  · rintro w ⟨u, ⟨a, hu⟩, v, ⟨b, hv⟩, rfl⟩
    rcases product_has_positive_or_zero_range hf hg hf₀ hg₀ with hp | hr
    · obtain ⟨c, z, ⟨p, hp, q, hq, rfl⟩, hpq⟩ := hp
      have hp0 : 0 < p := by nlinarith [hf₀ hp, hg₀ hq]
      have hq0 : 0 < q := by nlinarith [hf₀ hp, hg₀ hq]
      by_cases huv : u*v = 0
      · rw [huv]
        rcases mul_eq_zero.mp huv with hu0 | hv0
        · refine ⟨a, ?_⟩
          have hzero : a ∈ inverse f 0 ∪ inverse g 0 := Or.inl (hu0 ▸ hu)
          rw [← product_zero_fiber hf hg hf₀ hg₀ hp hq hp0 hq0] at hzero
          exact hzero
        · refine ⟨b, ?_⟩
          have hzero : b ∈ inverse f 0 ∪ inverse g 0 := Or.inr (hv0 ▸ hv)
          rw [← product_zero_fiber hf hg hf₀ hg₀ hp hq hp0 hq0] at hzero
          exact hzero
      · have hu0 : 0 < u := lt_of_le_of_ne (hf₀ hu) (fun h => huv (by simp [← h]))
        have hv0 : 0 < v := lt_of_le_of_ne (hg₀ hv) (fun h => huv (by simp [← h]))
        have hlf := logOp_maximal hf hf₀ ⟨p, ⟨c, hp⟩, hp0⟩
        have hlg := logOp_maximal hg hg₀ ⟨q, ⟨c, hq⟩, hq0⟩
        have hcommon : (dom (logOp f) ∩ dom (logOp g)).Nonempty :=
          ⟨c, ⟨Real.log p, ⟨p, hp, hp0, rfl⟩⟩, ⟨Real.log q, ⟨q, hq, hq0, rfl⟩⟩⟩
        have hsum : Real.log u + Real.log v ∈ ran (add (logOp f) (logOp g)) := by
          rw [ran_add_eq hlf hlg hcommon]
          exact ⟨Real.log u, ⟨a, ⟨u, hu, hu0, rfl⟩⟩,
            Real.log v, ⟨b, ⟨v, hv, hv0, rfl⟩⟩, rfl⟩
        rw [← logOp_mul hf₀ hg₀] at hsum
        obtain ⟨x, hx⟩ := hsum
        refine ⟨x, ?_⟩
        simpa [Real.exp_add, Real.exp_log hu0, Real.exp_log hv0] using logOp_mem_iff.mp hx
    · have hd := maximal_zero_range_dom hm hr
      have hc : max a b + 1 ∈ dom (mul f g) := by rw [hd]; trivial
      obtain ⟨z, p, hp, q, hq, hz⟩ := hc
      have hpa := hf.1.le_of_lt hu hp (by linarith [le_max_left a b])
      have hqb := hg.1.le_of_lt hv hq (by linarith [le_max_right a b])
      have hzero : p*q = 0 := by
        have : p*q ∈ ran (mul f g) := ⟨max a b + 1, p, hp, q, hq, rfl⟩
        simpa [hr] using this
      have huv0 : u*v = 0 := le_antisymm
        (by nlinarith [mul_le_mul hpa hqb (hg₀ hv) (hf₀ hp)])
        (mul_nonneg (hf₀ hu) (hg₀ hv))
      rw [hr, huv0]
      exact rfl

end ScalarMonotone
