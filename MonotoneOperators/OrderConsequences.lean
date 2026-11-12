import MonotoneOperators.OrderGeometry
import MonotoneOperators.IntervalEndpoints

/-! # Endpoint comparison, continuous functions, and resolvent identities -/

open Set

namespace ScalarMonotone

theorem lowerHull_eq_setAdd (A : Set ℝ) : lowerHull A = setAdd A (Iic 0) := by
  ext x
  constructor
  · rintro ⟨v, hv, hxv⟩
    exact ⟨v, hv, x-v, sub_nonpos.2 hxv, by ring⟩
  · rintro ⟨v, hv, d, hd, rfl⟩
    exact ⟨v, hv, add_le_of_nonpos_right hd⟩

theorem upperHull_eq_setAdd (A : Set ℝ) : upperHull A = setAdd A (Ici 0) := by
  ext x
  constructor
  · rintro ⟨v, hv, hvx⟩
    exact ⟨v, hv, x-v, sub_nonneg.2 hvx, by ring⟩
  · rintro ⟨v, hv, d, hd, rfl⟩
    exact ⟨v, hv, le_add_of_nonneg_right hd⟩

theorem incLE_fiber_endpoints {f g : Operator} (hf : MaximalIncreasing f)
    (hg : MaximalIncreasing g) (hfg : IncLE f g) {x : ℝ}
    (hxf : x ∈ dom f) (hxg : x ∈ dom g) :
    setLowerEndpoint (f x) ≤ setLowerEndpoint (g x) ∧
      setUpperEndpoint (f x) ≤ setUpperEndpoint (g x) :=
  intervalLE_endpoints (incLE_fiber hf hg hfg hxf hxg)

theorem decLE_fiber_endpoints {f g : Operator} (hf : MaximalDecreasing f)
    (hg : MaximalDecreasing g) (hfg : DecLE f g) {x : ℝ}
    (hxf : x ∈ dom f) (hxg : x ∈ dom g) :
    setLowerEndpoint (f x) ≤ setLowerEndpoint (g x) ∧
      setUpperEndpoint (f x) ≤ setUpperEndpoint (g x) :=
  intervalLE_endpoints (decLE_fiber hf hg hfg hxf hxg)

theorem incLE_iff_endpoints_of_dom_eq {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g) (hd : dom f = dom g) :
    IncLE f g ↔ ∀ x ∈ dom f,
      setLowerEndpoint (f x) ≤ setLowerEndpoint (g x) ∧
        setUpperEndpoint (f x) ≤ setUpperEndpoint (g x) := by
  rw [incLE_iff_fibers_of_dom_eq hf hg hd]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  exact intervalLE_iff_endpoints hx (maximal_fiber_closed hf x)
    (show x ∈ dom g from hd ▸ hx) (maximal_fiber_closed hg x)

theorem decLE_iff_endpoints_of_dom_eq {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g) (hd : dom f = dom g) :
    DecLE f g ↔ ∀ x ∈ dom f,
      setLowerEndpoint (f x) ≤ setLowerEndpoint (g x) ∧
        setUpperEndpoint (f x) ≤ setUpperEndpoint (g x) := by
  rw [decLE_iff_fibers_of_dom_eq hf hg hd]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  exact intervalLE_iff_endpoints hx (decreasing_fiber_closed hf x)
    (show x ∈ dom g from hd ▸ hx) (decreasing_fiber_closed hg x)

theorem ofFun_maximal_decreasing_of_continuous {φ : ℝ → ℝ}
    (hm : Antitone φ) (hc : Continuous φ) : MaximalDecreasing (ofFun φ) := by
  have heq : negOut (ofFun φ) = ofFun (fun x => -φ x) := by
    ext x u
    change -u = φ x ↔ u = -φ x
    constructor <;> intro h <;> linarith
  change MaximalIncreasing (negOut (ofFun φ))
  rw [heq]
  exact ofFun_maximal_of_continuous (fun _ _ h => neg_le_neg (hm h)) hc.neg

theorem continuous_monotone_comparison {φ ψ : ℝ → ℝ}
    (hφ : Monotone φ) (hψ : Monotone ψ) (cφ : Continuous φ) (cψ : Continuous ψ) :
    IncLE (ofFun φ) (ofFun ψ) ↔ ∀ x, φ x ≤ ψ x :=
  incLE_ofFun_iff (ofFun_maximal_of_continuous hφ cφ) (ofFun_maximal_of_continuous hψ cψ)

theorem continuous_antitone_comparison {φ ψ : ℝ → ℝ}
    (hφ : Antitone φ) (hψ : Antitone ψ) (cφ : Continuous φ) (cψ : Continuous ψ) :
    DecLE (ofFun φ) (ofFun ψ) ↔ ∀ x, φ x ≤ ψ x :=
  decLE_ofFun_iff (ofFun_maximal_decreasing_of_continuous hφ cφ)
    (ofFun_maximal_decreasing_of_continuous hψ cψ)

theorem resolvent_scale_order_iff {f g : Operator} (hf : MaximalIncreasing f)
    (hg : MaximalIncreasing g) {c : ℝ} (hc : 0 < c) :
    (∀ s, resolvent (outputScale c g) (outputScale_maximal hc hg) s ≤
      resolvent (outputScale c f) (outputScale_maximal hc hf) s) ↔
      ∀ s, resolvent g hg s ≤ resolvent f hf s := by
  rw [← incLE_iff_resolvent, incLE_outputScale_iff hc, incLE_iff_resolvent hf hg]

theorem decreasingResolvent_scale_order_iff {f g : Operator} (hf : MaximalDecreasing f)
    (hg : MaximalDecreasing g) {c : ℝ} (hc : 0 < c) :
    (∀ s, decreasingResolvent (outputScale c f) (outputScale_maximal_decreasing hc hf) s ≤
      decreasingResolvent (outputScale c g) (outputScale_maximal_decreasing hc hg) s) ↔
      ∀ s, decreasingResolvent f hf s ≤ decreasingResolvent g hg s := by
  rw [← decLE_iff_resolvent, decLE_outputScale_iff hc, decLE_iff_resolvent hf hg]

theorem resolvent_inverse {f : Operator} (hf : MaximalIncreasing f) (s : ℝ) :
    resolvent (inverse f) (inverse_maximal hf) s = s - resolvent f hf s := by
  have h : resolvent f hf s ∈ inverse f (s - resolvent f hf s) := resolvent_mem hf s
  simpa only [sub_add_cancel] using (resolvent_eq_iff (inverse_maximal hf)).2 h

theorem decreasingResolvent_inverse {f : Operator} (hf : MaximalDecreasing f) (s : ℝ) :
    decreasingResolvent (inverse f) (inverse_maximal_decreasing hf) s =
      s + decreasingResolvent f hf (-s) := by
  have h : decreasingResolvent f hf (-s) ∈ inverse f
      (s + decreasingResolvent f hf (-s)) := by
    simpa [sub_neg_eq_add, add_comm] using decreasing_resolvent_mem hf (-s)
  simpa only [add_sub_cancel_right] using
    (decreasing_resolvent_eq_iff (inverse_maximal_decreasing hf)).2 h

end ScalarMonotone
