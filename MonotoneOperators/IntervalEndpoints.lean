import MonotoneOperators.IntervalExtrema

/-!
# Extended-real endpoints of closed intervals

These endpoints are the actual infimum and supremum of a fiber.  They are
distinct from the neighboring-graph endpoint functions in `Basic.lean`.
-/

namespace ScalarMonotone

open Set

noncomputable def setLowerEndpoint (I : Set ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' I)

noncomputable def setUpperEndpoint (I : Set ℝ) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' I)

theorem setLowerEndpoint_le {I : Set ℝ} {x : ℝ} (hx : x ∈ I) :
    setLowerEndpoint I ≤ (x : EReal) := sInf_le ⟨x, hx, rfl⟩

theorem le_setUpperEndpoint {I : Set ℝ} {x : ℝ} (hx : x ∈ I) :
    (x : EReal) ≤ setUpperEndpoint I := le_sSup ⟨x, hx, rfl⟩

theorem lowerHull_eq_endpoint {I : Set ℝ} (hn : I.Nonempty) (hc : IsClosed I) :
    lowerHull I = {x : ℝ | (x : EReal) ≤ setUpperEndpoint I} := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (EReal.coe_le_coe_iff.mpr hxy).trans (le_setUpperEndpoint hy)
  · intro hx
    by_cases hb : BddAbove I
    · have hs := hc.csSup_mem hn hb
      refine ⟨sSup I, hs, ?_⟩
      apply EReal.coe_le_coe_iff.mp
      apply hx.trans
      apply sSup_le
      rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (le_csSup hb hy)
    · obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.mp hb x
      exact ⟨y, hy, hxy.le⟩

theorem upperHull_eq_endpoint {I : Set ℝ} (hn : I.Nonempty) (hc : IsClosed I) :
    upperHull I = {x : ℝ | setLowerEndpoint I ≤ (x : EReal)} := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (setLowerEndpoint_le hy).trans (EReal.coe_le_coe_iff.mpr hyx)
  · intro hx
    by_cases hb : BddBelow I
    · have hs := hc.csInf_mem hn hb
      refine ⟨sInf I, hs, ?_⟩
      apply EReal.coe_le_coe_iff.mp
      apply le_trans ?_ hx
      apply le_sInf
      rintro _ ⟨y, hy, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (csInf_le hb hy)
    · obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hb x
      exact ⟨y, hy, hyx.le⟩

theorem closed_interval_eq_endpoints {I : Set ℝ} (hn : I.Nonempty)
    (hc : IsClosed I) (ho : I.OrdConnected) :
    I = {x : ℝ | setLowerEndpoint I ≤ (x : EReal) ∧
      (x : EReal) ≤ setUpperEndpoint I} := by
  calc
    I = upperHull I ∩ lowerHull I := (hull_inter_eq ho).symm
    _ = _ := by rw [upperHull_eq_endpoint hn hc, lowerHull_eq_endpoint hn hc]; rfl

theorem intervalLE_endpoints {I J : Set ℝ} (h : IntervalLE I J) :
    setLowerEndpoint I ≤ setLowerEndpoint J ∧
      setUpperEndpoint I ≤ setUpperEndpoint J := by
  constructor
  · apply le_sInf
    rintro _ ⟨y, hy, rfl⟩
    rcases h.1 (mem_upperHull hy) with ⟨x, hx, hxy⟩
    exact (setLowerEndpoint_le hx).trans (EReal.coe_le_coe_iff.mpr hxy)
  · apply sSup_le
    rintro _ ⟨x, hx, rfl⟩
    rcases h.2 (mem_lowerHull hx) with ⟨y, hy, hxy⟩
    exact (EReal.coe_le_coe_iff.mpr hxy).trans (le_setUpperEndpoint hy)

theorem intervalLE_iff_endpoints {I J : Set ℝ}
    (hIn : I.Nonempty) (hIc : IsClosed I) (hJn : J.Nonempty) (hJc : IsClosed J) :
    IntervalLE I J ↔ setLowerEndpoint I ≤ setLowerEndpoint J ∧
      setUpperEndpoint I ≤ setUpperEndpoint J := by
  constructor
  · exact intervalLE_endpoints
  · intro h
    rw [IntervalLE, upperHull_eq_endpoint hIn hIc, upperHull_eq_endpoint hJn hJc,
      lowerHull_eq_endpoint hIn hIc, lowerHull_eq_endpoint hJn hJc]
    exact ⟨fun _ hx => h.1.trans hx, fun _ hx => hx.trans h.2⟩

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem intervalInf_eq_endpoints (I : ι → Set ℝ)
    (hn : ∀ i, (I i).Nonempty) (hc : ∀ i, IsClosed (I i)) :
    intervalInf I = {x : ℝ | (⨅ i, setLowerEndpoint (I i)) ≤ (x : EReal) ∧
      (x : EReal) ≤ ⨅ i, setUpperEndpoint (I i)} := by
  ext x
  simp only [intervalInf, mem_inter_iff, mem_iUnion, mem_iInter,
    upperHull_eq_endpoint (hn _) (hc _), lowerHull_eq_endpoint (hn _) (hc _), mem_setOf_eq,
    le_iInf_iff]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    exact ⟨(iInf_le (fun i => setLowerEndpoint (I i)) i).trans hi, h⟩
  · rintro ⟨h, hall⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => setLowerEndpoint (I i))
    exact ⟨⟨i, by simpa only [hi] using h⟩, hall⟩

theorem intervalSup_eq_endpoints (I : ι → Set ℝ)
    (hn : ∀ i, (I i).Nonempty) (hc : ∀ i, IsClosed (I i)) :
    intervalSup I = {x : ℝ | (⨆ i, setLowerEndpoint (I i)) ≤ (x : EReal) ∧
      (x : EReal) ≤ ⨆ i, setUpperEndpoint (I i)} := by
  ext x
  simp only [intervalSup, mem_inter_iff, mem_iUnion, mem_iInter,
    upperHull_eq_endpoint (hn _) (hc _), lowerHull_eq_endpoint (hn _) (hc _), mem_setOf_eq,
    iSup_le_iff]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    exact ⟨h, hi.trans (le_iSup (fun i => setUpperEndpoint (I i)) i)⟩
  · rintro ⟨hall, h⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => setUpperEndpoint (I i))
    exact ⟨⟨i, by simpa only [hi] using h⟩, hall⟩

end ScalarMonotone
