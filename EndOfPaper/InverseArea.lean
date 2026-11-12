import EndOfPaper.ScalarIntegration

/-!
The operator inverse-area identity (prop:area). Positive inverse levels are
derived from the paper hypotheses. Layer cake and ae singleton inverse fibers
retain possibly infinite ENNReal areas; no finite-area assumption is added.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem decreasing_value_le_of_lt {f : Operator} (hf : Decreasing f)
    {x y u v : ℝ} (hu : u ∈ f x) (hv : v ∈ f y) (hxy : x < y) : v ≤ u :=
  Decreasing.le_of_lt hf hu hv hxy

theorem decreasing_quadrant_range_above {f : Operator} (hf : MaximalDecreasing f)
    (hd : dom f ⊆ Ici 0) (p : ℝ) : ∃ x u, u ∈ f x ∧ p < u := by
  by_contra hn
  push_neg at hn
  have hc : ∀ ⦃y v : ℝ⦄, v ∈ f y → (-1-y)*(p-v) ≤ 0 := by
    intro y v hv
    have hy : 0 ≤ y := hd ⟨v, hv⟩
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr (hn y v hv))
  have hp : p ∈ f (-1) := (maximalDecreasing_iff_compatible.mp hf).2 (-1) p hc
  have hneg : (0 : ℝ) ≤ -1 := hd ⟨p, hp⟩
  norm_num at hneg

theorem decreasing_positive_fiber_bddAbove {f : Operator} (hf : Decreasing f)
    (hd : Ioi 0 ⊆ dom f) {x : ℝ} (hx : 0 < x) : BddAbove (f x) := by
  obtain ⟨v, hv⟩ := hd (show 0 < x/2 by linarith)
  exact ⟨v, fun u hu => decreasing_value_le_of_lt hf hv hu (by linarith)⟩

/-- Decay and the positive-quadrant domain force every positive inverse level
to be attained; this is a conclusion, not an extra hypothesis of the area theorem. -/
theorem decreasing_inverse_positive_domain {f : Operator} (hf : MaximalDecreasing f)
    (hd₀ : dom f ⊆ Ici 0) (hd : Ioi 0 ⊆ dom f)
    (hdecay : Tendsto (fun x => sSup (f x)) atTop (𝓝 0)) :
    Ioi 0 ⊆ dom (inverse f) := by
  intro p hp
  obtain ⟨x, hx, hsup⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hdecay.eventually_lt_const hp)).exists
  obtain ⟨v, hv⟩ := hd hx
  have hvp : v < p :=
    (le_csSup (decreasing_positive_fiber_bddAbove hf.1 hd hx) hv).trans_lt hsup
  obtain ⟨y, u, hu, hpu⟩ := decreasing_quadrant_range_above hf hd₀ p
  have hr : p ∈ ran f := (decreasing_ran_ordConnected hf).out
    (show v ∈ ran f from ⟨x, hv⟩) (show u ∈ ran f from ⟨y, hu⟩) ⟨hvp.le, hpu.le⟩
  exact hr

/-- Except at a possible endpoint, a strict superlevel section is the interval
from zero to the inverse value. The singleton-fiber condition will hold ae. -/
theorem decreasing_level_region_volume {f : Operator} (hf : Decreasing f)
    {s : ℝ → ℝ} (hs : SelectionOn f (Ioi 0) s) {p b : ℝ}
    (hb : b ∈ inverse f p) (hsub : (inverse f p).Subsingleton) :
    volume ({x : ℝ | p < s x} ∩ Ioi 0) = ENNReal.ofReal b := by
  have hlo : Ioo 0 b ⊆ {x : ℝ | p < s x} ∩ Ioi 0 := by
    intro x hx
    have hxs := hs x hx.1
    have hle : p ≤ s x := decreasing_value_le_of_lt hf hxs hb hx.2
    have hne : p ≠ s x := by
      intro he
      have hxi : x ∈ inverse f p := by
        change p ∈ f x
        rwa [he]
      exact hx.2.ne (hsub hxi hb)
    exact ⟨lt_of_le_of_ne hle hne, hx.1⟩
  have hhi : {x : ℝ | p < s x} ∩ Ioi 0 ⊆ Ioc 0 b := by
    rintro x ⟨hpx, hx⟩
    refine ⟨hx, ?_⟩
    by_contra hn
    have hbx : b < x := lt_of_not_ge hn
    have hle : s x ≤ p := decreasing_value_le_of_lt hf hb (hs x hx) hbx
    exact (not_lt_of_ge hle) hpx
  have hmlo := measure_mono (μ := volume) hlo
  have hmhi := measure_mono (μ := volume) hhi
  rw [Real.volume_Ioo, sub_zero] at hmlo
  rw [Real.volume_Ioc, sub_zero] at hmhi
  exact le_antisymm hmhi hmlo

/-- Tonelli's identity for arbitrary measurable selections. No finite area,
atomless probability law, or chosen scalar endpoint is assumed. -/
theorem decreasing_selection_inverse_area {f : Operator} (hf : Decreasing f)
    (hfn : Nonnegative f) {s q : ℝ → ℝ} (hsm : Measurable s)
    (hs : SelectionOn f (Ioi 0) s) (hq : SelectionOn (inverse f) (Ioi 0) q) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (s x)) =
      ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (q p) := by
  have hsn : 0 ≤ᵐ[volume.restrict (Ioi 0)] s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hfn (hs x hx)
  rw [expectation_tail_area (volume.restrict (Ioi (0 : ℝ))) hsm.aemeasurable hsn]
  apply lintegral_congr_ae
  have hnull := (countable_jumpInputs (inverse_decreasing hf)).ae_not_mem
    (volume.restrict (Ioi (0 : ℝ)))
  filter_upwards [hnull, ae_restrict_mem measurableSet_Ioi] with p hp hp₀
  have hsub : (inverse f p).Subsingleton := by
    intro x hx y hy
    apply neg_injective
    apply fiber_subsingleton_off_jumps (negOut (inverse f)) hp
    · simpa only [negOut, mem_setOf_eq, neg_neg] using hx
    · simpa only [negOut, mem_setOf_eq, neg_neg] using hy
  rw [Measure.restrict_apply' measurableSet_Ioi]
  exact decreasing_level_region_volume hf hs (hq p hp₀) hsub

/-- Manuscript-facing inverse-area identity, including infinite integrals and
the inverse-domain assertion. Both selections are constructed from the graph. -/
theorem inverse_area_identity {f : Operator} (hf : MaximalDecreasing f)
    (hd₀ : dom f ⊆ Ici 0) (hfn : Nonnegative f) (hd : Ioi 0 ⊆ dom f)
    (hdecay : Tendsto (fun x => sSup (f x)) atTop (𝓝 0)) :
    Ioi 0 ⊆ dom (inverse f) ∧
      ∃ s q : ℝ → ℝ, Measurable s ∧ Measurable q ∧
        SelectionOn f (Ioi 0) s ∧ SelectionOn (inverse f) (Ioi 0) q ∧
        (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (s x)) =
          ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (q p) := by
  have hdi := decreasing_inverse_positive_domain hf hd₀ hd hdecay
  obtain ⟨s, hsm, hs⟩ := exists_global_measurable_selection (Or.inr hf.1)
    measurableSet_Ioi hd
  obtain ⟨q, hqm, hq⟩ := exists_global_measurable_selection
    (Or.inr (inverse_maximal_decreasing hf).1) measurableSet_Ioi hdi
  exact ⟨hdi, s, q, hsm, hqm, hs, hq, decreasing_selection_inverse_area hf.1 hfn hsm hs hq⟩

end ScalarMonotone.EndOfPaper
end
