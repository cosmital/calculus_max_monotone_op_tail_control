import MonotoneOperators.Order
import MonotoneOperators.ProbabilityCore

/-!
# Probability bounds in pointwise resolvent order

This section supplies the comparison order missing from the first manuscript
excerpt, and proves the survival/quantile equivalence without selecting an
endpoint of a quantile fiber.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

namespace ScalarMonotone

/-- The lower tail probability belongs to its completed survival fiber. -/
theorem survival_lower_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    μ.real (Ioi t) ∈ survival μ t :=
  ⟨le_rfl, measureReal_mono Ioi_subset_Ici_self⟩

/-- Strict upper tails are right-continuous, including at atoms. -/
theorem survival_strict_tail_right_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Tendsto (fun y => μ.real (Ioi y)) (𝓝[>] t) (𝓝 (μ.real (Ioi t))) := by
  simp_rw [survival_lower_cdf μ]
  exact tendsto_const_nhds.sub (((cdf μ).right_continuous t).mono Ioi_subset_Ici_self)

/-- The strict-tail graph test is equivalent to decreasing separated-graph order.
The equivalence itself even holds when the target graph is not maximal. -/
theorem survival_comparison_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (α : Operator) :
    DecLE (survival μ) α ↔ ∀ ⦃t u : ℝ⦄, u ∈ α t → μ.real (Ioi t) ≤ u := by
  constructor
  · intro h t u htu
    apply le_of_tendsto (survival_strict_tail_right_continuous μ t)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact h (survival_lower_mem μ x) htu hx
  · intro h x v t u hv hu htx
    have hs : Ici x ⊆ Ioi t := fun y hy => htx.trans_le hy
    exact hv.2.trans ((measureReal_mono hs).trans (h hu))

/-- The previously external survival/quantile comparison equivalence. -/
theorem survival_le_iff_tailQuantile_le (μ : Measure ℝ) (α : Operator) :
    DecLE (survival μ) α ↔ DecLE (tailQuantile μ) (inverse α) :=
  decLE_inverse_iff.symm

/-- A random-variable formulation on an arbitrary underlying probability space. -/
theorem survival_map_comparison_iff {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ}
    (hX : Measurable X) (α : Operator) :
    DecLE (survival (Measure.map X ν)) α ↔ TailBound ν X α := by
  letI : IsProbabilityMeasure (Measure.map X ν) := isProbabilityMeasure_map hX.aemeasurable
  rw [survival_comparison_iff]
  simp only [map_measureReal_apply hX measurableSet_Ioi, TailBound, preimage_setOf_eq]
  rfl

/-- A graph-wise tail estimate gives the scaled survival comparison directly. -/
theorem survival_map_le_outputScale_of_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hX : Measurable X) {α : Operator} {c : ℝ}
    (hbound : ∀ ⦃t u : ℝ⦄, u ∈ α t → ν.real {ω | t < X ω} ≤ c * u) :
    DecLE (survival (Measure.map X ν)) (outputScale c α) := by
  apply (survival_map_comparison_iff ν hX _).2
  rintro t v ⟨u, hu, rfl⟩
  exact hbound hu

/-- The finite sum bound, together with maximality of the displayed profile. -/
theorem survival_finite_sum_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (α : ι → Operator)
    (hX : ∀ i, Measurable (X i))
    (hα : ∀ i, MaximalDecreasing (α i))
    (hbound : ∀ i, DecLE (survival (Measure.map (X i) ν)) (α i))
    (hcommon : ∃ u, ∀ i, u ∈ ran (α i)) :
    MaximalDecreasing (outputScale (Fintype.card ι : ℝ) (finiteParallelAdd α)) ∧
      DecLE (survival (Measure.map (fun ω => ∑ i, X i ω) ν))
        (outputScale (Fintype.card ι : ℝ) (finiteParallelAdd α)) := by
  constructor
  · apply outputScale_maximal_decreasing
      (show (0 : ℝ) < Fintype.card ι by exact_mod_cast Fintype.card_pos)
    exact finiteParallelAdd_maximal_decreasing α hα hcommon
  · apply survival_map_le_outputScale_of_tail_bound ν
      (Finset.measurable_sum _ (fun i _ => hX i))
    intro t u htu
    exact finite_sum_tail_bound ν X α
      (fun i => (survival_map_comparison_iff ν (hX i) _).1 (hbound i)) htu

/-- The finite nonnegative product bound. Maximality of the inverse product
is the exact qualification assumed in the manuscript. -/
theorem survival_finite_product_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (α : ι → Operator)
    (hX : ∀ i, Measurable (X i))
    (hbound : ∀ i, DecLE (survival (Measure.map (X i) ν)) (α i))
    (hnonneg : ∀ i, ∀ᵐ ω ∂ν, 0 ≤ X i ω)
    (hprod : MaximalDecreasing (finiteProduct fun i => inverse (α i))) :
    MaximalDecreasing (outputScale (Fintype.card ι : ℝ) (finiteParallelMul α)) ∧
      DecLE (survival (Measure.map (fun ω => ∏ i, X i ω) ν))
        (outputScale (Fintype.card ι : ℝ) (finiteParallelMul α)) := by
  constructor
  · apply outputScale_maximal_decreasing
      (show (0 : ℝ) < Fintype.card ι by exact_mod_cast Fintype.card_pos)
    exact inverse_maximal_decreasing hprod
  · apply survival_map_le_outputScale_of_tail_bound ν
      (Finset.measurable_prod _ (fun i _ => hX i))
    intro t u htu
    exact finite_product_tail_bound ν X α
      (fun i => (survival_map_comparison_iff ν (hX i) _).1 (hbound i)) hnonneg htu

/-- Centered sum comparison with exactly two exceptional events. -/
theorem survival_centered_sum_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {c d : ℝ} {α β : Operator}
    (hα : DecLE (survival (Measure.map (fun ω => |X ω - c|) ν)) α)
    (hβ : DecLE (survival (Measure.map (fun ω => |Y ω - d|) ν)) β)
    (hm : MaximalDecreasing (parallelAdd α β)) :
    MaximalDecreasing (outputScale 2 (parallelAdd α β)) ∧
      DecLE (survival (Measure.map (fun ω => |X ω + Y ω - c - d|) ν))
        (outputScale 2 (parallelAdd α β)) := by
  refine ⟨outputScale_maximal_decreasing (by norm_num) hm, ?_⟩
  apply survival_map_le_outputScale_of_tail_bound ν
    ((((hX.add hY).sub_const c).sub_const d).abs)
  intro t u htu
  exact centered_sum_tail_bound ν
    ((survival_map_comparison_iff ν (hX.sub_const c).abs _).1 hα)
    ((survival_map_comparison_iff ν (hY.sub_const d).abs _).1 hβ) htu

/-- Input division is the scalar linear composition in the centered formulas. -/
def inputDivide (c : ℝ) (f : Operator) : Operator := fun x => f (x / c)

theorem inputDivide_eq_comp (c : ℝ) (f : Operator) :
    inputDivide c f = comp f (ofFun fun x => x / c) := by
  ext x u
  simp [inputDivide, comp, ofFun]

theorem inverse_outputScale_inverse {c : ℝ} (hc : c ≠ 0) (f : Operator) :
    inverse (outputScale c (inverse f)) = inputDivide c f := by
  ext x u
  change (∃ v, u ∈ f v ∧ x = c * v) ↔ u ∈ f (x / c)
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [hc] using hv
  · intro hu
    exact ⟨x / c, hu, (mul_div_cancel₀ x hc).symm.trans (by ring)⟩

/-- The inverse-level polynomial used for centered products. It also handles
zero pivots; the corresponding zero linear term can then be deleted. -/
def centeredProductProfile (α β : Operator) (c d : ℝ) : Operator :=
  inverse (add (add (mul (inverse α) (inverse β)) (outputScale |d| (inverse α)))
    (outputScale |c| (inverse β)))

/-- For nonzero pivots, the inverse polynomial is exactly the manuscript's
parallel expression. -/
theorem centeredProductProfile_eq_parallel {α β : Operator} {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) :
    centeredProductProfile α β c d =
      parallelAdd (parallelAdd (parallelMul α β) (inputDivide |d| α))
        (inputDivide |c| β) := by
  rw [← inverse_outputScale_inverse (abs_ne_zero.mpr hd) α,
    ← inverse_outputScale_inverse (abs_ne_zero.mpr hc) β]
  simp only [parallelAdd, parallelMul, inverse_inverse, centeredProductProfile]

/-- A zero first pivot deletes the `|c|` linear term, including its domain
qualification, since the product term already supplies the required witness. -/
theorem centeredProductProfile_zero_left (α β : Operator) (d : ℝ) :
    centeredProductProfile α β 0 d =
      inverse (add (mul (inverse α) (inverse β)) (outputScale |d| (inverse α))) := by
  ext t u
  constructor
  · rintro ⟨v, hv, w, ⟨s, hs, hw⟩, ht⟩
    have hw0 : w = 0 := by simpa using hw
    have htv : t = v := by simpa only [hw0, add_zero] using ht
    change t ∈ add (mul (inverse α) (inverse β)) (outputScale |d| (inverse α)) u
    simpa only [htv] using hv
  · intro htu
    have htu' := htu
    obtain ⟨p, ⟨r, hr, s, hs, hp⟩, q, hq, ht⟩ := htu
    exact ⟨t, htu', 0, ⟨s, hs, by simp⟩, by simp⟩

/-- A zero second pivot deletes the `|d|` linear term. -/
theorem centeredProductProfile_zero_right (α β : Operator) (c : ℝ) :
    centeredProductProfile α β c 0 =
      inverse (add (mul (inverse α) (inverse β)) (outputScale |c| (inverse β))) := by
  ext t u
  constructor
  · rintro ⟨v, ⟨p, hp, q, ⟨r, hr, hq⟩, hv⟩, w, hw, ht⟩
    have hq0 : q = 0 := by simpa using hq
    have hvp : v = p := by simpa only [hq0, add_zero] using hv
    exact ⟨p, hp, w, hw, by simpa only [hvp] using ht⟩
  · rintro ⟨p, hp, q, hq, ht⟩
    have hp₀ := hp
    obtain ⟨r, hr, s, hs, hp'⟩ := hp
    exact ⟨p, ⟨p, hp₀, 0, ⟨r, hr, by simp⟩, by simp⟩, q, hq, ht⟩

theorem centeredProductProfile_zero_zero (α β : Operator) :
    centeredProductProfile α β 0 0 = parallelMul α β := by
  rw [centeredProductProfile_zero_left]
  ext t u
  constructor
  · rintro ⟨p, hp, q, ⟨r, hr, hq⟩, ht⟩
    have hq0 : q = 0 := by simpa using hq
    have htp : t = p := by simpa only [hq0, add_zero] using ht
    simpa only [htp] using hp
  · intro ht
    have ht₀ := ht
    obtain ⟨r, hr, s, hs, ht'⟩ := ht
    exact ⟨t, ht₀, 0, ⟨r, hr, by simp⟩, by simp⟩

/-- Only the two original exceptional events are counted, even though the
inverse polynomial contains three summands. -/
theorem centered_product_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X Y : Ω → ℝ}
    {c d : ℝ} {α β : Operator}
    (hX : TailBound ν (fun ω => |X ω - c|) α)
    (hY : TailBound ν (fun ω => |Y ω - d|) β)
    (hα : dom α ⊆ Ici 0) (hβ : dom β ⊆ Ici 0)
    {t u : ℝ} (htu : u ∈ centeredProductProfile α β c d t) :
    ν.real {ω | t < |X ω * Y ω - c * d|} ≤ 2 * u := by
  rcases htu with ⟨v, ⟨p, ⟨r, hr, s, hs, rfl⟩,
    q, ⟨r', hr', rfl⟩, rfl⟩, w, ⟨s', hs', rfl⟩, rfl⟩
  have hr₀ : 0 ≤ r := hα ⟨u, hr⟩
  have hr'₀ : 0 ≤ r' := hα ⟨u, hr'⟩
  have hs₀ : 0 ≤ s := hβ ⟨u, hs⟩
  have hs'₀ : 0 ≤ s' := hβ ⟨u, hs'⟩
  have hrmin : u ∈ α (min r r') := by
    rcases le_total r r' with h | h
    · simpa [min_eq_left h] using hr
    · simpa [min_eq_right h] using hr'
  have hsmin : u ∈ β (min s s') := by
    rcases le_total s s' with h | h
    · simpa [min_eq_left h] using hs
    · simpa [min_eq_right h] using hs'
  apply two_event_tail_bound ν hX hY hrmin hsmin
  filter_upwards [] with ω
  intro hxr hys
  calc
    |X ω * Y ω - c * d| ≤ min r r' * min s s' + |d| * min r r' + |c| * min s s' :=
      centered_product_pointwise _ _ _ _ _ _ hxr hys
    _ ≤ r * s + |d| * r' + |c| * s' := by
      gcongr <;> first | exact min_le_left _ _ | exact min_le_right _ _

/-- The centered product comparison, valid also when either pivot is zero. -/
theorem survival_centered_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {c d : ℝ} {α β : Operator}
    (hα : DecLE (survival (Measure.map (fun ω => |X ω - c|) ν)) α)
    (hβ : DecLE (survival (Measure.map (fun ω => |Y ω - d|) ν)) β)
    (hα₀ : dom α ⊆ Ici 0) (hβ₀ : dom β ⊆ Ici 0)
    (hm : MaximalDecreasing (centeredProductProfile α β c d)) :
    MaximalDecreasing (outputScale 2 (centeredProductProfile α β c d)) ∧
      DecLE (survival (Measure.map (fun ω => |X ω * Y ω - c * d|) ν))
        (outputScale 2 (centeredProductProfile α β c d)) := by
  refine ⟨outputScale_maximal_decreasing (by norm_num) hm, ?_⟩
  apply survival_map_le_outputScale_of_tail_bound ν ((hX.mul hY).sub_const (c*d)).abs
  intro t u htu
  exact centered_product_tail_bound ν
    ((survival_map_comparison_iff ν (hX.sub_const c).abs _).1 hα)
    ((survival_map_comparison_iff ν (hY.sub_const d).abs _).1 hβ) hα₀ hβ₀ htu

end ScalarMonotone
