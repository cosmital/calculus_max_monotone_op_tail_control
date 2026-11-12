import MonotoneOperators.Order
import MonotoneOperators.CompositionMaximal

/-!
# Compatibility of the pointwise resolvent order with operations

Separated-graph comparisons are used throughout. On maximal graphs these
are exactly the order defined by the scalar resolvents. Keeping `IncLE`
and `DecLE` explicit avoids confusing this order with graph inclusion.
-/

open Set

namespace ScalarMonotone

variable {f g h : Operator}

theorem decreasing_le_of_gt (hf : Decreasing f) {x u y v : ℝ}
    (hu : u ∈ f x) (hv : v ∈ f y) (hyx : y < x) : u ≤ v := by
  have hp := (reflect_increasing_iff.mpr hf).le_of_lt
    (show u ∈ reflect f (-x) by simpa [reflect] using hu)
    (show v ∈ reflect f (-y) by simpa [reflect] using hv)
    (neg_lt_neg hyx)
  exact hp

theorem IncLE.add_right (hfg : IncLE f g) (hh : Increasing h) :
    IncLE (add f h) (add g h) := by
  rintro x u y v ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩ hxy
  exact add_le_add (hfg ha hc hxy) (hh.le_of_lt hb hd hxy)

theorem DecLE.add_right (hfg : DecLE f g) (hh : Decreasing h) :
    DecLE (add f h) (add g h) := by
  rintro x u y v ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩ hyx
  exact add_le_add (hfg ha hc hyx) (decreasing_le_of_gt hh hb hd hyx)

theorem IncLE.add_left (hfg : IncLE f g) (hh : Increasing h) :
    IncLE (add h f) (add h g) := by
  simpa only [op_add_comm h] using hfg.add_right hh

theorem DecLE.add_left (hfg : DecLE f g) (hh : Decreasing h) :
    DecLE (add h f) (add h g) := by
  simpa only [op_add_comm h] using hfg.add_right hh

theorem IncLE.mul_right (hfg : IncLE f g) (hh : Increasing h)
    (_hf₀ : Nonnegative f) (hg₀ : Nonnegative g) (hh₀ : Nonnegative h) :
    IncLE (mul f h) (mul g h) := by
  rintro x u y v ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩ hxy
  exact mul_le_mul (hfg ha hc hxy) (hh.le_of_lt hb hd hxy) (hh₀ hb) (hg₀ hc)

theorem DecLE.mul_right (hfg : DecLE f g) (hh : Decreasing h)
    (_hf₀ : Nonnegative f) (hg₀ : Nonnegative g) (hh₀ : Nonnegative h) :
    DecLE (mul f h) (mul g h) := by
  rintro x u y v ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩ hyx
  exact mul_le_mul (hfg ha hc hyx) (decreasing_le_of_gt hh hb hd hyx)
    (hh₀ hb) (hg₀ hc)

theorem IncLE.mul_left (hfg : IncLE f g) (hh : Increasing h)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) (hh₀ : Nonnegative h) :
    IncLE (mul h f) (mul h g) := by
  simpa only [op_mul_comm h] using hfg.mul_right hh hf₀ hg₀ hh₀

theorem DecLE.mul_left (hfg : DecLE f g) (hh : Decreasing h)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) (hh₀ : Nonnegative h) :
    DecLE (mul h f) (mul h g) := by
  simpa only [op_mul_comm h] using hfg.mul_right hh hf₀ hg₀ hh₀

theorem IncLE.parallelAdd_right (hfg : IncLE f g) (hh : Increasing h) :
    IncLE (parallelAdd f h) (parallelAdd g h) := by
  exact incLE_inverse_iff.mpr
    ((incLE_inverse_iff.mpr hfg).add_right (inverse_increasing hh))

theorem DecLE.parallelAdd_right (hfg : DecLE f g) (hh : Decreasing h) :
    DecLE (parallelAdd f h) (parallelAdd g h) := by
  have hhi : Decreasing (inverse h) := inverse_decreasing hh
  exact decLE_inverse_iff.mpr ((decLE_inverse_iff.mpr hfg).add_right hhi)

theorem IncLE.parallelMul_right (hfg : IncLE f g) (hh : Increasing h)
    (hf₀ : Nonnegative (inverse f)) (hg₀ : Nonnegative (inverse g))
    (hh₀ : Nonnegative (inverse h)) :
    IncLE (parallelMul f h) (parallelMul g h) := by
  exact incLE_inverse_iff.mpr
    ((incLE_inverse_iff.mpr hfg).mul_right (inverse_increasing hh) hg₀ hf₀ hh₀)

theorem DecLE.parallelMul_right (hfg : DecLE f g) (hh : Decreasing h)
    (hf₀ : Nonnegative (inverse f)) (hg₀ : Nonnegative (inverse g))
    (hh₀ : Nonnegative (inverse h)) :
    DecLE (parallelMul f h) (parallelMul g h) := by
  have hhi : Decreasing (inverse h) := inverse_decreasing hh
  exact decLE_inverse_iff.mpr
    ((decLE_inverse_iff.mpr hfg).mul_right hhi hf₀ hg₀ hh₀)

/-- A singleton lower fiber allows a comparison at equal input coordinates. -/
theorem IncLE.le_at_of_subsingleton_left (hfg : IncLE f g)
    (hf : MaximalIncreasing f) {x u v : ℝ} (hfx : (f x).Subsingleton)
    (hu : u ∈ f x) (hv : v ∈ g x) : u ≤ v := by
  by_contra hn
  have hvu : v < u := lt_of_not_ge hn
  have hvf : v ∈ f x := hf.2 (compatible_iff_bounds.mpr ⟨
    fun _ _ hw hyx => hfg hw hv hyx,
    fun _ _ hw hxy => hvu.le.trans (hf.1.le_of_lt hu hw hxy)⟩)
  exact hn (le_of_eq (hfx hu hvf))

theorem DecLE.le_at_of_subsingleton_left (hfg : DecLE f g)
    (hf : MaximalDecreasing f) {x u v : ℝ} (hfx : (f x).Subsingleton)
    (hu : u ∈ f x) (hv : v ∈ g x) : u ≤ v := by
  have hr : IncLE (reflect f) (reflect g) := by
    intro a p b q hp hq hab
    exact hfg hp hq (neg_lt_neg hab)
  apply hr.le_at_of_subsingleton_left (reflect_maximal_iff.mpr hf)
    (x := -x)
  · simpa [reflect] using hfx
  · simpa [reflect] using hu
  · simpa [reflect] using hv

theorem IncLE.comp_right_of_increasing (hfg : IncLE f g)
    (hf : MaximalIncreasing f) (hh : Increasing h)
    (hcomp : Increasing (comp f h)) :
    IncLE (comp f h) (comp g h) := by
  rintro x u y v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩ hxy
  rcases (hh.le_of_lt ha hb hxy).eq_or_lt with hab | hab
  · subst b
    rcases noRectangle_of_comp_increasing hcomp a with hhf | hff
    · exact (hxy.ne (hhf ha hb)).elim
    · exact hfg.le_at_of_subsingleton_left hf hff hu hv
  · exact hfg hu hv hab

theorem IncLE.comp_right_of_decreasing (hfg : IncLE f g)
    (hf : MaximalIncreasing f) (hh : Decreasing h)
    (hcomp : Decreasing (comp f h)) :
    DecLE (comp f h) (comp g h) := by
  rintro x u y v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩ hyx
  rcases (decreasing_le_of_gt hh ha hb hyx).eq_or_lt with hab | hab
  · subst b
    have hr := (decreasing_comp_iff_noRectangle_of_decreasing_increasing hh hf.1).mp hcomp
    rcases hr a with hhf | hff
    · exact (hyx.ne (hhf hb ha)).elim
    · exact hfg.le_at_of_subsingleton_left hf hff hu hv
  · exact hfg hu hv hab

theorem DecLE.comp_right_of_increasing (hfg : DecLE f g)
    (hf : MaximalDecreasing f) (hh : Increasing h)
    (hcomp : Decreasing (comp f h)) :
    DecLE (comp f h) (comp g h) := by
  rintro x u y v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩ hyx
  rcases (hh.le_of_lt hb ha hyx).eq_or_lt with hba | hba
  · subst b
    have hr := (decreasing_comp_iff_noRectangle_of_increasing_decreasing hh hf.1).mp hcomp
    rcases hr a with hhf | hff
    · exact (hyx.ne (hhf hb ha)).elim
    · exact hfg.le_at_of_subsingleton_left hf hff hu hv
  · exact hfg hu hv hba

theorem DecLE.comp_right_of_decreasing (hfg : DecLE f g)
    (hf : MaximalDecreasing f) (hh : Decreasing h)
    (hcomp : Increasing (comp f h)) :
    IncLE (comp f h) (comp g h) := by
  rintro x u y v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩ hxy
  rcases (decreasing_le_of_gt hh hb ha hxy).eq_or_lt with hba | hba
  · subst b
    rcases noRectangle_of_comp_increasing hcomp a with hhf | hff
    · exact (hxy.ne (hhf ha hb)).elim
    · exact hfg.le_at_of_subsingleton_left hf hff hu hv
  · exact hfg hu hv hba

theorem IncLE.comp_left_of_increasing (hfg : IncLE f g)
    (hg : MaximalIncreasing g) (hh : Increasing h)
    (hcomp : Increasing (comp h g)) :
    IncLE (comp h f) (comp h g) := by
  have hi := (incLE_inverse_iff.mpr hfg).comp_right_of_increasing
    (inverse_maximal hg) (inverse_increasing hh)
    (by rw [← inverse_comp]; exact inverse_increasing hcomp)
  exact incLE_inverse_iff.mp (by simpa only [inverse_comp] using hi)

theorem IncLE.comp_left_of_decreasing (hfg : IncLE f g)
    (hg : MaximalIncreasing g) (hh : Decreasing h)
    (hcomp : Decreasing (comp h g)) :
    DecLE (comp h g) (comp h f) := by
  have hi := (incLE_inverse_iff.mpr hfg).comp_right_of_decreasing
    (inverse_maximal hg) (inverse_decreasing hh)
    (by rw [← inverse_comp]; exact inverse_decreasing hcomp)
  exact decLE_inverse_iff.mp (by simpa only [inverse_comp] using hi)

theorem DecLE.comp_left_of_increasing (hfg : DecLE f g)
    (hf : MaximalDecreasing f) (hh : Increasing h)
    (hcomp : Decreasing (comp h f)) :
    DecLE (comp h f) (comp h g) := by
  have hi := (decLE_inverse_iff.mpr hfg).comp_right_of_increasing
    (inverse_maximal_decreasing hf) (inverse_increasing hh)
    (by rw [← inverse_comp]; exact inverse_decreasing hcomp)
  exact decLE_inverse_iff.mp (by simpa only [inverse_comp] using hi)

theorem DecLE.comp_left_of_decreasing (hfg : DecLE f g)
    (hf : MaximalDecreasing f) (hh : Decreasing h)
    (hcomp : Increasing (comp h f)) :
    IncLE (comp h g) (comp h f) := by
  have hi := (decLE_inverse_iff.mpr hfg).comp_right_of_decreasing
    (inverse_maximal_decreasing hf) (inverse_decreasing hh)
    (by rw [← inverse_comp]; exact inverse_increasing hcomp)
  exact incLE_inverse_iff.mp (by simpa only [inverse_comp] using hi)

end ScalarMonotone
