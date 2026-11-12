import MonotoneOperators.IntervalExtrema
import MonotoneOperators.Algebra

/-!
# Multiplication of finite interval extrema

Only the fixed interval is required to be nonnegative. The varying intervals
may have arbitrary signs and may be unbounded or have open endpoints.
-/

open Set

namespace ScalarMonotone

theorem setMul_ordConnected {H I : Set ℝ} (hH : H.OrdConnected) (hI : I.OrdConnected) :
    (setMul H I).OrdConnected := by
  have he : setMul H I = (fun p : ℝ × ℝ => p.1 * p.2) '' (H ×ˢ I) := by
    ext w
    constructor
    · rintro ⟨h, hh, i, hi, rfl⟩
      exact ⟨(h, i), ⟨hh, hi⟩, rfl⟩
    · rintro ⟨⟨h, i⟩, ⟨hh, hi⟩, rfl⟩
      exact ⟨h, hh, i, hi, rfl⟩
  rw [he]
  exact ((hH.isPreconnected.prod hI.isPreconnected).image _
    (continuous_fst.mul continuous_snd).continuousOn).ordConnected

section Finite

variable {ι : Type*} [Finite ι] [Nonempty ι]
variable (H : Set ℝ) (I : ι → Set ℝ)
variable (hI : ∀ a, (I a).Nonempty) (hH₀ : ∀ h ∈ H, 0 ≤ h)

include hH₀

include hI in
theorem upperHull_setMul_intervalInf :
    upperHull (setMul H (intervalInf I)) = ⋃ a, upperHull (setMul H (I a)) := by
  ext w
  constructor
  · rintro ⟨p, ⟨h, hh, i, hi, rfl⟩, hpw⟩
    obtain ⟨a, v, hv, hvi⟩ := mem_iUnion.mp hi.1
    exact mem_iUnion.mpr ⟨a, h * v, ⟨h, hh, v, hv, rfl⟩,
      (mul_le_mul_of_nonneg_left hvi (hH₀ h hh)).trans hpw⟩
  · intro hw
    obtain ⟨a, p, ⟨h, hh, i, hi, rfl⟩, hpw⟩ := mem_iUnion.mp hw
    have hiH : i ∈ upperHull (intervalInf I) := by
      rw [upperHull_intervalInf I hI]
      exact mem_iUnion.mpr ⟨a, mem_upperHull hi⟩
    obtain ⟨v, hv, hvi⟩ := hiH
    exact ⟨h * v, ⟨h, hh, v, hv, rfl⟩,
      (mul_le_mul_of_nonneg_left hvi (hH₀ h hh)).trans hpw⟩

theorem lowerHull_setMul_intervalInf :
    lowerHull (setMul H (intervalInf I)) = ⋂ a, lowerHull (setMul H (I a)) := by
  classical
  ext w
  constructor
  · rintro ⟨p, ⟨h, hh, i, hi, rfl⟩, hwp⟩
    apply mem_iInter.mpr
    intro a
    obtain ⟨v, hv, hiv⟩ := mem_iInter.mp hi.2 a
    exact ⟨h * v, ⟨h, hh, v, hv, rfl⟩,
      hwp.trans (mul_le_mul_of_nonneg_left hiv (hH₀ h hh))⟩
  · intro hw
    have hp : ∀ a, ∃ h ∈ H, ∃ v ∈ I a, w ≤ h * v := by
      intro a
      obtain ⟨p, ⟨h, hh, v, hv, rfl⟩, hwp⟩ := mem_iInter.mp hw a
      exact ⟨h, hh, v, hv, hwp⟩
    choose h hh v hv hprod using hp
    obtain ⟨b, hb⟩ := finite_exists_min v
    have hvInf : v b ∈ intervalInf I :=
      ⟨mem_iUnion.mpr ⟨b, v b, hv b, le_rfl⟩,
        mem_iInter.mpr (fun a => ⟨v a, hv a, hb a⟩)⟩
    by_cases hw₀ : w ≤ 0
    · obtain ⟨c, hc⟩ := finite_exists_min h
      refine ⟨h c * v b, ⟨h c, hh c, v b, hvInf, rfl⟩, ?_⟩
      by_cases hv₀ : 0 ≤ v b
      · exact hw₀.trans (mul_nonneg (hH₀ _ (hh c)) hv₀)
      · exact (hprod b).trans
          (mul_le_mul_of_nonpos_right (hc b) (le_of_not_ge hv₀))
    · obtain ⟨c, hc⟩ := finite_exists_max h
      have hv₀ : 0 ≤ v b := by
        by_contra hvn
        have hn := mul_nonpos_of_nonneg_of_nonpos (hH₀ _ (hh b)) (le_of_not_ge hvn)
        exact hw₀ ((hprod b).trans hn)
      exact ⟨h c * v b, ⟨h c, hh c, v b, hvInf, rfl⟩,
        (hprod b).trans (mul_le_mul_of_nonneg_right (hc b) hv₀)⟩

include hI in
theorem lowerHull_setMul_intervalSup :
    lowerHull (setMul H (intervalSup I)) = ⋃ a, lowerHull (setMul H (I a)) := by
  ext w
  constructor
  · rintro ⟨p, ⟨h, hh, i, hi, rfl⟩, hwp⟩
    obtain ⟨a, v, hv, hiv⟩ := mem_iUnion.mp hi.1
    exact mem_iUnion.mpr ⟨a, h * v, ⟨h, hh, v, hv, rfl⟩,
      hwp.trans (mul_le_mul_of_nonneg_left hiv (hH₀ h hh))⟩
  · intro hw
    obtain ⟨a, p, ⟨h, hh, i, hi, rfl⟩, hwp⟩ := mem_iUnion.mp hw
    have hiH : i ∈ lowerHull (intervalSup I) := by
      rw [lowerHull_intervalSup I hI]
      exact mem_iUnion.mpr ⟨a, mem_lowerHull hi⟩
    obtain ⟨v, hv, hiv⟩ := hiH
    exact ⟨h * v, ⟨h, hh, v, hv, rfl⟩,
      hwp.trans (mul_le_mul_of_nonneg_left hiv (hH₀ h hh))⟩

theorem upperHull_setMul_intervalSup :
    upperHull (setMul H (intervalSup I)) = ⋂ a, upperHull (setMul H (I a)) := by
  classical
  ext w
  constructor
  · rintro ⟨p, ⟨h, hh, i, hi, rfl⟩, hpw⟩
    apply mem_iInter.mpr
    intro a
    obtain ⟨v, hv, hvi⟩ := mem_iInter.mp hi.2 a
    exact ⟨h * v, ⟨h, hh, v, hv, rfl⟩,
      (mul_le_mul_of_nonneg_left hvi (hH₀ h hh)).trans hpw⟩
  · intro hw
    have hp : ∀ a, ∃ h ∈ H, ∃ v ∈ I a, h * v ≤ w := by
      intro a
      obtain ⟨p, ⟨h, hh, v, hv, rfl⟩, hpw⟩ := mem_iInter.mp hw a
      exact ⟨h, hh, v, hv, hpw⟩
    choose h hh v hv hprod using hp
    obtain ⟨b, hb⟩ := finite_exists_max v
    have hvSup : v b ∈ intervalSup I :=
      ⟨mem_iUnion.mpr ⟨b, v b, hv b, le_rfl⟩,
        mem_iInter.mpr (fun a => ⟨v a, hv a, hb a⟩)⟩
    by_cases hw₀ : 0 ≤ w
    · obtain ⟨c, hc⟩ := finite_exists_min h
      refine ⟨h c * v b, ⟨h c, hh c, v b, hvSup, rfl⟩, ?_⟩
      by_cases hv₀ : v b ≤ 0
      · exact (mul_nonpos_of_nonneg_of_nonpos (hH₀ _ (hh c)) hv₀).trans hw₀
      · exact (mul_le_mul_of_nonneg_right (hc b) (le_of_not_ge hv₀)).trans (hprod b)
    · obtain ⟨c, hc⟩ := finite_exists_max h
      have hv₀ : v b ≤ 0 := by
        by_contra hvn
        have hn := mul_nonneg (hH₀ _ (hh b)) (le_of_not_ge hvn)
        exact hw₀ (hn.trans (hprod b))
      exact ⟨h c * v b, ⟨h c, hh c, v b, hvSup, rfl⟩,
        (mul_le_mul_of_nonpos_right (hc b) hv₀).trans (hprod b)⟩

include hI in
theorem setMul_intervalInf (hH : H.OrdConnected) :
    setMul H (intervalInf I) = intervalInf (fun a => setMul H (I a)) := by
  rw [← hull_inter_eq (setMul_ordConnected hH (intervalInf_ordConnected I)),
    upperHull_setMul_intervalInf H I hI hH₀,
    lowerHull_setMul_intervalInf H I hH₀]
  rfl

include hI in
theorem setMul_intervalSup (hH : H.OrdConnected) :
    setMul H (intervalSup I) = intervalSup (fun a => setMul H (I a)) := by
  rw [← hull_inter_eq (setMul_ordConnected hH (intervalSup_ordConnected I)),
    upperHull_setMul_intervalSup H I hH₀,
    lowerHull_setMul_intervalSup H I hI hH₀]
  exact inter_comm _ _

end Finite

end ScalarMonotone
