import MonotoneOperators.IntervalExtrema

/-! # Intersection commutes with interval extrema when all intersections are nonempty -/

namespace ScalarMonotone

open Set

theorem lowerHull_inter {D I : Set ℝ} (hD : D.OrdConnected) (hI : I.OrdConnected)
    (hne : (D ∩ I).Nonempty) : lowerHull (D ∩ I) = lowerHull D ∩ lowerHull I := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy.1, hxy⟩, ⟨y, hy.2, hxy⟩⟩
  · rintro ⟨⟨d, hd, hxd⟩, ⟨i, hi, hxi⟩⟩
    obtain ⟨c, hc⟩ := hne
    rcases le_total x c with hxc | hcx
    · exact ⟨c, hc, hxc⟩
    · have hcm : c ≤ min d i := hcx.trans (le_min hxd hxi)
      exact ⟨min d i, ⟨hD.out hc.1 hd ⟨hcm, min_le_left _ _⟩,
        hI.out hc.2 hi ⟨hcm, min_le_right _ _⟩⟩, le_min hxd hxi⟩

theorem upperHull_inter {D I : Set ℝ} (hD : D.OrdConnected) (hI : I.OrdConnected)
    (hne : (D ∩ I).Nonempty) : upperHull (D ∩ I) = upperHull D ∩ upperHull I := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy.1, hyx⟩, ⟨y, hy.2, hyx⟩⟩
  · rintro ⟨⟨d, hd, hdx⟩, ⟨i, hi, hix⟩⟩
    obtain ⟨c, hc⟩ := hne
    rcases le_total c x with hcx | hxc
    · exact ⟨c, hc, hcx⟩
    · have hmc : max d i ≤ c := (max_le hdx hix).trans hxc
      exact ⟨max d i, ⟨hD.out hd hc.1 ⟨le_max_left _ _, hmc⟩,
        hI.out hi hc.2 ⟨le_max_right _ _, hmc⟩⟩, max_le hdx hix⟩

theorem intervalInf_inter {ι : Type*} (D : Set ℝ) (I : ι → Set ℝ)
    (hD : D.OrdConnected) (hI : ∀ i, (I i).OrdConnected)
    (hne : ∀ i, (D ∩ I i).Nonempty) :
    intervalInf (fun i => D ∩ I i) = D ∩ intervalInf I := by
  ext x
  simp only [intervalInf, upperHull_inter hD (hI _) (hne _),
    lowerHull_inter hD (hI _) (hne _), mem_inter_iff, mem_iUnion, mem_iInter]
  constructor
  · rintro ⟨⟨i, hDu, hIu⟩, h⟩
    exact ⟨(hull_inter_eq hD).subset ⟨hDu, (h i).1⟩, ⟨i, hIu⟩, fun j => (h j).2⟩
  · rintro ⟨hD', ⟨i, hIu⟩, hIl⟩
    exact ⟨⟨i, mem_upperHull hD', hIu⟩, fun j => ⟨mem_lowerHull hD', hIl j⟩⟩

theorem intervalSup_inter {ι : Type*} (D : Set ℝ) (I : ι → Set ℝ)
    (hD : D.OrdConnected) (hI : ∀ i, (I i).OrdConnected)
    (hne : ∀ i, (D ∩ I i).Nonempty) :
    intervalSup (fun i => D ∩ I i) = D ∩ intervalSup I := by
  ext x
  simp only [intervalSup, upperHull_inter hD (hI _) (hne _),
    lowerHull_inter hD (hI _) (hne _), mem_inter_iff, mem_iUnion, mem_iInter]
  constructor
  · rintro ⟨⟨i, hDl, hIl⟩, h⟩
    exact ⟨(hull_inter_eq hD).subset ⟨(h i).1, hDl⟩, ⟨i, hIl⟩, fun j => (h j).2⟩
  · rintro ⟨hD', ⟨i, hIl⟩, hIu⟩
    exact ⟨⟨i, mem_lowerHull hD', hIl⟩, fun j => ⟨mem_upperHull hD', hIu j⟩⟩

end ScalarMonotone
