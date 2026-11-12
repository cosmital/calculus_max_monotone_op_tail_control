import MonotoneOperators.ExtremaFinite
import Mathlib.Tactic

/-!
Continuity-only finite range envelopes (eq:rangeenvelopes), including both
common orientations. No Lipschitz hypothesis is imposed.
-/

open Set
noncomputable section
namespace ScalarMonotone

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem continuous_finite_ciInf (q : ι → ℝ → ℝ) (hc : ∀ i, Continuous (q i)) :
    Continuous (fun s => ⨅ i, q i s) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf'_univ_eq_ciInf] using
    (Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => hc i))

theorem continuous_finite_ciSup (q : ι → ℝ → ℝ) (hc : ∀ i, Continuous (q i)) :
    Continuous (fun s => ⨆ i, q i s) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.sup'_univ_eq_ciSup] using
    (Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => hc i))

theorem range_finite_ciInf_monotone (q : ι → ℝ → ℝ)
    (hm : ∀ i, Monotone (q i)) (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨅ i, q i s) =
      {t | (∃ i s, q i s ≤ t) ∧ ∀ i, ∃ s, t ≤ q i s} := by
  classical
  letI := Fintype.ofFinite ι
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => q i s)
    exact ⟨⟨i, s, hi.le⟩, fun j => ⟨s, ciInf_le (finite_range _).bddBelow j⟩⟩
  · rintro ⟨⟨i, s₀, hs₀⟩, h⟩
    choose s hs using h
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
    have hlo : (⨅ l, q l s₀) ≤ t := (ciInf_le (finite_range _).bddBelow i).trans hs₀
    have hhi : t ≤ ⨅ l, q l (s j) :=
      le_ciInf (fun l => (hs l).trans (hm l (hj l (Finset.mem_univ l))))
    exact (isPreconnected_range (continuous_finite_ciInf q hc)).ordConnected.out
      (mem_range_self s₀) (mem_range_self (s j)) ⟨hlo, hhi⟩

theorem range_finite_ciSup_monotone (q : ι → ℝ → ℝ)
    (hm : ∀ i, Monotone (q i)) (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨆ i, q i s) =
      {t | (∀ i, ∃ s, q i s ≤ t) ∧ ∃ i s, t ≤ q i s} := by
  classical
  letI := Fintype.ofFinite ι
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => q i s)
    exact ⟨fun j => ⟨s, le_ciSup (finite_range (fun l => q l s)).bddAbove j⟩,
      ⟨i, s, hi.ge⟩⟩
  · rintro ⟨h, ⟨i, s₁, hs₁⟩⟩
    choose s hs using h
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ s Finset.univ_nonempty
    have hlo : (⨆ l, q l (s j)) ≤ t :=
      ciSup_le (fun l => (hm l (hj l (Finset.mem_univ l))).trans (hs l))
    have hhi : t ≤ ⨆ l, q l s₁ :=
      hs₁.trans (le_ciSup (finite_range (fun l => q l s₁)).bddAbove i)
    exact (isPreconnected_range (continuous_finite_ciSup q hc)).ordConnected.out
      (mem_range_self (s j)) (mem_range_self s₁) ⟨hlo, hhi⟩

theorem range_finite_ciInf_antitone (q : ι → ℝ → ℝ)
    (hm : ∀ i, Antitone (q i)) (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨅ i, q i s) =
      {t | (∃ i s, q i s ≤ t) ∧ ∀ i, ∃ s, t ≤ q i s} := by
  classical
  letI := Fintype.ofFinite ι
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => q i s)
    exact ⟨⟨i, s, hi.le⟩, fun j => ⟨s, ciInf_le (finite_range _).bddBelow j⟩⟩
  · rintro ⟨⟨i, s₀, hs₀⟩, h⟩
    choose s hs using h
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ s Finset.univ_nonempty
    have hlo : (⨅ l, q l s₀) ≤ t := (ciInf_le (finite_range _).bddBelow i).trans hs₀
    have hhi : t ≤ ⨅ l, q l (s j) :=
      le_ciInf (fun l => (hs l).trans (hm l (hj l (Finset.mem_univ l))))
    exact (isPreconnected_range (continuous_finite_ciInf q hc)).ordConnected.out
      (mem_range_self s₀) (mem_range_self (s j)) ⟨hlo, hhi⟩

theorem range_finite_ciSup_antitone (q : ι → ℝ → ℝ)
    (hm : ∀ i, Antitone (q i)) (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨆ i, q i s) =
      {t | (∀ i, ∃ s, q i s ≤ t) ∧ ∃ i s, t ≤ q i s} := by
  classical
  letI := Fintype.ofFinite ι
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => q i s)
    exact ⟨fun j => ⟨s, le_ciSup (finite_range (fun l => q l s)).bddAbove j⟩,
      ⟨i, s, hi.ge⟩⟩
  · rintro ⟨h, ⟨i, s₁, hs₁⟩⟩
    choose s hs using h
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
    have hlo : (⨆ l, q l (s j)) ≤ t :=
      ciSup_le (fun l => (hm l (hj l (Finset.mem_univ l))).trans (hs l))
    have hhi : t ≤ ⨆ l, q l s₁ :=
      hs₁.trans (le_ciSup (finite_range (fun l => q l s₁)).bddAbove i)
    exact (isPreconnected_range (continuous_finite_ciSup q hc)).ordConnected.out
      (mem_range_self (s j)) (mem_range_self s₁) ⟨hlo, hhi⟩

/-- The full manuscript range-infimum assertion under continuity alone, for
either common orientation. No Lipschitz bound is added. -/
theorem range_ciInf_eq_intervalInf_continuous (q : ι → ℝ → ℝ)
    (hm : (∀ i, Monotone (q i)) ∨ (∀ i, Antitone (q i)))
    (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨅ i, q i s) = intervalInf (fun i => range (q i)) := by
  have hr : range (fun s => ⨅ i, q i s) =
      {t | (∃ i s, q i s ≤ t) ∧ ∀ i, ∃ s, t ≤ q i s} := by
    rcases hm with hm | hm
    · exact range_finite_ciInf_monotone q hm hc
    · exact range_finite_ciInf_antitone q hm hc
  rw [hr]
  ext t
  simp only [mem_setOf_eq, intervalInf, mem_inter_iff, mem_iUnion, mem_iInter,
    upperHull, lowerHull, mem_range]
  constructor
  · rintro ⟨⟨i, s, hs⟩, hu⟩
    refine ⟨⟨i, q i s, ⟨s, rfl⟩, hs⟩, ?_⟩
    intro j
    obtain ⟨s, hs⟩ := hu j
    exact ⟨q j s, ⟨s, rfl⟩, hs⟩
  · rintro ⟨⟨i, y, ⟨s, rfl⟩, hs⟩, hu⟩
    refine ⟨⟨i, s, hs⟩, ?_⟩
    intro j
    obtain ⟨y, ⟨s, rfl⟩, hs⟩ := hu j
    exact ⟨s, hs⟩

theorem range_ciSup_eq_intervalSup_continuous (q : ι → ℝ → ℝ)
    (hm : (∀ i, Monotone (q i)) ∨ (∀ i, Antitone (q i)))
    (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨆ i, q i s) = intervalSup (fun i => range (q i)) := by
  have hr : range (fun s => ⨆ i, q i s) =
      {t | (∀ i, ∃ s, q i s ≤ t) ∧ ∃ i s, t ≤ q i s} := by
    rcases hm with hm | hm
    · exact range_finite_ciSup_monotone q hm hc
    · exact range_finite_ciSup_antitone q hm hc
  rw [hr]
  ext t
  simp only [mem_setOf_eq, intervalSup, mem_inter_iff, mem_iUnion, mem_iInter,
    upperHull, lowerHull, mem_range]
  constructor
  · rintro ⟨hl, ⟨i, s, hs⟩⟩
    refine ⟨⟨i, q i s, ⟨s, rfl⟩, hs⟩, ?_⟩
    intro j
    obtain ⟨s, hs⟩ := hl j
    exact ⟨q j s, ⟨s, rfl⟩, hs⟩
  · rintro ⟨⟨i, y, ⟨s, rfl⟩, hs⟩, hl⟩
    refine ⟨?_, ⟨i, s, hs⟩⟩
    intro j
    obtain ⟨y, ⟨s, rfl⟩, hs⟩ := hl j
    exact ⟨s, hs⟩

end ScalarMonotone
end
