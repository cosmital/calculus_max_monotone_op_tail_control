import MonotoneOperators.ExtremaOperations

/-!
# Finite extrema and algebraic operations: resolvent proofs

The hypotheses on `F` and `G` in the intermediate lemmas below express their
finite resolvent maxima or minima. They are discharged by the extremum
construction in the bundled corollaries. The proofs retain all fibers,
including empty ones, throughout.
-/

open Set

namespace ScalarMonotone

private theorem exists_lexicographic_max {ι : Type*} [Finite ι] [Nonempty ι]
    (x w : ι → ℝ) : ∃ b, (∀ a, x a ≤ x b) ∧
      (∀ a, x a = x b → w a ≤ w b) := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨c, _, hc⟩ := Finset.univ.exists_max_image x Finset.univ_nonempty
  let T := Finset.univ.filter (fun a => x a = x c)
  have hcT : c ∈ T := by simp [T]
  obtain ⟨b, hb, hbw⟩ := T.exists_max_image w ⟨c, hcT⟩
  have hbxc : x b = x c := (Finset.mem_filter.mp hb).2
  refine ⟨b, fun a => ?_, fun a hax => ?_⟩
  · rw [hbxc]
    exact hc a (Finset.mem_univ a)
  · exact hbw a (by simp [T, hax, hbxc])

private theorem exists_lexicographic_min {ι : Type*} [Finite ι] [Nonempty ι]
    (x w : ι → ℝ) : ∃ b, (∀ a, x b ≤ x a) ∧
      (∀ a, x a = x b → w b ≤ w a) := by
  obtain ⟨b, hb, hbw⟩ := exists_lexicographic_max (fun a => -x a) (fun a => -w a)
  exact ⟨b, fun a => neg_le_neg_iff.mp (hb a),
    fun a hax => neg_le_neg_iff.mp (hbw a (by rw [hax]))⟩

theorem resolvent_le_of_graph_bounds {f : Operator} (hf : MaximalIncreasing f)
    {x u y v : ℝ} (hv : v ∈ f y) (hyx : y ≤ x) (huv : u ≤ v) :
    resolvent f hf (x + u) ≤ x := by
  have hm := resolvent_monotone hf (show x + u ≤ x + v by linarith)
  have hc := resolvent_complement_monotone hf (show y + v ≤ x + v by linarith)
  dsimp only at hc
  rw [(resolvent_eq_iff hf).mpr hv] at hc
  linarith

theorem le_resolvent_of_graph_bounds {f : Operator} (hf : MaximalIncreasing f)
    {x u y v : ℝ} (hv : v ∈ f y) (hxy : x ≤ y) (hvu : v ≤ u) :
    x ≤ resolvent f hf (x + u) := by
  have hm := resolvent_monotone hf (show x + v ≤ x + u by linarith)
  have hc := resolvent_complement_monotone hf (show x + v ≤ y + v by linarith)
  dsimp only at hc
  rw [(resolvent_eq_iff hf).mpr hv] at hc
  linarith

private theorem finite_interval_subsingleton {ι : Type*} [Finite ι]
    {A : Set ℝ} {B : ι → Set ℝ} (hA : A.OrdConnected)
    (hB : ∀ a, (B a).Subsingleton) (hAB : A ⊆ ⋃ a, B a) : A.Subsingleton := by
  have hfin : A.Finite := (Set.finite_iUnion (fun a => (hB a).finite)).subset hAB
  intro u hu v hv
  rcases lt_trichotomy u v with huv | huv | hvu
  · exact ((Set.Icc_infinite huv) (hfin.subset (fun _ hw => hA.out hu hv hw))).elim
  · exact huv
  · exact ((Set.Icc_infinite hvu) (hfin.subset (fun _ hw => hA.out hv hu hw))).elim

section Increasing

variable {ι : Type*} [Finite ι] [Nonempty ι]
variable (f : ι → Operator) (hf : ∀ a, MaximalIncreasing (f a))
variable {F G h : Operator}

omit [Nonempty ι] in
theorem noRectangle_of_finite_resolvent_selector
    (hF : MaximalIncreasing F)
    (hFJ : ∀ s, resolvent F hF s ∈ range (fun a => resolvent (f a) (hf a) s))
    (hc : ∀ a, Increasing (comp (f a) h)) : NoRectangle h F := by
  intro z
  by_cases hz : (inverse h z).Subsingleton
  · exact Or.inl hz
  · right
    apply finite_interval_subsingleton (maximal_fiber_ordConnected hF z)
      (B := fun a => f a z)
    · intro a
      exact (noRectangle_of_comp_increasing (hc a) z).resolve_left hz
    · intro u hu
      obtain ⟨a, ha⟩ := hFJ (z + u)
      rw [(resolvent_eq_iff hF).mpr hu] at ha
      exact mem_iUnion.mpr ⟨a, (resolvent_eq_iff (hf a)).mp ha⟩

theorem add_eq_of_resolvent_maxima (hh : Increasing h)
    (hadd : ∀ a, MaximalIncreasing (add h (f a)))
    (hF : MaximalIncreasing F) (hG : MaximalIncreasing G)
    (hFJ : ∀ s, IsGreatest (range (fun a => resolvent (f a) (hf a) s))
      (resolvent F hF s))
    (hGJ : ∀ s, IsGreatest (range (fun a => resolvent (add h (f a)) (hadd a) s))
      (resolvent G hG s)) : add h F = G := by
  classical
  apply Eq.symm
  apply hG.eq_of_le (hh.add hF.1)
  intro x u hu
  let s := x + u
  let X := fun a => resolvent (add h (f a)) (hadd a) s
  have hm : ∀ a, ∃ w ∈ h (X a), ∃ v ∈ f a (X a), s - X a = w + v := by
    intro a
    exact resolvent_mem (hadd a) s
  choose w hw v hv he using hm
  obtain ⟨b, hb, hbw⟩ := exists_lexicographic_max X w
  have hwb : ∀ a, w a ≤ w b := by
    intro a
    rcases (hb a).eq_or_lt with hab | hab
    · exact hbw a hab
    · exact hh.le_of_lt (hw a) (hw b) hab
  have hX : resolvent G hG s = X b := by
    apply le_antisymm
    · obtain ⟨a, ha⟩ := (hGJ s).1
      rw [← ha]
      exact hb a
    · exact (hGJ s).2 (mem_range_self b)
  have hXF : resolvent F hF (X b + v b) = X b := by
    have hle : ∀ a, resolvent (f a) (hf a) (X b + v b) ≤ X b := by
      intro a
      have harg : X b + v b ≤ X a + v a := by
        have hea := he a
        have heb := he b
        have hwa := hwb a
        linarith
      exact ((resolvent_monotone (hf a) harg).trans_eq
        ((resolvent_eq_iff (hf a)).mpr (hv a))).trans (hb a)
    apply le_antisymm
    · obtain ⟨a, ha⟩ := (hFJ (X b + v b)).1
      rw [← ha]
      exact hle a
    · have hp := (hFJ (X b + v b)).2 (mem_range_self b)
      simpa only [(resolvent_eq_iff (hf b)).mpr (hv b)] using hp
  have hxb : X b = x := by
    rw [← hX]
    exact (resolvent_eq_iff hG).mpr hu
  have hvF := (resolvent_eq_iff hF).mp hXF
  refine ⟨w b, ?_, v b, ?_, ?_⟩
  · simpa [hxb] using hw b
  · simpa [hxb] using hvF
  · have heb := he b
    dsimp [s] at heb
    rw [hxb] at heb
    linarith

theorem add_eq_of_resolvent_minima (hh : Increasing h)
    (hadd : ∀ a, MaximalIncreasing (add h (f a)))
    (hF : MaximalIncreasing F) (hG : MaximalIncreasing G)
    (hFJ : ∀ s, IsLeast (range (fun a => resolvent (f a) (hf a) s))
      (resolvent F hF s))
    (hGJ : ∀ s, IsLeast (range (fun a => resolvent (add h (f a)) (hadd a) s))
      (resolvent G hG s)) : add h F = G := by
  classical
  apply Eq.symm
  apply hG.eq_of_le (hh.add hF.1)
  intro x u hu
  let s := x + u
  let X := fun a => resolvent (add h (f a)) (hadd a) s
  have hm : ∀ a, ∃ w ∈ h (X a), ∃ v ∈ f a (X a), s - X a = w + v := by
    intro a
    exact resolvent_mem (hadd a) s
  choose w hw v hv he using hm
  obtain ⟨b, hb, hbw⟩ := exists_lexicographic_min X w
  have hwb : ∀ a, w b ≤ w a := by
    intro a
    rcases (hb a).eq_or_lt with hab | hab
    · exact hbw a hab.symm
    · exact hh.le_of_lt (hw b) (hw a) hab
  have hX : resolvent G hG s = X b := by
    apply le_antisymm
    · exact (hGJ s).2 (mem_range_self b)
    · obtain ⟨a, ha⟩ := (hGJ s).1
      rw [← ha]
      exact hb a
  have hXF : resolvent F hF (X b + v b) = X b := by
    have hle : ∀ a, X b ≤ resolvent (f a) (hf a) (X b + v b) := by
      intro a
      have harg : X a + v a ≤ X b + v b := by
        have hea := he a
        have heb := he b
        have hwa := hwb a
        linarith
      exact (hb a).trans (((resolvent_eq_iff (hf a)).mpr (hv a)).symm.trans_le
        (resolvent_monotone (hf a) harg))
    apply le_antisymm
    · have hp := (hFJ (X b + v b)).2 (mem_range_self b)
      simpa only [(resolvent_eq_iff (hf b)).mpr (hv b)] using hp
    · obtain ⟨a, ha⟩ := (hFJ (X b + v b)).1
      rw [← ha]
      exact hle a
  have hxb : X b = x := by
    rw [← hX]
    exact (resolvent_eq_iff hG).mpr hu
  have hvF := (resolvent_eq_iff hF).mp hXF
  refine ⟨w b, ?_, v b, ?_, ?_⟩
  · simpa [hxb] using hw b
  · simpa [hxb] using hvF
  · have heb := he b
    dsimp [s] at heb
    rw [hxb] at heb
    linarith

theorem comp_eq_of_resolvent_maxima (hh : Increasing h)
    (hc : ∀ a, MaximalIncreasing (comp (f a) h))
    (hF : MaximalIncreasing F) (hG : MaximalIncreasing G)
    (hFJ : ∀ s, IsGreatest (range (fun a => resolvent (f a) (hf a) s))
      (resolvent F hF s))
    (hGJ : ∀ s, IsGreatest (range (fun a => resolvent (comp (f a) h) (hc a) s))
      (resolvent G hG s)) : comp F h = G := by
  classical
  have hrect := noRectangle_of_finite_resolvent_selector f hf hF
    (fun s => (hFJ s).1) (fun a => (hc a).1)
  apply Eq.symm
  apply hG.eq_of_le (hh.comp_of_noRectangle hF.1 hrect)
  intro x u hu
  let s := x + u
  let X := fun a => resolvent (comp (f a) h) (hc a) s
  have hm : ∀ a, ∃ z ∈ h (X a), s - X a ∈ f a z := by
    intro a
    exact resolvent_mem (hc a) s
  choose z hz hv using hm
  obtain ⟨b, hb, hbz⟩ := exists_lexicographic_max X z
  have hzb : ∀ a, z a ≤ z b := by
    intro a
    rcases (hb a).eq_or_lt with hab | hab
    · exact hbz a hab
    · exact hh.le_of_lt (hz a) (hz b) hab
  have hX : resolvent G hG s = X b := by
    apply le_antisymm
    · obtain ⟨a, ha⟩ := (hGJ s).1
      rw [← ha]
      exact hb a
    · exact (hGJ s).2 (mem_range_self b)
  have hXF : resolvent F hF (z b + (s - X b)) = z b := by
    have hle : ∀ a, resolvent (f a) (hf a) (z b + (s - X b)) ≤ z b := by
      intro a
      exact resolvent_le_of_graph_bounds (hf a) (hv a) (hzb a)
        (sub_le_sub_left (hb a) s)
    apply le_antisymm
    · obtain ⟨a, ha⟩ := (hFJ (z b + (s - X b))).1
      rw [← ha]
      exact hle a
    · have hp := (hFJ (z b + (s - X b))).2 (mem_range_self b)
      simpa only [(resolvent_eq_iff (hf b)).mpr (hv b)] using hp
  have hxb : X b = x := by
    rw [← hX]
    exact (resolvent_eq_iff hG).mpr hu
  refine ⟨z b, ?_, ?_⟩
  · simpa [hxb] using hz b
  · have hp := (resolvent_eq_iff hF).mp hXF
    simpa [hxb, s] using hp

theorem comp_eq_of_resolvent_minima (hh : Increasing h)
    (hc : ∀ a, MaximalIncreasing (comp (f a) h))
    (hF : MaximalIncreasing F) (hG : MaximalIncreasing G)
    (hFJ : ∀ s, IsLeast (range (fun a => resolvent (f a) (hf a) s))
      (resolvent F hF s))
    (hGJ : ∀ s, IsLeast (range (fun a => resolvent (comp (f a) h) (hc a) s))
      (resolvent G hG s)) : comp F h = G := by
  classical
  have hrect := noRectangle_of_finite_resolvent_selector f hf hF
    (fun s => (hFJ s).1) (fun a => (hc a).1)
  apply Eq.symm
  apply hG.eq_of_le (hh.comp_of_noRectangle hF.1 hrect)
  intro x u hu
  let s := x + u
  let X := fun a => resolvent (comp (f a) h) (hc a) s
  have hm : ∀ a, ∃ z ∈ h (X a), s - X a ∈ f a z := by
    intro a
    exact resolvent_mem (hc a) s
  choose z hz hv using hm
  obtain ⟨b, hb, hbz⟩ := exists_lexicographic_min X z
  have hzb : ∀ a, z b ≤ z a := by
    intro a
    rcases (hb a).eq_or_lt with hab | hab
    · exact hbz a hab.symm
    · exact hh.le_of_lt (hz b) (hz a) hab
  have hX : resolvent G hG s = X b := by
    apply le_antisymm
    · exact (hGJ s).2 (mem_range_self b)
    · obtain ⟨a, ha⟩ := (hGJ s).1
      rw [← ha]
      exact hb a
  have hXF : resolvent F hF (z b + (s - X b)) = z b := by
    have hle : ∀ a, z b ≤ resolvent (f a) (hf a) (z b + (s - X b)) := by
      intro a
      exact le_resolvent_of_graph_bounds (hf a) (hv a) (hzb a)
        (sub_le_sub_left (hb a) s)
    apply le_antisymm
    · have hp := (hFJ (z b + (s - X b))).2 (mem_range_self b)
      simpa only [(resolvent_eq_iff (hf b)).mpr (hv b)] using hp
    · obtain ⟨a, ha⟩ := (hFJ (z b + (s - X b))).1
      rw [← ha]
      exact hle a
  have hxb : X b = x := by
    rw [← hX]
    exact (resolvent_eq_iff hG).mpr hu
  refine ⟨z b, ?_, ?_⟩
  · simpa [hxb] using hz b
  · have hp := (resolvent_eq_iff hF).mp hXF
    simpa [hxb, s] using hp

end Increasing

end ScalarMonotone
