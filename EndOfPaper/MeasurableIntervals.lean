import EndOfPaper.Aumann
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-!
The hit-open/extended-endpoint equivalence in def:aumannintegral.
Nonempty interval values may be unbounded; the endpoints take values in
EReal, and the measure space is arbitrary. A countable rational interval
basis handles all open sets, including singleton irrational fibers.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

def intervalLowerExtended (A : Set ℝ) : EReal := sInf ((fun x : ℝ => (x : EReal)) '' A)
def intervalUpperExtended (A : Set ℝ) : EReal := sSup ((fun x : ℝ => (x : EReal)) '' A)

theorem lowerExtended_lt_iff_hit_Iio (A : Set ℝ) (a : ℝ) :
    intervalLowerExtended A < (a : EReal) ↔ (A ∩ Iio a).Nonempty := by
  classical
  constructor
  · intro h
    by_contra hn
    have hb : (a : EReal) ≤ intervalLowerExtended A := by
      apply le_sInf
      rintro y ⟨x, hx, rfl⟩
      change (a : EReal) ≤ (x : EReal)
      exact_mod_cast (le_of_not_gt (fun hxa => hn ⟨x, hx, hxa⟩) : a ≤ x)
    exact (not_le_of_gt h) hb
  · rintro ⟨x, hx, hxa⟩
    exact (sInf_le (show (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' A from
      ⟨x, hx, rfl⟩)).trans_lt (by exact_mod_cast hxa)

theorem lt_upperExtended_iff_hit_Ioi (A : Set ℝ) (a : ℝ) :
    (a : EReal) < intervalUpperExtended A ↔ (A ∩ Ioi a).Nonempty := by
  classical
  constructor
  · intro h
    by_contra hn
    have hb : intervalUpperExtended A ≤ (a : EReal) := by
      apply sSup_le
      rintro y ⟨x, hx, rfl⟩
      change (x : EReal) ≤ (a : EReal)
      exact_mod_cast (le_of_not_gt (fun hax => hn ⟨x, hx, hax⟩) : x ≤ a)
    exact (not_le_of_gt h) hb
  · rintro ⟨x, hx, hax⟩
    exact (show (a : EReal) < (x : EReal) by exact_mod_cast hax).trans_le
      (le_sSup (show (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' A from ⟨x, hx, rfl⟩))

theorem interval_hit_Ioo_iff {A : Set ℝ} (hA : A.OrdConnected) {a b : ℝ} (hab : a < b) :
    (A ∩ Ioo a b).Nonempty ↔
      intervalLowerExtended A < (b : EReal) ∧ (a : EReal) < intervalUpperExtended A := by
  constructor
  · rintro ⟨x, hx, hax, hxb⟩
    exact ⟨(lowerExtended_lt_iff_hit_Iio A b).mpr ⟨x, hx, hxb⟩,
      (lt_upperExtended_iff_hit_Ioi A a).mpr ⟨x, hx, hax⟩⟩
  · rintro ⟨hl, hu⟩
    obtain ⟨x, hx, hxb⟩ := (lowerExtended_lt_iff_hit_Iio A b).mp hl
    obtain ⟨y, hy, hay⟩ := (lt_upperExtended_iff_hit_Ioi A a).mp hu
    by_cases hax : a < x
    · exact ⟨x, hx, hax, hxb⟩
    by_cases hyb : y < b
    · exact ⟨y, hy, hay, hyb⟩
    have hxa : x ≤ a := le_of_not_gt hax
    have hby : b ≤ y := le_of_not_gt hyb
    refine ⟨(a+b)/2, hA.out hx hy ⟨by linarith, by linarith⟩, ?_, ?_⟩ <;> linarith

def HitOpenMeasurable {Θ : Type*} [MeasurableSpace Θ] (h : Θ → Set ℝ) : Prop :=
  ∀ O : Set ℝ, IsOpen O → MeasurableSet {θ | (h θ ∩ O).Nonempty}

/-- The extended endpoints are measurable even when the intervals are
unbounded; neither endpoint is replaced by a real-valued proxy. -/
theorem hitOpenMeasurable_endpoints {Θ : Type*} [MeasurableSpace Θ]
    {h : Θ → Set ℝ} (hn : ∀ θ, (h θ).Nonempty) (hh : HitOpenMeasurable h) :
    Measurable (fun θ => intervalLowerExtended (h θ)) ∧
      Measurable (fun θ => intervalUpperExtended (h θ)) := by
  constructor
  · apply measurable_of_Iio
    intro a
    induction a with
    | bot => simp
    | coe a =>
      convert hh (Iio a) isOpen_Iio using 1
      ext θ
      exact lowerExtended_lt_iff_hit_Iio (h θ) a
    | top =>
      have he : (fun θ => intervalLowerExtended (h θ)) ⁻¹' Iio ⊤ = univ := by
        ext θ
        simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
        obtain ⟨x, hx⟩ := hn θ
        exact (sInf_le (show (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' h θ from
          ⟨x, hx, rfl⟩)).trans_lt (by simp)
      rw [he]
      exact MeasurableSet.univ
  · apply measurable_of_Ioi
    intro a
    induction a with
    | bot =>
      have he : (fun θ => intervalUpperExtended (h θ)) ⁻¹' Ioi ⊥ = univ := by
        ext θ
        simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
        obtain ⟨x, hx⟩ := hn θ
        exact (show (⊥ : EReal) < (x : EReal) by simp).trans_le
          (le_sSup (show (x : EReal) ∈ (fun x : ℝ => (x : EReal)) '' h θ from ⟨x, hx, rfl⟩))
      rw [he]
      exact MeasurableSet.univ
    | coe a =>
      convert hh (Ioi a) isOpen_Ioi using 1
      ext θ
      exact lt_upperExtended_iff_hit_Ioi (h θ) a
    | top => simp

/-- Endpoint measurability implies hit-open measurability. The countable
basis consists of rational intervals, so singleton irrational fibers are also
handled; no countable set of point selections is substituted for the fibers. -/
theorem hitOpenMeasurable_of_endpoints {Θ : Type*} [MeasurableSpace Θ]
    {h : Θ → Set ℝ} (hord : ∀ θ, (h θ).OrdConnected)
    (hl : Measurable (fun θ => intervalLowerExtended (h θ)))
    (hu : Measurable (fun θ => intervalUpperExtended (h θ))) : HitOpenMeasurable h := by
  classical
  intro O hO
  let T := {ab : ℚ × ℚ // ab.1 < ab.2 ∧ Ioo (ab.1 : ℝ) (ab.2 : ℝ) ⊆ O}
  have he : {θ | (h θ ∩ O).Nonempty} =
      ⋃ t : T, {θ | (h θ ∩ Ioo (t.val.1 : ℝ) (t.val.2 : ℝ)).Nonempty} := by
    ext θ
    constructor
    · rintro ⟨x, hx, hxO⟩
      obtain ⟨a₀, b₀, ⟨ha₀, hb₀⟩, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds hxO)
      obtain ⟨a, haa₀, hax⟩ := exists_rat_btwn ha₀
      obtain ⟨b, hxb, hbb₀⟩ := exists_rat_btwn hb₀
      have hab : a < b := by exact_mod_cast hax.trans hxb
      have hcontain : Ioo (a : ℝ) (b : ℝ) ⊆ O := fun y hy =>
        hsub ⟨haa₀.trans hy.1, hy.2.trans hbb₀⟩
      refine mem_iUnion.mpr ⟨(⟨(a,b), hab, hcontain⟩ : T), ?_⟩
      exact ⟨x, hx, hax, hxb⟩
    · intro hθ
      obtain ⟨t, ht⟩ := mem_iUnion.mp hθ
      obtain ⟨x, hx, hxab⟩ := ht
      exact ⟨x, hx, t.property.2 hxab⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro t
  have hset : {θ | (h θ ∩ Ioo (t.val.1 : ℝ) (t.val.2 : ℝ)).Nonempty} =
      (fun θ => intervalLowerExtended (h θ)) ⁻¹' Iio ((t.val.2 : ℝ) : EReal) ∩
        (fun θ => intervalUpperExtended (h θ)) ⁻¹' Ioi ((t.val.1 : ℝ) : EReal) := by
    ext θ
    exact interval_hit_Ioo_iff (hord θ) (by exact_mod_cast t.property.1)
  rw [hset]
  exact (measurableSet_Iio.preimage hl).inter (measurableSet_Ioi.preimage hu)

/-- The interval-valued measurability equivalence in def:aumannintegral,
with genuine extended-real endpoints and arbitrary unbounded intervals. -/
theorem hitOpenMeasurable_iff_endpoints {Θ : Type*} [MeasurableSpace Θ]
    {h : Θ → Set ℝ} (hn : ∀ θ, (h θ).Nonempty) (hord : ∀ θ, (h θ).OrdConnected) :
    HitOpenMeasurable h ↔
      Measurable (fun θ => intervalLowerExtended (h θ)) ∧
        Measurable (fun θ => intervalUpperExtended (h θ)) :=
  ⟨fun hh => hitOpenMeasurable_endpoints hn hh,
   fun hh => hitOpenMeasurable_of_endpoints hord hh.1 hh.2⟩


end ScalarMonotone.EndOfPaper
end
