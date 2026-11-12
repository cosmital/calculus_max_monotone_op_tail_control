import Mathlib

/-!
Finite geometric scales, exact disjoint-band geometry and interval
indicator integration for the Hardy sharpness construction. The final band
ends at zero. All finite cases include the empty decomposition. Finite
nonnegative ranges imply L1 on every finite measure space. The complete
aggregate lower bound and sharpness supremum remain separate obligations.
-/

open Set Filter MeasureTheory
open scoped BigOperators Interval Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def geometricScale (p ε : ℝ) (m j : ℕ) : ℝ := if j < m then p*ε^j else 0

def geometricBand (p ε : ℝ) (m j : ℕ) : Set ℝ :=
  Ioc (geometricScale p ε m (j+1)) (geometricScale p ε m j)

theorem geometricScale_nonnegative {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε) (m j : ℕ) :
    0 ≤ geometricScale p ε m j := by
  unfold geometricScale
  split_ifs <;> positivity

theorem geometricScale_positive {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε)
    {m j : ℕ} (hj : j < m) : 0 < geometricScale p ε m j := by
  simp only [geometricScale, if_pos hj]
  exact mul_pos hp (pow_pos hε j)

theorem geometricScale_succ_le_mul {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 ≤ ε) (m j : ℕ) :
    geometricScale p ε m (j+1) ≤ ε*geometricScale p ε m j := by
  by_cases hj1 : j+1 < m
  · have hj : j < m := by omega
    simp only [geometricScale, if_pos hj1, if_pos hj, pow_succ]
    apply le_of_eq
    ring
  · have he : geometricScale p ε m (j+1) = 0 := by simp [geometricScale, hj1]
    rw [he]
    exact mul_nonneg hε (geometricScale_nonnegative hp hε m j)

theorem geometricScale_antitone {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : ℕ) : Antitone (geometricScale p ε m) := by
  apply antitone_nat_of_succ_le
  intro j
  exact (geometricScale_succ_le_mul hp hε0 m j).trans
    (mul_le_of_le_one_left (geometricScale_nonnegative hp hε0 m j) hε1)

theorem geometricScale_le_initial {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m j : ℕ) : geometricScale p ε m j ≤ p := by
  have hzero : geometricScale p ε m 0 ≤ p := by
    by_cases hm : 0 < m <;> simp [geometricScale, hm, hp]
  exact (geometricScale_antitone hp hε0 hε1 m (Nat.zero_le j)).trans hzero

theorem geometricBand_length_lower {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m j : ℕ) :
    0 ≤ geometricScale p ε m j-geometricScale p ε m (j+1) ∧
      (1-ε)*geometricScale p ε m j ≤
        geometricScale p ε m j-geometricScale p ε m (j+1) := by
  refine ⟨sub_nonneg.mpr (geometricScale_antitone hp hε0 hε1 m (Nat.le_succ j)), ?_⟩
  have ht := geometricScale_succ_le_mul hp hε0 m j
  linarith

theorem geometricBands_disjoint {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : ℕ) {j k : ℕ} (hne : j ≠ k) :
    Disjoint (geometricBand p ε m j) (geometricBand p ε m k) := by
  apply Set.disjoint_left.mpr
  intro u huj huk
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hs := geometricScale_antitone hp hε0 hε1 m (Nat.succ_le_iff.mpr hjk)
    exact not_lt_of_ge (huk.2.trans hs) huj.1
  · have hs := geometricScale_antitone hp hε0 hε1 m (Nat.succ_le_iff.mpr hkj)
    exact not_lt_of_ge (huj.2.trans hs) huk.1

theorem geometricBand_subset_prefix {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m j : ℕ) : geometricBand p ε m j ⊆ Ioc (0 : ℝ) p := by
  intro u hu
  exact ⟨(geometricScale_nonnegative hp hε0 m (j+1)).trans_lt hu.1,
    hu.2.trans (geometricScale_le_initial hp hε0 hε1 m j)⟩

theorem geometricBand_sum_lower {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : ℕ) (w : Fin m → ℝ) {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u)
    (hlower : ∀ j : Fin m, ∀ u ∈ geometricBand p ε m j.val, w j ≤ f u) (u : ℝ) :
    (∑ j : Fin m, (geometricBand p ε m j.val).indicator (fun _ => w j) u) ≤ f u := by
  classical
  by_cases h : ∃ j : Fin m, u ∈ geometricBand p ε m j.val
  · obtain ⟨j, hj⟩ := h
    have hz (k : Fin m) (hkj : k ≠ j) :
        (geometricBand p ε m k.val).indicator (fun _ => w k) u = 0 := by
      apply Set.indicator_of_not_mem
      intro hk
      have hne : k.val ≠ j.val := by intro he; exact hkj (Fin.ext he)
      exact Set.disjoint_left.mp (geometricBands_disjoint hp hε0 hε1 m hne) hk hj
    have he : (∑ k : Fin m, (geometricBand p ε m k.val).indicator (fun _ => w k) u) =
        (geometricBand p ε m j.val).indicator (fun _ => w j) u :=
      Finset.sum_eq_single j (fun k _ hkj => hz k hkj) (by simp)
    rw [he, Set.indicator_of_mem hj]
    exact hlower j u hj
  · have hz (j : Fin m) :
        (geometricBand p ε m j.val).indicator (fun _ => w j) u = 0 :=
      Set.indicator_of_not_mem (fun hj => h ⟨j, hj⟩) _
    simp only [hz, Finset.sum_const_zero]
    exact hf u

theorem interval_indicator_band_integrable (a b c p : ℝ) :
    IntervalIntegrable ((Ioc a b).indicator (fun _ : ℝ => c)) volume 0 p := by
  have hi : Integrable (fun _ : ℝ => c) (volume.restrict (Ι 0 p)) :=
    intervalIntegrable_iff.mp intervalIntegrable_const
  exact intervalIntegrable_iff.mpr (hi.indicator measurableSet_Ioc)

theorem interval_indicator_band_integral {a b p : ℝ} (h0a : 0 ≤ a) (hab : a ≤ b)
    (hbp : b ≤ p) (c : ℝ) :
    (∫ u in (0 : ℝ)..p, (Ioc a b).indicator (fun _ => c) u) = (b-a)*c := by
  have hp : 0 ≤ p := h0a.trans (hab.trans hbp)
  have hsub : Ioc a b ⊆ Ioc (0 : ℝ) p :=
    fun _ hu => ⟨h0a.trans_lt hu.1, hu.2.trans hbp⟩
  rw [intervalIntegral.integral_of_le hp, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hsub, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]

theorem finite_nonnegative_range_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hm : AEMeasurable X μ)
    (hn : ∀ ω, 0 ≤ X ω) (hf : (Set.range X).Finite) : Integrable X μ := by
  obtain ⟨C, hC⟩ := hf.bddAbove
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hn ω)]
    exact hC (Set.mem_range_self ω))

end ScalarMonotone.EndOfPaper
end
