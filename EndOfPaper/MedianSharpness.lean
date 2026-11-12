import EndOfPaper.MedianTransform
import EndOfPaper.HardySharpness

/-!
Exact equivalence of the ordered-coordinate median transform with
the minimum over every prescribed-size cut. Continuity is proved
for the actual median and its finite cut bound. Both exact Hardy
suprema and epsilon-optimal finite-valued comonotone existence
follow from the full geometric-band sharpness theorem.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem continuous_finite_ciInf {ι A : Type*} [Finite ι] [Nonempty ι]
    [TopologicalSpace A] {f : ι → A → ℝ} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun a => ⨅ i, f i a) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf'_univ_eq_ciInf] using
    (Continuous.finset_inf'_apply (f := f) Finset.univ_nonempty (fun i _ => hf i))

theorem continuous_finite_ciSup {ι A : Type*} [Finite ι] [Nonempty ι]
    [TopologicalSpace A] {f : ι → A → ℝ} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun a => ⨆ i, f i a) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.sup'_univ_eq_ciSup] using
    (Continuous.finset_sup'_apply (f := f) Finset.univ_nonempty (fun i _ => hf i))

theorem scalarMedian_continuous (r : ℕ) : Continuous (scalarMedian r) := by
  change Continuous (fun a : Fin (2*r+1) → ℝ =>
    ⨅ J : Majority r, ⨆ i : {i // i ∈ J.val}, a i.val)
  exact continuous_finite_ciInf (fun J =>
    continuous_finite_ciSup (fun i => continuous_apply i.val))

def medianCutSets (r : ℕ) (ℓ : Fin (r+1)) : Type :=
  {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)}

theorem medianCutSets_finite (r : ℕ) (ℓ : Fin (r+1)) : Finite (medianCutSets r ℓ) := by
  unfold medianCutSets
  infer_instance

theorem medianCutSets_nonempty (r : ℕ) (ℓ : Fin (r+1)) :
    Nonempty (medianCutSets r ℓ) := by
  obtain ⟨J, _, hJ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2*r+1)))) (n := r+(ℓ.val+1))
    (by simp; omega)
  exact ⟨⟨J, hJ⟩⟩

def medianCutBound (r : ℕ) (a : CoordinateVector (2*r+1)) : ℝ :=
  ⨅ ℓ : Fin (r+1), ⨅ J : medianCutSets r ℓ,
    (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ)

/-- Exact equivalence with the displayed minimum over all cuts. The reverse
inequality invokes the already proved full ordered-coordinate formula. -/
theorem median_transform_cut_formula (r : ℕ) (a : CoordinateVector (2*r+1))
    (ha : 0 ≤ a) : superadditiveTransform (scalarMedian r) a = medianCutBound r a := by
  classical
  letI (ℓ : Fin (r+1)) : Nonempty (medianCutSets r ℓ) := medianCutSets_nonempty r ℓ
  letI (ℓ : Fin (r+1)) : Finite (medianCutSets r ℓ) := medianCutSets_finite r ℓ
  apply le_antisymm
  · apply le_ciInf
    intro ℓ
    apply le_ciInf
    intro J
    exact median_transform_subset_upper r (ℓ.val+1) (by omega) J.val J.property ha
  · rw [median_transform_formula r a ha]
    apply le_ciInf
    intro ℓ
    let P := Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1))
    have hmn : r+(ℓ.val+1) ≤ 2*r+1 := by omega
    have hcard : (P.map (Tuple.sort a).toEmbedding).card = r+(ℓ.val+1) := by
      rw [Finset.card_map]
      exact prefix_filter_card hmn
    let J : medianCutSets r ℓ := ⟨P.map (Tuple.sort a).toEmbedding, hcard⟩
    have hu : medianCutBound r a ≤ (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ) :=
      (ciInf_le (finite_range (fun k : Fin (r+1) =>
        ⨅ K : medianCutSets r k, (∑ i ∈ K.val, a i) / ((k.val+1 : ℕ) : ℝ))).bddBelow ℓ).trans
        (ciInf_le (finite_range (fun K : medianCutSets r ℓ =>
          (∑ i ∈ K.val, a i) / ((ℓ.val+1 : ℕ) : ℝ))).bddBelow J)
    simpa only [J, Finset.sum_map, Equiv.toEmbedding_apply] using hu

theorem medianCutBound_continuous (r : ℕ) : Continuous (medianCutBound r) := by
  classical
  letI (ℓ : Fin (r+1)) : Nonempty (medianCutSets r ℓ) := medianCutSets_nonempty r ℓ
  letI (ℓ : Fin (r+1)) : Finite (medianCutSets r ℓ) := medianCutSets_finite r ℓ
  apply continuous_finite_ciInf
  intro ℓ
  apply continuous_finite_ciInf
  intro J
  exact (continuous_finset_sum J.val (fun i _ => continuous_apply i)).div_const _

theorem medianCutBound_aggregation_axioms (r : ℕ) : AggregationAxioms (medianCutBound r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [← median_transform_cut_formula r a ha]
    exact superadditiveTransform_nonneg (median_aggregation_axioms r) ha
  · intro a b ha hab
    have hb : 0 ≤ b := ha.trans hab
    rw [← median_transform_cut_formula r a ha, ← median_transform_cut_formula r b hb]
    exact superadditiveTransform_mono (median_aggregation_axioms r) ha hab
  · intro c hc a ha
    rw [← median_transform_cut_formula r (c • a) (smul_nonneg hc ha),
      ← median_transform_cut_formula r a ha]
    exact superadditiveTransform_smul (median_aggregation_axioms r) ha hc

universe uMedianSharpness

theorem median_hardy_tail_sharp (r : ℕ) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : CoordinateVector (2*r+1)} (ha : 0 ≤ a) :
    sSup (hardyTailValues.{uMedianSharpness} (scalarMedian r) p a) = medianCutBound r a ∧
      sSup (comonotoneHardyTailValues.{uMedianSharpness} (scalarMedian r) p a) = medianCutBound r a := by
  obtain ⟨hg, hc⟩ := hardy_tail_aggregation_sharp (median_aggregation_axioms r)
    (scalarMedian_continuous r).continuousOn hp ha
  rw [median_transform_cut_formula r a ha] at hg hc
  exact ⟨hg.symm, hc.symm⟩

/-- Explicit epsilon-optimal existence in the finite-valued comonotone class,
with exactly the prescribed actual completed marginal Hardy values. -/
theorem median_comonotone_near_sharp (r : ℕ) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : CoordinateVector (2*r+1)} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ comonotoneHardyTailValues.{uMedianSharpness} (scalarMedian r) p a,
      medianCutBound r a - ε < z := by
  by_contra hn
  push_neg at hn
  have hupper := csSup_le
    (comonotoneHardyTailValues_nonempty (median_aggregation_axioms r)
      (scalarMedian_continuous r).continuousOn hp ha) hn
  rw [(median_hardy_tail_sharp r hp ha).2] at hupper
  linarith

end ScalarMonotone.EndOfPaper
end
