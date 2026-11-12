import Mathlib.Data.Fin.Tuple.Sort
import EndOfPaper.MedianBounds
import EndOfPaper.MedianCapacity
import EndOfPaper.Hypersimplex

/-!
The complete odd-median sharp-transform formula (prop:mediantransform) and
its exact truncation identity. The lower bound constructs a genuine finite
decomposition; sorting is supplied by the pinned Mathlib permutation.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem median_binary_majority (r : ℕ) (v : Fin (2*r+1) → ℝ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hs : ∑ i, v i = ((r+1 : ℕ) : ℝ)) :
    scalarMedian r v = 1 := by
  classical
  let I := Finset.univ.filter (fun i => v i = 1)
  have hsum : (∑ i, v i) = (I.card : ℝ) := by
    calc
      _ = ∑ i, if v i = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rcases hv i with h | h <;> simp [h]
      _ = _ := by simp [I]
  have hI : I.card = r+1 := by exact_mod_cast (hsum.symm.trans hs)
  let J : Majority r := ⟨I, hI⟩
  apply le_antisymm
  · exact median_le_of_majority r v ⟨J, fun i _ => by
      rcases hv i with h | h <;> simp [h]⟩
  · exact le_median_of_majority r v ⟨J, fun i hi => by
      have h : v i = 1 := (Finset.mem_filter.mp hi).2
      simp [h]⟩

/-- A scaled hypersimplex point below a supplies a genuine finite admissible
decomposition with total median t. -/
theorem median_transform_ge_hypersimplex (r : ℕ)
    {a b : Fin (2*r+1) → ℝ} (hb : b ∈ hypersimplex (2*r+1) (r+1))
    {t : ℝ} (ht : 0 ≤ t) (hba : t • b ≤ a) :
    t ≤ superadditiveTransform (scalarMedian r) a := by
  classical
  obtain ⟨ι, hι, w, v, hw, hws, hv, hvs, hsum⟩ := hypersimplex_finite_decomposition hb
  letI := hι
  let u : ι → Fin (2*r+1) → ℝ := fun i => (t*w i) • v i
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i j
    rcases hv i j with h | h <;> simp [h]
  have hu0 : ∀ i, 0 ≤ u i := fun i j => mul_nonneg (mul_nonneg ht (hw i)) (hv0 i j)
  have hu : (∑ i, u i) = t • b := by
    rw [← hsum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (smul_smul t (w i) (v i)).symm
  have hm : ∀ i, scalarMedian r (u i) = t*w i := by
    intro i
    rw [show u i = (t*w i) • v i from rfl,
      median_nonneg_smul r (v i) (mul_nonneg ht (hw i)),
      median_binary_majority r (v i) (hv i) (hvs i), mul_one]
  have hsum0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu0 i)
  have hbound := aggregation_finset_bound (median_aggregation_axioms r)
    Finset.univ u (fun i _ => hu0 i)
  have he : (∑ i, scalarMedian r (u i)) = t := by
    simp only [hm, ← Finset.mul_sum, hws, mul_one]
  rw [he] at hbound
  exact hbound.trans (superadditiveTransform_mono (median_aggregation_axioms r)
    hsum0 (by rw [hu]; exact hba))

/-- The truncation capacity is sufficient for the lower bound; equality or
attainment of a minimizing cut is not an additional hypothesis. -/
theorem median_transform_lower_of_capacity (r : ℕ) {a : Fin (2*r+1) → ℝ}
    (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t)
    (hcap : ((r+1 : ℕ) : ℝ)*t ≤ ∑ i, min (a i) t) :
    t ≤ superadditiveTransform (scalarMedian r) a := by
  rcases ht.eq_or_lt with hzero | htpos
  · rw [← hzero]
    exact superadditiveTransform_nonneg (median_aggregation_axioms r) ha
  let c : ℝ := ∑ i, min (a i) t
  have hk : (0 : ℝ) < ((r+1 : ℕ) : ℝ) := by positivity
  have hc : 0 < c := lt_of_lt_of_le (mul_pos hk htpos) hcap
  let b : Fin (2*r+1) → ℝ := fun i => ((r+1 : ℕ) : ℝ) * min (a i) t / c
  have hb0 : 0 ≤ b := fun i => div_nonneg
    (mul_nonneg hk.le (le_min (ha i) ht)) hc.le
  have hb1 : b ≤ 1 := by
    intro i
    apply (div_le_one hc).mpr
    exact (mul_le_mul_of_nonneg_left (min_le_right (a i) t) hk.le).trans hcap
  have hbs : (∑ i, b i) = ((r+1 : ℕ) : ℝ) := by
    simp only [b, ← Finset.sum_div, ← Finset.mul_sum]
    change ((r+1 : ℕ) : ℝ)*c/c = ((r+1 : ℕ) : ℝ)
    exact mul_div_cancel_right₀ _ hc.ne'
  apply median_transform_ge_hypersimplex r (b := b) ⟨⟨hb0, hb1⟩, hbs⟩ ht
  intro i
  change t * (((r+1 : ℕ) : ℝ) * min (a i) t / c) ≤ a i
  have hcoef : t * ((r+1 : ℕ) : ℝ) / c ≤ 1 :=
    (div_le_one hc).mpr (by simpa [mul_comm] using hcap)
  calc
    _ = (t * ((r+1 : ℕ) : ℝ) / c) * min (a i) t := by ring
    _ ≤ 1 * min (a i) t := mul_le_mul_of_nonneg_right hcoef (le_min (ha i) ht)
    _ ≤ a i := by simpa using min_le_left (a i) t

/-- The displayed finite minimum, using an arbitrary sorting permutation. -/
theorem median_transform_ordered_coordinates (r : ℕ) (a : Fin (2*r+1) → ℝ)
    (ha : 0 ≤ a) (σ : Equiv.Perm (Fin (2*r+1))) (hσ : Monotone (a ∘ σ)) :
    superadditiveTransform (scalarMedian r) a =
      ⨅ ℓ : Fin (r+1),
        (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
          a (σ i)) / ((ℓ.val+1 : ℕ) : ℝ) := by
  classical
  let R : Fin (r+1) → ℝ := fun ℓ =>
    (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
      a (σ i)) / ((ℓ.val+1 : ℕ) : ℝ)
  let t : ℝ := ⨅ ℓ, R ℓ
  have ht : 0 ≤ t := le_ciInf (fun ℓ => div_nonneg
    (Finset.sum_nonneg (fun i _ => ha (σ i))) (by positivity))
  apply le_antisymm
  · apply le_ciInf
    intro ℓ
    let P := Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1))
    have hmn : r+(ℓ.val+1) ≤ 2*r+1 := by omega
    have hcard : (P.map σ.toEmbedding).card = r+(ℓ.val+1) := by
      rw [Finset.card_map]
      exact prefix_filter_card hmn
    have hu := median_transform_subset_upper r (ℓ.val+1) (by omega)
      (P.map σ.toEmbedding) hcard ha
    simpa only [Finset.sum_map, Equiv.toEmbedding_apply] using hu
  · change t ≤ superadditiveTransform (scalarMedian r) a
    apply median_transform_lower_of_capacity r ha ht
    apply odd_median_truncation_capacity r a ha ht
    intro I hI
    have hcardn : I.card ≤ 2*r+1 := by
      simpa using Finset.card_le_card (Finset.subset_univ I)
    let ℓ : Fin (r+1) := ⟨I.card-r-1, by omega⟩
    have he : ℓ.val+1 = I.card-r := by dsimp [ℓ]; omega
    have hcard : r+(ℓ.val+1) = I.card := by omega
    have hmn : r+(ℓ.val+1) ≤ 2*r+1 := by omega
    let K := I.map σ.symm.toEmbedding
    have hK : K.card = r+(ℓ.val+1) := by simp [K, hcard]
    have hpre := monotone_prefix_sum_le_subset hmn (a ∘ σ) hσ K hK
    have hKsum : (∑ i ∈ K, (a ∘ σ) i) = ∑ i ∈ I, a i := by
      simp [K, Function.comp_def]
    rw [hKsum] at hpre
    have htR : t ≤ R ℓ := ciInf_le (finite_range R).bddBelow ℓ
    have hd : (0 : ℝ) < ((ℓ.val+1 : ℕ) : ℝ) := by positivity
    have hp := (le_div_iff₀ hd).mp htR
    rw [← he]
    change ((ℓ.val+1 : ℕ) : ℝ)*t ≤ ∑ i ∈ I, a i
    simpa only [Function.comp_apply, mul_comm] using hp.trans hpre

/-- The complete arbitrary-odd-arity formula, with the sorting permutation
constructed rather than imposed as an additional hypothesis. Fin (r+1)
indexes the manuscript's integers 1,...,r+1 by ℓ ↦ ℓ.val+1. -/
theorem median_transform_formula (r : ℕ) (a : Fin (2*r+1) → ℝ) (ha : 0 ≤ a) :
    superadditiveTransform (scalarMedian r) a =
      ⨅ ℓ : Fin (r+1),
        (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
          a (Tuple.sort a i)) / ((ℓ.val+1 : ℕ) : ℝ) :=
  median_transform_ordered_coordinates r a ha (Tuple.sort a) (Tuple.monotone_sort a)

/-- The exact truncation identity used in the lower-bound proof, at the
specific finite minimum appearing in the manuscript. -/
theorem median_transform_truncation_identity (r : ℕ) (a : Fin (2*r+1) → ℝ)
    (ha : 0 ≤ a) (σ : Equiv.Perm (Fin (2*r+1))) (hσ : Monotone (a ∘ σ)) :
    let t : ℝ := ⨅ ℓ : Fin (r+1),
      (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
        a (σ i)) / ((ℓ.val+1 : ℕ) : ℝ)
    (∑ i, min (a i) t) = ((r+1 : ℕ) : ℝ)*t := by
  classical
  let R : Fin (r+1) → ℝ := fun ℓ =>
    (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
      a (σ i)) / ((ℓ.val+1 : ℕ) : ℝ)
  let t : ℝ := ⨅ ℓ, R ℓ
  change (∑ i, min (a i) t) = ((r+1 : ℕ) : ℝ)*t
  have hvalue : t = superadditiveTransform (scalarMedian r) a :=
    (median_transform_ordered_coordinates r a ha σ hσ).symm
  have ht : 0 ≤ t := by
    rw [hvalue]
    exact superadditiveTransform_nonneg (median_aggregation_axioms r) ha
  have hge : ((r+1 : ℕ) : ℝ)*t ≤ ∑ i, min (a i) t := by
    apply odd_median_truncation_capacity r a ha ht
    intro I hI
    have hu := median_transform_subset_upper r (I.card-r) (by omega)
      I (by omega) ha
    rw [← hvalue] at hu
    have hd : (0 : ℝ) < ((I.card-r : ℕ) : ℝ) := by exact_mod_cast (show 0 < I.card-r by omega)
    simpa [mul_comm] using (le_div_iff₀ hd).mp hu
  obtain ⟨ℓ, _, hmin⟩ := Finset.exists_min_image Finset.univ R Finset.univ_nonempty
  have hRt : R ℓ = t := le_antisymm
    (le_ciInf (fun j => hmin j (Finset.mem_univ j)))
    (ciInf_le (finite_range R).bddBelow ℓ)
  let P := Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1))
  let J := P.map σ.toEmbedding
  have hJ : J.card = r+(ℓ.val+1) := by
    rw [Finset.card_map]
    exact prefix_filter_card (by omega)
  have hd : (0 : ℝ) < ((ℓ.val+1 : ℕ) : ℝ) := by positivity
  have hsum : (∑ i ∈ J, a i) = ((ℓ.val+1 : ℕ) : ℝ)*t := by
    have he := (div_eq_iff hd.ne').mp hRt
    simpa only [J, Finset.sum_map, Equiv.toEmbedding_apply, mul_comm] using he
  have hu := truncation_sum_upper_cut a t J
  have hc : ((2*r+1 : ℕ) : ℝ)-(J.card : ℝ) =
      ((r+1 : ℕ) : ℝ)-((ℓ.val+1 : ℕ) : ℝ) := by
    rw [hJ]
    push_cast
    ring
  rw [hsum, hc] at hu
  exact le_antisymm (by nlinarith) hge


end ScalarMonotone.EndOfPaper
end
