import Mathlib.Tactic

/-!
Truncation capacities, cut constraints and sorted-prefix sum comparison.
These ingredients do not alone assert the final odd-median transform formula.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem truncation_cut_sum {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    (I : Finset (Fin n)) :
    (∑ i, ((if i ∈ I then a i-t else 0) + t)) =
      (∑ i ∈ I, a i) + ((n : ℝ)-(I.card : ℝ))*t := by
  classical
  have hfilter : (∑ i, if i ∈ I then a i-t else 0) = ∑ i ∈ I, (a i-t) := by
    have hset : Finset.univ.filter (fun i => i ∈ I) = I := by ext i; simp
    rw [← Finset.sum_filter, hset]
  rw [Finset.sum_add_distrib, hfilter, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem truncation_sum_upper_cut {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    (I : Finset (Fin n)) :
    (∑ i, min (a i) t) ≤ (∑ i ∈ I, a i) + ((n : ℝ)-(I.card : ℝ))*t := by
  classical
  rw [← truncation_cut_sum a t I]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ I
  · simpa only [if_pos hi, sub_add_cancel] using min_le_left (a i) t
  · simpa only [if_neg hi, zero_add] using min_le_right (a i) t

theorem truncation_sum_eq_cut {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    (∑ i, min (a i) t) =
      (∑ i ∈ Finset.univ.filter (fun i => a i ≤ t), a i) +
        ((n : ℝ)-((Finset.univ.filter (fun i => a i ≤ t)).card : ℝ))*t := by
  classical
  rw [← truncation_cut_sum a t (Finset.univ.filter (fun i => a i ≤ t))]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a i ≤ t
  · simp [hi, min_eq_left hi]
  · simp [hi, min_eq_right (le_of_not_ge hi)]

/-- The finite capacity criterion; it does not require positivity assumptions. -/
theorem truncation_sum_ge_iff_cuts {n : ℕ} (a : Fin n → ℝ) (t k : ℝ) :
    k*t ≤ ∑ i, min (a i) t ↔
      ∀ I : Finset (Fin n), (k+(I.card : ℝ)-(n : ℝ))*t ≤ ∑ i ∈ I, a i := by
  classical
  constructor
  · intro h I
    have hI := truncation_sum_upper_cut a t I
    nlinarith
  · intro h
    let I := Finset.univ.filter (fun i => a i ≤ t)
    have hI := h I
    have he := truncation_sum_eq_cut a t
    change (∑ i, min (a i) t) = (∑ i ∈ I, a i) + ((n : ℝ)-(I.card : ℝ))*t at he
    nlinarith

/-- An attained cut bound makes the capacity constraint an exact equality. -/
theorem truncation_sum_eq_of_attained_cut {n : ℕ} (a : Fin n → ℝ) (t k : ℝ)
    (h : ∀ I : Finset (Fin n), (k+(I.card : ℝ)-(n : ℝ))*t ≤ ∑ i ∈ I, a i)
    (I : Finset (Fin n)) (he : (∑ i ∈ I, a i) = (k+(I.card : ℝ)-(n : ℝ))*t) :
    (∑ i, min (a i) t) = k*t := by
  have hlo := (truncation_sum_ge_iff_cuts a t k).mpr h
  have hhi := truncation_sum_upper_cut a t I
  nlinarith

theorem odd_median_truncation_capacity (r : ℕ) (a : Fin (2*r+1) → ℝ)
    (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ I : Finset (Fin (2*r+1)), r < I.card →
      ((I.card-r : ℕ) : ℝ)*t ≤ ∑ i ∈ I, a i) :
    ((r+1 : ℕ) : ℝ)*t ≤ ∑ i, min (a i) t := by
  classical
  apply (truncation_sum_ge_iff_cuts a t ((r+1 : ℕ) : ℝ)).mpr
  intro I
  have hnonneg : 0 ≤ ∑ i ∈ I, a i := Finset.sum_nonneg (fun i _ => ha i)
  by_cases hI : r < I.card
  · have hi := h I hI
    rw [Nat.cast_sub (Nat.le_of_lt hI)] at hi
    push_cast at hi ⊢
    nlinarith
  · have hi : (I.card : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.le_of_not_gt hI
    push_cast
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi) ht]

theorem prefix_filter_card {n m : ℕ} (hmn : m ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < m)).card = m := by
  classical
  let e : Fin m ↪ Fin n := ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩,
    fun _ _ h => Fin.ext (congrArg (fun k : Fin n => k.val) h)⟩
  have he : Finset.univ.filter (fun i : Fin n => i.val < m) = Finset.univ.map e := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_map.mpr ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩,
        Finset.mem_univ _, Fin.ext rfl⟩
    · intro hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  rw [he]
  simp

/-- A sorted prefix minimizes the sum over subsets of the same cardinality.
This is the explicit bridge needed to replace all subset bounds by the
ordered-coordinate expression in the manuscript. -/
theorem monotone_prefix_sum_le_subset {n m : ℕ} (hmn : m ≤ n)
    (a : Fin n → ℝ) (ha : Monotone a) (I : Finset (Fin n)) (hcard : I.card = m) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), a i) ≤ ∑ i ∈ I, a i := by
  classical
  by_cases hm : m = 0
  · have hI : I = ∅ := Finset.card_eq_zero.mp (hcard.trans hm)
    simp [hm, hI]
  let j : Fin n := ⟨m-1, by omega⟩
  let P := Finset.univ.filter (fun i : Fin n => i.val < m)
  have hPcard : P.card = m := prefix_filter_card hmn
  have hmin : (∑ i, min (a i-a j) 0) = ∑ i ∈ P, (a i-a j) := by
    calc
      _ = ∑ i, if i ∈ P then a i-a j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.val < m
        · have hij : i ≤ j := by change i.val ≤ m-1; omega
          simp [P, hi, min_eq_left (sub_nonpos.mpr (ha hij))]
        · have hji : j ≤ i := by change m-1 ≤ i.val; omega
          simp [P, hi, min_eq_right (sub_nonneg.mpr (ha hji))]
      _ = _ := by
        simpa only [sub_zero, add_zero, mul_zero] using
          (truncation_cut_sum (fun i => a i-a j) 0 P)
  have hpartial : (∑ i, min (a i-a j) 0) ≤ ∑ i ∈ I, min (a i-a j) 0 := by
    have hn := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (f := fun i => -min (a i-a j) 0)
      (fun i _ _ => neg_nonneg.mpr (min_le_right (a i-a j) 0))
    simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using hn
  have hcompare : (∑ i ∈ P, (a i-a j)) ≤ ∑ i ∈ I, (a i-a j) := by
    rw [← hmin]
    exact hpartial.trans (Finset.sum_le_sum (fun i _ => min_le_left (a i-a j) 0))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hcompare
  simp only [Finset.sum_const, nsmul_eq_mul, hPcard, hcard] at hcompare
  change (∑ i ∈ P, a i) ≤ ∑ i ∈ I, a i
  linarith

end ScalarMonotone.EndOfPaper
end
