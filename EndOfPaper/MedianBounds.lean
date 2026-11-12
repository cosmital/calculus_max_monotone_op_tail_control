import MonotoneOperators.Median
import EndOfPaper.Superadditive

/-!
# Scalar median bounds used by the final section

Source: the upper bound in `mediantransform`, and the deterministic inequality
preceding `tailmedianestimators`.

The reverse inequality in `mediantransform` needs a decomposition of the
hypersimplex. It is NOT replaced here by assuming that decomposition or the
formula as a hypothesis. See END_COVERAGE.md for the unfinished lower bound.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- A majority below b puts the median below b. -/
theorem median_le_of_majority (r : ℕ) (q : Fin (2*r+1) → ℝ) {b : ℝ}
    (h : ∃ I : Majority r, ∀ i ∈ I.val, q i ≤ b) : scalarMedian r q ≤ b := by
  obtain ⟨I, hI⟩ := h
  change latticeMedianInfSup r q ≤ b
  exact (ciInf_le (finite_range (fun J : Majority r =>
    ⨆ i : {i // i ∈ J.val}, q i.val)).bddBelow I).trans
      (ciSup_le (fun i : {i // i ∈ I.val} => hI i.val i.property))

/-- A majority above b puts the median above b. -/
theorem le_median_of_majority (r : ℕ) (q : Fin (2*r+1) → ℝ) {b : ℝ}
    (h : ∃ I : Majority r, ∀ i ∈ I.val, b ≤ q i) : b ≤ scalarMedian r q := by
  obtain ⟨I, hI⟩ := h
  change b ≤ latticeMedianInfSup r q
  rw [scalar_median_minmax_eq_maxmin]
  exact (le_ciInf (fun i : {i // i ∈ I.val} => hI i.val i.property)).trans
    (le_ciSup (finite_range (fun J : Majority r =>
      ⨅ i : {i // i ∈ J.val}, q i.val)).bddAbove I)

/-- A minimizing majority exists because the index family is finite. -/
theorem median_upper_majority (r : ℕ) (q : Fin (2*r+1) → ℝ) :
    ∃ I : Majority r, ∀ i ∈ I.val, q i ≤ scalarMedian r q := by
  classical
  let v : Majority r → ℝ := fun I => ⨆ i : {i // i ∈ I.val}, q i.val
  obtain ⟨I, _, hI⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have he : v I = scalarMedian r q := by
    apply le_antisymm
    · exact le_ciInf (fun J => hI J (Finset.mem_univ J))
    · exact ciInf_le (finite_range v).bddBelow I
  refine ⟨I, ?_⟩
  intro i hi
  rw [← he]
  exact le_ciSup (finite_range (fun j : {j // j ∈ I.val} => q j.val)).bddAbove ⟨i, hi⟩

/-- A maximizing majority exists for the dual representation. -/
theorem median_lower_majority (r : ℕ) (q : Fin (2*r+1) → ℝ) :
    ∃ I : Majority r, ∀ i ∈ I.val, scalarMedian r q ≤ q i := by
  classical
  let v : Majority r → ℝ := fun I => ⨅ i : {i // i ∈ I.val}, q i.val
  obtain ⟨I, _, hI⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  have he : v I = scalarMedian r q := by
    change v I = latticeMedianInfSup r q
    rw [scalar_median_minmax_eq_maxmin]
    apply le_antisymm
    · exact le_ciSup (finite_range v).bddAbove I
    · exact ciSup_le (fun J => hI J (Finset.mem_univ J))
  refine ⟨I, ?_⟩
  intro i hi
  rw [← he]
  exact ciInf_le (finite_range (fun j : {j // j ∈ I.val} => q j.val)).bddBelow ⟨i, hi⟩

theorem median_mono (r : ℕ) {x y : Fin (2*r+1) → ℝ} (h : x ≤ y) :
    scalarMedian r x ≤ scalarMedian r y := by
  obtain ⟨I, hI⟩ := median_upper_majority r y
  exact median_le_of_majority r x ⟨I, fun i hi => (h i).trans (hI i hi)⟩

theorem median_nonneg (r : ℕ) {x : Fin (2*r+1) → ℝ} (hx : 0 ≤ x) :
    0 ≤ scalarMedian r x := by
  let I : Majority r := Classical.choice (inferInstance : Nonempty (Majority r))
  exact le_median_of_majority r x ⟨I, fun i _ => hx i⟩

theorem median_const (r : ℕ) (c : ℝ) :
    scalarMedian r (fun _ => c) = c := by
  let I : Majority r := Classical.choice (inferInstance : Nonempty (Majority r))
  exact le_antisymm (median_le_of_majority r _ ⟨I, by simp⟩)
    (le_median_of_majority r _ ⟨I, by simp⟩)

theorem median_nonneg_smul (r : ℕ) (x : Fin (2*r+1) → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    scalarMedian r (c • x) = c * scalarMedian r x := by
  apply le_antisymm
  · obtain ⟨I, hI⟩ := median_upper_majority r x
    exact median_le_of_majority r (c • x)
      ⟨I, fun i hi => mul_le_mul_of_nonneg_left (hI i hi) hc⟩
  · obtain ⟨I, hI⟩ := median_lower_majority r x
    exact le_median_of_majority r (c • x)
      ⟨I, fun i hi => mul_le_mul_of_nonneg_left (hI i hi) hc⟩

theorem median_aggregation_axioms (r : ℕ) :
    AggregationAxioms (scalarMedian r) where
  nonneg := fun _ hx => median_nonneg r hx
  mono := fun _ hxy => median_mono r hxy
  homogeneous := fun c hc x _ => median_nonneg_smul r x hc

/-- Deterministic estimator-error domination; no distributional assumptions. -/
theorem median_error_domination (r : ℕ) (x : Fin (2*r+1) → ℝ) (θ : ℝ) :
    |scalarMedian r x-θ| ≤ scalarMedian r (fun i => |x i-θ|) := by
  obtain ⟨I, hI⟩ := median_upper_majority r (fun i => |x i-θ|)
  have hlo : θ-scalarMedian r (fun i => |x i-θ|) ≤ scalarMedian r x := by
    apply le_median_of_majority r x
    refine ⟨I, ?_⟩
    intro i hi
    have h := (abs_le.mp (hI i hi)).1
    linarith
  have hhi : scalarMedian r x ≤ θ+scalarMedian r (fun i => |x i-θ|) := by
    apply median_le_of_majority r x
    refine ⟨I, ?_⟩
    intro i hi
    have h := (abs_le.mp (hI i hi)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The combinatorial upper bound ell*M(x) <= sum_{i in I} x_i. -/
theorem median_subset_sum_bound (r ℓ : ℕ) (x : Fin (2*r+1) → ℝ)
    (hx : 0 ≤ x) (I : Finset (Fin (2*r+1))) (hI : I.card = r+ℓ) :
    (ℓ : ℝ) * scalarMedian r x ≤ ∑ i ∈ I, x i := by
  classical
  obtain ⟨J, hJ⟩ := median_lower_majority r x
  let K := I ∩ J.val
  have hcard : ℓ ≤ K.card := by
    have he := Finset.card_union_add_card_inter I J.val
    have hu : (I ∪ J.val).card ≤ 2*r+1 := by
      simpa using Finset.card_le_card (Finset.subset_univ (I ∪ J.val))
    have hj := J.property
    dsimp [K]
    omega
  have hm := median_nonneg r hx
  calc
    (ℓ : ℝ) * scalarMedian r x ≤ (K.card : ℝ) * scalarMedian r x :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hm
    _ = ∑ i ∈ K, scalarMedian r x := by simp
    _ ≤ ∑ i ∈ K, x i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hJ i (Finset.mem_inter.mp hi).2
    _ ≤ ∑ i ∈ I, x i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun i _ _ => hx i)

/-- The complete upper half of the formula for the median transform,
expressed for every subset rather than using sorted coordinates. -/
theorem median_transform_subset_upper (r ℓ : ℕ) (hℓ : 0 < ℓ)
    (I : Finset (Fin (2*r+1))) (hI : I.card = r+ℓ)
    {a : Fin (2*r+1) → ℝ} (ha : 0 ≤ a) :
    superadditiveTransform (scalarMedian r) a ≤ (∑ i ∈ I, a i)/(ℓ : ℝ) := by
  let G : (Fin (2*r+1) → ℝ) → ℝ := fun x => (∑ i ∈ I, x i)/(ℓ : ℝ)
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  apply superadditiveTransform_le_majorant (median_aggregation_axioms r) (G := G)
  · intro x hx
    exact (le_div_iff₀ hℓ').mpr (by
      simpa [mul_comm] using median_subset_sum_bound r ℓ x hx I hI)
  · intro x y hx hy
    dsimp [G]
    rw [Finset.sum_add_distrib, add_div]
  · exact ha

/-- The common-input coefficient in the upper bound. Its optimality is NOT
asserted by this theorem; the probability construction remains to be added. -/
theorem median_transform_common_upper (r : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    superadditiveTransform (scalarMedian r) (fun _ => b) ≤
      ((2*r+1 : ℕ) : ℝ)/(r+1 : ℕ) * b := by
  have h := median_transform_subset_upper r (r+1) (Nat.succ_pos r)
    Finset.univ (by simp; omega) (a := fun _ => b) (fun _ => hb)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_assoc, div_mul_eq_mul_div] using h

end ScalarMonotone.EndOfPaper

end -- noncomputable section
