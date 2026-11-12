import MonotoneOperators.Interface

/-!
# Finite common-level probability bounds

All random variables may live on the same probability space. No independence
hypothesis occurs. `TailBound` exposes the strict-tail test before its
identification with the pointwise resolvent order.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace ScalarMonotone

/-- A strict-tail bound tested at every point of a comparison graph. -/
def TailBound {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (X : Ω → ℝ) (α : Operator) : Prop :=
  ∀ ⦃t u : ℝ⦄, u ∈ α t → ν.real {ω | t < X ω} ≤ u

/-- The sum of a finite family of fibers. -/
def finiteSum {ι : Type*} [Fintype ι] (f : ι → Operator) : Operator :=
  fun x => {t | ∃ q : ι → ℝ, (∀ i, q i ∈ f i x) ∧ t = ∑ i, q i}

/-- The product of a finite family of fibers. -/
def finiteProduct {ι : Type*} [Fintype ι] (f : ι → Operator) : Operator :=
  fun x => {t | ∃ q : ι → ℝ, (∀ i, q i ∈ f i x) ∧ t = ∏ i, q i}

/-- An arbitrary finite parallel sum, with a common probability-level witness. -/
def finiteParallelAdd {ι : Type*} [Fintype ι] (f : ι → Operator) : Operator :=
  inverse (finiteSum fun i => inverse (f i))

/-- An arbitrary finite parallel product. -/
def finiteParallelMul {ι : Type*} [Fintype ι] (f : ι → Operator) : Operator :=
  inverse (finiteProduct fun i => inverse (f i))

private def partialSum {ι : Type*} (s : Finset ι) (f : ι → Operator) : Operator :=
  fun x => {t | ∃ q : ι → ℝ, (∀ i ∈ s, q i ∈ f i x) ∧ t = ∑ i ∈ s, q i}

private theorem partialSum_empty {ι : Type*} (f : ι → Operator) :
    partialSum ∅ f = ofFun (fun _ => 0) := by
  ext x t
  constructor
  · rintro ⟨q, _, ht⟩
    simpa [ofFun] using ht
  · intro ht
    refine ⟨fun _ => 0, by simp, ?_⟩
    simpa [ofFun] using ht

private theorem partialSum_insert {ι : Type*} [DecidableEq ι]
    (f : ι → Operator) (s : Finset ι) {a : ι} (ha : a ∉ s) :
    partialSum (insert a s) f = add (f a) (partialSum s f) := by
  ext x t
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q a, hq a (Finset.mem_insert_self _ _), ∑ i ∈ s, q i,
      ⟨q, fun i hi => hq i (Finset.mem_insert_of_mem hi), rfl⟩, ?_⟩
    exact Finset.sum_insert ha
  · rintro ⟨u, hu, v, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨Function.update q a u, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hu
      · have hia : i ≠ a := fun h => ha (h ▸ hi)
        simpa [Function.update_of_ne hia] using hq i hi
    · rw [Finset.sum_insert ha, Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp only [Function.update_of_ne hia]

/-- Finite sum maximality needs only one point in all the domains. -/
theorem finiteSum_maximal_decreasing {ι : Type*} [Fintype ι]
    (f : ι → Operator) (hf : ∀ i, MaximalDecreasing (f i))
    (hc : ∃ c, ∀ i, (f i c).Nonempty) :
    MaximalDecreasing (finiteSum f) := by
  classical
  obtain ⟨c, hc⟩ := hc
  choose q hq using hc
  have h : ∀ s : Finset ι, MaximalDecreasing (partialSum s f) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [partialSum_empty]
        exact (constant_maximal_both 0).2
    | @insert a s ha ih =>
        rw [partialSum_insert f s ha]
        exact add_maximal_decreasing (hf a) ih
          ⟨c, ⟨q a, hq a⟩, ⟨∑ i ∈ s, q i, q, fun i _ => hq i, rfl⟩⟩
  have heq : partialSum Finset.univ f = finiteSum f := by
    funext x
    ext t
    simp [partialSum, finiteSum]
  rw [← heq]
  exact h Finset.univ

/-- The manuscript's common-range condition makes every finite parallel sum maximal. -/
theorem finiteParallelAdd_maximal_decreasing {ι : Type*} [Fintype ι]
    (f : ι → Operator) (hf : ∀ i, MaximalDecreasing (f i))
    (hc : ∃ u, ∀ i, u ∈ ran (f i)) :
    MaximalDecreasing (finiteParallelAdd f) := by
  apply inverse_maximal_decreasing
  exact finiteSum_maximal_decreasing _ (fun i => inverse_maximal_decreasing (hf i)) hc

private theorem probability_mono_ae {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {s t : Set Ω}
    (h : s ≤ᵐ[ν] t) : ν.real s ≤ ν.real t :=
  ENNReal.toReal_mono (measure_ne_top ν t) (measure_mono_ae h)

/-- A finite union estimate at a common comparison level. -/
theorem finite_sum_tail_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (α : ι → Operator)
    (hX : ∀ i, TailBound ν (X i) (α i)) {t u : ℝ}
    (htu : u ∈ finiteParallelAdd α t) :
    ν.real {ω | t < ∑ i, X i ω} ≤ (Fintype.card ι : ℝ) * u := by
  classical
  rcases htu with ⟨r, hr, rfl⟩
  have hsub : {ω | ∑ i, r i < ∑ i, X i ω} ⊆ ⋃ i, {ω | r i < X i ω} := by
    intro ω hω
    simp only [mem_iUnion, mem_setOf_eq]
    by_contra h
    push_neg at h
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
    exact (not_lt_of_ge hle) hω
  calc
    ν.real {ω | ∑ i, r i < ∑ i, X i ω}
        ≤ ν.real (⋃ i, {ω | r i < X i ω}) := measureReal_mono hsub
    _ ≤ ∑ i, ν.real {ω | r i < X i ω} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, u := Finset.sum_le_sum (fun i _ => hX i (hr i))
    _ = (Fintype.card ι : ℝ) * u := by simp

/-- The product estimate allows almost-sure nonnegativity and requires no independence. -/
theorem finite_product_tail_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (α : ι → Operator)
    (hX : ∀ i, TailBound ν (X i) (α i))
    (hnonneg : ∀ i, ∀ᵐ ω ∂ν, 0 ≤ X i ω) {t u : ℝ}
    (htu : u ∈ finiteParallelMul α t) :
    ν.real {ω | t < ∏ i, X i ω} ≤ (Fintype.card ι : ℝ) * u := by
  classical
  rcases htu with ⟨r, hr, rfl⟩
  have hsub : ({ω | ∏ i, r i < ∏ i, X i ω} : Set Ω) ≤ᵐ[ν]
      (⋃ i, {ω | r i < X i ω} : Set Ω) := by
    filter_upwards [ae_all_iff.2 hnonneg] with ω hω
    intro hprod
    change ω ∈ ⋃ i, {ω | r i < X i ω}
    simp only [mem_iUnion, mem_setOf_eq]
    by_contra h
    push_neg at h
    have hle := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => hω i) (fun i _ => h i)
    exact (not_lt_of_ge hle) hprod
  calc
    ν.real {ω | ∏ i, r i < ∏ i, X i ω}
        ≤ ν.real (⋃ i, {ω | r i < X i ω}) := probability_mono_ae ν hsub
    _ ≤ ∑ i, ν.real {ω | r i < X i ω} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, u := Finset.sum_le_sum (fun i _ => hX i (hr i))
    _ = (Fintype.card ι : ℝ) * u := by simp

/-- A two-event bound for any increasing deterministic error estimate. -/
theorem two_event_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {A B Z : Ω → ℝ} {α β : Operator}
    (hA : TailBound ν A α) (hB : TailBound ν B β)
    {r s t u : ℝ} (hr : u ∈ α r) (hs : u ∈ β s)
    (hgood : ∀ᵐ ω ∂ν, A ω ≤ r → B ω ≤ s → Z ω ≤ t) :
    ν.real {ω | t < Z ω} ≤ 2 * u := by
  have hsub : ({ω | t < Z ω} : Set Ω) ≤ᵐ[ν]
      ({ω | r < A ω} ∪ {ω | s < B ω} : Set Ω) := by
    filter_upwards [hgood] with ω hω
    intro ht
    by_contra h
    have hA' : A ω ≤ r := le_of_not_gt (fun hA' => h (Or.inl hA'))
    have hB' : B ω ≤ s := le_of_not_gt (fun hB' => h (Or.inr hB'))
    exact (not_lt_of_ge (hω hA' hB')) ht
  calc
    ν.real {ω | t < Z ω}
        ≤ ν.real ({ω | r < A ω} ∪ {ω | s < B ω}) := probability_mono_ae ν hsub
    _ ≤ ν.real {ω | r < A ω} + ν.real {ω | s < B ω} := measureReal_union_le _ _
    _ ≤ 2 * u := by linarith [hA hr, hB hs]

/-- The scalar centered sum estimate underlying the two-event corollary. -/
theorem centered_sum_pointwise (x y c d r s : ℝ)
    (hx : |x - c| ≤ r) (hy : |y - d| ≤ s) :
    |x + y - c - d| ≤ r + s := by
  calc
    |x + y - c - d| = |(x - c) + (y - d)| := by congr 1; ring
    _ ≤ |x - c| + |y - d| := abs_add _ _
    _ ≤ r + s := add_le_add hx hy

/-- The scalar centered product estimate, including zero pivots. -/
theorem centered_product_pointwise (x y c d r s : ℝ)
    (hx : |x - c| ≤ r) (hy : |y - d| ≤ s) :
    |x * y - c * d| ≤ r * s + |d| * r + |c| * s := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hx
  have hs : 0 ≤ s := (abs_nonneg _).trans hy
  calc
    |x * y - c * d| = |(x - c) * (y - d) + d * (x - c) + c * (y - d)| := by
      congr 1; ring
    _ ≤ |(x - c) * (y - d) + d * (x - c)| + |c * (y - d)| := abs_add _ _
    _ ≤ (|(x - c) * (y - d)| + |d * (x - c)|) + |c * (y - d)| := by
      exact add_le_add_right (abs_add _ _) _
    _ = |x - c| * |y - d| + |d| * |x - c| + |c| * |y - d| := by
      simp only [abs_mul]
    _ ≤ r * s + |d| * r + |c| * s := by gcongr

/-- Centering introduces no extra union-bound factor. -/
theorem centered_sum_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X Y : Ω → ℝ}
    {c d : ℝ} {α β : Operator}
    (hX : TailBound ν (fun ω => |X ω - c|) α)
    (hY : TailBound ν (fun ω => |Y ω - d|) β)
    {t u : ℝ} (htu : u ∈ parallelAdd α β t) :
    ν.real {ω | t < |X ω + Y ω - c - d|} ≤ 2 * u := by
  rcases htu with ⟨r, hr, s, hs, rfl⟩
  apply two_event_tail_bound ν hX hY hr hs
  filter_upwards [] with ω
  exact centered_sum_pointwise _ _ _ _ _ _

end ScalarMonotone
