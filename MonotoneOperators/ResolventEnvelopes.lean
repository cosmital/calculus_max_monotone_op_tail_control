import MonotoneOperators.Minty

/-!
# Bounded envelopes of scalar resolvents

Pointwise conditional suprema and infima preserve monotonicity and the common
Lipschitz constant.  These lemmas supply the analytic part of conditional
completeness, without any restriction on the cardinality of the family.
-/

namespace ScalarMonotone

open Set

variable {ι : Type*} {q : ι → ℝ → ℝ}

theorem monotone_ciSup (hq : ∀ i, Monotone (q i))
    (hb : ∀ x, BddAbove (range (fun i => q i x))) :
    Monotone (fun x => ⨆ i, q i x) := by
  intro x y hxy
  exact ciSup_mono (hb y) (fun i => hq i hxy)

theorem monotone_ciInf (hq : ∀ i, Monotone (q i))
    (hb : ∀ x, BddBelow (range (fun i => q i x))) :
    Monotone (fun x => ⨅ i, q i x) := by
  intro x y hxy
  exact ciInf_mono (hb x) (fun i => hq i hxy)

theorem lipschitz_ciSup [Nonempty ι] (hq : ∀ i, LipschitzWith 1 (q i))
    (hb : ∀ x, BddAbove (range (fun i => q i x))) :
    LipschitzWith 1 (fun x => ⨆ i, q i x) := by
  have hle : ∀ x y, (⨆ i, q i x) ≤ (⨆ i, q i y) + dist x y := by
    intro x y
    apply ciSup_le
    intro i
    have hd := (hq i).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
    have hle := le_ciSup (hb y) i
    have hd' := (abs_le.mp hd).2
    rw [Real.dist_eq]
    linarith
  apply LipschitzWith.mk_one
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hle y x
    rw [dist_comm y x] at h
    linarith
  · have h := hle x y
    linarith

theorem lipschitz_ciInf [Nonempty ι] (hq : ∀ i, LipschitzWith 1 (q i))
    (hb : ∀ x, BddBelow (range (fun i => q i x))) :
    LipschitzWith 1 (fun x => ⨅ i, q i x) := by
  have hle : ∀ x y, (⨅ i, q i x) ≤ (⨅ i, q i y) + dist x y := by
    intro x y
    have h : (⨅ i, q i x) - dist x y ≤ ⨅ i, q i y := by
      apply le_ciInf
      intro i
      have hd := (hq i).dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
      have hle := ciInf_le (hb x) i
      have hd' := (abs_le.mp hd).2
      rw [Real.dist_eq]
      linarith
    linarith
  apply LipschitzWith.mk_one
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hle y x
    rw [dist_comm y x] at h
    linarith
  · have h := hle x y
    linarith

/-- With a common Lipschitz constant, boundedness at one point propagates
to every point. -/
theorem boundedAbove_everywhere_of_one_point
    (hq : ∀ i, LipschitzWith 1 (q i)) {x₀ : ℝ}
    (hb : BddAbove (range (fun i => q i x₀))) (x : ℝ) :
    BddAbove (range (fun i => q i x)) := by
  rcases hb with ⟨M, hM⟩
  refine ⟨M + dist x x₀, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hM (mem_range_self i)
  have hd := (hq i).dist_le_mul x x₀
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
  rw [Real.dist_eq]
  have hd' := (abs_le.mp hd).2
  linarith

theorem boundedBelow_everywhere_of_one_point
    (hq : ∀ i, LipschitzWith 1 (q i)) {x₀ : ℝ}
    (hb : BddBelow (range (fun i => q i x₀))) (x : ℝ) :
    BddBelow (range (fun i => q i x)) := by
  rcases hb with ⟨M, hM⟩
  refine ⟨M - dist x x₀, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hM (mem_range_self i)
  have hd := (hq i).dist_le_mul x x₀
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
  rw [Real.dist_eq]
  have hd' := (abs_le.mp hd).1
  linarith

theorem finite_exists_min [Finite ι] [Nonempty ι] (a : ι → ℝ) :
    ∃ i, ∀ j, a i ≤ a j := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := a)
  exact ⟨i, fun j => hi ▸ ciInf_le (finite_range a).bddBelow j⟩

theorem finite_exists_max [Finite ι] [Nonempty ι] (a : ι → ℝ) :
    ∃ i, ∀ j, a j ≤ a i := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  exact ⟨i, fun j => hi ▸ le_ciSup (finite_range a).bddAbove j⟩

end ScalarMonotone
