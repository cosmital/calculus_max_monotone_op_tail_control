import MonotoneOperators.Cubic

/-!
# Positive monomial changes of variable

The positive-root profiles used in the cubic identity are themselves maximal.
Their fiber at zero is inherited from the original positive completion.
-/

namespace ScalarMonotone

open Set

noncomputable def monomialExtension (σ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then σ * x else σ * x ^ n

theorem monomialExtension_eq {σ x : ℝ} {n : ℕ} (hx : 0 ≤ x) :
    monomialExtension σ n x = σ * x ^ n := by
  simp only [monomialExtension, if_neg (not_lt.mpr hx)]

theorem monomialExtension_strictMono {σ : ℝ} {n : ℕ}
    (hσ : 0 < σ) (hn : n ≠ 0) : StrictMono (monomialExtension σ n) := by
  intro x y hxy
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · simpa only [monomialExtension, if_pos hx, if_pos hy] using
        mul_lt_mul_of_pos_left hxy hσ
    · rw [monomialExtension, if_pos hx, monomialExtension, if_neg hy]
      exact (mul_neg_of_pos_of_neg hσ hx).trans_le
        (mul_nonneg hσ.le (pow_nonneg (le_of_not_gt hy) n))
  · have hy : ¬ y < 0 := not_lt.mpr ((le_of_not_gt hx).trans hxy.le)
    simp only [monomialExtension, if_neg hx, if_neg hy]
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy (le_of_not_gt hx) hn) hσ

theorem monomialExtension_surjective {σ : ℝ} {n : ℕ}
    (hσ : 0 < σ) (hn : n ≠ 0) : Function.Surjective (monomialExtension σ n) := by
  intro t
  by_cases ht : t < 0
  · refine ⟨t / σ, ?_⟩
    have hx : t / σ < 0 := div_neg_of_neg_of_pos ht hσ
    simp only [monomialExtension, if_pos hx]
    field_simp
  · let x := (t / σ) ^ ((n : ℝ)⁻¹)
    have ht₀ : 0 ≤ t / σ := div_nonneg (le_of_not_gt ht) hσ.le
    have hx : 0 ≤ x := Real.rpow_nonneg ht₀ _
    refine ⟨x, ?_⟩
    rw [monomialExtension_eq hx]
    dsimp only [x]
    rw [Real.rpow_inv_natCast_pow ht₀ hn]
    field_simp

/-- Every positive-degree, positive-scale root profile is the maximal
completion on the transformed nonnegative domain. -/
theorem monomialProfile_maximal {α : Operator} (hα : MaximalDecreasing α)
    (hα₀ : dom α ⊆ Ici 0) {σ : ℝ} {n : ℕ} (hσ : 0 < σ) (hn : n ≠ 0) :
    MaximalDecreasing (monomialProfile α σ n) := by
  have heq : monomialProfile α σ n = inputChange (monomialExtension σ n) α := by
    ext t u
    constructor
    · rintro ⟨r, hr, ht⟩
      exact ⟨r, hr, ht.trans (monomialExtension_eq (hα₀ ⟨u, hr⟩)).symm⟩
    · rintro ⟨r, hr, ht⟩
      exact ⟨r, hr, ht.trans (monomialExtension_eq (hα₀ ⟨u, hr⟩))⟩
  rw [heq]
  exact inputChange_maximal_decreasing (monomialExtension_strictMono hσ hn)
    (monomialExtension_surjective hσ hn) hα

theorem monomialProfile_zero (α : Operator) {σ : ℝ} {n : ℕ}
    (hσ : σ ≠ 0) (hn : n ≠ 0) : monomialProfile α σ n 0 = α 0 := by
  ext u
  constructor
  · rintro ⟨r, hr, ht⟩
    have hp : r ^ n = 0 := (mul_eq_zero.mp ht.symm).resolve_left hσ
    have hr₀ : r = 0 := pow_eq_zero hp
    simpa only [hr₀] using hr
  · intro hu
    exact ⟨0, hu, by simp [zero_pow hn]⟩

theorem monomialProfile_neg {α : Operator} (hα₀ : dom α ⊆ Ici 0)
    {σ t : ℝ} {n : ℕ} (hσ : 0 ≤ σ) (ht : t < 0) :
    monomialProfile α σ n t = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro u ⟨r, hr, htpoly⟩
  have hp : 0 ≤ σ * r ^ n := mul_nonneg hσ (pow_nonneg (hα₀ ⟨u, hr⟩) n)
  exact (not_le_of_gt ht) (htpoly ▸ hp)

end ScalarMonotone
