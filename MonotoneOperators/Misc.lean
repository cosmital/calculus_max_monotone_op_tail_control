import MonotoneOperators.Interface

/-!
# Two explanatory facts

The zero-range logarithm is empty. On the real line, firm nonexpansiveness
is precisely monotonicity together with the one-Lipschitz property.
-/

open Set

namespace ScalarMonotone

variable {f : Operator}

def emptyOperator : Operator := fun _ => ∅

@[simp] theorem graph_emptyOperator : graph emptyOperator = ∅ := by
  ext p
  rfl

@[simp] theorem negOut_emptyOperator : negOut emptyOperator = emptyOperator := rfl

theorem emptyOperator_not_maximalIncreasing : ¬ MaximalIncreasing emptyOperator := by
  intro h
  obtain ⟨x, u, hu⟩ := maximal_nonempty h
  exact hu

theorem emptyOperator_not_maximalDecreasing : ¬ MaximalDecreasing emptyOperator :=
  emptyOperator_not_maximalIncreasing

/-- This implication needs no monotonicity assumption on the original operator. -/
theorem logOp_eq_empty_of_zero_range (hr : ran f = {0}) : logOp f = emptyOperator := by
  funext x
  apply Set.eq_empty_iff_forall_not_mem.2
  rintro t ⟨u, hu, hpos, _⟩
  have hu0 : u = 0 := by
    have h : u ∈ ran f := ⟨x, hu⟩
    simpa [hr] using h
  linarith

theorem graph_logOp_eq_empty_of_zero_range (hr : ran f = {0}) : graph (logOp f) = ∅ := by
  rw [logOp_eq_empty_of_zero_range hr, graph_emptyOperator]

theorem logOp_not_maximalIncreasing_of_zero_range (hr : ran f = {0}) :
    ¬ MaximalIncreasing (logOp f) := by
  rw [logOp_eq_empty_of_zero_range hr]
  exact emptyOperator_not_maximalIncreasing

theorem logOp_not_maximalDecreasing_of_zero_range (hr : ran f = {0}) :
    ¬ MaximalDecreasing (logOp f) := by
  rw [logOp_eq_empty_of_zero_range hr]
  exact emptyOperator_not_maximalDecreasing

/-- Firm nonexpansiveness on the real line is monotonicity plus one-Lipschitz continuity. -/
theorem firmly_nonexpansive_iff_monotone_lipschitz (J : ℝ → ℝ) :
    (∀ x y, (J x - J y) ^ 2 ≤ (J x - J y) * (x - y)) ↔
      Monotone J ∧ LipschitzWith 1 J := by
  constructor
  · intro hfirm
    have hmono : Monotone J := by
      intro x y hxy
      by_contra hn
      have hyx : J y < J x := lt_of_not_ge hn
      have hprod : (J x - J y) * (x - y) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hyx.le) (sub_nonpos.mpr hxy)
      have hsquare : (J x - J y) ^ 2 = 0 :=
        le_antisymm ((hfirm x y).trans hprod) (sq_nonneg (J x - J y))
      have heq : J x = J y := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
      exact (ne_of_gt hyx) heq
    have hslope : ∀ ⦃x y : ℝ⦄, x ≤ y → J y - J x ≤ y - x := by
      intro x y hxy
      by_contra hn
      have hlt : y - x < J y - J x := lt_of_not_ge hn
      have hpos : 0 < J y - J x := (sub_nonneg.mpr hxy).trans_lt hlt
      have hbad := mul_pos hpos (sub_pos.mpr hlt)
      have h := hfirm y x
      nlinarith
    refine ⟨hmono, LipschitzWith.mk_one ?_⟩
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr (hmono hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
      have h := hslope hxy
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hyx)), abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact hslope hyx
  · rintro ⟨hmono, hlip⟩ x y
    have hd := hlip.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
    rw [pow_two]
    rcases le_total x y with hxy | hyx
    · have hJ : J x ≤ J y := hmono hxy
      rw [abs_of_nonpos (sub_nonpos.mpr hJ), abs_of_nonpos (sub_nonpos.mpr hxy)] at hd
      exact mul_le_mul_of_nonpos_left (by linarith : x - y ≤ J x - J y)
        (sub_nonpos.mpr hJ)
    · have hJ : J y ≤ J x := hmono hyx
      rw [abs_of_nonneg (sub_nonneg.mpr hJ), abs_of_nonneg (sub_nonneg.mpr hyx)] at hd
      exact mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hJ)

end ScalarMonotone
