import MonotoneOperators.Products

/-!
# Decreasing products and parallel products

Input reflection transfers the ordinary-product theorems to the decreasing
orientation. Inversion then proves both parallel-product criteria.
-/

open Set

namespace ScalarMonotone

variable {f g : Operator}

@[simp] theorem dom_reflect (f : Operator) : dom (reflect f) = setNeg (dom f) := rfl

@[simp] theorem ran_reflect (f : Operator) : ran (reflect f) = ran f := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨-x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨-x, by simpa [reflect] using hx⟩

theorem Nonnegative.reflect (hf : Nonnegative f) : Nonnegative (reflect f) := by
  intro x u hu
  exact hf hu

theorem reflect_logOp (f : Operator) : reflect (logOp f) = logOp (reflect f) := rfl

theorem reflect_mul (f g : Operator) :
    reflect (mul f g) = mul (reflect f) (reflect g) := rfl

theorem setNeg_inter (A B : Set ℝ) : setNeg (A ∩ B) = setNeg A ∩ setNeg B := rfl

theorem logOp_decreasing (hf : Decreasing f) : Decreasing (logOp f) := by
  apply reflect_increasing_iff.1
  rw [reflect_logOp]
  exact logOp_increasing (reflect_increasing_iff.2 hf)

/-- The logarithm lemma in the decreasing orientation. -/
theorem logOp_maximal_decreasing (hf : MaximalDecreasing f) (hf₀ : Nonnegative f)
    (hpos : ∃ c ∈ ran f, 0 < c) : MaximalDecreasing (logOp f) := by
  apply reflect_maximal_iff.1
  rw [reflect_logOp]
  exact logOp_maximal (reflect_maximal_iff.2 hf) hf₀.reflect (by simpa using hpos)

theorem mul_decreasing (hf : Decreasing f) (hg : Decreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) : Decreasing (mul f g) := by
  apply reflect_increasing_iff.1
  rw [reflect_mul]
  exact (reflect_increasing_iff.2 hf).mul (reflect_increasing_iff.2 hg)
    hf₀.reflect hg₀.reflect

/-- The exact zero-degeneracy criterion in the decreasing orientation. -/
theorem mul_maximal_decreasing_iff (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) :
    MaximalDecreasing (mul f g) ↔ dom f ∩ dom g = univ ∨ ran (mul f g) ≠ {0} := by
  simpa only [← reflect_mul, reflect_maximal_iff, dom_reflect, ← setNeg_inter,
    setNeg_eq_univ_iff, ran_reflect] using
    mul_maximal_iff (reflect_maximal_iff.2 hf) (reflect_maximal_iff.2 hg)
      hf₀.reflect hg₀.reflect

theorem ran_mul_eq_decreasing (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) (hm : MaximalDecreasing (mul f g)) :
    ran (mul f g) = setMul (ran f) (ran g) := by
  have hm' : MaximalIncreasing (mul (reflect f) (reflect g)) := by
    rw [← reflect_mul]
    exact reflect_maximal_iff.2 hm
  simpa only [← reflect_mul, ran_reflect] using
    ran_mul_eq (reflect_maximal_iff.2 hf) (reflect_maximal_iff.2 hg)
      hf₀.reflect hg₀.reflect hm'

theorem nonnegative_inverse_iff : Nonnegative (inverse f) ↔ dom f ⊆ Ici 0 := by
  constructor
  · intro hf x hx
    obtain ⟨u, hu⟩ := hx
    exact hf (show x ∈ inverse f u from hu)
  · intro hf x u hu
    exact hf (show u ∈ dom f from ⟨x, hu⟩)

@[simp] theorem inverse_maximal_decreasing_iff :
    MaximalDecreasing (inverse f) ↔ MaximalDecreasing f :=
  ⟨fun h => inverse_maximal_decreasing h, inverse_maximal_decreasing⟩

theorem parallelMul_increasing (hf : Increasing f) (hg : Increasing g)
    (hf₀ : dom f ⊆ Ici 0) (hg₀ : dom g ⊆ Ici 0) : Increasing (parallelMul f g) := by
  exact inverse_increasing ((inverse_increasing hf).mul (inverse_increasing hg)
    (nonnegative_inverse_iff.2 hf₀) (nonnegative_inverse_iff.2 hg₀))

theorem parallelMul_decreasing (hf : Decreasing f) (hg : Decreasing g)
    (hf₀ : dom f ⊆ Ici 0) (hg₀ : dom g ⊆ Ici 0) : Decreasing (parallelMul f g) := by
  exact inverse_decreasing (mul_decreasing (inverse_decreasing hf) (inverse_decreasing hg)
    (nonnegative_inverse_iff.2 hf₀) (nonnegative_inverse_iff.2 hg₀))

/-- The exact parallel-product criterion for increasing graphs. -/
theorem parallelMul_maximal_iff (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : dom f ⊆ Ici 0) (hg₀ : dom g ⊆ Ici 0) :
    MaximalIncreasing (parallelMul f g) ↔
      ran f ∩ ran g = univ ∨ dom (parallelMul f g) ≠ {0} := by
  simpa only [parallelMul, inverse_maximal_iff, dom_inverse] using
    mul_maximal_iff (inverse_maximal hf) (inverse_maximal hg)
      (nonnegative_inverse_iff.2 hf₀) (nonnegative_inverse_iff.2 hg₀)

/-- The exact parallel-product criterion for decreasing graphs. -/
theorem parallelMul_maximal_decreasing_iff
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hf₀ : dom f ⊆ Ici 0) (hg₀ : dom g ⊆ Ici 0) :
    MaximalDecreasing (parallelMul f g) ↔
      ran f ∩ ran g = univ ∨ dom (parallelMul f g) ≠ {0} := by
  simpa only [parallelMul, inverse_maximal_decreasing_iff, dom_inverse] using
    mul_maximal_decreasing_iff (inverse_maximal_decreasing hf) (inverse_maximal_decreasing hg)
      (nonnegative_inverse_iff.2 hf₀) (nonnegative_inverse_iff.2 hg₀)

theorem dom_parallelMul_eq (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hf₀ : dom f ⊆ Ici 0) (hg₀ : dom g ⊆ Ici 0) (hm : MaximalIncreasing (parallelMul f g)) :
    dom (parallelMul f g) = setMul (dom f) (dom g) := by
  change ran (mul (inverse f) (inverse g)) = setMul (dom f) (dom g)
  have hm' : MaximalIncreasing (mul (inverse f) (inverse g)) := inverse_maximal hm
  simpa only [ran_inverse] using
    ran_mul_eq (inverse_maximal hf) (inverse_maximal hg)
      (nonnegative_inverse_iff.2 hf₀) (nonnegative_inverse_iff.2 hg₀) hm'

theorem dom_parallelMul_eq_decreasing
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hf₀ : dom f ⊆ Ici 0) (hg₀ : dom g ⊆ Ici 0) (hm : MaximalDecreasing (parallelMul f g)) :
    dom (parallelMul f g) = setMul (dom f) (dom g) := by
  change ran (mul (inverse f) (inverse g)) = setMul (dom f) (dom g)
  have hm' : MaximalDecreasing (mul (inverse f) (inverse g)) := inverse_maximal_decreasing hm
  simpa only [ran_inverse] using
    ran_mul_eq_decreasing (inverse_maximal_decreasing hf) (inverse_maximal_decreasing hg)
      (nonnegative_inverse_iff.2 hf₀) (nonnegative_inverse_iff.2 hg₀) hm'

end ScalarMonotone
