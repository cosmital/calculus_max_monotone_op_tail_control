import MonotoneOperators.Composition
import MonotoneOperators.Sums

/-!
# Maximality of compositions

These statements complete the composition proposition.  The hypothesis
`(dom (comp g f)).Nonempty` is precisely nonemptiness of the composite graph.
The four sign cases are stated separately, so the expected orientation and
the sign in the domain--range condition are explicit in each type.
-/

open Set

namespace ScalarMonotone

theorem maximal_iff_diagonal_range {f : Operator} (hf : Increasing f) :
    MaximalIncreasing f ↔ ran (add identity f) = univ := by
  rw [op_add_comm identity f]
  constructor
  · exact ran_add_identity_eq_univ
  · intro h
    apply maximal_of_minty hf
    intro s
    apply mem_ran_add_identity.mp
    rw [h]
    trivial

theorem comp_nonempty_iff_common_domain (f g : Operator) :
    (dom (comp g f)).Nonempty ↔ (dom (inverse f) ∩ dom g).Nonempty := by
  constructor
  · rintro ⟨x, u, z, hz, hu⟩
    exact ⟨z, ⟨x, hz⟩, ⟨u, hu⟩⟩
  · rintro ⟨z, ⟨x, hx⟩, ⟨u, hu⟩⟩
    exact ⟨x, u, z, hx, hu⟩

theorem comp_maximal_iff_of_increasing_increasing {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hne : (dom (comp g f)).Nonempty) (hrect : NoRectangle f g) :
    MaximalIncreasing (comp g f) ↔ setAdd (dom f) (ran g) = univ := by
  rw [maximal_iff_diagonal_range (hf.1.comp_of_noRectangle hg.1 hrect),
    ran_identity_add_comp,
    ran_add_eq (inverse_maximal hf) hg ((comp_nonempty_iff_common_domain f g).mp hne),
    ran_inverse]

theorem comp_maximal_iff_of_decreasing_decreasing {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hne : (dom (comp g f)).Nonempty) (hrect : NoRectangle f g) :
    MaximalIncreasing (comp g f) ↔ setAdd (dom f) (ran g) = univ := by
  have hm := (increasing_comp_iff_noRectangle_of_decreasing_decreasing hf.1 hg.1).mpr hrect
  rw [maximal_iff_diagonal_range hm, ran_identity_add_comp,
    ran_add_eq_decreasing (inverse_maximal_decreasing hf) hg
      ((comp_nonempty_iff_common_domain f g).mp hne), ran_inverse]

theorem comp_maximal_iff_of_increasing_decreasing {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalDecreasing g)
    (hne : (dom (comp g f)).Nonempty) (hrect : NoRectangle f g) :
    MaximalDecreasing (comp g f) ↔ setAdd (dom f) (setNeg (ran g)) = univ := by
  have hne' : (dom (comp (negOut g) f)).Nonempty := by
    rw [← negOut_comp, dom_negOut]
    exact hne
  have h := comp_maximal_iff_of_increasing_increasing hf hg hne'
    ((noRectangle_negOut_right f g).mpr hrect)
  simpa only [← negOut_comp, ran_negOut] using h

theorem comp_maximal_iff_of_decreasing_increasing {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalIncreasing g)
    (hne : (dom (comp g f)).Nonempty) (hrect : NoRectangle f g) :
    MaximalDecreasing (comp g f) ↔ setAdd (dom f) (setNeg (ran g)) = univ := by
  have hg' : MaximalDecreasing (negOut g) := by
    simpa only [MaximalDecreasing, negOut_negOut] using hg
  have hne' : (dom (comp (negOut g) f)).Nonempty := by
    rw [← negOut_comp, dom_negOut]
    exact hne
  have h := comp_maximal_iff_of_decreasing_decreasing hf hg' hne'
    ((noRectangle_negOut_right f g).mpr hrect)
  simpa only [← negOut_comp, ran_negOut] using h

end ScalarMonotone
