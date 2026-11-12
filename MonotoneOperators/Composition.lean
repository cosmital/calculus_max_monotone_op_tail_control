import MonotoneOperators.Algebra

/-!
# The exact obstruction to monotone composition

The rectangle condition is already exact for arbitrary monotone relations;
maximality and nonemptiness are not needed for this part of the proposition.
-/

open Set

namespace ScalarMonotone

theorem noRectangle_of_comp_increasing {f g : Operator}
    (h : Increasing (comp g f)) : NoRectangle f g := by
  intro z
  by_cases hf : (inverse f z).Subsingleton
  · exact Or.inl hf
  · right
    obtain ⟨a, ha, b, hb, hab⟩ :
        ∃ a ∈ inverse f z, ∃ b ∈ inverse f z, a ≠ b := by
      simpa only [Set.Subsingleton, not_forall, exists_prop] using hf
    intro u hu v hv
    have h₁ := h (show u ∈ comp g f a from ⟨z, ha, hu⟩)
      (show v ∈ comp g f b from ⟨z, hb, hv⟩)
    have h₂ := h (show v ∈ comp g f a from ⟨z, ha, hv⟩)
      (show u ∈ comp g f b from ⟨z, hb, hu⟩)
    have hz : (a - b) * (u - v) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab))

theorem Increasing.comp_of_noRectangle {f g : Operator}
    (hf : Increasing f) (hg : Increasing g) (hrect : NoRectangle f g) :
    Increasing (comp g f) := by
  apply increasing_iff_order.mpr
  rintro x u y v ⟨a, ha, hu⟩ ⟨b, hb, hv⟩ hxy
  have hab : a ≤ b := hf.le_of_lt ha hb hxy
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    rcases hrect a with hfiber | gfiber
    · have : x = y := hfiber ha hb
      exact (hxy.ne this).elim
    · exact le_of_eq (gfiber hu hv)
  · exact hg.le_of_lt hu hv hlt

theorem increasing_comp_iff_noRectangle {f g : Operator}
    (hf : Increasing f) (hg : Increasing g) :
    Increasing (comp g f) ↔ NoRectangle f g :=
  ⟨noRectangle_of_comp_increasing, hf.comp_of_noRectangle hg⟩

theorem subsingleton_negOut_iff (f : Operator) (x : ℝ) :
    (negOut f x).Subsingleton ↔ (f x).Subsingleton := by
  constructor
  · intro h u hu v hv
    have hneg : -u = -v := h (by simpa [negOut] using hu) (by simpa [negOut] using hv)
    exact neg_injective hneg
  · intro h u hu v hv
    have hneg : -u = -v := h hu hv
    exact neg_injective hneg

theorem noRectangle_negOut_right (f g : Operator) :
    NoRectangle f (negOut g) ↔ NoRectangle f g := by
  simp only [NoRectangle, subsingleton_negOut_iff]

theorem noRectangle_reflect_left (f g : Operator) :
    NoRectangle (reflect f) g ↔ NoRectangle f g := by
  have hfiber : ∀ z, (inverse (reflect f) z).Subsingleton ↔ (inverse f z).Subsingleton := by
    intro z
    change (negOut (inverse f) z).Subsingleton ↔ (inverse f z).Subsingleton
    exact subsingleton_negOut_iff (inverse f) z
  simp only [NoRectangle, hfiber]

theorem negOut_comp (f g : Operator) : negOut (comp g f) = comp (negOut g) f := rfl
theorem reflect_comp (f g : Operator) : reflect (comp g f) = comp g (reflect f) := rfl

theorem decreasing_comp_iff_noRectangle_of_increasing_decreasing {f g : Operator}
    (hf : Increasing f) (hg : Decreasing g) :
    Decreasing (comp g f) ↔ NoRectangle f g := by
  change Increasing (negOut (comp g f)) ↔ _
  rw [negOut_comp, increasing_comp_iff_noRectangle hf hg, noRectangle_negOut_right]

theorem decreasing_comp_iff_noRectangle_of_decreasing_increasing {f g : Operator}
    (hf : Decreasing f) (hg : Increasing g) :
    Decreasing (comp g f) ↔ NoRectangle f g := by
  change Increasing (negOut (comp g f)) ↔ _
  rw [← reflect_increasing_iff, reflect_comp,
    increasing_comp_iff_noRectangle (reflect_increasing_iff.mpr hf) hg,
    noRectangle_reflect_left]

theorem increasing_comp_iff_noRectangle_of_decreasing_decreasing {f g : Operator}
    (hf : Decreasing f) (hg : Decreasing g) :
    Increasing (comp g f) ↔ NoRectangle f g := by
  have h := decreasing_comp_iff_noRectangle_of_increasing_decreasing
    (reflect_increasing_iff.mpr hf) hg
  rw [noRectangle_reflect_left] at h
  change Increasing (negOut (comp g (reflect f))) ↔ _ at h
  change Increasing (reflect (negOut (comp g f))) ↔ _ at h
  rw [reflect_increasing_iff, negOut_negOut] at h
  exact h

/-- Reindexing by the intermediate graph value, as in the composition proof. -/
theorem ran_identity_add_comp (f g : Operator) :
    ran (add identity (comp g f)) = ran (add (inverse f) g) := by
  ext w
  constructor
  · rintro ⟨x, a, ha, u, ⟨z, hz, hu⟩, hwu⟩
    have hax : a = x := ha
    subst a
    exact ⟨z, x, hz, u, hu, hwu⟩
  · rintro ⟨z, x, hx, u, hu, hwu⟩
    exact ⟨x, x, rfl, u, ⟨z, hx, hu⟩, hwu⟩

end ScalarMonotone
