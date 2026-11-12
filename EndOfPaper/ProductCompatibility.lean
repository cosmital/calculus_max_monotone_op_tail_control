import MonotoneOperators.Basic

/-!
The literal compatible-point criterion and equivalence with monotonicity after adjoining the point, including the product specialization.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

def graphPointExtension (h : Operator) (x w : ℝ) : Operator :=
  fun y => {v | v ∈ h y ∨ (y = x ∧ v = w)}

theorem compatible_graph_criterion {h : Operator} {x w : ℝ} :
    Compatible h x w ↔ ∀ p ∈ graph h, 0 ≤ (x-p.1)*(w-p.2) := by
  constructor
  · intro hc p hp
    exact hc hp
  · intro hc y v hv
    exact hc (y,v) hv

theorem compatible_extension_iff {h : Operator} (hh : Increasing h) {x w : ℝ} :
    Increasing (graphPointExtension h x w) ↔ Compatible h x w := by
  constructor
  · intro he y v hv
    exact he (Or.inr ⟨rfl,rfl⟩) (Or.inl hv)
  · intro hc a p b q hp hq
    change p ∈ h a ∨ (a = x ∧ p = w) at hp
    change q ∈ h b ∨ (b = x ∧ q = w) at hq
    rcases hp with hp | ⟨rfl,rfl⟩ <;> rcases hq with hq | ⟨rfl,rfl⟩
    · exact hh hp hq
    · have h := hc hp
      nlinarith
    · exact hc hq
    · simp

theorem product_compatibility_criterion {f g : Operator} (hh : Increasing (mul f g)) {x w : ℝ} :
    Increasing (graphPointExtension (mul f g) x w) ↔
      ∀ p ∈ graph (mul f g), 0 ≤ (x-p.1)*(w-p.2) :=
  (compatible_extension_iff hh).trans compatible_graph_criterion

end ScalarMonotone.EndOfPaper
end
