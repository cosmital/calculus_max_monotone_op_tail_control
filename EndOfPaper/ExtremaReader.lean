import MonotoneOperators.ExtremaExamples

/-!
Explicit reader-facing bridges for both orientations: the full
least-upper-bound equivalence, both distributive identities and graph-point
attainment for arbitrary finite nonempty families of completed graphs.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem inc_sup_universal_property {ι : Type*} [Nonempty ι]
    (f : ι → IncGraph) (hb : BddAbove (Set.range f)) (h : IncGraph) :
    h = ⨆ i, f i ↔ (∀ i, f i ≤ h) ∧
      ∀ g : IncGraph, (∀ i, f i ≤ g) → h ≤ g := by
  constructor
  · rintro rfl
    exact ⟨fun i => le_ciSup hb i, fun _ hg => ciSup_le hg⟩
  · rintro ⟨hu, hl⟩
    exact le_antisymm (hl _ (fun i => le_ciSup hb i)) (ciSup_le hu)

theorem dec_sup_universal_property {ι : Type*} [Nonempty ι]
    (f : ι → DecGraph) (hb : BddAbove (Set.range f)) (h : DecGraph) :
    h = ⨆ i, f i ↔ (∀ i, f i ≤ h) ∧
      ∀ g : DecGraph, (∀ i, f i ≤ g) → h ≤ g := by
  constructor
  · rintro rfl
    exact ⟨fun i => le_ciSup hb i, fun _ hg => ciSup_le hg⟩
  · rintro ⟨hu, hl⟩
    exact le_antisymm (hl _ (fun i => le_ciSup hb i)) (ciSup_le hu)

theorem inc_graph_distributivity (f g h : IncGraph) :
    f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) ∧
      f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) :=
  ⟨inf_sup_left f g h, sup_inf_left f g h⟩

theorem dec_graph_distributivity (f g h : DecGraph) :
    f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) ∧
      f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) :=
  ⟨inf_sup_left f g h, sup_inf_left f g h⟩

theorem inc_finite_extremum_graph_points {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → IncGraph) (x u : ℝ) :
    (u ∈ (⨅ i, f i).val x → ∃ i, u ∈ (f i).val x) ∧
      (u ∈ (⨆ i, f i).val x → ∃ i, u ∈ (f i).val x) :=
  ⟨IncGraph.mem_iInf_imp_exists f, IncGraph.mem_iSup_imp_exists f⟩

theorem dec_finite_extremum_graph_points {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → DecGraph) (x u : ℝ) :
    (u ∈ (⨅ i, f i).val x → ∃ i, u ∈ (f i).val x) ∧
      (u ∈ (⨆ i, f i).val x → ∃ i, u ∈ (f i).val x) :=
  ⟨DecGraph.mem_iInf_imp_exists f, DecGraph.mem_iSup_imp_exists f⟩

end ScalarMonotone.EndOfPaper
end
