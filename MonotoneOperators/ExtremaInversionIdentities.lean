import MonotoneOperators.ExtremaIdentities

/-!
# Parallel sums and left composition of finite extrema

Inversion transports the direct identities with the appropriate reversal
of extrema in the increasing class.
-/

open Set

namespace ScalarMonotone

noncomputable section

theorem operator_inverse_injective : Function.Injective inverse := by
  intro f g h
  exact congrArg inverse h

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem inc_inverse_iInf_val (f : ι → IncGraph) :
    inverse (⨅ a, f a).val = (⨆ a, (f a).inv).val :=
  congrArg IncGraph.val (IncGraph.inv_iInf f (finite_range f).bddBelow)

theorem inc_inverse_iSup_val (f : ι → IncGraph) :
    inverse (⨆ a, f a).val = (⨅ a, (f a).inv).val :=
  congrArg IncGraph.val (IncGraph.inv_iSup f (finite_range f).bddAbove)

theorem dec_inverse_iInf_val (f : ι → DecGraph) :
    inverse (⨅ a, f a).val = (⨅ a, (f a).inv).val :=
  congrArg DecGraph.val (DecGraph.inv_iInf f (finite_range f).bddBelow)

theorem dec_inverse_iSup_val (f : ι → DecGraph) :
    inverse (⨆ a, f a).val = (⨆ a, (f a).inv).val :=
  congrArg DecGraph.val (DecGraph.inv_iSup f (finite_range f).bddAbove)

theorem inc_parallelAdd_iInf (f : ι → IncGraph) (h : IncGraph)
    (hp : ∀ a, MaximalIncreasing (parallelAdd h.val (f a).val)) :
    parallelAdd h.val (⨅ a, f a).val =
      (⨅ a, (⟨parallelAdd h.val (f a).val, hp a⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun a => ⟨parallelAdd h.val (f a).val, hp a⟩
  have hq : ∀ a, MaximalIncreasing (add h.inv.val (f a).inv.val) :=
    fun a => inverse_maximal (hp a)
  have hi := inc_add_iSup (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change add (inverse h.val) (inverse (⨅ a, f a).val) = inverse (⨅ a, g a).val
  rw [inc_inverse_iInf_val, inc_inverse_iInf_val]
  exact hi

theorem inc_parallelAdd_iSup (f : ι → IncGraph) (h : IncGraph)
    (hp : ∀ a, MaximalIncreasing (parallelAdd h.val (f a).val)) :
    parallelAdd h.val (⨆ a, f a).val =
      (⨆ a, (⟨parallelAdd h.val (f a).val, hp a⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun a => ⟨parallelAdd h.val (f a).val, hp a⟩
  have hq : ∀ a, MaximalIncreasing (add h.inv.val (f a).inv.val) :=
    fun a => inverse_maximal (hp a)
  have hi := inc_add_iInf (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change add (inverse h.val) (inverse (⨆ a, f a).val) = inverse (⨆ a, g a).val
  rw [inc_inverse_iSup_val, inc_inverse_iSup_val]
  exact hi

theorem dec_parallelAdd_iInf (f : ι → DecGraph) (h : DecGraph)
    (hp : ∀ a, MaximalDecreasing (parallelAdd h.val (f a).val)) :
    parallelAdd h.val (⨅ a, f a).val =
      (⨅ a, (⟨parallelAdd h.val (f a).val, hp a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨parallelAdd h.val (f a).val, hp a⟩
  have hq : ∀ a, MaximalDecreasing (add h.inv.val (f a).inv.val) :=
    fun a => inverse_maximal_decreasing (hp a)
  have hi := dec_add_iInf (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change add (inverse h.val) (inverse (⨅ a, f a).val) = inverse (⨅ a, g a).val
  rw [dec_inverse_iInf_val, dec_inverse_iInf_val]
  exact hi

theorem dec_parallelAdd_iSup (f : ι → DecGraph) (h : DecGraph)
    (hp : ∀ a, MaximalDecreasing (parallelAdd h.val (f a).val)) :
    parallelAdd h.val (⨆ a, f a).val =
      (⨆ a, (⟨parallelAdd h.val (f a).val, hp a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨parallelAdd h.val (f a).val, hp a⟩
  have hq : ∀ a, MaximalDecreasing (add h.inv.val (f a).inv.val) :=
    fun a => inverse_maximal_decreasing (hp a)
  have hi := dec_add_iSup (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change add (inverse h.val) (inverse (⨆ a, f a).val) = inverse (⨆ a, g a).val
  rw [dec_inverse_iSup_val, dec_inverse_iSup_val]
  exact hi

theorem inc_comp_left_iInf_inc (f : ι → IncGraph) (h : IncGraph)
    (hc : ∀ a, MaximalIncreasing (comp h.val (f a).val)) :
    comp h.val (⨅ a, f a).val =
      (⨅ a, (⟨comp h.val (f a).val, hc a⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalIncreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalIncreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal (hc a)
  have hi := inc_comp_right_iSup_inc (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨅ a, f a).val) = inverse (⨅ a, g a).val
  rw [inverse_comp, inc_inverse_iInf_val, inc_inverse_iInf_val]
  simpa only [IncGraph.inv, g, inverse_comp] using hi

theorem inc_comp_left_iSup_inc (f : ι → IncGraph) (h : IncGraph)
    (hc : ∀ a, MaximalIncreasing (comp h.val (f a).val)) :
    comp h.val (⨆ a, f a).val =
      (⨆ a, (⟨comp h.val (f a).val, hc a⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalIncreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalIncreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal (hc a)
  have hi := inc_comp_right_iInf_inc (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨆ a, f a).val) = inverse (⨆ a, g a).val
  rw [inverse_comp, inc_inverse_iSup_val, inc_inverse_iSup_val]
  simpa only [IncGraph.inv, g, inverse_comp] using hi

theorem inc_comp_left_iInf_dec (f : ι → IncGraph) (h : DecGraph)
    (hc : ∀ a, MaximalDecreasing (comp h.val (f a).val)) :
    comp h.val (⨅ a, f a).val =
      (⨆ a, (⟨comp h.val (f a).val, hc a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalDecreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalDecreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal_decreasing (hc a)
  have hi := inc_comp_right_iSup_dec (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨅ a, f a).val) = inverse (⨆ a, g a).val
  rw [inverse_comp, inc_inverse_iInf_val, dec_inverse_iSup_val]
  simpa only [IncGraph.inv, DecGraph.inv, g, inverse_comp] using hi

theorem inc_comp_left_iSup_dec (f : ι → IncGraph) (h : DecGraph)
    (hc : ∀ a, MaximalDecreasing (comp h.val (f a).val)) :
    comp h.val (⨆ a, f a).val =
      (⨅ a, (⟨comp h.val (f a).val, hc a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalDecreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalDecreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal_decreasing (hc a)
  have hi := inc_comp_right_iInf_dec (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨆ a, f a).val) = inverse (⨅ a, g a).val
  rw [inverse_comp, inc_inverse_iSup_val, dec_inverse_iInf_val]
  simpa only [IncGraph.inv, DecGraph.inv, g, inverse_comp] using hi

theorem dec_comp_left_iInf_inc (f : ι → DecGraph) (h : IncGraph)
    (hc : ∀ a, MaximalDecreasing (comp h.val (f a).val)) :
    comp h.val (⨅ a, f a).val =
      (⨅ a, (⟨comp h.val (f a).val, hc a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalDecreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalDecreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal_decreasing (hc a)
  have hi := dec_comp_right_iInf_inc (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨅ a, f a).val) = inverse (⨅ a, g a).val
  rw [inverse_comp, dec_inverse_iInf_val, dec_inverse_iInf_val]
  simpa only [IncGraph.inv, DecGraph.inv, g, inverse_comp] using hi

theorem dec_comp_left_iSup_inc (f : ι → DecGraph) (h : IncGraph)
    (hc : ∀ a, MaximalDecreasing (comp h.val (f a).val)) :
    comp h.val (⨆ a, f a).val =
      (⨆ a, (⟨comp h.val (f a).val, hc a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalDecreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalDecreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal_decreasing (hc a)
  have hi := dec_comp_right_iSup_inc (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨆ a, f a).val) = inverse (⨆ a, g a).val
  rw [inverse_comp, dec_inverse_iSup_val, dec_inverse_iSup_val]
  simpa only [IncGraph.inv, DecGraph.inv, g, inverse_comp] using hi

theorem dec_comp_left_iInf_dec (f : ι → DecGraph) (h : DecGraph)
    (hc : ∀ a, MaximalIncreasing (comp h.val (f a).val)) :
    comp h.val (⨅ a, f a).val =
      (⨆ a, (⟨comp h.val (f a).val, hc a⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalIncreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalIncreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal (hc a)
  have hi := dec_comp_right_iInf_dec (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨅ a, f a).val) = inverse (⨆ a, g a).val
  rw [inverse_comp, dec_inverse_iInf_val, inc_inverse_iSup_val]
  simpa only [IncGraph.inv, DecGraph.inv, g, inverse_comp] using hi

theorem dec_comp_left_iSup_dec (f : ι → DecGraph) (h : DecGraph)
    (hc : ∀ a, MaximalIncreasing (comp h.val (f a).val)) :
    comp h.val (⨆ a, f a).val =
      (⨅ a, (⟨comp h.val (f a).val, hc a⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun a => ⟨comp h.val (f a).val, hc a⟩
  have hq : ∀ a, MaximalIncreasing (comp (f a).inv.val h.inv.val) := by
    intro a
    change MaximalIncreasing (comp (inverse (f a).val) (inverse h.val))
    rw [← inverse_comp]
    exact inverse_maximal (hc a)
  have hi := dec_comp_right_iSup_dec (fun a => (f a).inv) h.inv hq
  apply operator_inverse_injective
  change inverse (comp h.val (⨆ a, f a).val) = inverse (⨅ a, g a).val
  rw [inverse_comp, dec_inverse_iSup_val, inc_inverse_iInf_val]
  simpa only [IncGraph.inv, DecGraph.inv, g, inverse_comp] using hi

end

end ScalarMonotone
