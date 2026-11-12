import MonotoneOperators.ExtremaFiniteOperations
import MonotoneOperators.ExtremaComplete

/-!
# Finite sum and composition identities

These are statements about the actual infima and suprema in the two
conditionally complete lattices. In particular, maximality of the operation
with the extremum is a conclusion, not an extra hypothesis.
-/

open Set

namespace ScalarMonotone

noncomputable section

def IncGraph.reflect (f : IncGraph) : DecGraph :=
  ⟨ScalarMonotone.reflect f.val, reflect_maximal_iff.mp (by simpa using f.property)⟩

def DecGraph.reflect (f : DecGraph) : IncGraph :=
  ⟨ScalarMonotone.reflect f.val, reflect_maximal_iff.mpr f.property⟩

@[simp] theorem IncGraph.reflect_reflect (f : IncGraph) : f.reflect.reflect = f :=
  IncGraph.ext_val (ScalarMonotone.reflect_reflect f.val)

@[simp] theorem DecGraph.reflect_reflect (f : DecGraph) : f.reflect.reflect = f :=
  DecGraph.ext_val (ScalarMonotone.reflect_reflect f.val)

def IncGraph.reflectionOrderIso : IncGraph ≃o DecGraph where
  toFun := IncGraph.reflect
  invFun := DecGraph.reflect
  left_inv := IncGraph.reflect_reflect
  right_inv := DecGraph.reflect_reflect
  map_rel_iff' := decLE_reflect_iff

def DecGraph.reflectionOrderIso : DecGraph ≃o IncGraph := IncGraph.reflectionOrderIso.symm

theorem IncGraph.reflect_iInf_bounded {ι : Type*} [Nonempty ι]
    (f : ι → IncGraph) (hf : BddBelow (range f)) :
    (⨅ a, f a).reflect = ⨅ a, (f a).reflect :=
  IncGraph.reflectionOrderIso.map_ciInf hf

theorem IncGraph.reflect_iSup_bounded {ι : Type*} [Nonempty ι]
    (f : ι → IncGraph) (hf : BddAbove (range f)) :
    (⨆ a, f a).reflect = ⨆ a, (f a).reflect :=
  IncGraph.reflectionOrderIso.map_ciSup hf

theorem DecGraph.reflect_iInf_bounded {ι : Type*} [Nonempty ι]
    (f : ι → DecGraph) (hf : BddBelow (range f)) :
    (⨅ a, f a).reflect = ⨅ a, (f a).reflect :=
  DecGraph.reflectionOrderIso.map_ciInf hf

theorem DecGraph.reflect_iSup_bounded {ι : Type*} [Nonempty ι]
    (f : ι → DecGraph) (hf : BddAbove (range f)) :
    (⨆ a, f a).reflect = ⨆ a, (f a).reflect :=
  DecGraph.reflectionOrderIso.map_ciSup hf

theorem comp_reflect_negOut (f h : Operator) :
    comp (ScalarMonotone.reflect f) (negOut h) = comp f h := by
  funext x
  ext u
  constructor
  · rintro ⟨z, hz, hu⟩
    exact ⟨-z, hz, hu⟩
  · rintro ⟨z, hz, hu⟩
    exact ⟨-z, by simpa [negOut] using hz,
      by simpa [ScalarMonotone.reflect] using hu⟩

section Finite

variable {ι : Type*} [Finite ι] [Nonempty ι]

@[simp] theorem IncGraph.reflect_iInf (f : ι → IncGraph) :
    (⨅ a, f a).reflect = ⨅ a, (f a).reflect :=
  IncGraph.reflectionOrderIso.map_ciInf (finite_range f).bddBelow

@[simp] theorem IncGraph.reflect_iSup (f : ι → IncGraph) :
    (⨆ a, f a).reflect = ⨆ a, (f a).reflect :=
  IncGraph.reflectionOrderIso.map_ciSup (finite_range f).bddAbove

@[simp] theorem DecGraph.reflect_iInf (f : ι → DecGraph) :
    (⨅ a, f a).reflect = ⨅ a, (f a).reflect :=
  DecGraph.reflectionOrderIso.map_ciInf (finite_range f).bddBelow

@[simp] theorem DecGraph.reflect_iSup (f : ι → DecGraph) :
    (⨆ a, f a).reflect = ⨆ a, (f a).reflect :=
  DecGraph.reflectionOrderIso.map_ciSup (finite_range f).bddAbove

theorem inc_finite_inf_resolvent (f : ι → IncGraph) (s : ℝ) :
    IsGreatest (range (fun a => (f a).J s)) ((⨅ a, f a).J s) := by
  rw [IncGraph.J_iInf f (finite_range f).bddBelow]
  refine ⟨exists_eq_ciSup_of_finite, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact le_ciSup (finite_range (fun a => (f a).J s)).bddAbove a

theorem inc_finite_sup_resolvent (f : ι → IncGraph) (s : ℝ) :
    IsLeast (range (fun a => (f a).J s)) ((⨆ a, f a).J s) := by
  rw [IncGraph.J_iSup f (finite_range f).bddAbove]
  refine ⟨exists_eq_ciInf_of_finite, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact ciInf_le (finite_range (fun a => (f a).J s)).bddBelow a

theorem inc_add_iInf (f : ι → IncGraph) (h : IncGraph)
    (hadd : ∀ a, MaximalIncreasing (add h.val (f a).val)) :
    add h.val (⨅ a, f a).val =
      (⨅ a, (⟨add h.val (f a).val, hadd a⟩ : IncGraph)).val := by
  exact add_eq_of_resolvent_maxima (fun a => (f a).val) (fun a => (f a).property)
    h.property.1 hadd (⨅ a, f a).property
    (⨅ a, (⟨add h.val (f a).val, hadd a⟩ : IncGraph)).property
    (inc_finite_inf_resolvent f)
    (inc_finite_inf_resolvent (fun a => ⟨add h.val (f a).val, hadd a⟩))

theorem inc_add_iSup (f : ι → IncGraph) (h : IncGraph)
    (hadd : ∀ a, MaximalIncreasing (add h.val (f a).val)) :
    add h.val (⨆ a, f a).val =
      (⨆ a, (⟨add h.val (f a).val, hadd a⟩ : IncGraph)).val := by
  exact add_eq_of_resolvent_minima (fun a => (f a).val) (fun a => (f a).property)
    h.property.1 hadd (⨆ a, f a).property
    (⨆ a, (⟨add h.val (f a).val, hadd a⟩ : IncGraph)).property
    (inc_finite_sup_resolvent f)
    (inc_finite_sup_resolvent (fun a => ⟨add h.val (f a).val, hadd a⟩))

theorem dec_add_iInf (f : ι → DecGraph) (h : DecGraph)
    (hadd : ∀ a, MaximalDecreasing (add h.val (f a).val)) :
    add h.val (⨅ a, f a).val =
      (⨅ a, (⟨add h.val (f a).val, hadd a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨add h.val (f a).val, hadd a⟩
  have hi := inc_add_iInf (fun a => (f a).reflect) h.reflect
    (fun a => reflect_maximal_iff.mpr (hadd a))
  have he : add h.reflect.val (⨅ a, (f a).reflect).val =
      (⨅ a, (g a).reflect).val := hi
  rw [← DecGraph.reflect_iInf, ← DecGraph.reflect_iInf] at he
  change ScalarMonotone.reflect (add h.val (⨅ a, f a).val) =
    ScalarMonotone.reflect (⨅ a, g a).val at he
  have hr := congrArg ScalarMonotone.reflect he
  simpa only [ScalarMonotone.reflect_reflect] using hr

theorem dec_add_iSup (f : ι → DecGraph) (h : DecGraph)
    (hadd : ∀ a, MaximalDecreasing (add h.val (f a).val)) :
    add h.val (⨆ a, f a).val =
      (⨆ a, (⟨add h.val (f a).val, hadd a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨add h.val (f a).val, hadd a⟩
  have hi := inc_add_iSup (fun a => (f a).reflect) h.reflect
    (fun a => reflect_maximal_iff.mpr (hadd a))
  have he : add h.reflect.val (⨆ a, (f a).reflect).val =
      (⨆ a, (g a).reflect).val := hi
  rw [← DecGraph.reflect_iSup, ← DecGraph.reflect_iSup] at he
  change ScalarMonotone.reflect (add h.val (⨆ a, f a).val) =
    ScalarMonotone.reflect (⨆ a, g a).val at he
  have hr := congrArg ScalarMonotone.reflect he
  simpa only [ScalarMonotone.reflect_reflect] using hr

theorem inc_comp_right_iInf_inc (f : ι → IncGraph) (h : IncGraph)
    (hc : ∀ a, MaximalIncreasing (comp (f a).val h.val)) :
    comp (⨅ a, f a).val h.val =
      (⨅ a, (⟨comp (f a).val h.val, hc a⟩ : IncGraph)).val := by
  exact comp_eq_of_resolvent_maxima (fun a => (f a).val) (fun a => (f a).property)
    h.property.1 hc (⨅ a, f a).property
    (⨅ a, (⟨comp (f a).val h.val, hc a⟩ : IncGraph)).property
    (inc_finite_inf_resolvent f)
    (inc_finite_inf_resolvent (fun a => ⟨comp (f a).val h.val, hc a⟩))

theorem inc_comp_right_iSup_inc (f : ι → IncGraph) (h : IncGraph)
    (hc : ∀ a, MaximalIncreasing (comp (f a).val h.val)) :
    comp (⨆ a, f a).val h.val =
      (⨆ a, (⟨comp (f a).val h.val, hc a⟩ : IncGraph)).val := by
  exact comp_eq_of_resolvent_minima (fun a => (f a).val) (fun a => (f a).property)
    h.property.1 hc (⨆ a, f a).property
    (⨆ a, (⟨comp (f a).val h.val, hc a⟩ : IncGraph)).property
    (inc_finite_sup_resolvent f)
    (inc_finite_sup_resolvent (fun a => ⟨comp (f a).val h.val, hc a⟩))

theorem inc_comp_right_iInf_dec (f : ι → IncGraph) (h : DecGraph)
    (hc : ∀ a, MaximalDecreasing (comp (f a).val h.val)) :
    comp (⨅ a, f a).val h.val =
      (⨅ a, (⟨comp (f a).val h.val, hc a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨comp (f a).val h.val, hc a⟩
  have hi := inc_comp_right_iInf_inc f h.reflect
    (fun a => reflect_maximal_iff.mpr (hc a))
  have he : comp (⨅ a, f a).val h.reflect.val =
      (⨅ a, (g a).reflect).val := hi
  rw [← DecGraph.reflect_iInf] at he
  change ScalarMonotone.reflect (comp (⨅ a, f a).val h.val) =
    ScalarMonotone.reflect (⨅ a, g a).val at he
  have hr := congrArg ScalarMonotone.reflect he
  simpa only [ScalarMonotone.reflect_reflect] using hr

theorem inc_comp_right_iSup_dec (f : ι → IncGraph) (h : DecGraph)
    (hc : ∀ a, MaximalDecreasing (comp (f a).val h.val)) :
    comp (⨆ a, f a).val h.val =
      (⨆ a, (⟨comp (f a).val h.val, hc a⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun a => ⟨comp (f a).val h.val, hc a⟩
  have hi := inc_comp_right_iSup_inc f h.reflect
    (fun a => reflect_maximal_iff.mpr (hc a))
  have he : comp (⨆ a, f a).val h.reflect.val =
      (⨆ a, (g a).reflect).val := hi
  rw [← DecGraph.reflect_iSup] at he
  change ScalarMonotone.reflect (comp (⨆ a, f a).val h.val) =
    ScalarMonotone.reflect (⨆ a, g a).val at he
  have hr := congrArg ScalarMonotone.reflect he
  simpa only [ScalarMonotone.reflect_reflect] using hr

theorem dec_comp_right_iInf_inc (f : ι → DecGraph) (h : IncGraph)
    (hc : ∀ a, MaximalDecreasing (comp (f a).val h.val)) :
    comp (⨅ a, f a).val h.val =
      (⨅ a, (⟨comp (f a).val h.val, hc a⟩ : DecGraph)).val := by
  let k : DecGraph := ⟨negOut h.val, by
    change MaximalIncreasing (negOut (negOut h.val))
    simpa only [negOut_negOut] using h.property⟩
  have hct : ∀ a, MaximalDecreasing (comp (f a).reflect.val k.val) := by
    intro a
    simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hc a
  have hi := inc_comp_right_iInf_dec (fun a => (f a).reflect) k hct
  rw [← DecGraph.reflect_iInf] at hi
  simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hi

theorem dec_comp_right_iSup_inc (f : ι → DecGraph) (h : IncGraph)
    (hc : ∀ a, MaximalDecreasing (comp (f a).val h.val)) :
    comp (⨆ a, f a).val h.val =
      (⨆ a, (⟨comp (f a).val h.val, hc a⟩ : DecGraph)).val := by
  let k : DecGraph := ⟨negOut h.val, by
    change MaximalIncreasing (negOut (negOut h.val))
    simpa only [negOut_negOut] using h.property⟩
  have hct : ∀ a, MaximalDecreasing (comp (f a).reflect.val k.val) := by
    intro a
    simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hc a
  have hi := inc_comp_right_iSup_dec (fun a => (f a).reflect) k hct
  rw [← DecGraph.reflect_iSup] at hi
  simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hi

theorem dec_comp_right_iInf_dec (f : ι → DecGraph) (h : DecGraph)
    (hc : ∀ a, MaximalIncreasing (comp (f a).val h.val)) :
    comp (⨅ a, f a).val h.val =
      (⨅ a, (⟨comp (f a).val h.val, hc a⟩ : IncGraph)).val := by
  let k : IncGraph := ⟨negOut h.val, h.property⟩
  have hct : ∀ a, MaximalIncreasing (comp (f a).reflect.val k.val) := by
    intro a
    simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hc a
  have hi := inc_comp_right_iInf_inc (fun a => (f a).reflect) k hct
  rw [← DecGraph.reflect_iInf] at hi
  simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hi

theorem dec_comp_right_iSup_dec (f : ι → DecGraph) (h : DecGraph)
    (hc : ∀ a, MaximalIncreasing (comp (f a).val h.val)) :
    comp (⨆ a, f a).val h.val =
      (⨆ a, (⟨comp (f a).val h.val, hc a⟩ : IncGraph)).val := by
  let k : IncGraph := ⟨negOut h.val, h.property⟩
  have hct : ∀ a, MaximalIncreasing (comp (f a).reflect.val k.val) := by
    intro a
    simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hc a
  have hi := inc_comp_right_iSup_inc (fun a => (f a).reflect) k hct
  rw [← DecGraph.reflect_iSup] at hi
  simpa only [DecGraph.reflect, k, comp_reflect_negOut] using hi

end Finite

end

end ScalarMonotone
