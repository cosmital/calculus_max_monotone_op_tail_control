import MonotoneOperators.Extrema

/-!
# Conditional lattice instances and inversion of extrema

The arbitrary fallback value used for an empty or unbounded set is not a
mathematical extremum.  Every theorem about `sInf`, `sSup`, `iInf`, or `iSup`
below explicitly supplies the nonemptiness and boundedness hypotheses.
-/

namespace ScalarMonotone

open Set
open scoped Classical

noncomputable section

def IncGraph.supSet (S : Set IncGraph) : IncGraph :=
  if h : S.Nonempty ∧ BddAbove S then
    @incSup S h.1.to_subtype (fun f => f.val) (by
      rcases h.2 with ⟨b, hb⟩
      exact ⟨b, by rintro _ ⟨f, rfl⟩; exact hb f.property⟩)
  else IncGraph.ofJ id monotone_id LipschitzWith.id

def IncGraph.infSet (S : Set IncGraph) : IncGraph :=
  if h : S.Nonempty ∧ BddBelow S then
    @incInf S h.1.to_subtype (fun f => f.val) (by
      rcases h.2 with ⟨b, hb⟩
      exact ⟨b, by rintro _ ⟨f, rfl⟩; exact hb f.property⟩)
  else IncGraph.ofJ id monotone_id LipschitzWith.id

def DecGraph.supSet (S : Set DecGraph) : DecGraph :=
  if h : S.Nonempty ∧ BddAbove S then
    @decSup S h.1.to_subtype (fun f => f.val) (by
      rcases h.2 with ⟨b, hb⟩
      exact ⟨b, by rintro _ ⟨f, rfl⟩; exact hb f.property⟩)
  else DecGraph.ofJ id monotone_id LipschitzWith.id

def DecGraph.infSet (S : Set DecGraph) : DecGraph :=
  if h : S.Nonempty ∧ BddBelow S then
    @decInf S h.1.to_subtype (fun f => f.val) (by
      rcases h.2 with ⟨b, hb⟩
      exact ⟨b, by rintro _ ⟨f, rfl⟩; exact hb f.property⟩)
  else DecGraph.ofJ id monotone_id LipschitzWith.id

theorem IncGraph.isLUB_supSet (S : Set IncGraph) (hn : S.Nonempty) (hb : BddAbove S) :
    IsLUB S (IncGraph.supSet S) := by
  unfold IncGraph.supSet
  rw [dif_pos ⟨hn, hb⟩]
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
    @incSup_isLUB S hn.to_subtype (fun f => f.val) _

theorem IncGraph.isGLB_infSet (S : Set IncGraph) (hn : S.Nonempty) (hb : BddBelow S) :
    IsGLB S (IncGraph.infSet S) := by
  unfold IncGraph.infSet
  rw [dif_pos ⟨hn, hb⟩]
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
    @incInf_isGLB S hn.to_subtype (fun f => f.val) _

theorem DecGraph.isLUB_supSet (S : Set DecGraph) (hn : S.Nonempty) (hb : BddAbove S) :
    IsLUB S (DecGraph.supSet S) := by
  unfold DecGraph.supSet
  rw [dif_pos ⟨hn, hb⟩]
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
    @decSup_isLUB S hn.to_subtype (fun f => f.val) _

theorem DecGraph.isGLB_infSet (S : Set DecGraph) (hn : S.Nonempty) (hb : BddBelow S) :
    IsGLB S (DecGraph.infSet S) := by
  unfold DecGraph.infSet
  rw [dif_pos ⟨hn, hb⟩]
  simpa only [Subtype.range_coe_subtype, setOf_mem_eq] using
    @decInf_isGLB S hn.to_subtype (fun f => f.val) _

instance : ConditionallyCompleteLattice IncGraph where
  __ := inferInstanceAs (Lattice IncGraph)
  sSup := IncGraph.supSet
  sInf := IncGraph.infSet
  le_csSup S a hb ha := (IncGraph.isLUB_supSet S ⟨a, ha⟩ hb).1 ha
  csSup_le S a hn ha := (IncGraph.isLUB_supSet S hn ⟨a, ha⟩).2 ha
  csInf_le S a hb ha := (IncGraph.isGLB_infSet S ⟨a, ha⟩ hb).1 ha
  le_csInf S a hn ha := (IncGraph.isGLB_infSet S hn ⟨a, ha⟩).2 ha

instance : ConditionallyCompleteLattice DecGraph where
  __ := inferInstanceAs (Lattice DecGraph)
  sSup := DecGraph.supSet
  sInf := DecGraph.infSet
  le_csSup S a hb ha := (DecGraph.isLUB_supSet S ⟨a, ha⟩ hb).1 ha
  csSup_le S a hn ha := (DecGraph.isLUB_supSet S hn ⟨a, ha⟩).2 ha
  csInf_le S a hb ha := (DecGraph.isGLB_infSet S ⟨a, ha⟩ hb).1 ha
  le_csInf S a hn ha := (DecGraph.isGLB_infSet S hn ⟨a, ha⟩).2 ha

variable {ι : Type*} [Nonempty ι]

theorem IncGraph.iInf_eq_incInf (f : ι → IncGraph) (hb : BddBelow (range f)) :
    (⨅ i, f i) = incInf f hb := (isGLB_ciInf hb).unique (incInf_isGLB f hb)
theorem IncGraph.iSup_eq_incSup (f : ι → IncGraph) (hb : BddAbove (range f)) :
    (⨆ i, f i) = incSup f hb := (isLUB_ciSup hb).unique (incSup_isLUB f hb)
theorem DecGraph.iInf_eq_decInf (f : ι → DecGraph) (hb : BddBelow (range f)) :
    (⨅ i, f i) = decInf f hb := (isGLB_ciInf hb).unique (decInf_isGLB f hb)
theorem DecGraph.iSup_eq_decSup (f : ι → DecGraph) (hb : BddAbove (range f)) :
    (⨆ i, f i) = decSup f hb := (isLUB_ciSup hb).unique (decSup_isLUB f hb)

theorem IncGraph.J_iInf (f : ι → IncGraph) (hb : BddBelow (range f)) (s : ℝ) :
    (⨅ i, f i).J s = ⨆ i, (f i).J s := by rw [IncGraph.iInf_eq_incInf f hb]; simp
theorem IncGraph.J_iSup (f : ι → IncGraph) (hb : BddAbove (range f)) (s : ℝ) :
    (⨆ i, f i).J s = ⨅ i, (f i).J s := by rw [IncGraph.iSup_eq_incSup f hb]; simp
theorem DecGraph.J_iInf (f : ι → DecGraph) (hb : BddBelow (range f)) (s : ℝ) :
    (⨅ i, f i).J s = ⨅ i, (f i).J s := by rw [DecGraph.iInf_eq_decInf f hb]; simp
theorem DecGraph.J_iSup (f : ι → DecGraph) (hb : BddAbove (range f)) (s : ℝ) :
    (⨆ i, f i).J s = ⨆ i, (f i).J s := by rw [DecGraph.iSup_eq_decSup f hb]; simp

def IncGraph.inv (f : IncGraph) : IncGraph := ⟨inverse f.val, inverse_maximal f.property⟩
def DecGraph.inv (f : DecGraph) : DecGraph :=
  ⟨inverse f.val, inverse_maximal_decreasing f.property⟩

@[simp] theorem IncGraph.inv_inv (f : IncGraph) : f.inv.inv = f :=
  IncGraph.ext_val (inverse_inverse f.val)
@[simp] theorem DecGraph.inv_inv (f : DecGraph) : f.inv.inv = f :=
  DecGraph.ext_val (inverse_inverse f.val)

def IncGraph.inverseOrderIso : IncGraph ≃o OrderDual IncGraph where
  toFun := IncGraph.inv
  invFun := IncGraph.inv
  left_inv := IncGraph.inv_inv
  right_inv := IncGraph.inv_inv
  map_rel_iff' := incLE_inverse_iff

def DecGraph.inverseOrderIso : DecGraph ≃o DecGraph where
  toFun := DecGraph.inv
  invFun := DecGraph.inv
  left_inv := DecGraph.inv_inv
  right_inv := DecGraph.inv_inv
  map_rel_iff' := decLE_inverse_iff

@[simp] theorem IncGraph.inv_le_inv_iff (f g : IncGraph) : f.inv ≤ g.inv ↔ g ≤ f :=
  incLE_inverse_iff

@[simp] theorem DecGraph.inv_le_inv_iff (f g : DecGraph) : f.inv ≤ g.inv ↔ f ≤ g :=
  decLE_inverse_iff

theorem IncGraph.bddAbove_inv_iff (f : ι → IncGraph) :
    BddAbove (range (fun i => (f i).inv)) ↔ BddBelow (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    have h : g.inv ≤ (f i).inv.inv :=
      IncGraph.inverseOrderIso.monotone (hg (mem_range_self i))
    simpa only [IncGraph.inv_inv] using h
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact IncGraph.inverseOrderIso.monotone (hg (mem_range_self i))

theorem IncGraph.bddBelow_inv_iff (f : ι → IncGraph) :
    BddBelow (range (fun i => (f i).inv)) ↔ BddAbove (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    have h : (f i).inv.inv ≤ g.inv :=
      IncGraph.inverseOrderIso.monotone (hg (mem_range_self i))
    simpa only [IncGraph.inv_inv] using h
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact IncGraph.inverseOrderIso.monotone (hg (mem_range_self i))

theorem DecGraph.bddAbove_inv_iff (f : ι → DecGraph) :
    BddAbove (range (fun i => (f i).inv)) ↔ BddAbove (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    have h : (f i).inv.inv ≤ g.inv :=
      DecGraph.inverseOrderIso.monotone (hg (mem_range_self i))
    simpa only [DecGraph.inv_inv] using h
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact DecGraph.inverseOrderIso.monotone (hg (mem_range_self i))

theorem DecGraph.bddBelow_inv_iff (f : ι → DecGraph) :
    BddBelow (range (fun i => (f i).inv)) ↔ BddBelow (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    have h : g.inv ≤ (f i).inv.inv :=
      DecGraph.inverseOrderIso.monotone (hg (mem_range_self i))
    simpa only [DecGraph.inv_inv] using h
  · rintro ⟨g, hg⟩
    refine ⟨g.inv, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact DecGraph.inverseOrderIso.monotone (hg (mem_range_self i))

theorem IncGraph.inv_iInf (f : ι → IncGraph) (hb : BddBelow (range f)) :
    (⨅ i, f i).inv = ⨆ i, (f i).inv := IncGraph.inverseOrderIso.map_ciInf hb
theorem IncGraph.inv_iSup (f : ι → IncGraph) (hb : BddAbove (range f)) :
    (⨆ i, f i).inv = ⨅ i, (f i).inv := IncGraph.inverseOrderIso.map_ciSup hb
theorem DecGraph.inv_iInf (f : ι → DecGraph) (hb : BddBelow (range f)) :
    (⨅ i, f i).inv = ⨅ i, (f i).inv := DecGraph.inverseOrderIso.map_ciInf hb
theorem DecGraph.inv_iSup (f : ι → DecGraph) (hb : BddAbove (range f)) :
    (⨆ i, f i).inv = ⨆ i, (f i).inv := DecGraph.inverseOrderIso.map_ciSup hb

end

end ScalarMonotone
