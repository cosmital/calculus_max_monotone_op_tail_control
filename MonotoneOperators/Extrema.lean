import MonotoneOperators.Order
import MonotoneOperators.ResolventEnvelopes

/-!
# Conditional completeness of the pointwise resolvent order

Both orientation classes are distributive, conditionally complete lattices.
The definitions below construct bounded extrema from the scalar envelopes;
all universal properties therefore concern the comparison order, not graph
inclusion.
-/

namespace ScalarMonotone

open Set

noncomputable section

def IncGraph.J (f : IncGraph) : ℝ → ℝ := resolvent f.val f.property
def DecGraph.J (f : DecGraph) : ℝ → ℝ := decreasingResolvent f.val f.property

theorem IncGraph.monotone_J (f : IncGraph) : Monotone f.J := resolvent_monotone f.property
theorem DecGraph.monotone_J (f : DecGraph) : Monotone f.J :=
  decreasing_resolvent_monotone f.property
theorem IncGraph.lipschitz_J (f : IncGraph) : LipschitzWith 1 f.J :=
  resolvent_lipschitz f.property
theorem DecGraph.lipschitz_J (f : DecGraph) : LipschitzWith 1 f.J :=
  decreasing_resolvent_lipschitz f.property

theorem IncGraph.le_iff_J {f g : IncGraph} : f ≤ g ↔ ∀ s, g.J s ≤ f.J s :=
  incLE_iff_resolvent f.property g.property
theorem DecGraph.le_iff_J {f g : DecGraph} : f ≤ g ↔ ∀ s, f.J s ≤ g.J s :=
  decLE_iff_resolvent f.property g.property

theorem IncGraph.J_injective : Function.Injective IncGraph.J := by
  intro f g h
  exact le_antisymm (IncGraph.le_iff_J.mpr (fun s => le_of_eq (congrFun h s).symm))
    (IncGraph.le_iff_J.mpr (fun s => le_of_eq (congrFun h s)))

theorem DecGraph.J_injective : Function.Injective DecGraph.J := by
  intro f g h
  exact le_antisymm (DecGraph.le_iff_J.mpr (fun s => le_of_eq (congrFun h s)))
    (DecGraph.le_iff_J.mpr (fun s => le_of_eq (congrFun h s).symm))

def IncGraph.ofJ (q : ℝ → ℝ) (hm : Monotone q) (hl : LipschitzWith 1 q) : IncGraph :=
  ⟨ofResolvent q, ofResolvent_maximal hm hl⟩

def DecGraph.ofJ (q : ℝ → ℝ) (hm : Monotone q) (hl : LipschitzWith 1 q) : DecGraph :=
  ⟨fun x => {u | q (x - u) = x}, maximal_decreasing_iff_resolvent.mpr
    ⟨q, hm, hl, fun _ _ => Iff.rfl⟩⟩

@[simp] theorem IncGraph.J_ofJ (q : ℝ → ℝ) (hm : Monotone q) (hl : LipschitzWith 1 q) :
    (IncGraph.ofJ q hm hl).J = q := resolvent_ofResolvent hm hl

@[simp] theorem DecGraph.J_ofJ (q : ℝ → ℝ) (hm : Monotone q) (hl : LipschitzWith 1 q) :
    (DecGraph.ofJ q hm hl).J = q := by
  funext s
  have h : q s - s ∈ (DecGraph.ofJ q hm hl).val (q s) := by
    change q (q s - (q s - s)) = q s
    simp
  simpa [DecGraph.J] using (decreasing_resolvent_eq_iff
    (DecGraph.ofJ q hm hl).property).mpr h

def IncGraph.infimum (f g : IncGraph) : IncGraph :=
  IncGraph.ofJ (fun s => max (f.J s) (g.J s)) (f.monotone_J.max g.monotone_J)
    (by simpa using f.lipschitz_J.max g.lipschitz_J)
def IncGraph.supremum (f g : IncGraph) : IncGraph :=
  IncGraph.ofJ (fun s => min (f.J s) (g.J s)) (f.monotone_J.min g.monotone_J)
    (by simpa using f.lipschitz_J.min g.lipschitz_J)
def DecGraph.infimum (f g : DecGraph) : DecGraph :=
  DecGraph.ofJ (fun s => min (f.J s) (g.J s)) (f.monotone_J.min g.monotone_J)
    (by simpa using f.lipschitz_J.min g.lipschitz_J)
def DecGraph.supremum (f g : DecGraph) : DecGraph :=
  DecGraph.ofJ (fun s => max (f.J s) (g.J s)) (f.monotone_J.max g.monotone_J)
    (by simpa using f.lipschitz_J.max g.lipschitz_J)

instance : Lattice IncGraph where
  __ := inferInstanceAs (PartialOrder IncGraph)
  inf := IncGraph.infimum
  sup := IncGraph.supremum
  inf_le_left f g := IncGraph.le_iff_J.mpr (by simp [IncGraph.infimum])
  inf_le_right f g := IncGraph.le_iff_J.mpr (by simp [IncGraph.infimum])
  le_inf f g h hfg hfh := IncGraph.le_iff_J.mpr (by
    intro s
    simpa [IncGraph.infimum] using max_le
      (IncGraph.le_iff_J.mp hfg s) (IncGraph.le_iff_J.mp hfh s))
  le_sup_left f g := IncGraph.le_iff_J.mpr (by simp [IncGraph.supremum])
  le_sup_right f g := IncGraph.le_iff_J.mpr (by simp [IncGraph.supremum])
  sup_le f g h hfh hgh := IncGraph.le_iff_J.mpr (by
    intro s
    simpa [IncGraph.supremum] using le_min
      (IncGraph.le_iff_J.mp hfh s) (IncGraph.le_iff_J.mp hgh s))

instance : Lattice DecGraph where
  __ := inferInstanceAs (PartialOrder DecGraph)
  inf := DecGraph.infimum
  sup := DecGraph.supremum
  inf_le_left f g := DecGraph.le_iff_J.mpr (by simp [DecGraph.infimum])
  inf_le_right f g := DecGraph.le_iff_J.mpr (by simp [DecGraph.infimum])
  le_inf f g h hfg hfh := DecGraph.le_iff_J.mpr (by
    intro s
    simpa [DecGraph.infimum] using le_min
      (DecGraph.le_iff_J.mp hfg s) (DecGraph.le_iff_J.mp hfh s))
  le_sup_left f g := DecGraph.le_iff_J.mpr (by simp [DecGraph.supremum])
  le_sup_right f g := DecGraph.le_iff_J.mpr (by simp [DecGraph.supremum])
  sup_le f g h hfh hgh := DecGraph.le_iff_J.mpr (by
    intro s
    simpa [DecGraph.supremum] using max_le
      (DecGraph.le_iff_J.mp hfh s) (DecGraph.le_iff_J.mp hgh s))

@[simp] theorem IncGraph.J_inf (f g : IncGraph) (s : ℝ) :
    (f ⊓ g).J s = max (f.J s) (g.J s) := by
  change (IncGraph.infimum f g).J s = _
  simp [IncGraph.infimum]
@[simp] theorem IncGraph.J_sup (f g : IncGraph) (s : ℝ) :
    (f ⊔ g).J s = min (f.J s) (g.J s) := by
  change (IncGraph.supremum f g).J s = _
  simp [IncGraph.supremum]
@[simp] theorem DecGraph.J_inf (f g : DecGraph) (s : ℝ) :
    (f ⊓ g).J s = min (f.J s) (g.J s) := by
  change (DecGraph.infimum f g).J s = _
  simp [DecGraph.infimum]
@[simp] theorem DecGraph.J_sup (f g : DecGraph) (s : ℝ) :
    (f ⊔ g).J s = max (f.J s) (g.J s) := by
  change (DecGraph.supremum f g).J s = _
  simp [DecGraph.supremum]

instance : DistribLattice IncGraph where
  __ := inferInstanceAs (Lattice IncGraph)
  le_sup_inf f g h := IncGraph.le_iff_J.mpr (by
    intro s
    simp only [IncGraph.J_inf, IncGraph.J_sup]
    exact le_of_eq (min_max_distrib_left _ _ _))

instance : DistribLattice DecGraph where
  __ := inferInstanceAs (Lattice DecGraph)
  le_sup_inf f g h := DecGraph.le_iff_J.mpr (by
    intro s
    simp only [DecGraph.J_inf, DecGraph.J_sup]
    exact le_of_eq (max_min_distrib_left _ _ _).symm)

variable {ι : Type*} [Nonempty ι]

theorem incFamily_boundedAbove_J (f : ι → IncGraph) (h : BddBelow (range f)) (s : ℝ) :
    BddAbove (range (fun i => (f i).J s)) := by
  rcases h with ⟨g, hg⟩
  refine ⟨g.J s, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact IncGraph.le_iff_J.mp (hg (mem_range_self i)) s

theorem incFamily_boundedBelow_J (f : ι → IncGraph) (h : BddAbove (range f)) (s : ℝ) :
    BddBelow (range (fun i => (f i).J s)) := by
  rcases h with ⟨g, hg⟩
  refine ⟨g.J s, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact IncGraph.le_iff_J.mp (hg (mem_range_self i)) s

theorem decFamily_boundedBelow_J (f : ι → DecGraph) (h : BddBelow (range f)) (s : ℝ) :
    BddBelow (range (fun i => (f i).J s)) := by
  rcases h with ⟨g, hg⟩
  refine ⟨g.J s, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact DecGraph.le_iff_J.mp (hg (mem_range_self i)) s

theorem decFamily_boundedAbove_J (f : ι → DecGraph) (h : BddAbove (range f)) (s : ℝ) :
    BddAbove (range (fun i => (f i).J s)) := by
  rcases h with ⟨g, hg⟩
  refine ⟨g.J s, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact DecGraph.le_iff_J.mp (hg (mem_range_self i)) s

def incInf (f : ι → IncGraph) (h : BddBelow (range f)) : IncGraph :=
  IncGraph.ofJ (fun s => ⨆ i, (f i).J s)
    (monotone_ciSup (fun i => (f i).monotone_J) (incFamily_boundedAbove_J f h))
    (lipschitz_ciSup (fun i => (f i).lipschitz_J) (incFamily_boundedAbove_J f h))
def incSup (f : ι → IncGraph) (h : BddAbove (range f)) : IncGraph :=
  IncGraph.ofJ (fun s => ⨅ i, (f i).J s)
    (monotone_ciInf (fun i => (f i).monotone_J) (incFamily_boundedBelow_J f h))
    (lipschitz_ciInf (fun i => (f i).lipschitz_J) (incFamily_boundedBelow_J f h))
def decInf (f : ι → DecGraph) (h : BddBelow (range f)) : DecGraph :=
  DecGraph.ofJ (fun s => ⨅ i, (f i).J s)
    (monotone_ciInf (fun i => (f i).monotone_J) (decFamily_boundedBelow_J f h))
    (lipschitz_ciInf (fun i => (f i).lipschitz_J) (decFamily_boundedBelow_J f h))
def decSup (f : ι → DecGraph) (h : BddAbove (range f)) : DecGraph :=
  DecGraph.ofJ (fun s => ⨆ i, (f i).J s)
    (monotone_ciSup (fun i => (f i).monotone_J) (decFamily_boundedAbove_J f h))
    (lipschitz_ciSup (fun i => (f i).lipschitz_J) (decFamily_boundedAbove_J f h))

@[simp] theorem incInf_resolvent (f : ι → IncGraph) (h : BddBelow (range f)) (s : ℝ) :
    (incInf f h).J s = ⨆ i, (f i).J s := by simp [incInf]
@[simp] theorem incSup_resolvent (f : ι → IncGraph) (h : BddAbove (range f)) (s : ℝ) :
    (incSup f h).J s = ⨅ i, (f i).J s := by simp [incSup]
@[simp] theorem decInf_resolvent (f : ι → DecGraph) (h : BddBelow (range f)) (s : ℝ) :
    (decInf f h).J s = ⨅ i, (f i).J s := by simp [decInf]
@[simp] theorem decSup_resolvent (f : ι → DecGraph) (h : BddAbove (range f)) (s : ℝ) :
    (decSup f h).J s = ⨆ i, (f i).J s := by simp [decSup]

theorem incInf_isGLB (f : ι → IncGraph) (h : BddBelow (range f)) :
    IsGLB (range f) (incInf f h) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact IncGraph.le_iff_J.mpr (fun s => by
      rw [incInf_resolvent]
      exact le_ciSup (incFamily_boundedAbove_J f h s) i)
  · intro g hg
    exact IncGraph.le_iff_J.mpr (fun s => by
      rw [incInf_resolvent]
      exact ciSup_le (fun i => IncGraph.le_iff_J.mp (hg (mem_range_self i)) s))

theorem incSup_isLUB (f : ι → IncGraph) (h : BddAbove (range f)) :
    IsLUB (range f) (incSup f h) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact IncGraph.le_iff_J.mpr (fun s => by
      rw [incSup_resolvent]
      exact ciInf_le (incFamily_boundedBelow_J f h s) i)
  · intro g hg
    exact IncGraph.le_iff_J.mpr (fun s => by
      rw [incSup_resolvent]
      exact le_ciInf (fun i => IncGraph.le_iff_J.mp (hg (mem_range_self i)) s))

theorem decInf_isGLB (f : ι → DecGraph) (h : BddBelow (range f)) :
    IsGLB (range f) (decInf f h) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact DecGraph.le_iff_J.mpr (fun s => by
      rw [decInf_resolvent]
      exact ciInf_le (decFamily_boundedBelow_J f h s) i)
  · intro g hg
    exact DecGraph.le_iff_J.mpr (fun s => by
      rw [decInf_resolvent]
      exact le_ciInf (fun i => DecGraph.le_iff_J.mp (hg (mem_range_self i)) s))

theorem decSup_isLUB (f : ι → DecGraph) (h : BddAbove (range f)) :
    IsLUB (range f) (decSup f h) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact DecGraph.le_iff_J.mpr (fun s => by
      rw [decSup_resolvent]
      exact le_ciSup (decFamily_boundedAbove_J f h s) i)
  · intro g hg
    exact DecGraph.le_iff_J.mpr (fun s => by
      rw [decSup_resolvent]
      exact ciSup_le (fun i => DecGraph.le_iff_J.mp (hg (mem_range_self i)) s))

theorem inc_exists_isGLB_iff (f : ι → IncGraph) :
    (∃ g, IsGLB (range f) g) ↔ BddBelow (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.1⟩
  · intro h
    exact ⟨incInf f h, incInf_isGLB f h⟩

theorem inc_exists_isLUB_iff (f : ι → IncGraph) :
    (∃ g, IsLUB (range f) g) ↔ BddAbove (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.1⟩
  · intro h
    exact ⟨incSup f h, incSup_isLUB f h⟩

theorem dec_exists_isGLB_iff (f : ι → DecGraph) :
    (∃ g, IsGLB (range f) g) ↔ BddBelow (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.1⟩
  · intro h
    exact ⟨decInf f h, decInf_isGLB f h⟩

theorem dec_exists_isLUB_iff (f : ι → DecGraph) :
    (∃ g, IsLUB (range f) g) ↔ BddAbove (range f) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.1⟩
  · intro h
    exact ⟨decSup f h, decSup_isLUB f h⟩

end

end ScalarMonotone
