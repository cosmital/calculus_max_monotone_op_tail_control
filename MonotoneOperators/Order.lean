import MonotoneOperators.Interface

/-!
# Pointwise resolvent order

The raw predicates `IncLE` and `DecLE` denote the comparison order of the
manuscript. The existing order on `Operator` remains graph inclusion.
The distinct bundles `IncGraph` and `DecGraph` carry the two comparison
partial orders, including their different conventions on vertical graphs.
-/

open Set

namespace ScalarMonotone

def IncLE (f g : Operator) : Prop :=
  ∀ ⦃x u y v : ℝ⦄, u ∈ f x → v ∈ g y → x < y → u ≤ v

def DecLE (f g : Operator) : Prop :=
  ∀ ⦃x u y v : ℝ⦄, u ∈ f x → v ∈ g y → y < x → u ≤ v

def lowerHull (A : Set ℝ) : Set ℝ := {u | ∃ v ∈ A, u ≤ v}
def upperHull (A : Set ℝ) : Set ℝ := {u | ∃ v ∈ A, v ≤ u}
def IntervalLE (A B : Set ℝ) : Prop :=
  upperHull B ⊆ upperHull A ∧ lowerHull A ⊆ lowerHull B

theorem mem_lowerHull {A : Set ℝ} {x : ℝ} (hx : x ∈ A) : x ∈ lowerHull A :=
  ⟨x, hx, le_rfl⟩

theorem mem_upperHull {A : Set ℝ} {x : ℝ} (hx : x ∈ A) : x ∈ upperHull A :=
  ⟨x, hx, le_rfl⟩

theorem hull_inter_eq {A : Set ℝ} (hA : A.OrdConnected) :
    upperHull A ∩ lowerHull A = A := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hxb⟩⟩
    exact hA.out ha hb ⟨hax, hxb⟩
  · intro hx
    exact ⟨mem_upperHull hx, mem_lowerHull hx⟩

theorem intervalLE_refl (A : Set ℝ) : IntervalLE A A := ⟨Subset.rfl, Subset.rfl⟩

theorem IntervalLE.trans {A B C : Set ℝ} (hAB : IntervalLE A B)
    (hBC : IntervalLE B C) : IntervalLE A C :=
  ⟨hBC.1.trans hAB.1, hAB.2.trans hBC.2⟩

theorem intervalLE_antisymm {A B : Set ℝ} (hA : A.OrdConnected) (hB : B.OrdConnected)
    (hAB : IntervalLE A B) (hBA : IntervalLE B A) : A = B := by
  have hu : upperHull A = upperHull B := Subset.antisymm hBA.1 hAB.1
  have hl : lowerHull A = lowerHull B := Subset.antisymm hAB.2 hBA.2
  rw [← hull_inter_eq hA, hu, hl, hull_inter_eq hB]

theorem incLE_refl {f : Operator} (hf : Increasing f) : IncLE f f :=
  fun _ _ _ _ hu hv hxy => hf.le_of_lt hu hv hxy

theorem decLE_iff_negOut {f g : Operator} : DecLE f g ↔ IncLE (negOut g) (negOut f) := by
  constructor
  · intro h x u y v hu hv hxy
    have := h hv hu hxy
    change -v ≤ -u at this
    linarith
  · intro h x u y v hu hv hyx
    have := h (show -v ∈ negOut g y by simpa [negOut] using hv)
      (show -u ∈ negOut f x by simpa [negOut] using hu) hyx
    linarith

theorem decLE_refl {f : Operator} (hf : Decreasing f) : DecLE f f :=
  decLE_iff_negOut.2 (incLE_refl hf)

/-- Separated-graph characterization of the increasing resolvent order. -/
theorem incLE_iff_resolvent {f g : Operator} (hf : MaximalIncreasing f)
    (hg : MaximalIncreasing g) :
    IncLE f g ↔ ∀ s, resolvent g hg s ≤ resolvent f hf s := by
  constructor
  · intro h s
    by_contra hn
    have := h (resolvent_mem hf s) (resolvent_mem hg s) (lt_of_not_ge hn)
    linarith
  · intro h x u y v hu hv hxy
    have hzx : resolvent g hg (x+u) ≤ x := by
      simpa only [(resolvent_eq_iff hf).2 hu] using h (x+u)
    have := hg.1.le_of_lt (resolvent_mem hg (x+u)) hv (hzx.trans_lt hxy)
    linarith

/-- Separated-graph characterization of the decreasing resolvent order. -/
theorem decLE_iff_resolvent {f g : Operator} (hf : MaximalDecreasing f)
    (hg : MaximalDecreasing g) :
    DecLE f g ↔ ∀ s, decreasingResolvent f hf s ≤ decreasingResolvent g hg s := by
  rw [decLE_iff_negOut, incLE_iff_resolvent hg hf]
  rfl

theorem incLE_trans {f g h : Operator} (hf : MaximalIncreasing f)
    (hg : MaximalIncreasing g) (hh : MaximalIncreasing h)
    (hfg : IncLE f g) (hgh : IncLE g h) : IncLE f h := by
  apply (incLE_iff_resolvent hf hh).2
  intro s
  exact ((incLE_iff_resolvent hg hh).1 hgh s).trans
    ((incLE_iff_resolvent hf hg).1 hfg s)

theorem incLE_antisymm {f g : Operator} (hf : MaximalIncreasing f)
    (hg : MaximalIncreasing g) (hfg : IncLE f g) (hgf : IncLE g f) : f = g := by
  have hJ : resolvent f hf = resolvent g hg := by
    funext s
    exact le_antisymm ((incLE_iff_resolvent hg hf).1 hgf s)
      ((incLE_iff_resolvent hf hg).1 hfg s)
  funext x
  ext u
  rw [← resolvent_eq_iff hf, ← resolvent_eq_iff hg, hJ]

theorem decLE_trans {f g h : Operator} (hf : MaximalDecreasing f)
    (hg : MaximalDecreasing g) (hh : MaximalDecreasing h)
    (hfg : DecLE f g) (hgh : DecLE g h) : DecLE f h :=
  decLE_iff_negOut.2 (incLE_trans hh hg hf
    (decLE_iff_negOut.1 hgh) (decLE_iff_negOut.1 hfg))

theorem decLE_antisymm {f g : Operator} (hf : MaximalDecreasing f)
    (hg : MaximalDecreasing g) (hfg : DecLE f g) (hgf : DecLE g f) : f = g := by
  have heq := incLE_antisymm hf hg (decLE_iff_negOut.1 hgf) (decLE_iff_negOut.1 hfg)
  simpa only [negOut_negOut] using congrArg negOut heq

structure IncGraph where
  val : Operator
  property : MaximalIncreasing val

structure DecGraph where
  val : Operator
  property : MaximalDecreasing val

instance : Coe IncGraph Operator := ⟨IncGraph.val⟩
instance : Coe DecGraph Operator := ⟨DecGraph.val⟩
instance : CoeFun IncGraph (fun _ => ℝ → Set ℝ) := ⟨IncGraph.val⟩
instance : CoeFun DecGraph (fun _ => ℝ → Set ℝ) := ⟨DecGraph.val⟩

@[ext] theorem IncGraph.ext_val {f g : IncGraph} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[ext] theorem DecGraph.ext_val {f g : DecGraph} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : PartialOrder IncGraph where
  le f g := IncLE f.val g.val
  le_refl f := incLE_refl f.property.1
  le_trans f g h := incLE_trans f.property g.property h.property
  le_antisymm f g hfg hgf := IncGraph.ext_val (incLE_antisymm f.property g.property hfg hgf)

instance : PartialOrder DecGraph where
  le f g := DecLE f.val g.val
  le_refl f := decLE_refl f.property.1
  le_trans f g h := decLE_trans f.property g.property h.property
  le_antisymm f g hfg hgf := DecGraph.ext_val (decLE_antisymm f.property g.property hfg hgf)

theorem incLE_inverse_iff {f g : Operator} :
    IncLE (inverse g) (inverse f) ↔ IncLE f g := by
  constructor <;> intro h x u y v hu hv hxy
  · by_contra hn
    have := h (show y ∈ inverse g v from hv) (show x ∈ inverse f u from hu)
      (lt_of_not_ge hn)
    linarith
  · by_contra hn
    have := h (show y ∈ f v from hv) (show x ∈ g u from hu) (lt_of_not_ge hn)
    linarith

theorem decLE_inverse_iff {f g : Operator} :
    DecLE (inverse f) (inverse g) ↔ DecLE f g := by
  constructor <;> intro h x u y v hu hv hyx
  · by_contra hn
    have := h (show x ∈ inverse f u from hu) (show y ∈ inverse g v from hv)
      (lt_of_not_ge hn)
    linarith
  · by_contra hn
    have := h (show x ∈ f u from hu) (show y ∈ g v from hv) (lt_of_not_ge hn)
    linarith

theorem decLE_reflect_iff {f g : Operator} : DecLE (reflect f) (reflect g) ↔ IncLE f g := by
  constructor <;> intro h x u y v hu hv hxy
  · have := h (show u ∈ reflect f (-x) by simpa [reflect] using hu)
      (show v ∈ reflect g (-y) by simpa [reflect] using hv) (by linarith)
    exact this
  · exact h hu hv (by linarith)

theorem incLE_reflect_iff {f g : Operator} : IncLE (reflect f) (reflect g) ↔ DecLE f g := by
  have h := @decLE_reflect_iff (reflect f) (reflect g)
  simpa only [reflect_reflect] using h.symm

theorem Decreasing.le_of_lt {f : Operator} (hf : Decreasing f) {x u y v : ℝ}
    (hu : u ∈ f x) (hv : v ∈ f y) (hxy : x < y) : v ≤ u := by
  have := Increasing.le_of_lt hf (show -u ∈ negOut f x by simpa [negOut] using hu)
    (show -v ∈ negOut f y by simpa [negOut] using hv) hxy
  linarith

def outputScale (c : ℝ) (f : Operator) : Operator := fun x =>
  {v | ∃ u ∈ f x, v = c * u}

theorem outputScale_mem_iff {c x u : ℝ} {f : Operator} (hc : c ≠ 0) :
    u ∈ outputScale c f x ↔ u / c ∈ f x := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [mul_div_cancel_left₀ v hc] using hv
  · intro hu
    exact ⟨u/c, hu, by field_simp⟩

theorem outputScale_increasing {c : ℝ} {f : Operator} (hc : 0 ≤ c) (hf : Increasing f) :
    Increasing (outputScale c f) := by
  apply increasing_iff_order.2
  rintro x u y v ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hxy
  exact mul_le_mul_of_nonneg_left (hf.le_of_lt ha hb hxy) hc

theorem outputScale_maximal {c : ℝ} {f : Operator} (hc : 0 < c)
    (hf : MaximalIncreasing f) : MaximalIncreasing (outputScale c f) := by
  refine ⟨outputScale_increasing hc.le hf.1, ?_⟩
  intro x u hu
  apply (outputScale_mem_iff hc.ne').2
  apply hf.2
  intro y v hv
  have h := hu (show c*v ∈ outputScale c f y from ⟨v, hv, rfl⟩)
  have he : (x-y)*(u-c*v) = c*((x-y)*(u/c-v)) := by field_simp
  rw [he] at h
  exact (mul_nonneg_iff_of_pos_left hc).1 h

theorem negOut_outputScale (c : ℝ) (f : Operator) :
    negOut (outputScale c f) = outputScale c (negOut f) := by
  ext x u
  change (∃ v ∈ f x, -u = c*v) ↔ ∃ v ∈ negOut f x, u = c*v
  constructor
  · rintro ⟨v, hv, hu⟩
    exact ⟨-v, by simpa [negOut] using hv, by nlinarith⟩
  · rintro ⟨v, hv, hu⟩
    exact ⟨-v, hv, by nlinarith⟩

theorem outputScale_maximal_decreasing {c : ℝ} {f : Operator} (hc : 0 < c)
    (hf : MaximalDecreasing f) : MaximalDecreasing (outputScale c f) := by
  change MaximalIncreasing (negOut (outputScale c f))
  rw [negOut_outputScale]
  exact outputScale_maximal hc hf

@[simp] theorem dom_outputScale (c : ℝ) (f : Operator) : dom (outputScale c f) = dom f := by
  ext x
  constructor
  · rintro ⟨v, u, hu, _⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨c*u, u, hu, rfl⟩

theorem incLE_outputScale_iff {c : ℝ} {f g : Operator} (hc : 0 < c) :
    IncLE (outputScale c f) (outputScale c g) ↔ IncLE f g := by
  constructor
  · intro h x u y v hu hv hxy
    have := h (show c*u ∈ outputScale c f x from ⟨u, hu, rfl⟩)
      (show c*v ∈ outputScale c g y from ⟨v, hv, rfl⟩) hxy
    exact (mul_le_mul_left hc).1 this
  · rintro h x u y v ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hxy
    exact mul_le_mul_of_nonneg_left (h ha hb hxy) hc.le

theorem decLE_outputScale_iff {c : ℝ} {f g : Operator} (hc : 0 < c) :
    DecLE (outputScale c f) (outputScale c g) ↔ DecLE f g := by
  rw [decLE_iff_negOut, negOut_outputScale, negOut_outputScale,
    incLE_outputScale_iff hc, decLE_iff_negOut]

/-- Comparison of an increasing resolvent with a nonempty fiber. -/
theorem resolvent_le_iff_lowerHull {f : Operator} (hf : MaximalIncreasing f)
    {x u : ℝ} (hx : x ∈ dom f) :
    resolvent f hf (x+u) ≤ x ↔ u ∈ lowerHull (f x) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · obtain ⟨v, hv⟩ := hx
      have := hf.1.le_of_lt (resolvent_mem hf (x+u)) hv hlt
      exact ⟨v, hv, by linarith⟩
    · exact ⟨u, (resolvent_eq_iff hf).1 heq, le_rfl⟩
  · rintro ⟨v, hv, huv⟩
    have := resolvent_monotone hf (add_le_add_left huv x)
    simpa only [(resolvent_eq_iff hf).2 hv] using this

theorem resolvent_ge_iff_upperHull {f : Operator} (hf : MaximalIncreasing f)
    {x u : ℝ} (hx : x ∈ dom f) :
    x ≤ resolvent f hf (x+u) ↔ u ∈ upperHull (f x) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · obtain ⟨v, hv⟩ := hx
      have := hf.1.le_of_lt hv (resolvent_mem hf (x+u)) hlt
      exact ⟨v, hv, by linarith⟩
    · exact ⟨u, (resolvent_eq_iff hf).1 heq.symm, le_rfl⟩
  · rintro ⟨v, hv, hvu⟩
    have := resolvent_monotone hf (add_le_add_left hvu x)
    simpa only [(resolvent_eq_iff hf).2 hv] using this

theorem decreasingResolvent_ge_iff_lowerHull {f : Operator} (hf : MaximalDecreasing f)
    {x u : ℝ} (hx : x ∈ dom f) :
    x ≤ decreasingResolvent f hf (x-u) ↔ u ∈ lowerHull (f x) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · obtain ⟨v, hv⟩ := hx
      have := Decreasing.le_of_lt hf.1 hv (decreasing_resolvent_mem hf (x-u)) hlt
      exact ⟨v, hv, by linarith⟩
    · exact ⟨u, (decreasing_resolvent_eq_iff hf).1 heq.symm, le_rfl⟩
  · rintro ⟨v, hv, huv⟩
    have := decreasing_resolvent_monotone hf (sub_le_sub_left huv x)
    simpa only [(decreasing_resolvent_eq_iff hf).2 hv] using this

theorem decreasingResolvent_le_iff_upperHull {f : Operator} (hf : MaximalDecreasing f)
    {x u : ℝ} (hx : x ∈ dom f) :
    decreasingResolvent f hf (x-u) ≤ x ↔ u ∈ upperHull (f x) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · obtain ⟨v, hv⟩ := hx
      have := Decreasing.le_of_lt hf.1 (decreasing_resolvent_mem hf (x-u)) hv hlt
      exact ⟨v, hv, by linarith⟩
    · exact ⟨u, (decreasing_resolvent_eq_iff hf).1 heq, le_rfl⟩
  · rintro ⟨v, hv, hvu⟩
    have := decreasing_resolvent_monotone hf (sub_le_sub_left hvu x)
    simpa only [(decreasing_resolvent_eq_iff hf).2 hv] using this

theorem incLE_fiber {f g : Operator} (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : IncLE f g) {x : ℝ} (hxf : x ∈ dom f) (hxg : x ∈ dom g) :
    IntervalLE (f x) (g x) := by
  have hJ := (incLE_iff_resolvent hf hg).1 hfg
  constructor
  · rintro u ⟨v, hv, hvu⟩
    have hj : x ≤ resolvent f hf (x+v) := by
      simpa only [(resolvent_eq_iff hg).2 hv] using hJ (x+v)
    obtain ⟨w, hw, hwv⟩ := (resolvent_ge_iff_upperHull hf hxf).1 hj
    exact ⟨w, hw, hwv.trans hvu⟩
  · rintro u ⟨v, hv, huv⟩
    have hj : resolvent g hg (x+v) ≤ x := by
      simpa only [(resolvent_eq_iff hf).2 hv] using hJ (x+v)
    obtain ⟨w, hw, hvw⟩ := (resolvent_le_iff_lowerHull hg hxg).1 hj
    exact ⟨w, hw, huv.trans hvw⟩

theorem decLE_fiber {f g : Operator} (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : DecLE f g) {x : ℝ} (hxf : x ∈ dom f) (hxg : x ∈ dom g) :
    IntervalLE (f x) (g x) := by
  have hJ := (decLE_iff_resolvent hf hg).1 hfg
  constructor
  · rintro u ⟨v, hv, hvu⟩
    have hj : decreasingResolvent f hf (x-v) ≤ x := by
      simpa only [(decreasing_resolvent_eq_iff hg).2 hv] using hJ (x-v)
    obtain ⟨w, hw, hwv⟩ := (decreasingResolvent_le_iff_upperHull hf hxf).1 hj
    exact ⟨w, hw, hwv.trans hvu⟩
  · rintro u ⟨v, hv, huv⟩
    have hj : x ≤ decreasingResolvent g hg (x-v) := by
      simpa only [(decreasing_resolvent_eq_iff hf).2 hv] using hJ (x-v)
    obtain ⟨w, hw, hvw⟩ := (decreasingResolvent_ge_iff_lowerHull hg hxg).1 hj
    exact ⟨w, hw, huv.trans hvw⟩

end ScalarMonotone
