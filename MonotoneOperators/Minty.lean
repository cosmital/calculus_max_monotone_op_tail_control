import MonotoneOperators.Basic

/-!
# Scalar Minty representation

The surjectivity argument uses conditional completeness of the real line,
through mathlib's `exists_between_of_forall_le`. No Hilbert-space Minty
theorem is assumed.
-/

open Set

namespace ScalarMonotone

variable {f : Operator}

/-- Monotonicity orders the lower and upper bounds for a prescribed Minty parameter. -/
private theorem minty_lower_le_upper (hf : Increasing f)
    {a u b v : ℝ} (hu : u ∈ f a) (hv : v ∈ f b) (s : ℝ) :
    min a (s - u) ≤ max b (s - v) := by
  by_contra h
  have hh : max b (s - v) < min a (s - u) := lt_of_not_ge h
  have hba : b < a :=
    (le_max_left b (s - v)).trans_lt (hh.trans_le (min_le_left a (s - u)))
  have hvu : s - v < s - u :=
    (le_max_right b (s - v)).trans_lt (hh.trans_le (min_le_right a (s - u)))
  have horder := hf.le_of_lt hv hu hba
  linarith

/-- Every real number is the sum of the two coordinates of a maximal increasing graph point. -/
theorem minty_surjective (hf : MaximalIncreasing f) (s : ℝ) :
    ∃ x, s - x ∈ f x := by
  let L : Set ℝ := {l | ∃ y v, v ∈ f y ∧ l = min y (s - v)}
  let U : Set ℝ := {u | ∃ y v, v ∈ f y ∧ u = max y (s - v)}
  obtain ⟨a, b, hab⟩ := maximal_nonempty hf
  have hL : L.Nonempty := ⟨min a (s - b), a, b, hab, rfl⟩
  have hU : U.Nonempty := ⟨max a (s - b), a, b, hab, rfl⟩
  have hLU : ∀ l ∈ L, ∀ u ∈ U, l ≤ u := by
    rintro l ⟨y, v, hv, rfl⟩ u ⟨z, w, hw, rfl⟩
    exact minty_lower_le_upper hf.1 hv hw s
  obtain ⟨x, hxL, hxU⟩ := exists_between_of_forall_le hL hU hLU
  refine ⟨x, hf.2 ?_⟩
  intro y v hv
  have hl : min y (s - v) ≤ x := hxL ⟨y, v, hv, rfl⟩
  have hu : x ≤ max y (s - v) := hxU ⟨y, v, hv, rfl⟩
  rcases le_total y (s - v) with h | h
  · rw [min_eq_left h] at hl
    rw [max_eq_right h] at hu
    exact mul_nonneg (by linarith) (by linarith)
  · rw [min_eq_right h] at hl
    rw [max_eq_left h] at hu
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- A monotone graph with every Minty parameter is maximal. -/
theorem maximal_of_minty (hf : Increasing f)
    (hs : ∀ s : ℝ, ∃ x, s - x ∈ f x) : MaximalIncreasing f := by
  refine ⟨hf, ?_⟩
  intro x u hc
  obtain ⟨y, hy⟩ := hs (x + u)
  have h := hc hy
  have hz : (x - y) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y)]
  have hxy : x = y := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  simpa [hxy] using hy

/-- Scalar Minty's criterion. -/
theorem maximal_iff_minty (hf : Increasing f) :
    MaximalIncreasing f ↔ ∀ s : ℝ, ∃ x, s - x ∈ f x :=
  ⟨minty_surjective, maximal_of_minty hf⟩

/-- A Minty parameter determines at most one input coordinate. -/
theorem minty_unique (hf : Increasing f) {s x y : ℝ}
    (hx : s - x ∈ f x) (hy : s - y ∈ f y) : x = y := by
  have h := hf hx hy
  have hz : (x - y) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- The everywhere-defined single-valued resolvent of a maximal increasing graph. -/
noncomputable def resolvent (f : Operator) (hf : MaximalIncreasing f) (s : ℝ) : ℝ :=
  Classical.choose (minty_surjective hf s)

theorem resolvent_mem (hf : MaximalIncreasing f) (s : ℝ) :
    s - resolvent f hf s ∈ f (resolvent f hf s) :=
  Classical.choose_spec (minty_surjective hf s)

/-- Membership in the original graph is the resolvent identity. -/
theorem resolvent_eq_iff (hf : MaximalIncreasing f) {x u : ℝ} :
    resolvent f hf (x + u) = x ↔ u ∈ f x := by
  constructor
  · intro h
    simpa [h] using resolvent_mem hf (x + u)
  · intro hu
    exact minty_unique hf.1 (resolvent_mem hf (x + u)) (by simpa using hu)

theorem resolvent_monotone (hf : MaximalIncreasing f) : Monotone (resolvent f hf) := by
  intro s t hst
  by_contra h
  have hj : resolvent f hf t < resolvent f hf s := lt_of_not_ge h
  have hu := hf.1.le_of_lt (resolvent_mem hf t) (resolvent_mem hf s) hj
  linarith

theorem resolvent_complement_monotone (hf : MaximalIncreasing f) :
    Monotone (fun s => s - resolvent f hf s) := by
  intro s t hst
  change s - resolvent f hf s ≤ t - resolvent f hf t
  rcases lt_or_eq_of_le (resolvent_monotone hf hst) with h | h
  · exact hf.1.le_of_lt (resolvent_mem hf s) (resolvent_mem hf t) h
  · linarith

theorem resolvent_lipschitz (hf : MaximalIncreasing f) : LipschitzWith 1 (resolvent f hf) := by
  apply LipschitzWith.mk_one
  intro s t
  rcases le_total s t with hst | hts
  · have hj := resolvent_monotone hf hst
    have hu := resolvent_complement_monotone hf hst
    dsimp only at hu
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hj),
      abs_of_nonpos (sub_nonpos.mpr hst)]
    linarith
  · have hj := resolvent_monotone hf hts
    have hu := resolvent_complement_monotone hf hts
    dsimp only at hu
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hj),
      abs_of_nonneg (sub_nonneg.mpr hts)]
    linarith

theorem resolvent_continuous (hf : MaximalIncreasing f) : Continuous (resolvent f hf) :=
  (resolvent_lipschitz hf).continuous

theorem dom_eq_range_resolvent (hf : MaximalIncreasing f) :
    dom f = Set.range (resolvent f hf) := by
  ext x
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨x + u, (resolvent_eq_iff hf).mpr hu⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s - resolvent f hf s, resolvent_mem hf s⟩

theorem ran_eq_range_resolvent_complement (hf : MaximalIncreasing f) :
    ran f = Set.range (fun s => s - resolvent f hf s) := by
  ext u
  constructor
  · rintro ⟨x, hu⟩
    refine ⟨x + u, ?_⟩
    dsimp only
    rw [(resolvent_eq_iff hf).mpr hu]
    ring
  · rintro ⟨s, rfl⟩
    exact ⟨resolvent f hf s, resolvent_mem hf s⟩

theorem dom_ordConnected (hf : MaximalIncreasing f) : (dom f).OrdConnected := by
  rw [dom_eq_range_resolvent hf]
  exact (isPreconnected_range (resolvent_continuous hf)).ordConnected

theorem ran_ordConnected (hf : MaximalIncreasing f) : (ran f).OrdConnected := by
  rw [ran_eq_range_resolvent_complement hf]
  exact (isPreconnected_range (continuous_id.sub (resolvent_continuous hf))).ordConnected

theorem graph_eq_range_minty (hf : MaximalIncreasing f) :
    graph f = Set.range (fun s => (resolvent f hf s, s - resolvent f hf s)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p.1 + p.2, ?_⟩
    have h := (resolvent_eq_iff hf).mpr hp
    apply Prod.ext
    · exact h
    · dsimp
      rw [h]
      ring
  · rintro ⟨s, rfl⟩
    exact resolvent_mem hf s

theorem graph_closed (hf : MaximalIncreasing f) : IsClosed (graph f) := by
  have heq : graph f = {p : ℝ × ℝ | resolvent f hf (p.1 + p.2) = p.1} := by
    ext p
    exact (resolvent_eq_iff hf).symm
  rw [heq]
  exact isClosed_eq ((resolvent_continuous hf).comp (continuous_fst.add continuous_snd))
    continuous_fst

theorem graph_connected (hf : MaximalIncreasing f) : IsConnected (graph f) := by
  rw [graph_eq_range_minty hf]
  exact isConnected_range ((resolvent_continuous hf).prodMk
    (continuous_id.sub (resolvent_continuous hf)))

/-- The Minty parametrization is a homeomorphism from the real line onto the graph. -/
noncomputable def mintyHomeomorph (f : Operator) (hf : MaximalIncreasing f) :
    ℝ ≃ₜ graph f where
  toFun s := ⟨(resolvent f hf s, s - resolvent f hf s), resolvent_mem hf s⟩
  invFun p := p.val.1 + p.val.2
  left_inv s := by dsimp; ring
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (resolvent_eq_iff hf).mpr p.property
    · dsimp
      rw [(resolvent_eq_iff hf).mpr p.property]
      ring
  continuous_toFun := ((resolvent_continuous hf).prodMk
    (continuous_id.sub (resolvent_continuous hf))).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).add
    (continuous_snd.comp continuous_subtype_val)

/-- The graph constructed from a prospective resolvent. -/
def ofResolvent (J : ℝ → ℝ) : Operator := fun x => {u | J (x + u) = x}

theorem ofResolvent_increasing {J : ℝ → ℝ} (hJ : Monotone J)
    (hLip : LipschitzWith 1 J) : Increasing (ofResolvent J) := by
  intro x u y v hu hv
  change J (x + u) = x at hu
  change J (y + v) = y at hv
  have hd := hLip.dist_le_mul (x + u) (y + v)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, hu, hv] at hd
  rcases le_total (x + u) (y + v) with hs | hs
  · have hxy : x ≤ y := by simpa [hu, hv] using hJ hs
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hs)] at hd
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have hyx : y ≤ x := by simpa [hu, hv] using hJ hs
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr hs)] at hd
    exact mul_nonneg (by linarith) (by linarith)

/-- Every monotone nonexpansive real function is a resolvent. -/
theorem ofResolvent_maximal {J : ℝ → ℝ} (hJ : Monotone J)
    (hLip : LipschitzWith 1 J) : MaximalIncreasing (ofResolvent J) := by
  apply maximal_of_minty (ofResolvent_increasing hJ hLip)
  intro s
  exact ⟨J s, by simp [ofResolvent]⟩

theorem resolvent_ofResolvent {J : ℝ → ℝ} (hJ : Monotone J)
    (hLip : LipschitzWith 1 J) :
    resolvent (ofResolvent J) (ofResolvent_maximal hJ hLip) = J := by
  funext s
  exact minty_unique (ofResolvent_increasing hJ hLip)
    (resolvent_mem (ofResolvent_maximal hJ hLip) s) (by simp [ofResolvent])

/-- Scalar Minty's full single-valued correspondence, without assuming maximality in advance. -/
theorem maximal_iff_resolvent : MaximalIncreasing f ↔
    ∃ J : ℝ → ℝ, Monotone J ∧ LipschitzWith 1 J ∧
      ∀ x u, u ∈ f x ↔ J (x + u) = x := by
  constructor
  · intro hf
    exact ⟨resolvent f hf, resolvent_monotone hf, resolvent_lipschitz hf,
      fun _ _ => (resolvent_eq_iff hf).symm⟩
  · rintro ⟨J, hJ, hLip, hgraph⟩
    have heq : f = ofResolvent J := by
      funext x
      ext u
      exact hgraph x u
    rw [heq]
    exact ofResolvent_maximal hJ hLip

/-- The decreasing resolvent is the increasing resolvent of the negated output graph. -/
noncomputable def decreasingResolvent (f : Operator) (hf : MaximalDecreasing f) : ℝ → ℝ :=
  resolvent (negOut f) hf

theorem decreasing_resolvent_mem (hf : MaximalDecreasing f) (s : ℝ) :
    decreasingResolvent f hf s - s ∈ f (decreasingResolvent f hf s) := by
  have h := resolvent_mem hf s
  simpa [decreasingResolvent, negOut] using h

theorem decreasing_resolvent_eq_iff (hf : MaximalDecreasing f) {x u : ℝ} :
    decreasingResolvent f hf (x - u) = x ↔ u ∈ f x := by
  have h := resolvent_eq_iff hf (x := x) (u := -u)
  simpa [decreasingResolvent, negOut, sub_eq_add_neg] using h

theorem decreasing_resolvent_monotone (hf : MaximalDecreasing f) :
    Monotone (decreasingResolvent f hf) := resolvent_monotone hf

theorem decreasing_resolvent_lipschitz (hf : MaximalDecreasing f) :
    LipschitzWith 1 (decreasingResolvent f hf) := resolvent_lipschitz hf

theorem decreasing_resolvent_continuous (hf : MaximalDecreasing f) :
    Continuous (decreasingResolvent f hf) := resolvent_continuous hf

theorem maximal_decreasing_iff_resolvent : MaximalDecreasing f ↔
    ∃ J : ℝ → ℝ, Monotone J ∧ LipschitzWith 1 J ∧
      ∀ x u, u ∈ f x ↔ J (x - u) = x := by
  constructor
  · intro hf
    exact ⟨decreasingResolvent f hf, decreasing_resolvent_monotone hf,
      decreasing_resolvent_lipschitz hf, fun _ _ => (decreasing_resolvent_eq_iff hf).symm⟩
  · rintro ⟨J, hJ, hLip, hgraph⟩
    apply (maximal_iff_resolvent (f := negOut f)).mpr
    refine ⟨J, hJ, hLip, ?_⟩
    intro x u
    change -u ∈ f x ↔ J (x + u) = x
    simpa using hgraph x (-u)

theorem decreasing_graph_eq_range_minty (hf : MaximalDecreasing f) :
    graph f = Set.range (fun s =>
      (decreasingResolvent f hf s, decreasingResolvent f hf s - s)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p.1 - p.2, ?_⟩
    have h := (decreasing_resolvent_eq_iff hf).mpr hp
    apply Prod.ext
    · exact h
    · dsimp
      rw [h]
      ring
  · rintro ⟨s, rfl⟩
    exact decreasing_resolvent_mem hf s

theorem decreasing_graph_closed (hf : MaximalDecreasing f) : IsClosed (graph f) := by
  have heq : graph f = {p : ℝ × ℝ | decreasingResolvent f hf (p.1 - p.2) = p.1} := by
    ext p
    exact (decreasing_resolvent_eq_iff hf).symm
  rw [heq]
  exact isClosed_eq ((decreasing_resolvent_continuous hf).comp
    (continuous_fst.sub continuous_snd)) continuous_fst

theorem decreasing_graph_connected (hf : MaximalDecreasing f) : IsConnected (graph f) := by
  rw [decreasing_graph_eq_range_minty hf]
  exact isConnected_range ((decreasing_resolvent_continuous hf).prodMk
    ((decreasing_resolvent_continuous hf).sub continuous_id))

theorem decreasing_dom_ordConnected (hf : MaximalDecreasing f) : (dom f).OrdConnected := by
  have heq : dom (negOut f) = dom f := by
    ext x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨-u, hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨-u, by simpa [negOut] using hu⟩
  rw [← heq]
  exact dom_ordConnected hf

theorem decreasing_ran_ordConnected (hf : MaximalDecreasing f) : (ran f).OrdConnected := by
  simpa only [dom_inverse] using
    decreasing_dom_ordConnected (inverse_maximal_decreasing hf)

theorem decreasing_fiber_ordConnected (hf : MaximalDecreasing f) (x : ℝ) :
    (f x).OrdConnected := by
  constructor
  intro u hu v hv w hw
  have hnu : -u ∈ negOut f x := by simpa [negOut] using hu
  have hnv : -v ∈ negOut f x := by simpa [negOut] using hv
  have hnw := (maximal_fiber_ordConnected hf x).out hnv hnu
    (show -w ∈ Icc (-v) (-u) by constructor <;> linarith [hw.1, hw.2])
  simpa [negOut] using hnw

theorem decreasing_fiber_closed (hf : MaximalDecreasing f) (x : ℝ) : IsClosed (f x) := by
  have heq : f x = (fun u : ℝ => -u) ⁻¹' (negOut f x) := by
    ext u
    simp [negOut]
  rw [heq]
  exact (maximal_fiber_closed hf x).preimage continuous_neg

/-- The decreasing Minty parametrization, with parameter `x-u`. -/
noncomputable def decreasingMintyHomeomorph (f : Operator) (hf : MaximalDecreasing f) :
    ℝ ≃ₜ graph f where
  toFun s := ⟨(decreasingResolvent f hf s, decreasingResolvent f hf s - s),
    decreasing_resolvent_mem hf s⟩
  invFun p := p.val.1 - p.val.2
  left_inv s := by dsimp; ring
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (decreasing_resolvent_eq_iff hf).mpr p.property
    · dsimp
      rw [(decreasing_resolvent_eq_iff hf).mpr p.property]
      ring
  continuous_toFun := ((decreasing_resolvent_continuous hf).prodMk
    ((decreasing_resolvent_continuous hf).sub continuous_id)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).sub
    (continuous_snd.comp continuous_subtype_val)

end ScalarMonotone
