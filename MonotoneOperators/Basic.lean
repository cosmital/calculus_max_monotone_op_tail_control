import MonotoneOperators.Defs

open Set

namespace ScalarMonotone

variable {f g : Operator} {x u y v : ℝ}

@[simp] theorem inverse_inverse (f : Operator) : inverse (inverse f) = f := rfl
@[simp] theorem dom_inverse (f : Operator) : dom (inverse f) = ran f := rfl
@[simp] theorem ran_inverse (f : Operator) : ran (inverse f) = dom f := rfl
@[simp] theorem negOut_negOut (f : Operator) : negOut (negOut f) = f := by
  funext x; ext u; simp [negOut]
@[simp] theorem reflect_reflect (f : Operator) : reflect (reflect f) = f := by
  funext x; simp [reflect]

theorem Increasing.le_of_lt (hf : Increasing f) (hu : u ∈ f x)
    (hv : v ∈ f y) (hxy : x < y) : u ≤ v := by
  have h := hf hu hv
  by_contra hn
  have hneg : (x - y) * (u - v) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hxy) (sub_pos.mpr (lt_of_not_ge hn))
  linarith

theorem increasing_iff_order : Increasing f ↔
    ∀ ⦃x u y v : ℝ⦄, u ∈ f x → v ∈ f y → x < y → u ≤ v := by
  constructor
  · exact fun hf _ _ _ _ hu hv hxy => hf.le_of_lt hu hv hxy
  · intro h x u y v hu hv
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy.le)
        (sub_nonpos.mpr (h hu hv hxy))
    · simp
    · exact mul_nonneg (sub_nonneg.mpr hyx.le) (sub_nonneg.mpr (h hv hu hyx))

theorem compatible_iff_bounds : Compatible f x u ↔
    (∀ ⦃y v⦄, v ∈ f y → y < x → v ≤ u) ∧
    (∀ ⦃y v⦄, v ∈ f y → x < y → u ≤ v) := by
  constructor
  · intro h
    constructor
    · intro y v hv hyx
      have h' := h hv
      by_contra hn
      have : (x-y)*(u-v) < 0 := mul_neg_of_pos_of_neg
        (sub_pos.mpr hyx) (sub_neg.mpr (lt_of_not_ge hn))
      linarith
    · intro y v hv hxy
      have h' := h hv
      by_contra hn
      have : (x-y)*(u-v) < 0 := mul_neg_of_neg_of_pos
        (sub_neg.mpr hxy) (sub_pos.mpr (lt_of_not_ge hn))
      linarith
  · rintro ⟨hl, hr⟩ y v hv
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy.le)
        (sub_nonpos.mpr (hr hv hxy))
    · simp
    · exact mul_nonneg (sub_nonneg.mpr hyx.le) (sub_nonneg.mpr (hl hv hyx))

theorem Increasing.compatible (hf : Increasing f) (hu : u ∈ f x) : Compatible f x u :=
  fun {_y _v} hv => hf hu hv

theorem maximal_nonempty (hf : MaximalIncreasing f) : ∃ x u, u ∈ f x := by
  by_contra hn
  have hempty : ∀ x u, u ∉ f x := by simpa using hn
  exact hempty 0 0 (hf.2 (fun {y v} hv => (hempty y v hv).elim))

theorem MaximalIncreasing.eq_of_le (hf : MaximalIncreasing f)
    (hg : Increasing g) (hfg : f ≤ g) : f = g := by
  apply le_antisymm hfg
  intro x u hu
  exact hf.2 (fun {y v} hv => hg hu (hfg _ hv))

/-- Maximality is precisely absence of a proper monotone graph extension. -/
theorem maximal_iff_no_extension : MaximalIncreasing f ↔
    Increasing f ∧ ∀ g : Operator, Increasing g → f ≤ g → f = g := by
  constructor
  · exact fun hf => ⟨hf.1, fun g hg hfg => hf.eq_of_le hg hfg⟩
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro x u hc
    let g : Operator := fun y => {v | v ∈ f y ∨ (y = x ∧ v = u)}
    have hmono : Increasing g := by
      intro a p b q hp hq
      rcases hp with hp | ⟨rfl, rfl⟩ <;> rcases hq with hq | ⟨rfl, rfl⟩
      · exact hf hp hq
      · have := hc hp
        nlinarith
      · exact hc hq
      · simp
    have heq := hmax g hmono (fun _ _ h => Or.inl h)
    rw [heq]
    exact Or.inr ⟨rfl, rfl⟩

theorem maximal_iff_negative_witness : MaximalIncreasing f ↔
    Increasing f ∧ ∀ x u, u ∉ f x → ∃ y v, v ∈ f y ∧ (x-y)*(u-v) < 0 := by
  constructor
  · rintro ⟨hf, hm⟩
    refine ⟨hf, ?_⟩
    intro x u hn
    by_contra h
    have hc : Compatible f x u := by
      intro y v hv
      by_contra hneg
      exact h ⟨y, v, hv, lt_of_not_ge hneg⟩
    exact hn (hm hc)
  · rintro ⟨hf, hm⟩
    refine ⟨hf, ?_⟩
    intro x u hc
    by_contra hn
    obtain ⟨y, v, hv, hneg⟩ := hm x u hn
    exact (not_lt_of_ge (hc hv)) hneg

theorem inverse_increasing (hf : Increasing f) : Increasing (inverse f) := by
  intro x u y v hu hv
  simpa only [mul_comm] using hf hu hv

theorem inverse_maximal (hf : MaximalIncreasing f) : MaximalIncreasing (inverse f) := by
  refine ⟨inverse_increasing hf.1, ?_⟩
  intro x u hc
  apply hf.2
  intro y v hv
  simpa only [mul_comm] using hc (show y ∈ inverse f v from hv)

@[simp] theorem inverse_maximal_iff : MaximalIncreasing (inverse f) ↔ MaximalIncreasing f :=
  ⟨fun h => inverse_maximal h, inverse_maximal⟩

theorem negOut_increasing_iff : Increasing (negOut f) ↔
    ∀ ⦃x u y v : ℝ⦄, u ∈ f x → v ∈ f y → (x-y)*(u-v) ≤ 0 := by
  constructor
  · intro hf x u y v hu hv
    have h := hf (show -u ∈ negOut f x by simpa [negOut] using hu)
      (show -v ∈ negOut f y by simpa [negOut] using hv)
    nlinarith
  · intro hf x u y v hu hv
    have h := hf hu hv
    dsimp [negOut] at hu hv
    nlinarith

theorem reflect_increasing_iff : Increasing (reflect f) ↔ Increasing (negOut f) := by
  rw [negOut_increasing_iff]
  constructor
  · intro hf x u y v hu hv
    have h := hf (show u ∈ reflect f (-x) by simpa [reflect] using hu)
      (show v ∈ reflect f (-y) by simpa [reflect] using hv)
    nlinarith
  · intro hf x u y v hu hv
    have h := hf hu hv
    nlinarith

theorem reflect_maximal_iff : MaximalIncreasing (reflect f) ↔ MaximalDecreasing f := by
  constructor
  · rintro ⟨hm, hx⟩
    refine ⟨reflect_increasing_iff.mp hm, ?_⟩
    intro x u hc
    have hp : -u ∈ reflect f (-x) := hx (by
      intro y v hv
      have h := hc (show -v ∈ negOut f (-y) by simpa [negOut, reflect] using hv)
      nlinarith)
    simpa [reflect, negOut] using hp
  · rintro ⟨hm, hx⟩
    refine ⟨reflect_increasing_iff.mpr hm, ?_⟩
    intro x u hc
    have hp : -u ∈ negOut f (-x) := hx (by
      intro y v hv
      have h := hc (show -v ∈ reflect f (-y) by simpa [reflect, negOut] using hv)
      nlinarith)
    simpa [negOut, reflect] using hp

/-- Fiber characterization without extended-real endpoints. This is exactly
the lower-supremum/upper-infimum interval, including empty and infinite cases. -/
theorem maximal_iff_fibers (hf : Increasing f) : MaximalIncreasing f ↔
    ∀ x u, u ∈ f x ↔
      (∀ ⦃y v⦄, v ∈ f y → y < x → v ≤ u) ∧
      (∀ ⦃y v⦄, v ∈ f y → x < y → u ≤ v) := by
  constructor
  · intro hm x u
    rw [← compatible_iff_bounds]
    exact ⟨hf.compatible, fun h => hm.2 h⟩
  · intro h
    exact ⟨hf, fun {x u} hc => (h x u).mpr (compatible_iff_bounds.mp hc)⟩

theorem maximal_fiber_ordConnected (hf : MaximalIncreasing f) (x : ℝ) :
    (f x).OrdConnected := by
  constructor
  intro u hu v hv w hw
  apply hf.2
  rw [compatible_iff_bounds]
  constructor
  · intro y z hz hyx
    exact (hf.1.le_of_lt hz hu hyx).trans hw.1
  · intro y z hz hxy
    exact hw.2.trans (hf.1.le_of_lt hv hz hxy)

theorem maximal_fiber_closed (hf : MaximalIncreasing f) (x : ℝ) : IsClosed (f x) := by
  have heq : f x = ⋂ (p : ℝ × ℝ) (_ : p.2 ∈ f p.1),
      {u : ℝ | 0 ≤ (x-p.1)*(u-p.2)} := by
    ext u
    simp only [mem_iInter, mem_setOf_eq]
    exact ⟨fun hu p hp => hf.1 hu hp,
      fun h => hf.2 (fun {y v} hv => h (y,v) hv)⟩
  rw [heq]
  exact isClosed_iInter (fun p => isClosed_iInter (fun _ =>
    isClosed_le continuous_const (continuous_const.mul (continuous_id.sub continuous_const))))

noncomputable def lowerEndpoint (f : Operator) (x : ℝ) : EReal :=
  ⨆ (y : ℝ) (_ : y < x) (v : ℝ) (_ : v ∈ f y), (v : EReal)

noncomputable def upperEndpoint (f : Operator) (x : ℝ) : EReal :=
  ⨅ (y : ℝ) (_ : x < y) (v : ℝ) (_ : v ∈ f y), (v : EReal)

/-- The manuscript's fiber formula, with genuinely extended-real endpoints. -/
theorem maximal_fiber_eq_extended_interval (hf : MaximalIncreasing f) (x : ℝ) :
    f x = {u : ℝ | lowerEndpoint f x ≤ (u : EReal) ∧ (u : EReal) ≤ upperEndpoint f x} := by
  ext u
  rw [(maximal_iff_fibers hf.1).mp hf x u]
  simp only [mem_setOf_eq, lowerEndpoint, upperEndpoint, iSup_le_iff, le_iInf_iff,
    EReal.coe_le_coe_iff]
  aesop

theorem inverse_maximal_decreasing (hf : MaximalDecreasing f) :
    MaximalDecreasing (inverse f) := by
  refine ⟨?_, ?_⟩
  · rw [negOut_increasing_iff]
    intro x u y v hu hv
    have h := negOut_increasing_iff.mp hf.1 hu hv
    nlinarith
  · intro x u hc
    have hp : -x ∈ negOut f (-u) := hf.2 (by
      intro y v hv
      have h := hc (show -y ∈ negOut (inverse f) (-v) by
        simpa [negOut, inverse] using hv)
      nlinarith)
    simpa [negOut, inverse] using hp

end ScalarMonotone
