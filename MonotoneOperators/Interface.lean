import MonotoneOperators.ProductsDual
import MonotoneOperators.CompositionMaximal
import MonotoneOperators.Completion
import MonotoneOperators.Survival

/-!
# The manuscript's relational notation

These interface lemmas identify the functional resolvents with the relational
inverses appearing in the Minty table. They also state maximality directly in
the decreasing orientation and record the constant and vertical graphs.
-/

open Set

namespace ScalarMonotone

variable {f g : Operator}

/-- The increasing resolvent is exactly the relational inverse `(id + f)⁻¹`. -/
theorem inverse_identity_add_eq_resolvent (hf : MaximalIncreasing f) :
    inverse (add identity f) = ofFun (resolvent f hf) := by
  ext s x
  change s ∈ add identity f x ↔ x = resolvent f hf s
  constructor
  · rintro ⟨u, hu, v, hv, hs⟩
    have hux : u = x := hu
    subst u
    rw [hs]
    exact ((resolvent_eq_iff hf).2 hv).symm
  · intro hx
    refine ⟨x, rfl, s - x, ?_, by ring⟩
    simpa only [hx] using resolvent_mem hf s

/-- The decreasing resolvent is exactly the relational inverse `(id - f)⁻¹`. -/
theorem inverse_identity_sub_eq_decreasingResolvent (hf : MaximalDecreasing f) :
    inverse (add identity (negOut f)) = ofFun (decreasingResolvent f hf) :=
  inverse_identity_add_eq_resolvent hf

theorem MaximalDecreasing.eq_of_le (hf : MaximalDecreasing f)
    (hg : Decreasing g) (hfg : f ≤ g) : f = g := by
  have hneg : negOut f ≤ negOut g := fun x _ hu => hfg x hu
  have heq := MaximalIncreasing.eq_of_le hf hg hneg
  have h := congrArg negOut heq
  simpa using h

/-- No proper decreasing graph extension is equivalent to maximal decreasingness. -/
theorem maximalDecreasing_iff_no_extension : MaximalDecreasing f ↔
    Decreasing f ∧ ∀ g : Operator, Decreasing g → f ≤ g → f = g := by
  constructor
  · intro hf
    exact ⟨hf.1, fun g hg hfg => hf.eq_of_le hg hfg⟩
  · rintro ⟨hf, hmax⟩
    apply maximal_iff_no_extension.2
    refine ⟨hf, ?_⟩
    intro g hg hfg
    have hdec : Decreasing (negOut g) := by
      change Increasing (negOut (negOut g))
      simpa using hg
    have hle : f ≤ negOut g := by
      intro x u hu
      exact hfg x (show -u ∈ negOut f x by simpa [negOut] using hu)
    have heq := hmax (negOut g) hdec hle
    have h := congrArg negOut heq
    simpa using h

/-- Every point outside a maximal decreasing graph has a strictly positive witness. -/
theorem maximalDecreasing_iff_positive_witness : MaximalDecreasing f ↔
    Decreasing f ∧ ∀ x u, u ∉ f x →
      ∃ y v, v ∈ f y ∧ 0 < (x - y) * (u - v) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro x u hn
    have hn' : -u ∉ negOut f x := by simpa [negOut] using hn
    obtain ⟨y, v, hv, hneg⟩ := (maximal_iff_negative_witness.1 hf).2 x (-u) hn'
    exact ⟨y, -v, hv, by nlinarith⟩
  · rintro ⟨hf, hpos⟩
    apply maximal_iff_negative_witness.2
    refine ⟨hf, ?_⟩
    intro x u hn
    obtain ⟨y, v, hv, hpos⟩ := hpos x (-u) hn
    exact ⟨y, -v, by simpa [negOut] using hv, by nlinarith⟩

/-- The nonincreasing version of the compatible-point characterization. -/
theorem maximalDecreasing_iff_compatible : MaximalDecreasing f ↔
    Decreasing f ∧ ∀ x u,
      (∀ ⦃y v⦄, v ∈ f y → (x - y) * (u - v) ≤ 0) → u ∈ f x := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro x u hc
    have hnu : -u ∈ negOut f x := hf.2 (by
      intro y v hv
      have h := hc hv
      nlinarith)
    simpa [negOut] using hnu
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro x u hc
    apply hmax x (-u)
    intro y v hv
    have h := hc (show -v ∈ negOut f y by simpa [negOut] using hv)
    nlinarith

theorem constant_maximal_decreasing (c : ℝ) :
    MaximalDecreasing (ofFun (fun _ => c)) := by
  change MaximalIncreasing (negOut (ofFun (fun _ => c)))
  have heq : negOut (ofFun (fun _ => c)) = ofFun (fun _ => -c) := by
    ext x u
    change (-u = c) ↔ u = -c
    constructor <;> intro h <;> linarith
  rw [heq]
  exact constant_maximal (-c)

/-- A constant graph is maximal in both orientations. -/
theorem constant_maximal_both (c : ℝ) :
    MaximalIncreasing (ofFun (fun _ => c)) ∧
      MaximalDecreasing (ofFun (fun _ => c)) :=
  ⟨constant_maximal c, constant_maximal_decreasing c⟩

/-- The vertical graph through input `c`, whose only nonempty fiber is all of `ℝ`. -/
def vertical (c : ℝ) : Operator := fun x => {_u | x = c}

theorem vertical_eq_inverse_constant (c : ℝ) :
    vertical c = inverse (ofFun (fun _ => c)) := rfl

@[simp] theorem vertical_fiber (c : ℝ) : vertical c c = univ := by
  ext u
  simp [vertical]

theorem vertical_fiber_empty {c x : ℝ} (hx : x ≠ c) : vertical c x = ∅ := by
  ext u
  simp [vertical, hx]

theorem vertical_maximal (c : ℝ) : MaximalIncreasing (vertical c) :=
  inverse_maximal (constant_maximal c)

theorem vertical_maximal_decreasing (c : ℝ) : MaximalDecreasing (vertical c) :=
  inverse_maximal_decreasing (constant_maximal_decreasing c)

/-- A vertical graph is maximal in both orientations. -/
theorem vertical_maximal_both (c : ℝ) :
    MaximalIncreasing (vertical c) ∧ MaximalDecreasing (vertical c) :=
  ⟨vertical_maximal c, vertical_maximal_decreasing c⟩

end ScalarMonotone
