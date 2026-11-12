import MonotoneOperators.OrderOperations

/-!
# Order bounds for existing extrema

These four universal-property arguments apply to both orientation classes
and to maps between the classes. The set `S` permits a map to be monotone
only where its images are admissible, as in the manuscript's partially
defined maximal-operator operations.
-/

open Set

namespace ScalarMonotone

section UniversalProperties

variable {α β ι : Type*} [Preorder α] [Preorder β]
variable {S : Set α} {Φ : α → β} {f : ι → α} {F : α} {G : β}

theorem monotoneOn_inf_bound (hΦ : MonotoneOn Φ S)
    (hf : ∀ i, f i ∈ S) (hF : F ∈ S)
    (hi : IsGLB (range f) F) (hG : IsGLB (range (Φ ∘ f)) G) :
    Φ F ≤ G := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ hF (hf i) (hi.1 (mem_range_self i))

theorem monotoneOn_sup_bound (hΦ : MonotoneOn Φ S)
    (hf : ∀ i, f i ∈ S) (hF : F ∈ S)
    (hi : IsLUB (range f) F) (hG : IsLUB (range (Φ ∘ f)) G) :
    G ≤ Φ F := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ (hf i) hF (hi.1 (mem_range_self i))

theorem antitoneOn_inf_bound (hΦ : AntitoneOn Φ S)
    (hf : ∀ i, f i ∈ S) (hF : F ∈ S)
    (hi : IsGLB (range f) F) (hG : IsLUB (range (Φ ∘ f)) G) :
    G ≤ Φ F := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ hF (hf i) (hi.1 (mem_range_self i))

theorem antitoneOn_sup_bound (hΦ : AntitoneOn Φ S)
    (hf : ∀ i, f i ∈ S) (hF : F ∈ S)
    (hi : IsLUB (range f) F) (hG : IsGLB (range (Φ ∘ f)) G) :
    Φ F ≤ G := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ (hf i) hF (hi.1 (mem_range_self i))

end UniversalProperties

section PartialMaps

variable {α β ι : Type*} [Preorder α] [Preorder β]
variable {P : α → Prop} (Φ : ∀ x, P x → β)
variable {f : ι → α} (hf : ∀ i, P (f i)) {F : α} (hF : P F) {G : β}

/-- This dependent map models an operation whose output is maximal only on
its admissible inputs. No value or order assumption is imposed elsewhere. -/
theorem partial_orderPreserving_inf_bound
    (hΦ : ∀ {x y} (hx : P x) (hy : P y), x ≤ y → Φ x hx ≤ Φ y hy)
    (hi : IsGLB (range f) F)
    (hG : IsGLB (range (fun i => Φ (f i) (hf i))) G) : Φ F hF ≤ G := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ hF (hf i) (hi.1 (mem_range_self i))

theorem partial_orderPreserving_sup_bound
    (hΦ : ∀ {x y} (hx : P x) (hy : P y), x ≤ y → Φ x hx ≤ Φ y hy)
    (hi : IsLUB (range f) F)
    (hG : IsLUB (range (fun i => Φ (f i) (hf i))) G) : G ≤ Φ F hF := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ (hf i) hF (hi.1 (mem_range_self i))

theorem partial_orderReversing_inf_bound
    (hΦ : ∀ {x y} (hx : P x) (hy : P y), x ≤ y → Φ y hy ≤ Φ x hx)
    (hi : IsGLB (range f) F)
    (hG : IsLUB (range (fun i => Φ (f i) (hf i))) G) : G ≤ Φ F hF := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ hF (hf i) (hi.1 (mem_range_self i))

theorem partial_orderReversing_sup_bound
    (hΦ : ∀ {x y} (hx : P x) (hy : P y), x ≤ y → Φ y hy ≤ Φ x hx)
    (hi : IsLUB (range f) F)
    (hG : IsGLB (range (fun i => Φ (f i) (hf i))) G) : Φ F hF ≤ G := by
  apply hG.2
  rintro _ ⟨i, rfl⟩
  exact hΦ (hf i) hF (hi.1 (mem_range_self i))

end PartialMaps

end ScalarMonotone
