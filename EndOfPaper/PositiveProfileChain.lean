import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
The literal positive selected-profile vectors and origin form a nonnegative coordinate chain.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveProfileChain {ι : Type*} (s : ι → ℝ → ℝ) (I : Set ℝ) : Set (ι → ℝ) :=
  {z | z = 0 ∨ ∃ u ∈ I, (∀ i, 0 < s i u) ∧ z = (fun i => s i u)}

theorem positiveProfileChain_zero {ι : Type*} (s : ι → ℝ → ℝ) (I : Set ℝ) :
    (0 : ι → ℝ) ∈ positiveProfileChain s I := Or.inl rfl

theorem positiveProfileChain_positive_or_zero {ι : Type*} {s : ι → ℝ → ℝ} {I : Set ℝ}
    {z : ι → ℝ} (hz : z ∈ positiveProfileChain s I) : z = 0 ∨ ∀ i, 0 < z i := by
  rcases hz with hzero | ⟨u,_hu,hpos,he⟩
  · exact Or.inl hzero
  · exact Or.inr (fun i => by rw [he]; exact hpos i)

theorem positiveProfileChain_nonnegative {ι : Type*} {s : ι → ℝ → ℝ} {I : Set ℝ}
    {z : ι → ℝ} (hz : z ∈ positiveProfileChain s I) : ∀ i, 0 ≤ z i := by
  rcases positiveProfileChain_positive_or_zero hz with hzero | hpos
  · intro i
    simp only [hzero,Pi.zero_apply,le_refl]
  · exact fun i => (hpos i).le

theorem positiveProfileChain_total {ι : Type*} {s : ι → ℝ → ℝ} {I : Set ℝ}
    (hs : ∀ i, AntitoneOn (s i) I) :
    ∀ x ∈ positiveProfileChain s I, ∀ y ∈ positiveProfileChain s I, x ≤ y ∨ y ≤ x := by
  intro x hx y hy
  rcases hx with hx0 | ⟨u,hu,hup,hx⟩
  · exact Or.inl (fun i => by rw [hx0]; exact positiveProfileChain_nonnegative hy i)
  · rcases hy with hy0 | ⟨v,hv,hvp,hy⟩
    · exact Or.inr (fun i => by rw [hy0,hx]; exact (hup i).le)
    · rcases le_total u v with huv | hvu
      · exact Or.inr (fun i => by rw [hx,hy]; exact hs i hu hv huv)
      · exact Or.inl (fun i => by rw [hx,hy]; exact hs i hv hu hvu)

theorem positiveProfileChain_properties {ι : Type*} {s : ι → ℝ → ℝ} {I : Set ℝ}
    (hs : ∀ i, AntitoneOn (s i) I) :
    (∀ x ∈ positiveProfileChain s I, ∀ i, 0 ≤ x i) ∧
    (∀ x ∈ positiveProfileChain s I, x = 0 ∨ ∀ i, 0 < x i) ∧
    (∀ x ∈ positiveProfileChain s I, ∀ y ∈ positiveProfileChain s I, x ≤ y ∨ y ≤ x) ∧
    (0 : ι → ℝ) ∈ positiveProfileChain s I :=
  ⟨fun _ hx => positiveProfileChain_nonnegative hx,
    fun _ hx => positiveProfileChain_positive_or_zero hx,
    positiveProfileChain_total hs,positiveProfileChain_zero s I⟩

end ScalarMonotone.EndOfPaper
end
