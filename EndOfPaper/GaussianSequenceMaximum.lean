import EndOfPaper.GaussianSoftmaxApprox
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Basic

/-!
Increasing finite maxima along a deterministic dense sequence.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianSequenceMaximum (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  gaussianFiniteMaximum (fun k : Fin (N+1) => b k.val)

theorem gaussian_finite_maximum_add_constant {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (c : ℝ) :
    gaussianFiniteMaximum (fun i => b i+c) = gaussianFiniteMaximum b+c := by
  apply le_antisymm
  · exact gaussian_finite_maximum_le _ (fun i => add_le_add_right (gaussian_le_finite_maximum b i) c)
  · obtain ⟨i,hi,hMax⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty b
    change Finset.univ.sup' Finset.univ_nonempty b+c ≤ _
    rw [hMax]
    exact gaussian_le_finite_maximum (fun i => b i+c) i

theorem gaussian_sequence_maximum_upper (b : ℕ → ℝ) {c : ℝ}
    (h : ∀ k, b k ≤ c) (N : ℕ) : gaussianSequenceMaximum b N ≤ c :=
  gaussian_finite_maximum_le _ (fun k => h k.val)

theorem gaussian_le_sequence_maximum (b : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) :
    b k ≤ gaussianSequenceMaximum b N :=
  gaussian_le_finite_maximum (fun i : Fin (N+1) => b i.val) (⟨k,Nat.lt_succ_of_le h⟩ : Fin (N+1))

theorem gaussian_sequence_maximum_monotone (b : ℕ → ℝ) :
    Monotone (gaussianSequenceMaximum b) := by
  intro N M hNM
  apply gaussian_finite_maximum_le
  intro k
  exact gaussian_le_sequence_maximum b ((Nat.le_of_lt_succ k.isLt).trans hNM)

theorem gaussian_sequence_maximum_isLUB (b : ℕ → ℝ) {c : ℝ}
    (h : IsLUB (range b) c) : IsLUB (range (gaussianSequenceMaximum b)) c := by
  constructor
  · rintro _ ⟨N,rfl⟩
    exact gaussian_sequence_maximum_upper b (fun k => h.1 (mem_range_self k)) N
  · intro d hd
    apply h.2
    rintro _ ⟨k,rfl⟩
    exact (gaussian_le_sequence_maximum b (le_refl k)).trans (hd (mem_range_self k))

theorem gaussian_sequence_maximum_tendsto (b : ℕ → ℝ) {c : ℝ}
    (h : IsLUB (range b) c) : Tendsto (gaussianSequenceMaximum b) atTop (𝓝 c) :=
  tendsto_atTop_isLUB (gaussian_sequence_maximum_monotone b) (gaussian_sequence_maximum_isLUB b h)

theorem gaussian_dense_continuous_isLUB {E : Type*} [TopologicalSpace E]
    (q : ℕ → E) (hq : DenseRange q) {f : E → ℝ} (hf : Continuous f)
    {c : ℝ} (h : IsLUB (range f) c) : IsLUB (range (f ∘ q)) c := by
  constructor
  · rintro _ ⟨k,rfl⟩
    exact h.1 (mem_range_self (q k))
  · intro d hd
    have hClosed : IsClosed {x : E | f x ≤ d} := isClosed_le hf continuous_const
    have hRange : range q ⊆ {x : E | f x ≤ d} := by
      rintro _ ⟨k,rfl⟩
      exact hd (mem_range_self k)
    apply h.2
    rintro _ ⟨x,rfl⟩
    exact (hClosed.closure_subset_iff.mpr hRange) (hq x)

end ScalarMonotone.EndOfPaper
end
