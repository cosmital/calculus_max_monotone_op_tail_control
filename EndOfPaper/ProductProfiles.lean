import EndOfPaper.ProductPolynomial
import MonotoneOperators.Cubic
import MonotoneOperators.Monomial
import MonotoneOperators.Envelopes

/-!
The whole arbitrary-dimensional parallel-monomial identity,
including every jump fiber, maximality, range and the weighted
finite lattice-supremum envelope.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem product_interval_diagonal {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) {I : Set ℝ} (hI : I.OrdConnected) (hI0 : I ⊆ Ici 0)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ I) :
    ∃ r ∈ I, productDeviation a σ r =
      ∑ k : Fin n, productCoefficient a σ (k.val+1)*(x k)^(k.val+1) := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ x hne
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ x hne
  have hij : x i ≤ x j := hmin j (Finset.mem_univ j)
  have hlower : productDeviation a σ (x i) ≤
      ∑ k : Fin n, productCoefficient a σ (k.val+1)*(x k)^(k.val+1) := by
    rw [product_polynomial_expansion]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hI0 (hx i)) (hmin k (Finset.mem_univ k)) _)
      (productCoefficient_nonnegative a σ hσ _)
  have hupper : (∑ k : Fin n, productCoefficient a σ (k.val+1)*(x k)^(k.val+1)) ≤
      productDeviation a σ (x j) := by
    rw [product_polynomial_expansion]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hI0 (hx k)) (hmax k (Finset.mem_univ k)) _)
      (productCoefficient_nonnegative a σ hσ _)
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hij
    (productDeviation_continuous a σ).continuousOn ⟨hlower, hupper⟩
  exact ⟨r, hI.out (hx i) (hx j) hr, he⟩

def productProfile {n : ℕ} (α : Operator) (a σ : Fin n → ℝ) : Operator :=
  fun t => {u | ∃ r, u ∈ α r ∧ t = productDeviation a σ r}

theorem inverse_productProfile {n : ℕ} (α : Operator) (a σ : Fin n → ℝ) (u : ℝ) :
    inverse (productProfile α a σ) u = productDeviation a σ '' inverse α u := by
  ext t
  constructor
  · rintro ⟨r, hr, ht⟩
    exact ⟨r, hr, ht.symm⟩
  · rintro ⟨r, hr, ht⟩
    exact ⟨r, hr, ht.symm⟩

theorem productProfile_parallel_monomials {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) {α : Operator} (hα : MaximalDecreasing α)
    (hα0 : dom α ⊆ Ici 0) :
    productProfile α a σ = finiteParallelAdd (fun k : Fin n =>
      monomialProfile α (productCoefficient a σ (k.val+1)) (k.val+1)) := by
  classical
  ext t u
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨(fun k => productCoefficient a σ (k.val+1)*r^(k.val+1)), ?_,
      product_polynomial_expansion a σ r⟩
    intro k
    exact ⟨r, hr, rfl⟩
  · rintro ⟨v, hv, ht⟩
    have hex (k : Fin n) : ∃ r : ℝ, u ∈ α r ∧
        v k = productCoefficient a σ (k.val+1)*r^(k.val+1) := hv k
    choose x hx he using hex
    obtain ⟨r, hr, hsum⟩ := product_interval_diagonal hn a σ hσ
      (decreasing_fiber_ordConnected (inverse_maximal_decreasing hα) u)
      (fun x hx => hα0 ⟨u, hx⟩) x hx
    refine ⟨r, hr, ?_⟩
    rw [ht]
    simp_rw [he]
    exact hsum.symm

theorem productProfile_range {n : ℕ} (α : Operator) (a σ : Fin n → ℝ) :
    ran (productProfile α a σ) = ran α := by
  ext u
  constructor
  · rintro ⟨t, r, hr, ht⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨productDeviation a σ r, r, hr, rfl⟩

theorem monomialProfile_range (α : Operator) (c : ℝ) (d : ℕ) :
    ran (monomialProfile α c d) = ran α := by
  ext u
  constructor
  · rintro ⟨t, r, hr, ht⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨c*r^d, r, hr, rfl⟩

def productMonomialGraphs {n : ℕ} (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0) : Fin n → DecGraph := fun k =>
  ⟨monomialProfile α (productCoefficient a σ (k.val+1)) (k.val+1),
    monomialProfile_maximal hα hα0 (productCoefficient_positive a σ ha hσ (by omega))
      (Nat.succ_ne_zero k.val)⟩

theorem productMonomialGraphs_range {n : ℕ} (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0) :
    ∀ k, ran (productMonomialGraphs a σ ha hσ hα hα0 k).val = ran α := by
  intro k
  exact monomialProfile_range α _ _

theorem productProfile_maximal {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0) :
    MaximalDecreasing (productProfile α a σ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let g := productMonomialGraphs a σ ha hσ hα hα0
  have hD := productMonomialGraphs_range a σ ha hσ hα hα0
  have hM := (DecGraph.parallelSumGraph g hD).property
  change MaximalDecreasing (finiteParallelAdd (fun k : Fin n =>
    monomialProfile α (productCoefficient a σ (k.val+1)) (k.val+1))) at hM
  rwa [← productProfile_parallel_monomials hn a σ (fun i => (hσ i).le) hα hα0] at hM

theorem productProfile_weighted_envelope {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0) (θ : PositiveWeights (Fin n)) :
    let g := productMonomialGraphs a σ ha hσ hα hα0
    DecLE (productProfile α a σ) (⨆ k, DecGraph.weightedProfile g θ k).val := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let g := productMonomialGraphs a σ ha hσ hα hα0
  have hD := productMonomialGraphs_range a σ ha hσ hα hα0
  have hb := (DecGraph.parallelSum_envelopes g hD θ).2
  change DecLE (finiteParallelAdd (fun k : Fin n =>
    monomialProfile α (productCoefficient a σ (k.val+1)) (k.val+1)))
      (⨆ k, DecGraph.weightedProfile g θ k).val at hb
  rwa [← productProfile_parallel_monomials hn a σ (fun i => (hσ i).le) hα hα0] at hb

end ScalarMonotone.EndOfPaper
end
