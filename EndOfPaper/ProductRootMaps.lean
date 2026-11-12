import EndOfPaper.ProductPolynomial
import EndOfPaper.SignedHardySum
import MonotoneOperators.Monomial
import MonotoneOperators.ProbabilityCore

/-!
The ordinary inverse-polynomial parallel-root identity before
composition with a tail profile. Every root is an ordinary map on
the nonnegative half-line, including its literal singleton at zero.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem product_positive_polynomial_graph_sum {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ) :
    (fun r : ℝ => if 0 ≤ r then ({productDeviation a σ r} : Set ℝ) else ∅) =
      finiteSum (fun k : Fin n => fun r : ℝ =>
        if 0 ≤ r then {productCoefficient a σ (k.val+1)*r^(k.val+1)} else ∅) := by
  classical
  ext r t
  by_cases hr : 0 ≤ r
  · have hsingle (k : Fin n) :
        (if 0 ≤ r then ({productCoefficient a σ (k.val+1)*r^(k.val+1)} : Set ℝ) else ∅) =
          {productCoefficient a σ (k.val+1)*r^(k.val+1)} := if_pos hr
    rw [finiteSum_singletons hsingle]
    simp only [if_pos hr, product_polynomial_expansion]
  · constructor
    · intro h
      simpa only [if_neg hr, mem_empty_iff_false] using h
    · rintro ⟨q, hq, ht⟩
      have h := hq (⟨0, hn⟩ : Fin n)
      simpa only [if_neg hr, mem_empty_iff_false] using h

theorem inverse_nonnegative_monomial_graph {c : ℝ} (hc : 0 < c) {d : ℕ} (hd : d ≠ 0) :
    inverse (fun r : ℝ => if 0 ≤ r then ({c*r^d} : Set ℝ) else ∅) =
      (fun t : ℝ => if 0 ≤ t then {(t/c)^((d : ℝ)⁻¹)} else ∅) := by
  let α : Operator := fun r => if 0 ≤ r then {r} else ∅
  have hα0 : dom α ⊆ Ici 0 := by
    rintro r ⟨u, hu⟩
    change 0 ≤ r
    by_contra h
    simpa only [α, if_neg h, mem_empty_iff_false] using hu
  have he : inverse (fun r : ℝ => if 0 ≤ r then ({c*r^d} : Set ℝ) else ∅) =
      monomialProfile α c d := by
    ext t u
    constructor
    · intro ht
      change t ∈ (if 0 ≤ u then ({c*u^d} : Set ℝ) else ∅) at ht
      by_cases hu : 0 ≤ u
      · refine ⟨u, ?_, ?_⟩
        · simp only [α, if_pos hu, mem_singleton_iff]
        · simpa only [if_pos hu, mem_singleton_iff] using ht
      · simpa only [if_neg hu, mem_empty_iff_false] using ht
    · rintro ⟨r, hu, ht⟩
      by_cases hr : 0 ≤ r
      · have hur : u = r := by simpa only [α, if_pos hr, mem_singleton_iff] using hu
        rw [hur]
        change t ∈ (if 0 ≤ r then ({c*r^d} : Set ℝ) else ∅)
        simpa only [if_pos hr, mem_singleton_iff] using ht
      · simpa only [α, if_neg hr, mem_empty_iff_false] using hu
  rw [he]
  ext t u
  rw [monomialProfile_mem_iff hα0 hc hd]
  by_cases ht : 0 ≤ t
  · have hroot : 0 ≤ (t/c)^((d : ℝ)⁻¹) := Real.rpow_nonneg (div_nonneg ht hc.le) _
    simp [ht, α, hroot]
  · simp [ht]

theorem product_inverse_parallel_root_maps {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) :
    inverse (fun r : ℝ => if 0 ≤ r then ({productDeviation a σ r} : Set ℝ) else ∅) =
      finiteParallelAdd (fun k : Fin n => fun t : ℝ => if 0 ≤ t then
        {(t/productCoefficient a σ (k.val+1))^(((k.val+1 : ℕ) : ℝ)⁻¹)} else ∅) := by
  let M : Fin n → Operator := fun k => fun r : ℝ => if 0 ≤ r then
    {productCoefficient a σ (k.val+1)*r^(k.val+1)} else ∅
  have hroot : (fun k : Fin n => fun t : ℝ => if 0 ≤ t then
      ({(t/productCoefficient a σ (k.val+1))^(((k.val+1 : ℕ) : ℝ)⁻¹)} : Set ℝ) else ∅) =
        (fun k => inverse (M k)) := by
    funext k
    exact (inverse_nonnegative_monomial_graph
      (productCoefficient_positive a σ ha hσ (by omega)) (Nat.succ_ne_zero k.val)).symm
  rw [hroot]
  change inverse (fun r : ℝ => if 0 ≤ r then ({productDeviation a σ r} : Set ℝ) else ∅) =
    inverse (finiteSum M)
  rw [← product_positive_polynomial_graph_sum hn a σ]

end ScalarMonotone.EndOfPaper
end
