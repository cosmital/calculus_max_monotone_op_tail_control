import EndOfPaper.ProductProfiles

/-!
The ordinary inverse on the nonnegative half-line represents
the entire product profile, including zero and negative inputs. The
weighted monomial graph has its literal root-substitution fibers.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem productProfile_root_representation {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα0 : dom α ⊆ Ici 0) :
    ∃ g : ℝ → ℝ,
      (∀ t ≥ 0, 0 ≤ g t ∧ productDeviation a σ (g t) = t) ∧
      (∀ r ≥ 0, g (productDeviation a σ r) = r) ∧
      productProfile α a σ = comp α (fun t => if 0 ≤ t then {g t} else ∅) := by
  classical
  have hroot (t : Ici (0 : ℝ)) : ∃ r ∈ Ici (0 : ℝ), productDeviation a σ r = t.val :=
    productDeviation_surjOn hn a σ ha hσ t.property
  let g : ℝ → ℝ := fun t => if ht : 0 ≤ t then Classical.choose (hroot ⟨t, ht⟩) else 0
  have hg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g t ∧ productDeviation a σ (g t) = t := by
    dsimp only [g]
    rw [dif_pos ht]
    exact Classical.choose_spec (hroot ⟨t, ht⟩)
  have hinj := (productDeviation_strictMonoOn hn a σ ha hσ).injOn
  have hleft (r : ℝ) (hr : 0 ≤ r) : g (productDeviation a σ r) = r := by
    have hP0 := productDeviation_nonnegative a σ (fun i => (hσ i).le) hr
    exact hinj (hg _ hP0).1 hr (hg _ hP0).2
  refine ⟨g, hg, hleft, ?_⟩
  ext t u
  constructor
  · rintro ⟨r, hr, ht⟩
    have hr0 : 0 ≤ r := hα0 ⟨u, hr⟩
    have ht0 : 0 ≤ t := by
      rw [ht]
      exact productDeviation_nonnegative a σ (fun i => (hσ i).le) hr0
    have hgr : g t = r := by rw [ht]; exact hleft r hr0
    refine ⟨g t, ?_, ?_⟩
    · simp only [if_pos ht0, mem_singleton_iff]
    · rwa [hgr]
  · rintro ⟨s, hs, hu⟩
    by_cases ht : 0 ≤ t
    · have hsg : s = g t := by simpa only [if_pos ht, mem_singleton_iff] using hs
      rw [hsg] at hu
      exact ⟨g t, hu, (hg t ht).2.symm⟩
    · simp only [if_neg ht, mem_empty_iff_false] at hs

theorem productWeightedProfile_mem_iff {n : ℕ} (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0)
    (θ : PositiveWeights (Fin n)) (k : Fin n) (t u : ℝ) :
    u ∈ (DecGraph.weightedProfile (productMonomialGraphs a σ ha hσ hα hα0) θ k).val t ↔
      0 ≤ t ∧ u ∈ α ((θ k*t/productCoefficient a σ (k.val+1))^(((k.val+1 : ℕ) : ℝ)⁻¹)) := by
  rw [DecGraph.weightedProfile_val]
  have he : u ∈ comp (productMonomialGraphs a σ ha hσ hα hα0 k).val
      (ofFun (fun x => θ k*x)) t ↔
      u ∈ monomialProfile α (productCoefficient a σ (k.val+1)) (k.val+1) (θ k*t) := by
    simp only [comp, ofFun, mem_singleton_iff, exists_eq_left] <;> rfl
  rw [he, monomialProfile_mem_iff hα0 (productCoefficient_positive a σ ha hσ (by omega))
    (Nat.succ_ne_zero _)]
  rw [mul_nonneg_iff_of_pos_left (θ.positive k)]

end ScalarMonotone.EndOfPaper
end
