import EndOfPaper.SignedHardySum

/-!
The signed original-space Hardy scalar bound for every
replicated average, with literal equality of each marginal law
and the exact normalization by the number of coordinates.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem replicated_average_hardy_values {Ω : Type*} [MeasurableSpace Ω]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (laws : Fin n → Measure ℝ)
    (X : Fin n → Fin m → Ω → ℝ) (hXm : ∀ i j, Measurable (X i j))
    (hXi : ∀ i j, Integrable (X i j) μ)
    (hLaw : ∀ i j, Measure.map (X i j) μ = laws i)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      (∀ i, quantileHardy (laws i) p = {a i}) ∧
      quantileHardy (Measure.map
        (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ) p = {b} ∧
      b ≤ (∑ i, a i)/(n : ℝ) := by
  classical
  let Y : (Fin n × Fin m) → Ω → ℝ := fun ij => X ij.1 ij.2
  have hYm (ij) : Measurable (Y ij) := hXm ij.1 ij.2
  have hYi (ij) : Integrable (Y ij) μ := hXi ij.1 ij.2
  obtain ⟨A, z, hA, hz, hbound⟩ := signed_hardy_sum_values μ Y hYm hYi hp
  have hA' (i : Fin n) (j : Fin m) : quantileHardy (laws i) p = {A (i,j)} := by
    have h := hA (i,j)
    change quantileHardy (Measure.map (X i j) μ) p = _ at h
    rwa [hLaw i j] at h
  let j₀ : Fin m := ⟨0, hm⟩
  let a : Fin n → ℝ := fun i => A (i,j₀)
  have hEq (i : Fin n) (j : Fin m) : A (i,j) = a i :=
    Set.singleton_injective ((hA' i j).symm.trans (hA' i j₀))
  have hsum : (∑ ij : Fin n × Fin m, A ij) = (m : ℝ)*(∑ i, a i) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hEq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  let c : ℝ := 1/((n : ℝ)*(m : ℝ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hSm : Measurable (fun ω => ∑ ij, Y ij ω) := Finset.measurable_sum _ (fun ij _ => hYm ij)
  have hSi : Integrable (fun ω => ∑ ij, Y ij ω) μ := integrable_finset_sum _ (fun ij _ => hYi ij)
  have hscaled := quantileHardy_smul_value μ hSm hSi hc hp hz
  have hfun : (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) =
      (fun ω => c*(∑ ij, Y ij ω)) := by
    funext ω
    simp only [Fintype.sum_prod_type, Y, c, one_div, div_eq_mul_inv, mul_comm, mul_one]
  refine ⟨a, c*z, fun i => hA' i j₀, ?_, ?_⟩
  · rw [hfun]
    exact hscaled
  · calc
      c*z ≤ c*((m : ℝ)*(∑ i, a i)) :=
        mul_le_mul_of_nonneg_left (hbound.trans_eq hsum) hc
      _ = (∑ i, a i)/(n : ℝ) := by
        dsimp [c]
        field_simp [hn0.ne', hm0.ne']
        <;> ring

end ScalarMonotone.EndOfPaper
end
