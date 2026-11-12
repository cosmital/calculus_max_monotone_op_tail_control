import EndOfPaper.ProductProfiles
import MonotoneOperators.ProbabilityBounds

/-!
Arbitrary original-space finite product deviation tails and
the completed survival comparison with the exact parallel profile
and its weighted lattice envelope, without independence or L1.
-/

open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem product_common_level_tail_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → (Fin n → ℝ)) (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hX : ∀ i, TailBound μ (fun ω => |X ω i-a i|) (inputDivide (σ i) α))
    {r u : ℝ} (hu : u ∈ α r) :
    μ.real {ω | productDeviation a σ r < |(∏ i, X ω i)-(∏ i, a i)|} ≤ (n : ℝ)*u := by
  classical
  have hsub : {ω | productDeviation a σ r < |(∏ i, X ω i)-(∏ i, a i)|} ⊆
      ⋃ i : Fin n, {ω | σ i*r < |X ω i-a i|} := by
    intro ω hω
    simp only [mem_iUnion, mem_setOf_eq]
    by_contra h
    push_neg at h
    exact (not_lt_of_ge (product_deviation_bound (X ω) a σ r h)) hω
  have hMarg (i : Fin n) : μ.real {ω | σ i*r < |X ω i-a i|} ≤ u := by
    apply hX i
    change u ∈ α (σ i*r/σ i)
    have he : σ i*r/σ i = r := by field_simp [(hσ i).ne']
    rwa [he]
  calc
    μ.real {ω | productDeviation a σ r < |(∏ i, X ω i)-(∏ i, a i)|} ≤
        μ.real (⋃ i : Fin n, {ω | σ i*r < |X ω i-a i|}) := measureReal_mono hsub
    _ ≤ ∑ i : Fin n, μ.real {ω | σ i*r < |X ω i-a i|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, u := Finset.sum_le_sum (fun i _ => hMarg i)
    _ = (n : ℝ)*u := by simp

theorem product_error_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Ω → (Fin n → ℝ)} (hm : Measurable X) (a : Fin n → ℝ) :
    Measurable (fun ω => |(∏ i, X ω i)-(∏ i, a i)|) :=
  ((Finset.measurable_prod _ (fun i _ => measurable_pi_iff.mp hm i)).sub measurable_const).abs

theorem survival_product_profile_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : Measurable X) (a σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hX : ∀ i, DecLE (survival (Measure.map (fun ω => |X ω i-a i|) μ))
      (inputDivide (σ i) α)) :
    DecLE (survival (Measure.map (fun ω => |(∏ i, X ω i)-(∏ i, a i)|) μ))
      (outputScale (n : ℝ) (productProfile α a σ)) := by
  apply survival_map_le_outputScale_of_tail_bound μ (product_error_measurable hm a)
  rintro t u ⟨r, hr, rfl⟩
  exact product_common_level_tail_bound μ X a σ hσ
    (fun i => (survival_map_comparison_iff μ
      ((measurable_pi_iff.mp hm i).sub measurable_const).abs _).mp (hX i)) hr

theorem multilevel_product_operator_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : Measurable X) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0)
    (hX : ∀ i, DecLE (survival (Measure.map (fun ω => |X ω i-a i|) μ))
      (inputDivide (σ i) α)) (θ : PositiveWeights (Fin n)) :
    let g := productMonomialGraphs a σ ha hσ hα hα0
    MaximalDecreasing (productProfile α a σ) ∧
      DecLE (survival (Measure.map (fun ω => |(∏ i, X ω i)-(∏ i, a i)|) μ))
        (outputScale (n : ℝ) (productProfile α a σ)) ∧
      DecLE (survival (Measure.map (fun ω => |(∏ i, X ω i)-(∏ i, a i)|) μ))
        (outputScale (n : ℝ) (⨆ k, DecGraph.weightedProfile g θ k).val) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Y : Ω → ℝ := fun ω => |(∏ i, X ω i)-(∏ i, a i)|
  have hYm : Measurable Y := product_error_measurable hm a
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hYm.aemeasurable
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hP := productProfile_maximal hn a σ ha hσ hα hα0
  have hSP := survival_product_profile_bound μ hm a σ hσ hX
  have hPE := productProfile_weighted_envelope hn a σ ha hσ hα hα0 θ
  let g := productMonomialGraphs a σ ha hσ hα hα0
  let E : DecGraph := ⨆ k, DecGraph.weightedProfile g θ k
  have hscaled : DecLE (outputScale (n : ℝ) (productProfile α a σ))
      (outputScale (n : ℝ) E.val) := by
    rintro x u y v ⟨u', hu, rfl⟩ ⟨v', hv, rfl⟩ hxy
    exact mul_le_mul_of_nonneg_left (hPE hu hv hxy) hn0.le
  exact ⟨hP, hSP, decLE_trans (survival_maximal (Measure.map Y μ))
    (outputScale_maximal_decreasing hn0 hP)
    (outputScale_maximal_decreasing hn0 E.property) hSP hscaled⟩

end ScalarMonotone.EndOfPaper
end
