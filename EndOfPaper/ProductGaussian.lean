import EndOfPaper.ProductProbability

/-!
The explicit arbitrary-degree Gaussian multilevel product
tail bound, with the exact count of positive coefficients, the
finite minimum over all degrees and the probability cap at one.
-/

open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveProductDegreeCount {n : ℕ} (a σ : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => 0 < productCoefficient a σ (k.val+1))).card

theorem positiveProductDegreeCount_eq {n : ℕ} (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) : positiveProductDegreeCount a σ = n := by
  have he : Finset.univ.filter (fun k : Fin n => 0 < productCoefficient a σ (k.val+1)) =
      Finset.univ := Finset.filter_eq_self.mpr (fun k _ => productCoefficient_positive a σ ha hσ (by omega))
  simp only [positiveProductDegreeCount, he, Finset.card_univ, Fintype.card_fin]

theorem gaussian_product_tail_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → (Fin n → ℝ))
    (a σ : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i)
    (hTail : ∀ i, ∀ r > 0, μ.real {ω | σ i*r < |X ω i-a i|} ≤ Real.exp (-(r^2)))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t < |(∏ i, X ω i)-(∏ i, a i)|} ≤
      min 1 ((n : ℝ)*Real.exp (-(⨅ k : Fin n,
        (t/((n : ℝ)*productCoefficient a σ (k.val+1)))^((2 : ℝ)/((k.val+1 : ℕ) : ℝ))))) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let c : Fin n → ℝ := fun k => productCoefficient a σ (k.val+1)
  have hc (k : Fin n) : 0 < c k := productCoefficient_positive a σ ha hσ (by omega)
  let ρ : Fin n → ℝ := fun k => (t/((n : ℝ)*c k))^(((k.val+1 : ℕ) : ℝ)⁻¹)
  have hbase (k) : 0 < t/((n : ℝ)*c k) := div_pos ht (mul_pos hn0 (hc k))
  have hρ (k) : 0 < ρ k := Real.rpow_pos_of_pos (hbase k) _
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image Finset.univ ρ Finset.univ_nonempty
  let r := ρ j
  have hr : 0 < r := hρ j
  have hPr : productDeviation a σ r ≤ t := by
    rw [product_polynomial_expansion]
    calc
      (∑ k : Fin n, c k*r^(k.val+1)) ≤ ∑ k : Fin n, c k*(ρ k)^(k.val+1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hr.le (hmin k (Finset.mem_univ k)) _) (hc k).le
      _ = ∑ _k : Fin n, t/(n : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have he : (ρ k)^(k.val+1) = t/((n : ℝ)*c k) :=
          Real.rpow_inv_natCast_pow (hbase k).le (Nat.succ_ne_zero _)
        rw [he]
        field_simp [hn0.ne', (hc k).ne'] <;> ring
      _ = t := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [hn0.ne']
  have hsub : {ω | t < |(∏ i, X ω i)-(∏ i, a i)|} ⊆
      ⋃ i : Fin n, {ω | σ i*r < |X ω i-a i|} := by
    intro ω hω
    simp only [mem_iUnion, mem_setOf_eq]
    exact Classical.byContradiction (fun hnot => by
      have hAll (i : Fin n) : |X ω i-a i| ≤ σ i*r :=
        le_of_not_gt (fun hi => hnot ⟨i, hi⟩)
      exact (not_lt_of_ge ((product_deviation_bound (X ω) a σ r hAll).trans hPr)) hω)
  have hbound : μ.real {ω | t < |(∏ i, X ω i)-(∏ i, a i)|} ≤
      (n : ℝ)*Real.exp (-(r^2)) := by
    calc
      μ.real {ω | t < |(∏ i, X ω i)-(∏ i, a i)|} ≤
          μ.real (⋃ i : Fin n, {ω | σ i*r < |X ω i-a i|}) := measureReal_mono hsub
      _ ≤ ∑ i : Fin n, μ.real {ω | σ i*r < |X ω i-a i|} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin n, Real.exp (-(r^2)) := Finset.sum_le_sum (fun i _ => hTail i r hr)
      _ = (n : ℝ)*Real.exp (-(r^2)) := by simp
  have hsquare (k : Fin n) : (ρ k)^2 =
      (t/((n : ℝ)*c k))^((2 : ℝ)/((k.val+1 : ℕ) : ℝ)) := by
    change ((t/((n : ℝ)*c k))^(((k.val+1 : ℕ) : ℝ)⁻¹))^2 = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hbase k).le]
    congr 1
    ring
  have hrate : r^2 = ⨅ k : Fin n,
      (t/((n : ℝ)*c k))^((2 : ℝ)/((k.val+1 : ℕ) : ℝ)) := by
    apply le_antisymm
    · apply le_ciInf
      intro k
      rw [← hsquare k]
      exact pow_le_pow_left₀ hr.le (hmin k (Finset.mem_univ k)) 2
    · have hb := ciInf_le (finite_range (fun k : Fin n =>
          (t/((n : ℝ)*c k))^((2 : ℝ)/((k.val+1 : ℕ) : ℝ)))).bddBelow j
      simpa only [← hsquare j] using hb
  exact le_min measureReal_le_one (by simpa only [hrate] using hbound)

theorem multilevel_product_gaussian_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : Measurable X) (a σ : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i)
    {α : Operator} (hGauss : ∀ r > 0, α r = {Real.exp (-(r^2))})
    (hX : ∀ i, DecLE (survival (Measure.map (fun ω => |X ω i-a i|) μ))
      (inputDivide (σ i) α)) {t : ℝ} (ht : 0 < t) :
    let d := positiveProductDegreeCount a σ
    μ.real {ω | t < |(∏ i, X ω i)-(∏ i, a i)|} ≤
      min 1 ((n : ℝ)*Real.exp (-(⨅ k : Fin n,
        (t/((d : ℝ)*productCoefficient a σ (k.val+1)))^((2 : ℝ)/((k.val+1 : ℕ) : ℝ))))) := by
  dsimp only
  rw [positiveProductDegreeCount_eq a σ ha hσ]
  apply gaussian_product_tail_bound hn μ X a σ ha hσ ?_ ht
  intro i r hr
  apply (survival_map_comparison_iff μ
    ((measurable_pi_iff.mp hm i).sub measurable_const).abs _).mp (hX i)
  change Real.exp (-(r^2)) ∈ α (σ i*r/σ i)
  have he : σ i*r/σ i = r := by field_simp [(hσ i).ne']
  rw [he, hGauss r hr]
  exact mem_singleton _

end ScalarMonotone.EndOfPaper
end
