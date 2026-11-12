import EndOfPaper.ProductExpansion

/-!
The exact arbitrary-dimensional polynomial expansion, positivity of every
coefficient under nonzero pivots and positive scales, and the strictly
increasing bijection of the nonnegative half-line.
-/

open Set Filter
open scoped BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem productCoefficient_zero {n : ℕ} (a σ : Fin n → ℝ) :
    productCoefficient a σ 0 = ∏ i, |a i| := by
  simp [productCoefficient, productSubsetCoefficient]

theorem productCoefficient_positive {n k : ℕ} (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) (hk : k ≤ n) :
    0 < productCoefficient a σ k := by
  apply Finset.sum_pos
  · intro A hA
    exact mul_pos (Finset.prod_pos (fun i _ => hσ i))
      (Finset.prod_pos (fun i _ => abs_pos.mpr (ha i)))
  · exact Finset.powersetCard_nonempty.mpr (by simpa using hk)

theorem product_polynomial_expansion {n : ℕ} (a σ : Fin n → ℝ) (r : ℝ) :
    productDeviation a σ r = ∑ k : Fin n, productCoefficient a σ (k.val+1)*r^(k.val+1) := by
  classical
  have hsum : (∑ A ∈ Finset.univ.powerset, productSubsetCoefficient a σ A*r^A.card) =
      ∑ k ∈ Finset.range (n+1), productCoefficient a σ k*r^k := by
    rw [Finset.sum_powerset]
    simp only [Finset.card_univ, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro k hk
    rw [productCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    rw [(Finset.mem_powersetCard.mp hA).2]
  have he := Finset.prod_add (fun i => σ i*r) (fun i => |a i|) Finset.univ
  have hterm (A : Finset (Fin n)) :
      ((∏ i ∈ A, σ i*r) * ∏ i ∈ Finset.univ \ A, |a i|) =
        productSubsetCoefficient a σ A*r^A.card := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, productSubsetCoefficient]
    ring
  simp_rw [hterm] at he
  rw [hsum, Finset.sum_range_succ'] at he
  simp only [productCoefficient_zero, pow_zero, mul_one] at he
  unfold productDeviation
  rw [show (fun i => |a i|+σ i*r) = (fun i => σ i*r+|a i|) from by funext i; ring, he]
  rw [Finset.sum_range (fun k : ℕ => productCoefficient a σ (k+1)*r^(k+1))]
  ring

theorem productDeviation_zero {n : ℕ} (a σ : Fin n → ℝ) : productDeviation a σ 0 = 0 := by
  simp [productDeviation]

theorem productDeviation_continuous {n : ℕ} (a σ : Fin n → ℝ) :
    Continuous (productDeviation a σ) := by
  unfold productDeviation
  fun_prop

theorem productDeviation_strictMonoOn {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) :
    StrictMonoOn (productDeviation a σ) (Ici 0) := by
  intro x hx y hy hxy
  have h0 (i) : 0 < |a i|+σ i*x :=
    add_pos_of_pos_of_nonneg (abs_pos.mpr (ha i)) (mul_nonneg (hσ i).le hx)
  have hlt (i) : |a i|+σ i*x < |a i|+σ i*y :=
    add_lt_add_left (mul_lt_mul_of_pos_left hxy (hσ i)) _
  have hp := Finset.prod_lt_prod (fun i _ => h0 i) (fun i _ => (hlt i).le)
    ⟨(⟨0, hn⟩ : Fin n), Finset.mem_univ _, hlt _⟩
  exact sub_lt_sub_right hp _

theorem productDeviation_linear_lower {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) {r : ℝ} (hr : 0 ≤ r) :
    productCoefficient a σ 1*r ≤ productDeviation a σ r := by
  rw [product_polynomial_expansion]
  have hb := Finset.single_le_sum
    (f := fun k : Fin n => productCoefficient a σ (k.val+1)*r^(k.val+1))
    (fun k _ => mul_nonneg (productCoefficient_nonnegative a σ hσ _) (pow_nonneg hr _))
    (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  simpa only [Fin.val_mk, zero_add, pow_one] using hb

theorem productDeviation_nonnegative {n : ℕ} (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ productDeviation a σ r := by
  have hb := product_deviation_bound a a σ r (fun i => by
    rw [sub_self, abs_zero]
    exact mul_nonneg (hσ i) hr)
  simpa only [sub_self, abs_zero] using hb

theorem productDeviation_surjOn {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) :
    SurjOn (productDeviation a σ) (Ici 0) (Ici 0) := by
  intro y hy
  let c := productCoefficient a σ 1
  have hc : 0 < c := productCoefficient_positive a σ ha hσ (by omega)
  let R := y/c+1
  have hR : 0 < R := add_pos_of_nonneg_of_pos (div_nonneg hy hc.le) zero_lt_one
  have hupper : y ≤ productDeviation a σ R := by
    have hb := productDeviation_linear_lower hn a σ (fun i => (hσ i).le) hR.le
    change c*R ≤ productDeviation a σ R at hb
    have he : c*R = y+c := by dsimp [R]; field_simp [hc.ne'] <;> ring
    rw [he] at hb
    linarith
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hR.le
    (productDeviation_continuous a σ).continuousOn
    ⟨by simpa only [productDeviation_zero] using hy, hupper⟩
  exact ⟨r, hr.1, he⟩

theorem productDeviation_bijOn {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) :
    BijOn (productDeviation a σ) (Ici 0) (Ici 0) :=
  ⟨fun r hr => productDeviation_nonnegative a σ (fun i => (hσ i).le) hr,
    (productDeviation_strictMonoOn hn a σ ha hσ).injOn,
    productDeviation_surjOn hn a σ ha hσ⟩

end ScalarMonotone.EndOfPaper
end
