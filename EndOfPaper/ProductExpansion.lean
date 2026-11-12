import MonotoneOperators.ProbabilityCore

/-!
Arbitrary finite product deviations and their exact subset
expansion. The product coefficients are defined by subset cardinality,
are nonnegative, and the top coefficient is exactly the positive
product of all scales. The full polynomial/operator assembly is separate.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def productDeviation {n : ℕ} (a σ : Fin n → ℝ) (r : ℝ) : ℝ :=
  (∏ i, (|a i|+σ i*r)) - ∏ i, |a i|

theorem centered_product_finset_bound {ι : Type*} (s : Finset ι) (x a d : ι → ℝ)
    (hx : ∀ i ∈ s, |x i-a i| ≤ d i) :
    |(∏ i ∈ s, x i)-(∏ i ∈ s, a i)| ≤
      (∏ i ∈ s, (|a i|+d i)) - ∏ i ∈ s, |a i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hxi : |x i-a i| ≤ d i := hx i (Finset.mem_insert_self _ _)
    have hrest := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    have hb := centered_product_pointwise (x i) (∏ j ∈ s, x j) (a i) (∏ j ∈ s, a j)
      (d i) ((∏ j ∈ s, (|a j|+d j)) - ∏ j ∈ s, |a j|) hxi hrest
    rw [Finset.abs_prod] at hb
    simp only [Finset.prod_insert his]
    exact hb.trans_eq (by ring)

theorem product_deviation_bound {n : ℕ} (x a σ : Fin n → ℝ) (r : ℝ)
    (hx : ∀ i, |x i-a i| ≤ σ i*r) :
    |(∏ i, x i)-(∏ i, a i)| ≤ productDeviation a σ r :=
  centered_product_finset_bound Finset.univ x a (fun i => σ i*r) (fun i _ => hx i)

def productSubsetCoefficient {n : ℕ} (a σ : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  (∏ i ∈ A, σ i) * ∏ i ∈ Finset.univ \ A, |a i|

def productCoefficient {n : ℕ} (a σ : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ Finset.univ.powersetCard k, productSubsetCoefficient a σ A

theorem productDeviation_powerset_expansion {n : ℕ} (a σ : Fin n → ℝ) (r : ℝ) :
    productDeviation a σ r =
      ∑ A ∈ Finset.univ.powerset.erase ∅, productSubsetCoefficient a σ A*r^A.card := by
  classical
  have he := Finset.prod_add (fun i => σ i*r) (fun i => |a i|) Finset.univ
  have hterm (A : Finset (Fin n)) :
      ((∏ i ∈ A, σ i*r) * ∏ i ∈ Finset.univ \ A, |a i|) =
        productSubsetCoefficient a σ A*r^A.card := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, productSubsetCoefficient]
    ring
  simp_rw [hterm] at he
  have hempty : (∅ : Finset (Fin n)) ∈ Finset.univ.powerset := by simp
  have hsplit := Finset.sum_erase_add Finset.univ.powerset
    (fun A : Finset (Fin n) => productSubsetCoefficient a σ A*r^A.card) hempty
  simp only [productSubsetCoefficient, Finset.prod_empty, Finset.sdiff_empty,
    Finset.card_empty, pow_zero, one_mul, mul_one] at hsplit
  change (∑ A ∈ Finset.univ.powerset.erase ∅, productSubsetCoefficient a σ A*r^A.card) +
      (∏ i, |a i|) = ∑ A ∈ Finset.univ.powerset, productSubsetCoefficient a σ A*r^A.card at hsplit
  unfold productDeviation
  rw [show (fun i => |a i|+σ i*r) = (fun i => σ i*r+|a i|) from by funext i; ring, he]
  linarith

theorem productCoefficient_nonnegative {n : ℕ} (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (k : ℕ) : 0 ≤ productCoefficient a σ k := by
  apply Finset.sum_nonneg
  intro A hA
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hσ i))
    (Finset.prod_nonneg (fun i _ => abs_nonneg (a i)))

theorem productCoefficient_top {n : ℕ} (a σ : Fin n → ℝ) :
    productCoefficient a σ n = ∏ i, σ i := by
  have he : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  simp only [productCoefficient, he, Finset.sum_singleton, productSubsetCoefficient,
    Finset.sdiff_self, Finset.prod_empty, mul_one]

theorem productCoefficient_top_positive {n : ℕ} (a σ : Fin n → ℝ)
    (hσ : ∀ i, 0 < σ i) : 0 < productCoefficient a σ n := by
  rw [productCoefficient_top]
  exact Finset.prod_pos (fun i _ => hσ i)

end ScalarMonotone.EndOfPaper
end
