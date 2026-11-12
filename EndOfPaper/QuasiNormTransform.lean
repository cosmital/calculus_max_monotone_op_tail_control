import EndOfPaper.Superadditive
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
The actual finite-dimensional quasi-norm is superadditive on the
nonnegative cone for every 0<q<=1. Monotonicity, positive homogeneity,
the zero case and the reverse Minkowski inequality are proved; its
sharp transform equals the quasi-norm itself.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def coordinateQuasiNorm {n : ℕ} (q : ℝ) (x : CoordinateVector n) : ℝ :=
  (∑ i, (x i)^q)^(1/q)

theorem coordinateQuasiNorm_nonneg {n : ℕ} {q : ℝ} {x : CoordinateVector n}
    (hx : 0 ≤ x) : 0 ≤ coordinateQuasiNorm q x :=
  Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) _)) _

theorem coordinateQuasiNorm_rpow {n : ℕ} {q : ℝ} (hq : 0 < q)
    {x : CoordinateVector n} (hx : 0 ≤ x) :
    (coordinateQuasiNorm q x)^q = ∑ i, (x i)^q := by
  simpa only [coordinateQuasiNorm, one_div] using
    Real.rpow_inv_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) q)) hq.ne'

theorem coordinateQuasiNorm_zero {n : ℕ} {q : ℝ} (hq : 0 < q) :
    coordinateQuasiNorm q (0 : CoordinateVector n) = 0 := by
  simp only [coordinateQuasiNorm, Pi.zero_apply, Real.zero_rpow hq.ne', Finset.sum_const_zero]
  exact Real.zero_rpow (one_div_ne_zero hq.ne')

theorem coordinateQuasiNorm_eq_zero {n : ℕ} {q : ℝ} (hq : 0 < q)
    {x : CoordinateVector n} (hx : 0 ≤ x) (he : coordinateQuasiNorm q x = 0) : x = 0 := by
  have hs := coordinateQuasiNorm_rpow hq hx
  rw [he, Real.zero_rpow hq.ne'] at hs
  ext i
  have hi : (x i)^q ≤ ∑ j, (x j)^q :=
    Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hx j) q) (Finset.mem_univ i)
  have hz : (x i)^q = 0 := le_antisymm (by linarith) (Real.rpow_nonneg (hx i) q)
  exact (Real.rpow_eq_zero_iff_of_nonneg (hx i)).mp hz |>.1

theorem coordinateQuasiNorm_smul {n : ℕ} {q : ℝ} (hq : 0 < q)
    {x : CoordinateVector n} (hx : 0 ≤ x) {c : ℝ} (hc : 0 ≤ c) :
    coordinateQuasiNorm q (c • x) = c*coordinateQuasiNorm q x := by
  unfold coordinateQuasiNorm
  simp only [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hc (hx _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hc _)
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) q)), one_div,
    Real.rpow_rpow_inv hc hq.ne']

theorem coordinateQuasiNorm_aggregation_axioms (n : ℕ) {q : ℝ} (hq : 0 < q) :
    AggregationAxioms (@coordinateQuasiNorm n q) where
  nonneg := fun _ hx => coordinateQuasiNorm_nonneg hx
  mono := fun hx hxy => Real.rpow_le_rpow
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) q))
    (Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (hx i) (hxy i) hq.le))
    (one_div_pos.mpr hq).le
  homogeneous := fun c hc x hx => coordinateQuasiNorm_smul hq hx hc

theorem coordinateQuasiNorm_normalized_power_sum {n : ℕ} {q : ℝ} (hq : 0 < q)
    {x : CoordinateVector n} (hx : 0 ≤ x) (hN : 0 < coordinateQuasiNorm q x) :
    (∑ i, (x i / coordinateQuasiNorm q x)^q) = 1 := by
  simp_rw [Real.div_rpow (hx _) hN.le q]
  rw [← Finset.sum_div, ← coordinateQuasiNorm_rpow hq hx]
  exact div_self (Real.rpow_pos_of_pos hN q).ne'

theorem coordinateQuasiNorm_superadditive {n : ℕ} {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {x y : CoordinateVector n} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    coordinateQuasiNorm q x+coordinateQuasiNorm q y ≤ coordinateQuasiNorm q (x+y) := by
  by_cases hx0 : coordinateQuasiNorm q x = 0
  · have he := coordinateQuasiNorm_eq_zero hq hx hx0
    subst x
    simp only [zero_add, coordinateQuasiNorm_zero hq, le_refl]
  by_cases hy0 : coordinateQuasiNorm q y = 0
  · have he := coordinateQuasiNorm_eq_zero hq hy hy0
    subst y
    simp only [add_zero, coordinateQuasiNorm_zero hq, le_refl]
  have hA := lt_of_le_of_ne (coordinateQuasiNorm_nonneg hx) (Ne.symm hx0)
  have hB := lt_of_le_of_ne (coordinateQuasiNorm_nonneg hy) (Ne.symm hy0)
  let A := coordinateQuasiNorm q x
  let B := coordinateQuasiNorm q y
  have hAB : 0 < A+B := add_pos hA hB
  have hwa : 0 ≤ A/(A+B) := (div_pos hA hAB).le
  have hwb : 0 ≤ B/(A+B) := (div_pos hB hAB).le
  have hw : A/(A+B)+B/(A+B) = 1 := by rw [← add_div]; exact div_self hAB.ne'
  have hc := Real.concaveOn_rpow hq.le hq1
  have hpt (i : Fin n) :
      A/(A+B)*(x i/A)^q+B/(A+B)*(y i/B)^q ≤ ((x i+y i)/(A+B))^q := by
    have ht := hc.2 (show x i/A ∈ Ici 0 from div_nonneg (hx i) hA.le)
      (show y i/B ∈ Ici 0 from div_nonneg (hy i) hB.le) hwa hwb hw
    have he : A/(A+B)*(x i/A)+B/(A+B)*(y i/B) = (x i+y i)/(A+B) := by
      field_simp [hA.ne', hB.ne', hAB.ne'] <;> ring
    simpa only [smul_eq_mul, he] using ht
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    coordinateQuasiNorm_normalized_power_sum hq hx hA,
    coordinateQuasiNorm_normalized_power_sum hq hy hB, mul_one, mul_one, hw] at hs
  have hxy : 0 ≤ x+y := add_nonneg hx hy
  have hdiv : (∑ i, ((x i+y i)/(A+B))^q) = (∑ i, (x i+y i)^q)/(A+B)^q := by
    simp_rw [Real.div_rpow (add_nonneg (hx _) (hy _)) hAB.le q]
    rw [Finset.sum_div]
  rw [hdiv] at hs
  have hpow : (A+B)^q ≤ ∑ i, (x i+y i)^q := by
    have ht := (le_div_iff₀ (Real.rpow_pos_of_pos hAB q)).mp hs
    simpa only [one_mul] using ht
  have ht := Real.rpow_le_rpow (Real.rpow_nonneg hAB.le q) hpow (one_div_pos.mpr hq).le
  have he : ((A+B)^q)^(1/q) = A+B := by
    simpa only [one_div] using Real.rpow_rpow_inv hAB.le hq.ne'
  rw [he] at ht
  exact ht

theorem quasi_norm_superadditive_transform {n : ℕ} {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform (coordinateQuasiNorm q) a = coordinateQuasiNorm q a :=
  superadditiveTransform_eq_self (coordinateQuasiNorm_aggregation_axioms n hq)
    (fun _ _ hx hy => coordinateQuasiNorm_superadditive hq hq1 hx hy) ha

end ScalarMonotone.EndOfPaper
end
