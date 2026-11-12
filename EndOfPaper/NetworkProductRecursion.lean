import Mathlib

/-!
Zero-safe product error induction and the exact finite Cauchy--Schwarz dimension factor.
-/

open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_product_error_prefix {d δ B : ℕ → ℝ} {R K : ℝ}
    (hB : ∀ l, 0 ≤ B l) (hδ : ∀ l, 0 ≤ δ l)
    (hR : ∀ l, R ≤ K*B l)
    (hstep : ∀ l, d (l+1) ≤ B l*d l+δ l*R*(∏ j ∈ Finset.range l, B j)) :
    ∀ l, d l ≤ (d 0+K*(∑ j ∈ Finset.range l, δ j))*(∏ j ∈ Finset.range l, B j) := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    have hprod : 0 ≤ ∏ j ∈ Finset.range l, B j := Finset.prod_nonneg (fun j _ => hB j)
    have hfirst := mul_le_mul_of_nonneg_left ih (hB l)
    have hsecond := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hR l) (hδ l)) hprod
    calc
      d (l+1) ≤ B l*d l+δ l*R*(∏ j ∈ Finset.range l, B j) := hstep l
      _ ≤ B l*((d 0+K*(∑ j ∈ Finset.range l, δ j))*(∏ j ∈ Finset.range l, B j))+
          δ l*(K*B l)*(∏ j ∈ Finset.range l, B j) := add_le_add hfirst hsecond
      _ = _ := by rw [Finset.sum_range_succ,Finset.prod_range_succ]; ring

theorem network_exact_cauchy_factor {ι : Type*} [Fintype ι]
    {K δx : ℝ} {δw dim : ι → ℝ} (hK : 0 ≤ K) (hx : 0 ≤ δx)
    (hw : ∀ i, 0 ≤ δw i) (hd : ∀ i, 0 < dim i) :
    δx+K*(∑ i, δw i/Real.sqrt (dim i)) ≤
      Real.sqrt (1+K^2*(∑ i, (dim i)⁻¹))*Real.sqrt (δx^2+∑ i, (δw i)^2) := by
  let a : Option ι → ℝ := fun j => match j with | none => 1 | some i => K/Real.sqrt (dim i)
  let e : Option ι → ℝ := fun j => match j with | none => δx | some i => δw i
  have hsum : (∑ j, a j*e j) = δx+K*(∑ i, δw i/Real.sqrt (dim i)) := by
    rw [Fintype.sum_option]
    simp only [a,e,one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ha : (∑ j, (a j)^2) = 1+K^2*(∑ i, (dim i)⁻¹) := by
    rw [Fintype.sum_option]
    simp only [a,one_pow,div_pow]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (hd i).le,div_eq_mul_inv]
  have he : (∑ j, (e j)^2) = δx^2+∑ i, (δw i)^2 := by rw [Fintype.sum_option]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a e
  rw [hsum,ha,he] at hcs
  have hleft : 0 ≤ δx+K*(∑ i, δw i/Real.sqrt (dim i)) :=
    add_nonneg hx (mul_nonneg hK (Finset.sum_nonneg (fun i _ => div_nonneg (hw i) (Real.sqrt_nonneg _))))
  have hcoef : 0 ≤ 1+K^2*(∑ i, (dim i)⁻¹) :=
    add_nonneg zero_le_one (mul_nonneg (sq_nonneg K)
      (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hd i).le)))
  have herr : 0 ≤ δx^2+∑ i, (δw i)^2 := add_nonneg (sq_nonneg δx)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (δw i)))
  apply (sq_le_sq₀ hleft (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rwa [mul_pow,Real.sq_sqrt hcoef,Real.sq_sqrt herr]

end ScalarMonotone.EndOfPaper
end
