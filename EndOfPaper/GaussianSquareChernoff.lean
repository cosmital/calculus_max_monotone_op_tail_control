import EndOfPaper.GaussianSquareSumLaplace
import Mathlib.Probability.Moments.Basic

/-!
Chernoff bounds for actual independent standard Gaussian squares and the exact square-root norm threshold.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_square_laplace_bound (n : ℕ) {t : ℝ} (ht : t < 1/2) :
    ((Real.sqrt (1-2*t))⁻¹)^n ≤ Real.exp ((n : ℝ)*t/(1-2*t)) := by
  have ha : 0 < (1 : ℝ)-2*t := by linarith
  have hlog : -Real.log (1-2*t) ≤ 2*t/(1-2*t) := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
    rw [Real.log_inv] at hh
    calc
      _ ≤ (1-2*t)⁻¹-1 := hh
      _ = _ := by field_simp [ha.ne'] <;> ring
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos ha,← Real.exp_neg,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  calc
    _ = ((n : ℝ)/2)*(-Real.log (1-2*t)) := by ring
    _ ≤ ((n : ℝ)/2)*(2*t/(1-2*t)) :=
      mul_le_mul_of_nonneg_left hlog (div_nonneg (Nat.cast_nonneg n) (by norm_num))
    _ = _ := by ring

theorem gaussian_square_sum_chernoff {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 1)
    {t ε : ℝ} (ht0 : 0 ≤ t) (ht : t < 1/2) :
    μ.real {ω | ε ≤ ∑ i, (X i ω)^2} ≤
      Real.exp (-t*ε+(Fintype.card ι : ℝ)*t/(1-2*t)) := by
  have hInt := gaussian_square_sum_laplace hi hm hLaw ht
  have hb := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i, (X i ω)^2) (μ := μ) ε ht0 hInt.1
  have hMGF : mgf (fun ω => ∑ i, (X i ω)^2) μ t ≤
      Real.exp ((Fintype.card ι : ℝ)*t/(1-2*t)) := by
    rw [mgf,hInt.2]
    exact gaussian_square_laplace_bound _ ht
  exact (hb.trans (mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le)).trans_eq
    (Real.exp_add _ _).symm

theorem gaussian_square_sum_norm_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | (Real.sqrt (Fintype.card ι : ℝ)+s)^2 ≤ ∑ i, (X i ω)^2} ≤
      Real.exp (-(s^2)/2) := by
  by_cases hs0 : s = 0
  · simp only [hs0,zero_pow (by norm_num : (2 : ℕ) ≠ 0),neg_zero,zero_div,Real.exp_zero]
    exact measureReal_le_one
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  let r := Real.sqrt (Fintype.card ι : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hrSq : r^2 = (Fintype.card ι : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hrs : 0 < r+s := add_pos hr hspos
  let t := s/(2*(r+s))
  have ht0 : 0 < t := div_pos hspos (mul_pos (by norm_num) hrs)
  have ht : t < 1/2 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrs)).mpr
    linarith only [hr]
  have ha : 1-2*t = r/(r+s) := by
    dsimp only [t]
    field_simp [hrs.ne']
    <;> ring
  have he : -t*(r+s)^2+(Fintype.card ι : ℝ)*t/(1-2*t) = -(s^2)/2 := by
    rw [ha,← hrSq]
    dsimp only [t]
    field_simp [hrs.ne',hr.ne']
    <;> ring
  have hb := gaussian_square_sum_chernoff hi hm hLaw (ε := (r+s)^2) ht0.le ht
  rw [he] at hb
  exact hb

end ScalarMonotone.EndOfPaper
end
