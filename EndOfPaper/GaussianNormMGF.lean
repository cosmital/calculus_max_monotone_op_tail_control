import EndOfPaper.GaussianLipschitzIntegrability

/-!
The exact exponential-moment bound for the norm of a standard Gaussian vector, derived from its square Laplace transform.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem linear_le_positive_quadratic {a t x : ℝ} (ht : 0 < t) :
    a*x ≤ t*x^2+a^2/(4*t) := by
  have h4 : 0 < (4 : ℝ)*t := mul_pos (by norm_num) ht
  apply (mul_le_mul_right h4).mp
  rw [add_mul,div_mul_cancel₀ _ h4.ne']
  nlinarith only [sq_nonneg (2*t*x-a)]

theorem gaussian_euclidean_norm_mgf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun ω => Real.exp (a*‖X ω‖)) μ ∧
      (∫ ω, Real.exp (a*‖X ω‖) ∂μ) ≤ Real.exp (a*Real.sqrt (Fintype.card ι : ℝ)+a^2/2) := by
  have hNorm : LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => ‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using abs_norm_sub_norm_le x y
  have hInt := gaussian_lipschitz_exponential_integrable hX hi hm hLaw hNorm a
  refine ⟨hInt,?_⟩
  by_cases ha0 : a = 0
  · simp only [ha0,zero_mul,Real.exp_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,zero_add]
    simp
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let r := Real.sqrt (Fintype.card ι : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hrSq : r^2 = (Fintype.card ι : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hra : 0 < r+a := add_pos hr hapos
  let t := a/(2*(r+a))
  have ht0 : 0 < t := div_pos hapos (mul_pos (by norm_num) hra)
  have ht : t < 1/2 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hra)).mpr
    linarith only [hr]
  have hsq (ω : Ω) : ‖X ω‖^2 = ∑ i, (X ω i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  have hQ := gaussian_square_sum_laplace hi hm hLaw ht
  have hQInt : Integrable (fun ω => Real.exp (t*‖X ω‖^2)) μ := by
    simpa only [hsq] using hQ.1
  have hQB : (∫ ω, Real.exp (t*‖X ω‖^2) ∂μ) ≤
      Real.exp ((Fintype.card ι : ℝ)*t/(1-2*t)) := by
    simpa only [hsq] using hQ.2.le.trans (gaussian_square_laplace_bound (Fintype.card ι) ht)
  have hIneq : (∫ ω, Real.exp (a*‖X ω‖) ∂μ) ≤
      Real.exp (a^2/(4*t))*(∫ ω, Real.exp (t*‖X ω‖^2) ∂μ) := by
    calc
      _ ≤ ∫ ω, Real.exp (a^2/(4*t))*Real.exp (t*‖X ω‖^2) ∂μ := by
        apply integral_mono hInt (hQInt.const_mul _)
        intro ω
        have hh := linear_le_positive_quadratic (a := a) (x := ‖X ω‖) ht0
        calc
          _ ≤ Real.exp (a^2/(4*t)+t*‖X ω‖^2) := Real.exp_le_exp.mpr (by linarith only [hh])
          _ = _ := Real.exp_add _ _
      _ = _ := integral_const_mul _ _
  have hOne : 1-2*t = r/(r+a) := by
    dsimp only [t]
    field_simp [hra.ne']
    <;> ring
  have hExp : a^2/(4*t)+(Fintype.card ι : ℝ)*t/(1-2*t) = a*r+a^2/2 := by
    rw [hOne,← hrSq]
    dsimp only [t]
    field_simp [hapos.ne',hr.ne',hra.ne']
    <;> ring
  calc
    _ ≤ Real.exp (a^2/(4*t))*Real.exp ((Fintype.card ι : ℝ)*t/(1-2*t)) :=
      hIneq.trans (mul_le_mul_of_nonneg_left hQB (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add,hExp]

end ScalarMonotone.EndOfPaper
end
