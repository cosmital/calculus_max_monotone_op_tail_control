import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
The exact Gaussian midpoint domination for tilted Lipschitz observations. This supplies the pointwise premise needed for a midpoint integral inequality; it is not itself a Gaussian concentration theorem.
-/

open Set
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianKernel {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  Real.exp (-(‖x‖^2)/2)

theorem gaussian_midpoint_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    ‖x‖^2/2+‖y‖^2/2 = ‖(1/2 : ℝ) • (x+y)‖^2+‖x-y‖^2/4 := by
  have hh := parallelogram_law_with_norm ℝ x y
  have hm : ‖(1/2 : ℝ) • (x+y)‖ = (1/2 : ℝ)*‖x+y‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  rw [hm]
  nlinarith only [hh]

theorem gaussian_lipschitz_midpoint_domination {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : E → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) (x y : E) :
    (Real.exp (a*f x)*gaussianKernel x)*(Real.exp (-a*f y)*gaussianKernel y) ≤
      (Real.exp ((a^2)/2)*gaussianKernel ((1/2 : ℝ) • (x+y)))^2 := by
  have hLip : |f x-f y| ≤ ‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using hf.dist_le_mul x y
  have hlin : a*(f x-f y) ≤ |a| * ‖x-y‖ := by
    apply (le_abs_self (a*(f x-f y))).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hLip (abs_nonneg a)
  have hquad : a*(f x-f y)-‖x-y‖^2/4 ≤ a^2 := by
    nlinarith [sq_nonneg (‖x-y‖/2-|a|),sq_abs a]
  have hEnergy := gaussian_midpoint_energy x y
  unfold gaussianKernel
  simp only [← Real.exp_add,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith only [hquad,hEnergy]

end ScalarMonotone.EndOfPaper
end
