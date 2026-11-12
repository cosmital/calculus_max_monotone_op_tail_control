import EndOfPaper.EndpointSymmetry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
The exact common inverse-square-root dimension coefficient for normalized one-Lipschitz norm observations.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem inv_sqrt_dimension_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f : E → ℝ} (hf : LipschitzWith 1 f) {d D : ℝ} (hd : 0 < d) (hdD : d ≤ D) :
    LipschitzWith ⟨(Real.sqrt d)⁻¹,inv_nonneg.mpr (Real.sqrt_nonneg _)⟩
      (fun x => f x/Real.sqrt D) := by
  have hD : 0 < D := hd.trans_le hdD
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |f x/Real.sqrt D-f y/Real.sqrt D| ≤ (Real.sqrt d)⁻¹*dist x y
  rw [← sub_div,abs_div,abs_of_pos (Real.sqrt_pos.mpr hD)]
  calc
    |f x-f y|/Real.sqrt D ≤ dist x y/Real.sqrt D :=
      div_le_div_of_nonneg_right (by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul x y)
        (Real.sqrt_nonneg _)
    _ ≤ dist x y/Real.sqrt d :=
      div_le_div_of_nonneg_left dist_nonneg (Real.sqrt_pos.mpr hd) (Real.sqrt_le_sqrt hdD)
    _ = (Real.sqrt d)⁻¹*dist x y := by rw [div_eq_mul_inv,mul_comm]

end ScalarMonotone.EndOfPaper
end
