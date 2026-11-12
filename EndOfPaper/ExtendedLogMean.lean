import EndOfPaper.ExtendedLogZero
import EndOfPaper.ScalarIntegralConventions
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
The explicit extended logarithmic prefix integral and geometric
mean. Finite area gives the usual exponential average; negative
infinite logarithmic area gives zero.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

open scoped ENNReal Interval

/-- Signed logarithmic area with the explicit negative-infinite value at zero.
As in the existing scalar integration convention, none records precisely the
undefined infinity-minus-infinity case. -/
def extendedLogIntegral (s : ℝ → ℝ) (p : ℝ) : Option EReal :=
  let P := ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))
  let N := ∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)
  if P = ∞ ∧ N = ∞ then none else some ((P : EReal)-(N : EReal))

/-- The real classical geometric prefix value. The undefined-area fallback is
outside the manuscript admissible class: finite positive-log area rules it out. -/
def geometricPrefixValue (s : ℝ → ℝ) (p : ℝ) : ℝ :=
  match extendedLogIntegral s p with
  | none => 0
  | some A => ((EReal.exp A)^(p⁻¹ : ℝ)).toReal

theorem extendedLogIntegral_defined_of_finite_positive_area {s : ℝ → ℝ} {p : ℝ}
    (hP : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) ≠ ∞) :
    ∃ A : EReal, extendedLogIntegral s p = some A := by
  refine ⟨(↑(∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) : EReal)-
    (↑(∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) : EReal), ?_⟩
  simp only [extendedLogIntegral,hP,false_and,if_false]

theorem extendedLogIntegral_of_integrable {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) :
    extendedLogIntegral s p = some (↑(∫ x in (0 : ℝ)..p, Real.log (s x)) : EReal) := by
  have hi' : Integrable (fun x => Real.log (s x)) (volume.restrict (Ioo (0 : ℝ) p)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mp hi
  have hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) =
      ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (-Real.log (s x)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact negativeLogWithZero_of_pos (hpos x hx)
  have heq : extendedLogIntegral s p =
      signedExtendedIntegral (volume.restrict (Ioo (0 : ℝ) p)) (fun x => Real.log (s x)) := by
    simp only [extendedLogIntegral,signedExtendedIntegral,hN]
  rw [heq,signedExtendedIntegral_of_integrable hi',
    intervalIntegral.integral_of_le hp.le,integral_Ioc_eq_integral_Ioo]

theorem geometricPrefixValue_of_integrable {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) :
    geometricPrefixValue s p = Real.exp (hardyScalar (fun x => Real.log (s x)) p) := by
  have hA := extendedLogIntegral_of_integrable hp hi hpos
  simp only [geometricPrefixValue,hA,EReal.exp_coe,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp,hardyScalar,div_eq_mul_inv]

theorem extendedLogIntegral_of_negative_area_top {s : ℝ → ℝ} {p : ℝ}
    (hP : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) ≠ ∞)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞) :
    extendedLogIntegral s p = some ⊥ := by
  simp [extendedLogIntegral,hP,hN]

theorem geometricPrefixValue_of_negative_area_top {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hP : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) ≠ ∞)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞) :
    geometricPrefixValue s p = 0 := by
  simp [geometricPrefixValue,extendedLogIntegral_of_negative_area_top hP hN,
    ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)]


end ScalarMonotone.EndOfPaper
end
