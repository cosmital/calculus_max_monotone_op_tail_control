import EndOfPaper.HardyScalar
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
The scalar internal-zero example: exact finite logarithmic
prefix integrals, the value -1/2 at the zero level, and the
explicit exponential/power formula before that level.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

def zeroRamp (u : ℝ) : ℝ := max (1-2*u) 0

theorem zeroRamp_nonnegative (u : ℝ) : 0 ≤ zeroRamp u := le_max_right _ _

theorem zeroRamp_continuous : Continuous zeroRamp := by
  unfold zeroRamp
  fun_prop

theorem zeroRamp_antitone : Antitone zeroRamp := by
  intro x y hxy
  exact max_le_max (by linarith) le_rfl

theorem zeroRamp_log_affine_integrable (p : ℝ) :
    IntervalIntegrable (fun s => Real.log (1-2*s)) volume 0 p := by
  have h := ((intervalIntegral.intervalIntegrable_log' : IntervalIntegrable Real.log volume
    (1 : ℝ) (1-2*p)).comp_sub_left 1).comp_mul_left 2
  convert h using 1 <;> ring

theorem zeroRamp_log_affine_integral (p : ℝ) :
    (∫ s in (0 : ℝ)..p, Real.log (1-2*s)) =
      -p-(1-2*p)/2*Real.log (1-2*p) := by
  rw [intervalIntegral.integral_comp_sub_mul Real.log (by norm_num : (2 : ℝ) ≠ 0) 1,
    integral_log]
  norm_num [smul_eq_mul]
  <;> ring

theorem zeroRamp_log_half_integral :
    (∫ s in (0 : ℝ)..(1/2 : ℝ), Real.log (1-2*s)) = -(1/2 : ℝ) := by
  rw [zeroRamp_log_affine_integral]
  norm_num

theorem zeroRamp_log_hardy_formula {p : ℝ} (hp : 0 < p) :
    hardyScalar (fun s => Real.log (1-2*s)) p =
      -1-(1-2*p)/(2*p)*Real.log (1-2*p) := by
  rw [hardyScalar,zeroRamp_log_affine_integral]
  field_simp [hp.ne']
  <;> ring

theorem zeroRamp_geometric_prefix_formula {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1/2 : ℝ)) :
    Real.exp (hardyScalar (fun s => Real.log (1-2*s)) p) =
      Real.exp (-1)*(1-2*p)^(-(1-2*p)/(2*p)) := by
  have hbase : 0 < 1-2*p := by linarith [hp.2]
  rw [zeroRamp_log_hardy_formula hp.1,Real.rpow_def_of_pos hbase,← Real.exp_add]
  congr 1
  ring

end ScalarMonotone.EndOfPaper
end
