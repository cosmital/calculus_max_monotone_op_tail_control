import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Integrating a positive exponential preserves its logarithmic Lipschitz modulus. This is an ordinary integral comparison, not a concentration input.
-/

open Set MeasureTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def logExpIntegral {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : E → Ω → ℝ) (x : E) : ℝ :=
  Real.log (∫ ω, Real.exp (F x ω) ∂μ)

theorem exponential_integral_comparison {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F G : Ω → ℝ} (hF : Integrable (fun ω => Real.exp (F ω)) μ)
    (hG : Integrable (fun ω => Real.exp (G ω)) μ) {c : ℝ} (h : ∀ ω, F ω ≤ G ω+c) :
    (∫ ω, Real.exp (F ω) ∂μ) ≤ Real.exp c*(∫ ω, Real.exp (G ω) ∂μ) := by
  calc
    _ ≤ ∫ ω, Real.exp c*Real.exp (G ω) ∂μ := by
      apply integral_mono hF (hG.const_mul _)
      intro ω
      calc
        _ ≤ Real.exp (c+G ω) := Real.exp_le_exp.mpr (by linarith only [h ω])
        _ = _ := Real.exp_add _ _
    _ = _ := integral_const_mul _ _

theorem log_exp_integral_lipschitz {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    {μ : Measure Ω} [NeZero μ] {F : E → Ω → ℝ} {K : ℝ≥0}
    (hInt : ∀ x, Integrable (fun ω => Real.exp (F x ω)) μ)
    (hLip : ∀ x y ω, |F x ω-F y ω| ≤ (K : ℝ)*dist x y) :
    LipschitzWith K (logExpIntegral μ F) := by
  have hPos (x : E) : 0 < ∫ ω, Real.exp (F x ω) ∂μ := integral_exp_pos (hInt x)
  have hLog (x y : E) : logExpIntegral μ F x-logExpIntegral μ F y ≤ (K : ℝ)*dist x y := by
    have hh := exponential_integral_comparison (hInt x) (hInt y) (c := (K : ℝ)*dist x y)
      (fun ω => by have hb := (abs_le.mp (hLip x y ω)).2; linarith only [hb])
    have hlog := Real.log_le_log (hPos x) hh
    rw [Real.log_mul (Real.exp_ne_zero _) (hPos y).ne',Real.log_exp] at hlog
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hlog)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |logExpIntegral μ F x-logExpIntegral μ F y| ≤ (K : ℝ)*dist x y
  have hxy := hLog x y
  have hyx := hLog y x
  rw [dist_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith only [hyx],hxy⟩

end ScalarMonotone.EndOfPaper
end
