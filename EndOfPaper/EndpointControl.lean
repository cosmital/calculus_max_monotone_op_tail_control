import EndOfPaper.CutoffLayerIntegral
import EndOfPaper.EndpointSymmetry
import EndOfPaper.EndpointTwoSet

/-!
The manuscript logarithmic endpoint estimate on the original
probability space. Every cutoff hypothesis is discharged using the
actual extremal extensions, quantile tests and independent-copy symmetry.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem logarithmic_endpoint_cutoff_half {Ω E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hSwap : IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ)
    {q : Operator} (hcontrol : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    {h U : E → ℝ} (hhm : Measurable h) (hUm : Measurable U)
    {C s r a t : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (ht : t ∈ q a) (hrs : 2*r ≤ s)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y) :
    μ.real {ω | C*Real.exp s*t < |h (Z ω)-h (Z' ω)| ∧
      U (Z ω) ≤ r ∧ U (Z' ω) ≤ s-r} ≤ a := by
  classical
  by_cases hA : {x | U x ≤ r}.Nonempty
  · obtain ⟨l,u,hLl,hLu,heL,heU,hbr⟩ := two_level_lipschitz_brackets hC.le hrs hA hmod
    apply exchangeable_two_set_tail_bound hZ hZ' hSwap
      (measurableSet_le hUm measurable_const) (measurableSet_le hUm measurable_const)
      (show {x | U x ≤ r} ⊆ {x | U x ≤ s-r} from fun x hx => by
        change U x ≤ r at hx
        change U x ≤ s-r
        linarith)
      hhm hLl.continuous.measurable hLu.continuous.measurable heL heU
      (fun y hy => hbr y hy) ha
    · exact scaled_lipschitz_tail_of_quantile_control hZ hZ' hcontrol ht
        (K := ⟨C*Real.exp s,mul_nonneg hC.le (Real.exp_pos s).le⟩)
        (mul_pos hC (Real.exp_pos s)) hLl
    · exact scaled_lipschitz_tail_of_quantile_control hZ hZ' hcontrol ht
        (K := ⟨C*Real.exp s,mul_nonneg hC.le (Real.exp_pos s).le⟩)
        (mul_pos hC (Real.exp_pos s)) hLu
  · have hnone : ∀ x, ¬ U x ≤ r := fun x hx => hA ⟨x,hx⟩
    have he : {ω | C*Real.exp s*t < |h (Z ω)-h (Z' ω)| ∧
        U (Z ω) ≤ r ∧ U (Z' ω) ≤ s-r} = (∅ : Set Ω) := by
      ext ω
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact fun hω => hnone (Z ω) hω.2.1
    rw [he,measureReal_empty]
    exact ha

theorem logarithmic_endpoint_cutoff {Ω E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hSwap : IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ)
    {q : Operator} (hcontrol : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    {h U : E → ℝ} (hhm : Measurable h) (hUm : Measurable U)
    {C s a t : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (ht : t ∈ q a)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y) (r : ℝ) :
    μ.real {ω | C*Real.exp s*t < |h (Z ω)-h (Z' ω)| ∧
      U (Z ω) ≤ r ∧ U (Z' ω) ≤ s-r} ≤ a := by
  by_cases hrs : 2*r ≤ s
  · exact logarithmic_endpoint_cutoff_half hZ hZ' hSwap hcontrol hhm hUm hC ha ht hrs hmod
  · rw [exchangeable_cutoff_symmetry hSwap hhm hUm]
    have hsmall : 2*(s-r) ≤ s := by linarith
    have hb := logarithmic_endpoint_cutoff_half hZ hZ' hSwap hcontrol hhm hUm hC ha ht hsmall hmod
    simpa only [sub_sub_cancel] using hb

theorem logarithmic_endpoint_control {Ω E : Type*}
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ)
    {q : Operator} (_hq : MaximalDecreasing q)
    (_hqi : Ioo (0 : ℝ) 1 ⊆ interior (dom q))
    (_hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hcontrol : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    {h U : E → ℝ} (hhm : Measurable h) (hUm : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hm : (∫⁻ ω, ENNReal.ofReal (U (Z ω)) ∂μ) < ∞)
    {C : ℝ} (hC : 0 < C)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y)
    {a s t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (ht : t ∈ q a) :
    μ.real {ω | C*Real.exp s*t < |h (Z ω)-h (Z' ω)|} ≤
      a+2*(∫ ω, U (Z ω) ∂μ)/s := by
  have hmu : Measurable (fun ω => U (Z ω)) := hUm.comp hZ
  have hmv : Measurable (fun ω => U (Z' ω)) := hUm.comp hZ'
  have hui : Integrable (fun ω => U (Z ω)) μ :=
    ⟨hmu.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (fun ω => hU0 (Z ω)))).mpr hm⟩
  have hidU := hident.comp hUm
  have hvi : Integrable (fun ω => U (Z' ω)) μ := hidU.integrable_snd hui
  have hSwap := independent_copy_exchangeable hindep hident
  have hD : MeasurableSet {ω | C*Real.exp s*t < |h (Z ω)-h (Z' ω)|} :=
    measurableSet_lt measurable_const ((hhm.comp hZ).sub (hhm.comp hZ')).abs
  have hb := cutoff_averaging_tail_bound hD hmu hmv
    (fun ω => hU0 (Z ω)) (fun ω => hU0 (Z' ω)) hui hvi hs
    (fun r _hr => logarithmic_endpoint_cutoff hZ hZ' hSwap hcontrol hhm hUm hC ha.1.le ht hmod r)
  have hmean : (∫ ω, U (Z' ω) ∂μ) = ∫ ω, U (Z ω) ∂μ := hidU.integral_eq.symm
  simpa only [hmean,← two_mul] using hb

end ScalarMonotone.EndOfPaper
end
