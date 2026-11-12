import EndOfPaper.LipschitzBrackets
import MonotoneOperators.ProbabilityBounds
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
The exact exchangeable two-sublevel tail estimate from both
extremal extensions, and cutoff symmetry. The coefficient of a
is one, as required by logarithmic endpoint control.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem exchangeable_two_set_tail_bound {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z Z' : Ω → E} (hZ : Measurable Z) (hZ' : Measurable Z')
    (hSwap : IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {h l u : E → ℝ} (hhm : Measurable h) (hlm : Measurable l) (hum : Measurable u)
    (hL : EqOn h l A) (hU : EqOn h u A) (hbr : ∀ y ∈ B, l y ≤ h y ∧ h y ≤ u y)
    {τ a : ℝ} (ha : 0 ≤ a)
    (hTl : μ.real {ω | τ < |l (Z ω)-l (Z' ω)|} ≤ a)
    (hTu : μ.real {ω | τ < |u (Z ω)-u (Z' ω)|} ≤ a) :
    μ.real {ω | τ < |h (Z ω)-h (Z' ω)| ∧ Z ω ∈ A ∧ Z' ω ∈ B} ≤ a := by
  classical
  let S : Set Ω := {ω | τ < |h (Z ω)-h (Z' ω)| ∧ Z ω ∈ A ∧ Z' ω ∈ B}
  let Sswap : Set Ω := {ω | τ < |h (Z ω)-h (Z' ω)| ∧ Z' ω ∈ A ∧ Z ω ∈ B}
  let TL : Set Ω := {ω | τ < |l (Z ω)-l (Z' ω)|}
  let TU : Set Ω := {ω | τ < |u (Z ω)-u (Z' ω)|}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const ((hhm.comp hZ).sub (hhm.comp hZ')).abs).inter
      ((hA.preimage hZ).inter (hB.preimage hZ'))
  have hSS : MeasurableSet Sswap :=
    (measurableSet_lt measurable_const ((hhm.comp hZ).sub (hhm.comp hZ')).abs).inter
      ((hA.preimage hZ').inter (hB.preimage hZ))
  have hTL : MeasurableSet TL :=
    measurableSet_lt measurable_const ((hlm.comp hZ).sub (hlm.comp hZ')).abs
  have hTU : MeasurableSet TU :=
    measurableSet_lt measurable_const ((hum.comp hZ).sub (hum.comp hZ')).abs
  let J : Set (E × E) := {z | τ < |h z.1-h z.2| ∧ z.1 ∈ A ∧ z.2 ∈ B}
  have hJ : MeasurableSet J :=
    (measurableSet_lt measurable_const ((hhm.comp measurable_fst).sub (hhm.comp measurable_snd)).abs).inter
      ((hA.preimage measurable_fst).inter (hB.preimage measurable_snd))
  have hsym : μ S = μ Sswap := by
    simpa only [J,S,Sswap,preimage_setOf_eq,abs_sub_comm] using hSwap.measure_mem_eq hJ
  have h1S : Measurable (S.indicator (fun _ : Ω => (1 : ℝ≥0∞))) := measurable_const.indicator hS
  have h1SS : Measurable (Sswap.indicator (fun _ : Ω => (1 : ℝ≥0∞))) := measurable_const.indicator hSS
  have h1TL : Measurable (TL.indicator (fun _ : Ω => (1 : ℝ≥0∞))) := measurable_const.indicator hTL
  have h1TU : Measurable (TU.indicator (fun _ : Ω => (1 : ℝ≥0∞))) := measurable_const.indicator hTU
  have hsum : μ S+μ Sswap ≤ μ TL+μ TU := by
    calc
      _ = ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) ω+Sswap.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_add_aux h1S h1SS,lintegral_indicator_const hS,lintegral_indicator_const hSS,one_mul,one_mul]
      _ ≤ ∫⁻ ω, TL.indicator (fun _ => (1 : ℝ≥0∞)) ω+TU.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        apply lintegral_mono
        intro ω
        simpa only [S,Sswap,TL,TU,indicator_apply,mem_setOf_eq] using
          bracket_two_tail_indicator_bound hAB hL hU hbr (Z ω) (Z' ω) τ
      _ = _ := by rw [lintegral_add_aux h1TL h1TU,lintegral_indicator_const hTL,lintegral_indicator_const hTU,one_mul,one_mul]
  have htL : μ TL ≤ ENNReal.ofReal a := by
    calc
      _ = ENNReal.ofReal (μ.real TL) := (ENNReal.ofReal_toReal (measure_ne_top μ TL)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hTl
  have htU : μ TU ≤ ENNReal.ofReal a := by
    calc
      _ = ENNReal.ofReal (μ.real TU) := (ENNReal.ofReal_toReal (measure_ne_top μ TU)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hTu
  have htwice : (2 : ℝ≥0∞)*μ S ≤ (2 : ℝ≥0∞)*ENNReal.ofReal a := by
    calc
      _ = μ S+μ S := two_mul (μ S)
      _ = μ S+μ Sswap := by rw [← hsym]
      _ ≤ μ TL+μ TU := hsum
      _ ≤ ENNReal.ofReal a+ENNReal.ofReal a := add_le_add htL htU
      _ = _ := (two_mul (ENNReal.ofReal a)).symm
  have hp := (ENNReal.mul_le_mul_left (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp htwice
  change μ.real S ≤ a
  simpa only [measureReal_def,ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hp

theorem exchangeable_cutoff_symmetry {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {Z Z' : Ω → E}
    (hSwap : IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ)
    {h U : E → ℝ} (hhm : Measurable h) (hUm : Measurable U) (τ r s : ℝ) :
    μ.real {ω | τ < |h (Z ω)-h (Z' ω)| ∧ U (Z ω) ≤ r ∧ U (Z' ω) ≤ s-r} =
      μ.real {ω | τ < |h (Z ω)-h (Z' ω)| ∧ U (Z ω) ≤ s-r ∧ U (Z' ω) ≤ r} := by
  let J : Set (E × E) := {z | τ < |h z.1-h z.2| ∧ U z.1 ≤ r ∧ U z.2 ≤ s-r}
  have hJ : MeasurableSet J :=
    (measurableSet_lt measurable_const ((hhm.comp measurable_fst).sub (hhm.comp measurable_snd)).abs).inter
      ((measurableSet_le (hUm.comp measurable_fst) measurable_const).inter
        (measurableSet_le (hUm.comp measurable_snd) measurable_const))
  simpa only [measureReal_def,J,preimage_setOf_eq,abs_sub_comm,and_assoc,and_left_comm,and_comm] using
    congrArg ENNReal.toReal (hSwap.measure_mem_eq hJ)

end ScalarMonotone.EndOfPaper
end
