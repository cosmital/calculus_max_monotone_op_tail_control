import EndOfPaper.GeometricScalarCompletion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
Whole geometric Hardy dilation on the actual maximally
completed interval J_c. The input is the completed restriction
of q(c*x); infinite log areas and arbitrary selections are retained.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_prefix_map_dilation {c p : ℝ} (hc : 0 < c) :
    Measure.map (fun x : ℝ => c*x) (volume.restrict (Ioo (0 : ℝ) p)) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Ioo (0 : ℝ) (c*p)) := by
  have hpre : (fun x : ℝ => c*x) ⁻¹' Ioo (0 : ℝ) (c*p) = Ioo (0 : ℝ) p := by
    ext x
    change (0 < c*x ∧ c*x < c*p) ↔ (0 < x ∧ x < p)
    exact and_congr (mul_pos_iff_of_pos_left hc) (mul_lt_mul_left hc)
  have he := Measure.restrict_map (μ := (volume : Measure ℝ)) (measurable_const_mul c)
    (show MeasurableSet (Ioo (0 : ℝ) (c*p)) from measurableSet_Ioo)
  rw [hpre,Real.map_volume_mul_left hc.ne',abs_of_pos (inv_pos.mpr hc),Measure.restrict_smul] at he
  exact he.symm

theorem lintegral_positive_prefix_dilation {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {c p : ℝ} (hc : 0 < c) :
    (∫⁻ x in Ioo (0 : ℝ) p, F (c*x)) =
      ENNReal.ofReal c⁻¹*(∫⁻ x in Ioo (0 : ℝ) (c*p), F x) := by
  rw [← lintegral_map hF (measurable_const_mul c),positive_prefix_map_dilation hc,
    lintegral_smul_measure]
  rfl

theorem negativeLogWithZero_measurable : Measurable negativeLogWithZero := by
  unfold negativeLogWithZero
  apply Measurable.ite (show MeasurableSet {t : ℝ | t = 0} from measurableSet_singleton 0)
  · exact measurable_const
  · fun_prop

theorem hardyScalar_positive_dilation (f : ℝ → ℝ) {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    hardyScalar (fun x => f (c*x)) p = hardyScalar f (c*p) := by
  simp only [hardyScalar,intervalIntegral.integral_comp_mul_left f hc.ne',mul_zero,smul_eq_mul]
  field_simp [hc.ne',hp.ne']
  <;> ring

theorem positive_log_area_dilation_finite {s : ℝ → ℝ} {B C c : ℝ}
    (hm : Measurable s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hc : 0 < c) (hcover : c*C ≤ B) :
    (∫⁻ x in Ioo (0 : ℝ) C, ENNReal.ofReal (max (Real.log (s (c*x))) 0)) < ∞ := by
  rw [lintegral_positive_prefix_dilation
    (F := fun x : ℝ => ENNReal.ofReal (max (Real.log (s x)) 0)) (by fun_prop) hc]
  apply lt_top_iff_ne_top.mpr
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ne_of_lt
  exact lt_of_le_of_lt (lintegral_mono_set
    (show Ioo (0 : ℝ) (c*C) ⊆ Ioo (0 : ℝ) B from fun x hx => ⟨hx.1,hx.2.trans_le hcover⟩)) hP

theorem geometricPrefixValue_positive_dilation {q : DecGraph} {B c p : ℝ}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hc : 0 < c) (hp : 0 < p) (hcp : c*p ∈ Ioo (0 : ℝ) B) :
    geometricPrefixValue (fun x => s (c*x)) p = geometricPrefixValue s (c*p) := by
  classical
  have hk : ENNReal.ofReal c⁻¹ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc))
  have hPf := raw_positive_log_prefix_finite hm hP hcp
  have hPscale : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s (c*x)))) =
      ENNReal.ofReal c⁻¹*(∫⁻ x in Ioo (0 : ℝ) (c*p), ENNReal.ofReal (Real.log (s x))) :=
    lintegral_positive_prefix_dilation
      (F := fun x : ℝ => ENNReal.ofReal (Real.log (s x))) (by fun_prop) hc
  have hPscaled : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s (c*x)))) ≠ ∞ := by
    rw [hPscale]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPf
  have hNscale : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s (c*x))) =
      ENNReal.ofReal c⁻¹*(∫⁻ x in Ioo (0 : ℝ) (c*p), negativeLogWithZero (s x)) :=
    lintegral_positive_prefix_dilation (negativeLogWithZero_measurable.comp hm) hc
  by_cases hN : (∫⁻ x in Ioo (0 : ℝ) (c*p), negativeLogWithZero (s x)) = ∞
  · have hNs : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s (c*x))) = ∞ := by
      rw [hNscale,hN,ENNReal.mul_top hk]
    rw [geometricPrefixValue_of_negative_area_top hp hPscaled hNs,
      geometricPrefixValue_of_negative_area_top hcp.1 hPf hN]
  · have hlog := logarithm_prefix_integrable_of_finite_negative_area hq0 hm hs hP hcp hN
    have hpos := positive_prefix_of_finite_negative_log_area
      (selection_antitoneOn q.property.1 hs) (fun x hx => hq0 x hx (s x) (hs x hx)) hcp hN
    have hlogScaled : IntervalIntegrable (fun x => Real.log (s (c*x))) volume 0 p := by
      simpa only [zero_div,mul_div_cancel_left₀ _ hc.ne'] using hlog.comp_mul_left c
    have hposScaled : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s (c*x) := by
      intro x hx
      exact hpos (c*x) ⟨mul_pos hc hx.1,(mul_lt_mul_left hc).mpr hx.2⟩
    rw [geometricPrefixValue_of_integrable hp hlogScaled hposScaled,
      geometricPrefixValue_of_integrable hcp.1 hlog hpos,
      hardyScalar_positive_dilation (fun x : ℝ => Real.log (s x)) hc hp]

theorem initial_dilation_mapsTo {B C c : ℝ} (hc : 0 < c) (hcover : c*C ≤ B) :
    MapsTo (fun x : ℝ => c*x) (Ioo (0 : ℝ) C) (Ioo (0 : ℝ) B) := by
  intro x hx
  exact ⟨mul_pos hc hx.1,((mul_lt_mul_left hc).mpr hx.2).trans_le hcover⟩

def completedProfileDilation (B C c : ℝ) (q : DecGraph)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hC : 0 < C) (hc : 0 < c) (hcover : c*C ≤ B) : DecGraph := by
  refine ⟨completedDecreasingRestriction (Ioo (0 : ℝ) C) (positiveInputDilation c q.val),?_⟩
  apply completedDecreasingRestriction_maximal (positiveInputDilation_maximal q.property hc)
    ordConnected_Ioo (nonempty_Ioo.mpr hC)
  intro x hx
  change c*x ∈ dom q.val
  apply interior_subset
  rw [hqi]
  exact initial_dilation_mapsTo hc hcover hx

theorem completedProfileDilation_properties {B C c : ℝ} {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hC : 0 < C) (hc : 0 < c) (hcover : c*C ≤ B) :
    let d := completedProfileDilation B C c q hqi hC hc hcover
    interior (dom d.val) = Ioo (0 : ℝ) C ∧
      ∀ x ∈ Ioo (0 : ℝ) C, d.val x = q.val (c*x) := by
  let f := positiveInputDilation c q.val
  have hf : MaximalDecreasing f := positiveInputDilation_maximal q.property hc
  have hdom : Ioo (0 : ℝ) C ⊆ dom f := by
    intro x hx
    change c*x ∈ dom q.val
    apply interior_subset
    rw [hqi]
    exact initial_dilation_mapsTo hc hcover hx
  change interior (dom (completedDecreasingRestriction (Ioo (0 : ℝ) C) f)) = Ioo (0 : ℝ) C ∧
    ∀ x ∈ Ioo (0 : ℝ) C, completedDecreasingRestriction (Ioo (0 : ℝ) C) f x = q.val (c*x)
  refine ⟨(completedDecreasingRestriction_domain hf isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr hC) hdom).1,?_⟩
  intro x hx
  exact completedDecreasingRestriction_value hf isOpen_Ioo hdom hx

theorem geometric_hardy_dilation_on_initial_interval {q : DecGraph} {B C c : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hC : 0 < C) (hc : 0 < c) (hcover : c*C ≤ B) :
    geometricHardyTransform C (completedProfileDilation B C c q hqi hC hc hcover) =
      completedDecreasingRestriction (Ioo (0 : ℝ) C)
        (positiveInputDilation c (geometricHardyTransform B q)) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  have htP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rwa [harea]
  let d := completedProfileDilation B C c q hqi hC hc hcover
  have hd : interior (dom d.val) = Ioo (0 : ℝ) C ∧
      ∀ x ∈ Ioo (0 : ℝ) C, d.val x = q.val (c*x) :=
    completedProfileDilation_properties hqi hC hc hcover
  have hd0 : ∀ x ∈ Ioo (0 : ℝ) C, ∀ v ∈ d.val x, 0 ≤ v := by
    intro x hx v hv
    rw [hd.2 x hx] at hv
    exact hq0 (c*x) (initial_dilation_mapsTo hc hcover hx) v hv
  have hds : SelectionOn d.val (Ioo (0 : ℝ) C) (fun x => t (c*x)) := by
    intro x hx
    rw [hd.2 x hx]
    exact hts (c*x) (initial_dilation_mapsTo hc hcover hx)
  have hdP := positive_log_area_dilation_finite ht htP hc hcover
  have hGD := geometricHardyTransform_well_defined hC hd.1 hd0 (by fun_prop) hds hdP
  have hphiD := geometric_hardy_scalar_selection hC hd.1 hd0 hds hdP
  have hG := geometricHardyTransform_well_defined hB hqi hq0 ht hts htP
  let Gq : DecGraph := ⟨geometricHardyTransform B q,hG.1⟩
  let outD := completedProfileDilation B C c Gq hG.2.1 hC hc hcover
  have hout : interior (dom outD.val) = Ioo (0 : ℝ) C ∧
      ∀ x ∈ Ioo (0 : ℝ) C, outD.val x = Gq.val (c*x) :=
    completedProfileDilation_properties hG.2.1 hC hc hcover
  have hphiQ := geometric_hardy_scalar_selection hB hqi hq0 hts htP
  have hselOut : SelectionOn outD.val (Ioo (0 : ℝ) C)
      (geometricPrefixValue (fun x => t (c*x))) := by
    intro x hx
    rw [hout.2 x hx,geometricPrefixValue_positive_dilation hq0 ht hts htP hc hx.1
      (initial_dilation_mapsTo hc hcover hx)]
    exact hphiQ (c*x) (initial_dilation_mapsTo hc hcover hx)
  change geometricHardyTransform C d = outD.val
  exact (initial_profile_eq_completed_scalar hC hGD.1 hGD.2.1 hphiD).trans
    (initial_profile_eq_completed_scalar hC outD.property hout.1 hselOut).symm

theorem geometric_hardy_dilation {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {c : ℝ} (hc : 0 < c) :
    let C := min (1 : ℝ) (1/c)
    let hC : 0 < C := lt_min zero_lt_one (one_div_pos.mpr hc)
    let hcover : c*C ≤ 1 := by
      calc
        c*min (1 : ℝ) (1/c) ≤ c*(1/c) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
        _ = 1 := by field_simp [hc.ne']
    geometricHardyTransform C (completedProfileDilation 1 C c q hqi hC hc hcover) =
      completedDecreasingRestriction (Ioo (0 : ℝ) C)
        (positiveInputDilation c (geometricHardyTransform 1 q)) := by
  dsimp only
  exact geometric_hardy_dilation_on_initial_interval (by norm_num) hqi hq0 hs hP
    (lt_min zero_lt_one (one_div_pos.mpr hc)) hc (by
      calc
        c*min (1 : ℝ) (1/c) ≤ c*(1/c) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
        _ = 1 := by field_simp [hc.ne'])

end ScalarMonotone.EndOfPaper
end
