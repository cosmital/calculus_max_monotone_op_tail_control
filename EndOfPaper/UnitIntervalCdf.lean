import EndOfPaper.CopyCdfIntegral
import EndOfPaper.UnitIntervalCopyMoment

/-!
The exact ordinary unit-interval CDF formula used in the manuscript, with integrability and endpoint treatment proved.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem cdf_complement_tail_real (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    ν.real (Ioi t) = 1-cdf ν t := by
  rw [cdf_eq_real]
  have he := measureReal_compl (μ := ν) (s := Iic t) measurableSet_Iic
  simpa only [compl_Iic,measureReal_def,measure_univ,ENNReal.toReal_one] using he

theorem cdf_crossing_integrand (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    ν (Iic t)*ν (Ioi t)+ν (Ioi t)*ν (Iic t) =
      ENNReal.ofReal (2*cdf ν t*(1-cdf ν t)) := by
  have hTail : ν (Ioi t) = ENNReal.ofReal (1-cdf ν t) := by
    rw [← cdf_complement_tail_real ν t,measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top ν _)]
  have hF0 := cdf_nonneg ν t
  have hT0 : 0 ≤ 1-cdf ν t := sub_nonneg.mpr (cdf_le_one ν t)
  simp_rw [← ofReal_cdf ν t,hTail]
  calc
    _ = ENNReal.ofReal (cdf ν t*(1-cdf ν t))+ENNReal.ofReal ((1-cdf ν t)*cdf ν t) := by
      rw [ENNReal.ofReal_mul hF0,ENNReal.ofReal_mul hT0]
    _ = ENNReal.ofReal (cdf ν t*(1-cdf ν t)+(1-cdf ν t)*cdf ν t) :=
      (ENNReal.ofReal_add (mul_nonneg hF0 hT0) (mul_nonneg hT0 hF0)).symm
    _ = _ := by congr 1; ring

theorem copy_moment_cdf_ofReal (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1-z.2| ∂(ν.prod ν)) =
      ∫⁻ t : ℝ, ENNReal.ofReal (2*cdf ν t*(1-cdf ν t)) := by
  rw [copy_moment_cdf_extended]
  exact lintegral_congr (fun t => cdf_crossing_integrand ν t)

theorem cdf_unit_interval_outside (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∉ Ioo (0 : ℝ) 1) (ht0 : t ≠ 0) : cdf ν t*(1-cdf ν t) = 0 := by
  have hNull : ν {x | ¬ x ∈ Icc (0 : ℝ) 1} = 0 := ae_iff.mp hsupp
  by_cases hnonpos : t ≤ 0
  · have hneg : t < 0 := lt_of_le_of_ne hnonpos ht0
    have hsub : Iic t ⊆ {x | ¬ x ∈ Icc (0 : ℝ) 1} := by
      intro x hx hxI
      change x ≤ t at hx
      linarith [hxI.1]
    have hν0 : ν (Iic t) = 0 := measure_mono_null hsub hNull
    have hF0 : cdf ν t = 0 := by
      have he := ofReal_cdf ν t
      rw [hν0] at he
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp he) (cdf_nonneg ν t)
    simp only [hF0,zero_mul]
  · have ht1 : 1 ≤ t := le_of_not_gt (fun hlt => ht ⟨lt_of_not_ge hnonpos,hlt⟩)
    have hsub : Ioi t ⊆ {x | ¬ x ∈ Icc (0 : ℝ) 1} := by
      intro x hx hxI
      change t < x at hx
      linarith [hxI.2]
    have hν0 : ν (Ioi t) = 0 := measure_mono_null hsub hNull
    have hF1 : cdf ν t = 1 := by
      have he := cdf_complement_tail_real ν t
      rw [measureReal_def,hν0,ENNReal.toReal_zero] at he
      linarith
    simp only [hF1,sub_self,mul_zero]

theorem cdf_unit_interval_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Integrable (fun t : ℝ => cdf ν t*(1-cdf ν t)) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  letI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp [Real.volume_Ioo]⟩
  have hF : Measurable (fun t : ℝ => cdf ν t) := (monotone_cdf ν).measurable
  apply (integrable_const (1 : ℝ)).mono' (hF.mul (measurable_const.sub hF)).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (cdf_nonneg ν t) (sub_nonneg.mpr (cdf_le_one ν t)))]
  nlinarith [cdf_le_one ν t,sq_nonneg (cdf ν t)]

theorem copy_moment_cdf_unit_interval (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1) :
    (∫ z : ℝ × ℝ, |z.1-z.2| ∂(ν.prod ν)) =
      2*(∫ t in Ioo (0 : ℝ) 1, cdf ν t*(1-cdf ν t)) := by
  have hMoment : (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1-z.2| ∂(ν.prod ν)) ≤ ENNReal.ofReal (1/2 : ℝ) := by
    simpa only [Real.rpow_one] using unit_interval_product_moment_le_half ν hsupp (r := 1) (by norm_num)
  have hNN : 0 ≤ᵐ[ν.prod ν] (fun z : ℝ × ℝ => |z.1-z.2|) :=
    Eventually.of_forall (fun z => abs_nonneg _)
  have hAbs : Measurable (fun z : ℝ × ℝ => |z.1-z.2|) :=
    (continuous_fst.sub continuous_snd).abs.measurable
  have hFi : Integrable (fun z : ℝ × ℝ => |z.1-z.2|) (ν.prod ν) :=
    ⟨hAbs.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hNN).mpr
      (hMoment.trans_lt ENNReal.ofReal_lt_top)⟩
  have hGi := cdf_unit_interval_integrable ν
  have hHi : Integrable (fun t : ℝ => 2*cdf ν t*(1-cdf ν t)) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    simpa only [mul_assoc] using hGi.const_mul 2
  have hH0 (t : ℝ) : 0 ≤ 2*cdf ν t*(1-cdf ν t) :=
    mul_nonneg (mul_nonneg (by norm_num) (cdf_nonneg ν t)) (sub_nonneg.mpr (cdf_le_one ν t))
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    apply ae_iff.mpr
    have he : {t : ℝ | ¬ t ≠ 0} = ({0} : Set ℝ) := by ext t; simp
    rw [he,measure_singleton]
  have hAE : (fun t : ℝ => ENNReal.ofReal (2*cdf ν t*(1-cdf ν t))) =ᵐ[volume]
      (Ioo (0 : ℝ) 1).indicator (fun t : ℝ => ENNReal.ofReal (2*cdf ν t*(1-cdf ν t))) := by
    filter_upwards [hne] with t ht
    by_cases hI : t ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hI]
    · rw [indicator_of_not_mem hI]
      have hg := cdf_unit_interval_outside ν hsupp hI ht
      have hz : 2*cdf ν t*(1-cdf ν t) = 0 := by nlinarith [hg]
      rw [hz,ENNReal.ofReal_zero]
  have hExt : ENNReal.ofReal (∫ z : ℝ × ℝ, |z.1-z.2| ∂(ν.prod ν)) =
      ENNReal.ofReal (2*(∫ t in Ioo (0 : ℝ) 1, cdf ν t*(1-cdf ν t))) := by
    calc
      _ = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1-z.2| ∂(ν.prod ν) :=
        ofReal_integral_eq_lintegral_ofReal hFi hNN
      _ = ∫⁻ t : ℝ, ENNReal.ofReal (2*cdf ν t*(1-cdf ν t)) := copy_moment_cdf_ofReal ν
      _ = ∫⁻ t : ℝ, (Ioo (0 : ℝ) 1).indicator
          (fun t : ℝ => ENNReal.ofReal (2*cdf ν t*(1-cdf ν t))) t := lintegral_congr_ae hAE
      _ = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*cdf ν t*(1-cdf ν t)) :=
        lintegral_indicator measurableSet_Ioo _
      _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, 2*cdf ν t*(1-cdf ν t)) :=
        (ofReal_integral_eq_lintegral_ofReal hHi (Eventually.of_forall hH0)).symm
      _ = _ := by
        congr 1
        have he : (fun t : ℝ => 2*cdf ν t*(1-cdf ν t)) =
            (fun t : ℝ => 2*(cdf ν t*(1-cdf ν t))) := by funext t; ring
        rw [he,integral_const_mul]
  have hLeft : 0 ≤ ∫ z : ℝ × ℝ, |z.1-z.2| ∂(ν.prod ν) := integral_nonneg (fun z => abs_nonneg _)
  have hRight : 0 ≤ 2*(∫ t in Ioo (0 : ℝ) 1, cdf ν t*(1-cdf ν t)) :=
    mul_nonneg (by norm_num) (integral_nonneg
      (fun t => mul_nonneg (cdf_nonneg ν t) (sub_nonneg.mpr (cdf_le_one ν t))))
  have he := congrArg ENNReal.toReal hExt
  simpa only [ENNReal.toReal_ofReal hLeft,ENNReal.toReal_ofReal hRight] using he

end ScalarMonotone.EndOfPaper
end
