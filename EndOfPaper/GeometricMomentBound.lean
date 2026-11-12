import EndOfPaper.GeometricDilation
import EndOfPaper.PolyaKnopp
import EndOfPaper.ProfileMomentComparison

/-!
An actual completed geometric quantile bound yields
the extended moment bound with coefficient exp(1)/c.
No moment finiteness or global log L1 is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem geometric_quantile_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : 0 ≤ᵐ[μ] X) {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val p, 0 ≤ v)
    {sq : ℝ → ℝ} (hsq : SelectionOn q.val (Ioo (0 : ℝ) 1) sq)
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p)) 0)) < ∞)
    {c r : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (hr : 0 < r)
    (hQ : DecLE (tailQuantile (Measure.map X μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation c (geometricHardyTransform 1 q)))) :
    (∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ) ≤
      ENNReal.ofReal (Real.exp 1/c)*(∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((sq p)^r)) := by
  classical
  have hG := geometricHardyTransform_well_defined_any_selection (by norm_num) hqi hq0 hsq hP
  let G : DecGraph := ⟨geometricHardyTransform 1 q,hG.1⟩
  obtain ⟨sg,hsgm,hsg⟩ := exists_global_measurable_selection (Or.inr hG.1.1) measurableSet_Ioo
    (fun p hp => interior_subset (show p ∈ interior (dom G.val) from by rw [hG.2.1]; exact hp))
  have hcover : c*1 ≤ 1 := by simpa only [mul_one] using hc.2
  let D := completedProfileDilation 1 1 c G hG.2.1 (by norm_num) hc.1 hcover
  have hDP := completedProfileDilation_properties (q := G) hG.2.1 (by norm_num) hc.1 hcover
  have hSD : SelectionOn D.val (Ioo (0 : ℝ) 1) (fun p => sg (c*p)) := by
    intro p hp
    rw [hDP.2 p hp]
    exact hsg _ (initial_dilation_mapsTo hc.1 hcover hp)
  have hQD : DecLE (tailQuantile (Measure.map X μ)) D.val := hQ
  let ψ := fun x : ℝ => ENNReal.ofReal ((max x 0)^r)
  have hψm : Measurable ψ := by dsimp [ψ]; fun_prop
  have hψ : Monotone ψ := fun x y hxy => ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (le_max_right x 0) (max_le_max hxy le_rfl) hr.le)
  have hb := random_variable_profile_lintegral_bound μ hX D.property
    (fun p hp => interior_subset (show p ∈ interior (dom D.val) from by rw [hDP.1]; exact hp))
    hQD hSD hψm hψ
  have heX : (∫⁻ ω, ψ (X ω) ∂μ) = ∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hX0] with ω hω
    change 0 ≤ X ω at hω
    dsimp [ψ]
    rw [max_eq_left hω]
  have heD : (∫⁻ p in Ioo (0 : ℝ) 1, ψ (sg (c*p))) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((sg (c*p))^r) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have hcp := initial_dilation_mapsTo hc.1 hcover hp
    have hnn : 0 ≤ sg (c*p) := hG.2.2.1 (c*p) hcp (sg (c*p)) (hsg _ hcp)
    dsimp [ψ]
    rw [max_eq_left hnn]
  rw [heX,heD] at hb
  have hDil := lintegral_positive_prefix_dilation
    (F := fun x : ℝ => ENNReal.ofReal ((sg x)^r)) (by fun_prop) hc.1 (p := (1 : ℝ))
  have hKn := polya_knopp (by norm_num) hqi hq0 hsq hsg hP hr hc
  have hPrefix : (∫⁻ p in Ioo (0 : ℝ) c, ENNReal.ofReal ((sq p)^r)) ≤
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((sq p)^r) :=
    lintegral_mono_set (fun p hp => ⟨hp.1,hp.2.trans_le hc.2⟩)
  have hCoeff : ENNReal.ofReal c⁻¹*ENNReal.ofReal (Real.exp 1) = ENNReal.ofReal (Real.exp 1/c) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.1.le)]
    congr 1
    rw [div_eq_mul_inv,mul_comm]
  calc
    _ ≤ ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((sg (c*p))^r) := hb
    _ = ENNReal.ofReal c⁻¹*(∫⁻ p in Ioo (0 : ℝ) c, ENNReal.ofReal ((sg p)^r)) := by
      simpa only [mul_one] using hDil
    _ ≤ ENNReal.ofReal c⁻¹*(ENNReal.ofReal (Real.exp 1)*
        (∫⁻ p in Ioo (0 : ℝ) c, ENNReal.ofReal ((sq p)^r))) := mul_le_mul_left' hKn _
    _ ≤ ENNReal.ofReal c⁻¹*(ENNReal.ofReal (Real.exp 1)*
        (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((sq p)^r))) :=
      mul_le_mul_left' (mul_le_mul_left' hPrefix _) _
    _ = _ := by rw [← mul_assoc,hCoeff]

end ScalarMonotone.EndOfPaper
end
