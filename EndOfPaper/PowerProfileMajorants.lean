import EndOfPaper.InitialProfileAffine
import EndOfPaper.AffinePositiveLogArea
import EndOfPaper.AffinePowerProfile
import EndOfPaper.GeometricHardyArithmetic
import EndOfPaper.LogarithmicExpectations

/-!
Power control derives the original log-area hypothesis and the exact geometric affine majorants for every alpha>0, without power-profile L1.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem decLE_value_le_singleton {f g : Operator} (hf : MaximalDecreasing f)
    (hg : MaximalDecreasing g) (hfg : DecLE f g) {p v b : ℝ}
    (hv : v ∈ f p) (hgp : g p = {b}) : v ≤ b := by
  have hb : b ∈ g p := by rw [hgp]; rfl
  obtain ⟨w,hw,hvw⟩ := (decLE_fiber hf hg hfg ⟨v,hv⟩ ⟨b,hb⟩).2 (mem_lowerHull hv)
  rw [hgp] at hw
  have he : w = b := hw
  rwa [he] at hvw

theorem power_control_value_bound {q : DecGraph} {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hQ : DecLE q.val (affinePowerProfile 0 A α hA.le hα).val) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val p, v ≤ A*p^(-α) := by
  intro p hp v hv
  have hP := affine_power_profile_properties (m := 0) (by norm_num) hA.le hα
  apply decLE_value_le_singleton q.property (affinePowerProfile 0 A α hA.le hα).property hQ hv
  simpa only [zero_add] using hP.2.1 p hp

theorem positive_log_area_of_power_control {q : DecGraph}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hQ : DecLE q.val (affinePowerProfile 0 A α hA.le hα).val) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞ := by
  have hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (A*x^(-α))) 0)) < ∞ := by
    simpa only [zero_add] using affine_power_positive_log_area (m := 0) (by norm_num) hA.le hα
  apply lt_of_le_of_lt _ hP
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  apply ENNReal.ofReal_le_ofReal
  exact positive_log_part_monotoneOn_nonnegative (hq0 x hx _ (hs x hx))
    (mul_nonneg hA.le (Real.rpow_nonneg hx.1.le _))
    (power_control_value_bound hA hα hQ x hx _ (hs x hx))

theorem affine_geometric_power_majorant {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hQ : DecLE q.val (affinePowerProfile 0 A α hA.le hα).val)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ geometricHardyTransform 1 (completedProfileAffine 1 m c q (by norm_num) hqi hc) u) :
    v ≤ Real.exp α*(m+c*A*u^(-α)) := by
  let r := completedProfileAffine 1 m c q (by norm_num) hqi hc
  let P := affinePowerProfile m (c*A) α (mul_nonneg hc hA.le) hα
  have hrdom := (completedProfileAffine_domain (m := m) (by norm_num) hqi hc).1
  have hr0 := completedProfileAffine_nonnegative (by norm_num) hqi hm hc hq0
  have hrs := completedProfileAffine_selection (m := m) (by norm_num) hqi hc hs
  have hrP := positive_log_area_affine_finite hsm (fun x hx => hq0 x hx _ (hs x hx))
    (positive_log_area_of_power_control hq0 hs hA hα hQ) hm hc
  have hP := affine_power_profile_properties hm (mul_nonneg hc hA.le) hα
  have hPs : SelectionOn P.val (Ioo (0 : ℝ) 1) (fun x => m+(c*A)*x^(-α)) := by
    intro x hx
    rw [hP.2.1 x hx]
    rfl
  have hPP := affine_power_positive_log_area hm (mul_nonneg hc hA.le) hα
  have hOrd : DecLE r.val P.val := by
    apply initial_decLE_of_selection_ae_le (by norm_num) r.property P.property hrdom hP.1 hrs hPs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    calc
      _ ≤ m+c*(A*x^(-α)) := add_le_add_left
        (mul_le_mul_of_nonneg_left (power_control_value_bound hA hα hQ x hx _ (hs x hx)) hc) m
      _ = _ := by ring
  have hGOrd := geometric_hardy_order_preserving (by norm_num) hrdom hP.1 hr0 hP.2.2 hrs hPs hrP hPP hOrd
  have hGr := geometricHardyTransform_well_defined (by norm_num) hrdom hr0 (by fun_prop) hrs hrP
  have hGP := affine_power_geometric_bound hm (mul_nonneg hc hA.le) hα
  have hGPsel := geometric_hardy_scalar_selection (by norm_num) hP.1 hP.2.2 hPs hPP u hu
  obtain ⟨w,hw,hvw⟩ := (decLE_fiber hGr.1 hGP.1 hGOrd ⟨v,hv⟩ ⟨_,hGPsel⟩).2 (mem_lowerHull hv)
  exact hvw.trans (hGP.2.2 u hu w hw)

end ScalarMonotone.EndOfPaper
end
