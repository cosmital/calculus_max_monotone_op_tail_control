import EndOfPaper.SqrtLogProfile
import EndOfPaper.PowerProfileMajorants

/-!
Exact geometric square-root logarithmic majorants, with all integrability derived from the displayed scalar bound and zero profiles included.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem sqrt_log_control_value_bound {q : DecGraph} {A : ℝ} (hA : 0 ≤ A)
    (hQ : DecLE q.val (affineSqrtLogProfile 0 A hA).val) :
    ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val u, v ≤ A*sqrtLogScalar u := by
  intro u hu v hv
  have hP := affine_sqrt_log_profile_properties (m := 0) (by norm_num) hA
  apply decLE_value_le_singleton q.property (affineSqrtLogProfile 0 A hA).property hQ hv
  simpa only [zero_add] using hP.2.1 u hu

theorem positive_log_area_of_sqrt_log_control {q : DecGraph}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {A : ℝ} (hA : 0 ≤ A) (hQ : DecLE q.val (affineSqrtLogProfile 0 A hA).val) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞ := by
  have hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (A*sqrtLogScalar x)) 0)) < ∞ := by
    simpa only [zero_add] using affine_sqrt_log_positive_log_area (m := 0) (by norm_num) hA
  apply lt_of_le_of_lt _ hP
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  apply ENNReal.ofReal_le_ofReal
  exact positive_log_part_monotoneOn_nonnegative (hq0 x hx _ (hs x hx))
    (mul_nonneg hA (Real.sqrt_nonneg _)) (sqrt_log_control_value_bound hA hQ x hx _ (hs x hx))

theorem affine_sqrt_log_geometric_bound {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c)
    {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ geometricHardyTransform 1 (affineSqrtLogProfile m c hc) u) :
    v ≤ m+c*Real.sqrt (Real.log 2+1-Real.log u) := by
  let P := affineSqrtLogProfile m c hc
  have hP := affine_sqrt_log_profile_properties hm hc
  have hPs : SelectionOn P.val (Ioo (0 : ℝ) 1) (fun x => m+c*sqrtLogScalar x) := by
    intro x hx
    rw [hP.2.1 x hx]
    rfl
  have hPsm : Measurable (fun x => m+c*sqrtLogScalar x) := by unfold sqrtLogScalar; fun_prop
  have hPP := affine_sqrt_log_positive_log_area hm hc
  have hPi := affine_sqrt_log_integrable m c
  have hG := geometricHardyTransform_well_defined (by norm_num) hP.1 hP.2.2 hPsm hPs hPP
  have hH := initial_profile_hardy_data (by norm_num) P.property hP.1 hPs hPi
  have hGH := geometricHardyTransform_le_hardy (by norm_num) hP.1 hP.2.2 hPsm hPs hPi hPP
  have hB := decLE_value_le_singleton hG.1 hH.1 hGH hv (hH.2.2.2.1 u hu)
  have hmean := sqrt_log_hardy_prefix hu.1 hu.2.le
  have he : hardyScalar (fun x => m+c*sqrtLogScalar x) u = m+c*hardyScalar sqrtLogScalar u :=
    hardyScalar_affine hu.1 hmean.1 m c
  rw [he] at hB
  exact hB.trans (add_le_add_left (mul_le_mul_of_nonneg_left hmean.2 hc) m)

theorem affine_geometric_sqrt_log_majorant {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {A : ℝ} (hA : 0 ≤ A) (hQ : DecLE q.val (affineSqrtLogProfile 0 A hA).val)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ geometricHardyTransform 1 (completedProfileAffine 1 m c q (by norm_num) hqi hc) u) :
    v ≤ m+c*A*Real.sqrt (Real.log 2+1-Real.log u) := by
  let r := completedProfileAffine 1 m c q (by norm_num) hqi hc
  let P := affineSqrtLogProfile m (c*A) (mul_nonneg hc hA)
  have hrdom := (completedProfileAffine_domain (m := m) (by norm_num) hqi hc).1
  have hr0 := completedProfileAffine_nonnegative (by norm_num) hqi hm hc hq0
  have hrs := completedProfileAffine_selection (m := m) (by norm_num) hqi hc hs
  have hrP := positive_log_area_affine_finite hsm (fun x hx => hq0 x hx _ (hs x hx))
    (positive_log_area_of_sqrt_log_control hq0 hs hA hQ) hm hc
  have hP := affine_sqrt_log_profile_properties hm (mul_nonneg hc hA)
  have hPs : SelectionOn P.val (Ioo (0 : ℝ) 1) (fun x => m+(c*A)*sqrtLogScalar x) := by
    intro x hx
    rw [hP.2.1 x hx]
    rfl
  have hPP := affine_sqrt_log_positive_log_area hm (mul_nonneg hc hA)
  have hOrd : DecLE r.val P.val := by
    apply initial_decLE_of_selection_ae_le (by norm_num) r.property P.property hrdom hP.1 hrs hPs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    calc
      _ ≤ m+c*(A*sqrtLogScalar x) := add_le_add_left
        (mul_le_mul_of_nonneg_left (sqrt_log_control_value_bound hA hQ x hx _ (hs x hx)) hc) m
      _ = _ := by ring
  have hGOrd := geometric_hardy_order_preserving (by norm_num) hrdom hP.1 hr0 hP.2.2 hrs hPs hrP hPP hOrd
  have hGr := geometricHardyTransform_well_defined (by norm_num) hrdom hr0 (by fun_prop) hrs hrP
  have hGP := geometricHardyTransform_well_defined (by norm_num) hP.1 hP.2.2
    (show Measurable (fun x => m+(c*A)*sqrtLogScalar x) from by unfold sqrtLogScalar; fun_prop) hPs hPP
  have hGPsel := geometric_hardy_scalar_selection (by norm_num) hP.1 hP.2.2 hPs hPP u hu
  obtain ⟨w,hw,hvw⟩ := (decLE_fiber hGr.1 hGP.1 hGOrd ⟨v,hv⟩ ⟨_,hGPsel⟩).2 (mem_lowerHull hv)
  exact hvw.trans (affine_sqrt_log_geometric_bound hm (mul_nonneg hc hA) hu hw)

end ScalarMonotone.EndOfPaper
end
