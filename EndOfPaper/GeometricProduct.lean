import EndOfPaper.GeometricDilation
import EndOfPaper.InitialProfileProduct

/-!
Whole geometric Hardy product compatibility for the actual
interior graph products and their maximal completions.
Arbitrary selections, zeros and infinite negative areas are included.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem initial_decLE_of_selection_ae_le {f g : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    (hgi : interior (dom g) = Ioo (0 : ℝ) B)
    {s t : ℝ → ℝ} (hs : SelectionOn f (Ioo (0 : ℝ) B) s)
    (ht : SelectionOn g (Ioo (0 : ℝ) B) t)
    (hle : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) B)), s x ≤ t x) : DecLE f g := by
  have hne : (Ioo (0 : ℝ) B).Nonempty := nonempty_Ioo.mpr hB
  have hfd : dom f ⊆ closure (Ioo (0 : ℝ) B) := by
    have hn : (interior (dom f)).Nonempty := by rwa [hfi]
    simpa only [hfi] using decreasing_dom_subset_closure_interior hf hn
  have hgd : dom g ⊆ Icc (0 : ℝ) B := by
    have hn : (interior (dom g)).Nonempty := by rwa [hgi]
    simpa only [hgi,closure_Ioo hB.ne] using decreasing_dom_subset_closure_interior hg hn
  have hfI : Ioo (0 : ℝ) B ⊆ dom f := by intro x hx; apply interior_subset; rwa [hfi]
  have hgI : Ioo (0 : ℝ) B ⊆ dom g := by intro x hx; apply interior_subset; rwa [hgi]
  apply decLE_of_initial_interior hf.1 hg.1 isOpen_Ioo ordConnected_Ioo hne
    (by rw [closure_Ioo hB.ne]; exact ⟨le_rfl,hB.le⟩) hfd
    (fun _ hx => (hgd hx).1) hfI hgI
  intro x hx y hy hyx u hu v hv
  have hsub : Ioo y x ⊆ Ioo (0 : ℝ) B :=
    fun w hw => ⟨hy.1.trans hw.1,hw.2.trans hx.2⟩
  have he : ∀ᵐ w ∂(volume.restrict (Ioo y x)), s w ≤ t w :=
    ae_restrict_of_ae_restrict_of_subset hsub hle
  have hvol : volume (Ioo y x) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hyx))
  obtain ⟨w,hw,hst⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol he
  exact (Decreasing.le_of_lt hf.1 (hs w (hsub hw)) hu hw.2).trans
    (hst.trans (Decreasing.le_of_lt hg.1 hv (ht w (hsub hw)) hw.1))

theorem initial_profile_eq_of_selection_ae_eq {f g : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    (hgi : interior (dom g) = Ioo (0 : ℝ) B)
    {s t : ℝ → ℝ} (hs : SelectionOn f (Ioo (0 : ℝ) B) s)
    (ht : SelectionOn g (Ioo (0 : ℝ) B) t)
    (he : s =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] t) : f = g := by
  apply decLE_antisymm hf hg
  · exact initial_decLE_of_selection_ae_le hB hf hg hfi hgi hs ht (he.mono (fun _ h => h.le))
  · exact initial_decLE_of_selection_ae_le hB hg hf hgi hfi ht hs (he.mono (fun _ h => h.ge))

theorem positive_log_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (Real.log (a*b)) 0 ≤ max (Real.log a) 0+max (Real.log b) 0 := by
  by_cases ha0 : a = 0
  · simpa only [ha0,zero_mul,Real.log_zero,max_self,zero_add] using le_max_right (Real.log b) 0
  by_cases hb0 : b = 0
  · simpa only [hb0,mul_zero,Real.log_zero,max_self,add_zero] using le_max_right (Real.log a) 0
  rw [Real.log_mul ha0 hb0]
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem negative_log_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negativeLogWithZero a ≤ negativeLogWithZero (a*b)+ENNReal.ofReal (max (Real.log b) 0) := by
  by_cases ha0 : a = 0
  · simp [ha0,negativeLogWithZero]
  by_cases hb0 : b = 0
  · simp [hb0,negativeLogWithZero]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  rw [negativeLogWithZero_of_pos hap,negativeLogWithZero_of_pos (mul_pos hap hbp),Real.log_mul ha0 hb0]
  calc
    _ ≤ ENNReal.ofReal (-(Real.log a+Real.log b)+max (Real.log b) 0) :=
      ENNReal.ofReal_le_ofReal (by linarith [le_max_left (Real.log b) 0])
    _ ≤ _ := ENNReal.ofReal_add_le

theorem positive_log_area_mul_finite {s t : ℝ → ℝ} {B : ℝ}
    (hms : Measurable s) (hmt : Measurable t)
    (hs0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ s x) (ht0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ t x)
    (hPs : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hPt : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞) :
    (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x*t x)) 0)) < ∞ := by
  apply lt_of_le_of_lt ?_ (ENNReal.add_lt_top.mpr ⟨hPs,hPt⟩)
  calc
    _ ≤ ∫⁻ x in Ioo (0 : ℝ) B,
        ENNReal.ofReal (max (Real.log (s x)) 0)+ENNReal.ofReal (max (Real.log (t x)) 0) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      calc
        _ ≤ ENNReal.ofReal (max (Real.log (s x)) 0+max (Real.log (t x)) 0) :=
          ENNReal.ofReal_le_ofReal (positive_log_mul_le (hs0 x hx) (ht0 x hx))
        _ = _ := ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)
    _ = _ := lintegral_add_aux
      (f := fun x => ENNReal.ofReal (max (Real.log (s x)) 0))
      (g := fun x => ENNReal.ofReal (max (Real.log (t x)) 0)) (by fun_prop) (by fun_prop)

theorem negative_log_area_mul_top_left {s t : ℝ → ℝ} {p : ℝ}
    (hms : Measurable s) (hmt : Measurable t)
    (hs0 : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ s x) (ht0 : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ t x)
    (hPt : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞)
    (hNs : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x*t x)) = ∞ := by
  have hle : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≤
      (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x*t x))+
        ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (Real.log (t x)) 0) := by
    calc
      _ ≤ ∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x*t x)+
          ENNReal.ofReal (max (Real.log (t x)) 0) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact negative_log_mul_le (hs0 x hx) (ht0 x hx)
      _ = _ := lintegral_add_aux
        (f := fun x => negativeLogWithZero (s x*t x))
        (g := fun x => ENNReal.ofReal (max (Real.log (t x)) 0))
        (negativeLogWithZero_measurable.comp (hms.mul hmt)) (by fun_prop)
  by_contra hN
  have hfinite := ENNReal.add_ne_top.mpr ⟨hN,ne_of_lt hPt⟩
  apply hfinite
  exact top_le_iff.mp (by simpa only [hNs] using hle)

theorem logarithmic_mul_prefix_integrable {s t : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (his : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hit : IntervalIntegrable (fun x => Real.log (t x)) volume 0 p)
    (hs : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) (ht : ∀ x ∈ Ioo (0 : ℝ) p, 0 < t x) :
    IntervalIntegrable (fun x => Real.log (s x*t x)) volume 0 p := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mp (his.add hit)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (Real.log_mul (hs x hx).ne' (ht x hx).ne').symm

theorem hardy_log_mul_prefix {s t : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (his : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hit : IntervalIntegrable (fun x => Real.log (t x)) volume 0 p)
    (hs : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) (ht : ∀ x ∈ Ioo (0 : ℝ) p, 0 < t x) :
    hardyScalar (fun x => Real.log (s x*t x)) p =
      hardyScalar (fun x => Real.log (s x)) p+hardyScalar (fun x => Real.log (t x)) p := by
  have he : (∫ x in (0 : ℝ)..p, Real.log (s x*t x)) =
      ∫ x in (0 : ℝ)..p, (Real.log (s x)+Real.log (t x)) := by
    simp only [intervalIntegral.integral_of_le hp.le,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.log_mul (hs x hx).ne' (ht x hx).ne'
  rw [hardyScalar,he,intervalIntegral.integral_add his hit,hardyScalar,hardyScalar]
  ring

theorem geometricPrefixValue_mul {q r : DecGraph} {B p : ℝ}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {s t : ℝ → ℝ} (hms : Measurable s) (hmt : Measurable t)
    (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (ht : SelectionOn r.val (Ioo (0 : ℝ) B) t)
    (hPs : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hPt : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) :
    geometricPrefixValue (fun x => s x*t x) p = geometricPrefixValue s p*geometricPrefixValue t p := by
  classical
  have hs0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ s x := fun x hx => hq0 x hx (s x) (hs x hx)
  have ht0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ t x := fun x hx => hr0 x hx (t x) (ht x hx)
  have hPP := positive_log_area_mul_finite hms hmt hs0 ht0 hPs hPt
  have hPf := raw_positive_log_prefix_finite (hms.mul hmt) hPP hp
  have hs0p : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ s x := fun x hx => hs0 x ⟨hx.1,hx.2.trans hp.2⟩
  have ht0p : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ t x := fun x hx => ht0 x ⟨hx.1,hx.2.trans hp.2⟩
  by_cases hNs : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞
  · have hNprod := negative_log_area_mul_top_left hms hmt hs0p ht0p
      (positive_log_prefix_area_finite hmt hPt hp) hNs
    rw [geometricPrefixValue_of_negative_area_top hp.1 hPf hNprod,
      geometricPrefixValue_of_negative_area_top hp.1 (raw_positive_log_prefix_finite hms hPs hp) hNs,zero_mul]
  by_cases hNt : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (t x)) = ∞
  · have hNprod : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x*t x)) = ∞ := by
      simpa only [mul_comm] using negative_log_area_mul_top_left hmt hms ht0p hs0p
        (positive_log_prefix_area_finite hms hPs hp) hNt
    rw [geometricPrefixValue_of_negative_area_top hp.1 hPf hNprod,
      geometricPrefixValue_of_negative_area_top hp.1 (raw_positive_log_prefix_finite hmt hPt hp) hNt,mul_zero]
  have hlogs := logarithm_prefix_integrable_of_finite_negative_area hq0 hms hs hPs hp hNs
  have hlogt := logarithm_prefix_integrable_of_finite_negative_area hr0 hmt ht hPt hp hNt
  have hposs := positive_prefix_of_finite_negative_log_area (selection_antitoneOn q.property.1 hs) hs0 hp hNs
  have hpost := positive_prefix_of_finite_negative_log_area (selection_antitoneOn r.property.1 ht) ht0 hp hNt
  rw [geometricPrefixValue_of_integrable hp.1 (logarithmic_mul_prefix_integrable hp.1 hlogs hlogt hposs hpost)
      (fun x hx => mul_pos (hposs x hx) (hpost x hx)),
    geometricPrefixValue_of_integrable hp.1 hlogs hposs,
    geometricPrefixValue_of_integrable hp.1 hlogt hpost,
    hardy_log_mul_prefix hp.1 hlogs hlogt hposs hpost,Real.exp_add]


theorem geometric_hardy_product {q r : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {sq sr : ℝ → ℝ} (hqs : SelectionOn q.val (Ioo (0 : ℝ) B) sq)
    (hrs : SelectionOn r.val (Ioo (0 : ℝ) B) sr)
    (hPq : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hPr : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sr x)) 0)) < ∞) :
    let P := completedProfileProduct B q r hB hqi hri hq0 hr0
    let hGq := geometricHardyTransform_well_defined_any_selection hB hqi hq0 hqs hPq
    let hGr := geometricHardyTransform_well_defined_any_selection hB hri hr0 hrs hPr
    let Gq : DecGraph := ⟨geometricHardyTransform B q,hGq.1⟩
    let Gr : DecGraph := ⟨geometricHardyTransform B r,hGr.1⟩
    geometricHardyTransform B P =
      (completedProfileProduct B Gq Gr hB hGq.2.1 hGr.2.1 hGq.2.2.1 hGr.2.2.1).val := by
  dsimp only
  obtain ⟨s,hms,hs,hqarea⟩ := measurable_selection_same_positive_log_area hqi hqs
  obtain ⟨t,hmt,ht,hrarea⟩ := measurable_selection_same_positive_log_area hri hrs
  have hPs : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞ := by
    rwa [hqarea]
  have hPt : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rwa [hrarea]
  let P := completedProfileProduct B q r hB hqi hri hq0 hr0
  have hPD : interior (dom P.val) = Ioo (0 : ℝ) B :=
    (completedProfileProduct_domain hB hqi hri hq0 hr0).1
  have hP0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ P.val x, 0 ≤ v :=
    completedProfileProduct_nonnegative hB hqi hri hq0 hr0
  have hsP : SelectionOn P.val (Ioo (0 : ℝ) B) (fun x => s x*t x) :=
    completedProfileProduct_selection hB hqi hri hq0 hr0 hs ht
  have hPP := positive_log_area_mul_finite hms hmt
    (fun x hx => hq0 x hx (s x) (hs x hx)) (fun x hx => hr0 x hx (t x) (ht x hx)) hPs hPt
  have hGP := geometricHardyTransform_well_defined hB hPD hP0 (hms.mul hmt) hsP hPP
  have hphiP := geometric_hardy_scalar_selection hB hPD hP0 hsP hPP
  have hGq := geometricHardyTransform_well_defined hB hqi hq0 hms hs hPs
  have hGr := geometricHardyTransform_well_defined hB hri hr0 hmt ht hPt
  let Gq : DecGraph := ⟨geometricHardyTransform B q,hGq.1⟩
  let Gr : DecGraph := ⟨geometricHardyTransform B r,hGr.1⟩
  let outP := completedProfileProduct B Gq Gr hB hGq.2.1 hGr.2.1 hGq.2.2.1 hGr.2.2.1
  have houtD : interior (dom outP.val) = Ioo (0 : ℝ) B :=
    (completedProfileProduct_domain hB hGq.2.1 hGr.2.1 hGq.2.2.1 hGr.2.2.1).1
  have hphiQ : SelectionOn Gq.val (Ioo (0 : ℝ) B) (geometricPrefixValue s) :=
    geometric_hardy_scalar_selection hB hqi hq0 hs hPs
  have hphiR : SelectionOn Gr.val (Ioo (0 : ℝ) B) (geometricPrefixValue t) :=
    geometric_hardy_scalar_selection hB hri hr0 ht hPt
  have hphiOut : SelectionOn outP.val (Ioo (0 : ℝ) B)
      (fun x => geometricPrefixValue s x*geometricPrefixValue t x) :=
    completedProfileProduct_selection hB hGq.2.1 hGr.2.1 hGq.2.2.1 hGr.2.2.1 hphiQ hphiR
  have he : geometricPrefixValue (fun x => s x*t x) =ᵐ[volume.restrict (Ioo (0 : ℝ) B)]
      (fun x => geometricPrefixValue s x*geometricPrefixValue t x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact geometricPrefixValue_mul hq0 hr0 hms hmt hs ht hPs hPt hx
  change geometricHardyTransform B P = outP.val
  exact initial_profile_eq_of_selection_ae_eq hB hGP.1 outP.property hGP.2.1 houtD hphiP hphiOut he

end ScalarMonotone.EndOfPaper
end
