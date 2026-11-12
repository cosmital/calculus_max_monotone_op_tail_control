import EndOfPaper.GeometricScalarCompletion
import EndOfPaper.KnoppWeightedJensen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
The full extended Polya--Knopp inequality for every r>0.
Arbitrary input/output selections and infinite moments are
allowed; local L1 is derived only in the finite-moment branch.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem knopp_kernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun p : ℝ => (p^2)⁻¹) (Ioi x) volume := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).congr_fun
    (fun p hp => ?_) measurableSet_Ioi
  rw [Real.rpow_neg (hx.trans hp).le,Real.rpow_two]

theorem knopp_kernel_lintegral {x : ℝ} (hx : 0 < x) :
    (∫⁻ p in Ioi x, ENNReal.ofReal ((p^2)⁻¹)) = ENNReal.ofReal x⁻¹ := by
  have hi := knopp_kernel_integrable hx
  have hnn : ∀ᵐ p ∂(volume.restrict (Ioi x)), 0 ≤ (p^2)⁻¹ :=
    Eventually.of_forall (fun p => inv_nonneg.mpr (sq_nonneg p))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  calc
    _ = ∫ p in Ioi x, p^(-2 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      rw [Real.rpow_neg (hx.trans hp).le,Real.rpow_two]
    _ = -x^((-2 : ℝ)+1)/((-2 : ℝ)+1) :=
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx
    _ = x⁻¹ := by norm_num [Real.rpow_neg_one]

theorem knopp_kernel_prefix_bound {a x : ℝ} (hx : 0 < x) :
    (∫⁻ p in Ioo (0 : ℝ) a, if x < p then ENNReal.ofReal ((p^2)⁻¹) else 0) ≤
      ENNReal.ofReal x⁻¹ := by
  have he : (fun p : ℝ => if x < p then ENNReal.ofReal ((p^2)⁻¹) else 0) =
      (Ioi x).indicator (fun p : ℝ => ENNReal.ofReal ((p^2)⁻¹)) := by
    funext p
    simp only [indicator_apply,mem_Ioi]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  calc
    _ ≤ ∫⁻ p in Ioi x, ENNReal.ofReal ((p^2)⁻¹) :=
      lintegral_mono_set inter_subset_left
    _ = _ := knopp_kernel_lintegral hx

theorem knopp_weighted_lintegral_bound {f : ℝ → ℝ≥0∞} (hf : Measurable f) {a : ℝ}
    (ha : 0 < a) :
    (∫⁻ p in Ioo (0 : ℝ) a, ∫⁻ x in Ioo (0 : ℝ) p,
      ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*f x) ≤ ∫⁻ x in Ioo (0 : ℝ) a, f x := by
  let μ := volume.restrict (Ioo (0 : ℝ) a)
  let K : ℝ → ℝ → ℝ≥0∞ := fun p x =>
    if x < p then ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*f x else 0
  have hK : Measurable (Function.uncurry K) := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    · fun_prop
    · exact measurable_const
  have hinner : ∀ᵐ p ∂μ,
      (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*f x) =
        ∫⁻ x, K p x ∂μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have hset : Iio p ∩ Ioo (0 : ℝ) a = Ioo (0 : ℝ) p := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.2.1,hx.1⟩
      · intro hx
        exact ⟨hx.2,hx.1,hx.2.trans hp.2⟩
    have he : K p = (Iio p).indicator
        (fun x => ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*f x) := by
      funext x
      simp only [K,indicator_apply,mem_Iio]
    rw [he,lintegral_indicator measurableSet_Iio]
    change _ = ∫⁻ x, ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*f x ∂(μ.restrict (Iio p))
    rw [show μ.restrict (Iio p) = volume.restrict (Ioo (0 : ℝ) p) by
      dsimp only [μ]; rw [Measure.restrict_restrict measurableSet_Iio,hset] ]
  calc
    _ = ∫⁻ p, ∫⁻ x, K p x ∂μ ∂μ := lintegral_congr_ae hinner
    _ = ∫⁻ x, ∫⁻ p, K p x ∂μ ∂μ := lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ x, f x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have he : (fun p => K p x) = (fun p => (ENNReal.ofReal x*f x)*
          (if x < p then ENNReal.ofReal ((p^2)⁻¹) else 0)) := by
        funext p
        by_cases hxp : x < p
        · simp only [K,if_pos hxp]
          ac_rfl
        · simp only [K,if_neg hxp,mul_zero]
      rw [he,lintegral_const_mul (ENNReal.ofReal x*f x)
        (by apply Measurable.ite (measurableSet_lt measurable_const measurable_id); fun_prop; exact measurable_const)]
      calc
        _ ≤ (ENNReal.ofReal x*f x)*ENNReal.ofReal x⁻¹ :=
          mul_le_mul_left' (knopp_kernel_prefix_bound hx.1) _
        _ = (ENNReal.ofReal x*ENNReal.ofReal x⁻¹)*f x := by ac_rfl
        _ = f x := by
          rw [← ENNReal.ofReal_mul hx.1.le,mul_inv_cancel₀ hx.1.ne',ENNReal.ofReal_one,one_mul]

theorem logarithmic_power_prefix_integrable {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) (r : ℝ) :
    IntervalIntegrable (fun x => Real.log ((s x)^r)) volume 0 p := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mp (hi.const_mul r)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (Real.log_rpow (hpos x hx) r).symm

theorem hardy_log_power_prefix {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) (r : ℝ) :
    hardyScalar (fun x => Real.log ((s x)^r)) p =
      r*hardyScalar (fun x => Real.log (s x)) p := by
  have he : (∫ x in (0 : ℝ)..p, Real.log ((s x)^r)) =
      ∫ x in (0 : ℝ)..p, r*Real.log (s x) := by
    simp only [intervalIntegral.integral_of_le hp.le,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.log_rpow (hpos x hx) r
  rw [hardyScalar,he,intervalIntegral.integral_const_mul,hardyScalar]
  ring

theorem geometric_power_weighted_prefix_upper {q : DecGraph} {B p r : ℝ}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) (hr : 0 < r)
    (hi : IntervalIntegrable (fun x => (s x)^r) volume 0 p) :
    (geometricPrefixValue s p)^r ≤ Real.exp 1/p^2*(∫ x in (0 : ℝ)..p, x*(s x)^r) := by
  classical
  by_cases hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞
  · rw [geometricPrefixValue_of_negative_area_top hp.1 (raw_positive_log_prefix_finite hm hP hp) hN,
      Real.zero_rpow hr.ne']
    apply mul_nonneg (div_nonneg (Real.exp_pos 1).le (sq_nonneg p))
    rw [intervalIntegral.integral_of_le hp.1.le,integral_Ioc_eq_integral_Ioo]
    apply setIntegral_nonneg_of_ae_restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxI : x ∈ Ioo (0 : ℝ) B := ⟨hx.1,hx.2.trans hp.2⟩
    exact mul_nonneg hx.1.le (Real.rpow_nonneg (hq0 x hxI (s x) (hs x hxI)) r)
  · have hlog := logarithm_prefix_integrable_of_finite_negative_area hq0 hm hs hP hp hN
    have hpos := positive_prefix_of_finite_negative_log_area
      (selection_antitoneOn q.property.1 hs) (fun x hx => hq0 x hx (s x) (hs x hx)) hp hN
    have he : (geometricPrefixValue s p)^r =
        Real.exp (hardyScalar (fun x => Real.log ((s x)^r)) p) := by
      rw [geometricPrefixValue_of_integrable hp.1 hlog hpos,
        Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,hardy_log_power_prefix hp.1 hlog hpos r]
      congr 1
      ring
    rw [he]
    exact geometric_weighted_prefix_upper hp.1 hi
      (logarithmic_power_prefix_integrable hp.1 hlog hpos r)
      (fun x hx => Real.rpow_pos_of_pos (hpos x hx) r)

theorem knopp_weighted_ofReal_prefix {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p) (hnn : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ f x) :
    ENNReal.ofReal (Real.exp 1/p^2*(∫ x in (0 : ℝ)..p, x*f x)) =
      ENNReal.ofReal (Real.exp 1)*(∫⁻ x in Ioo (0 : ℝ) p,
        ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*ENNReal.ofReal (f x)) := by
  have hxi : IntervalIntegrable (fun x => x*f x) volume 0 p :=
    hi.continuousOn_mul continuous_id.continuousOn
  have hxi' : Integrable (fun x => x*f x) (volume.restrict (Ioo (0 : ℝ) p)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mp hxi
  have hN : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) p)), 0 ≤ x*f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg hx.1.le (hnn x hx)
  have hI : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal x*ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x in (0 : ℝ)..p, x*f x) := by
    calc
      _ = ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (x*f x) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact (ENNReal.ofReal_mul hx.1.le).symm
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hxi' hN,
          intervalIntegral.integral_of_le hp.le,integral_Ioc_eq_integral_Ioo]
  have he : (fun x => ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*ENNReal.ofReal (f x)) =
      (fun x => ENNReal.ofReal ((p^2)⁻¹)*(ENNReal.ofReal x*ENNReal.ofReal (f x))) := by
    funext x
    exact mul_assoc _ _ _
  rw [he,lintegral_const_mul' (ENNReal.ofReal ((p^2)⁻¹)) _ ENNReal.ofReal_ne_top,hI,
    ← mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos (1 : ℝ)).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos (1 : ℝ)).le (inv_nonneg.mpr (sq_nonneg p)))]
  congr 1

theorem polya_knopp_scalar_measurable {q : DecGraph} {B a r : ℝ}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hr : 0 < r) (ha : a ∈ Ioc (0 : ℝ) B) :
    (∫⁻ p in Ioo (0 : ℝ) a, ENNReal.ofReal ((geometricPrefixValue s p)^r)) ≤
      ENNReal.ofReal (Real.exp 1)*(∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((s x)^r)) := by
  classical
  by_cases hInf : (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((s x)^r)) = ∞
  · rw [hInf,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (1 : ℝ))))]
    exact le_top
  have hFm : Measurable (fun x => (s x)^r) := by fun_prop
  have hF0 : ∀ x ∈ Ioo (0 : ℝ) a, 0 ≤ (s x)^r := by
    intro x hx
    have hxI : x ∈ Ioo (0 : ℝ) B := ⟨hx.1,hx.2.trans_le ha.2⟩
    exact Real.rpow_nonneg (hq0 x hxI (s x) (hs x hxI)) r
  have hFi : IntegrableOn (fun x => (s x)^r) (Ioo (0 : ℝ) a) volume := by
    apply (lintegral_ofReal_ne_top_iff_integrable hFm.aestronglyMeasurable ?_).mp hInf
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hF0 x hx
  have hPoint : ∀ p ∈ Ioo (0 : ℝ) a,
      ENNReal.ofReal ((geometricPrefixValue s p)^r) ≤
        ENNReal.ofReal (Real.exp 1)*(∫⁻ x in Ioo (0 : ℝ) p,
          ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*ENNReal.ofReal ((s x)^r)) := by
    intro p hp
    have hpI : p ∈ Ioo (0 : ℝ) B := ⟨hp.1,hp.2.trans_le ha.2⟩
    have hpi : IntervalIntegrable (fun x => (s x)^r) volume 0 p :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.1.le).mpr
        (hFi.mono_set (fun x hx => ⟨hx.1,hx.2.trans hp.2⟩))
    calc
      _ ≤ ENNReal.ofReal (Real.exp 1/p^2*(∫ x in (0 : ℝ)..p, x*(s x)^r)) :=
        ENNReal.ofReal_le_ofReal (geometric_power_weighted_prefix_upper hq0 hm hs hP hpI hr hpi)
      _ = _ := knopp_weighted_ofReal_prefix hp.1 hpi (fun x hx => hF0 x ⟨hx.1,hx.2.trans hp.2⟩)
  calc
    _ ≤ ∫⁻ p in Ioo (0 : ℝ) a, ENNReal.ofReal (Real.exp 1)*
        (∫⁻ x in Ioo (0 : ℝ) p,
          ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*ENNReal.ofReal ((s x)^r)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
      exact hPoint p hp
    _ = ENNReal.ofReal (Real.exp 1)*(∫⁻ p in Ioo (0 : ℝ) a, ∫⁻ x in Ioo (0 : ℝ) p,
        ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*ENNReal.ofReal ((s x)^r)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_left' (knopp_weighted_lintegral_bound (by fun_prop) ha.1) _

theorem polya_knopp {q : DecGraph} {B a r : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s g : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hg : SelectionOn (geometricHardyTransform B q) (Ioo (0 : ℝ) B) g)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hr : 0 < r) (ha : a ∈ Ioc (0 : ℝ) B) :
    (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((g x)^r)) ≤
      ENNReal.ofReal (Real.exp 1)*(∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((s x)^r)) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  have htP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rwa [harea]
  have hG := geometricHardyTransform_well_defined hB hqi hq0 ht hts htP
  have hphi := geometric_hardy_scalar_selection hB hqi hq0 hts htP
  have heG := decreasing_selections_ae_eq hG.1.1 hg hphi volume measurableSet_Ioo
  have heS := decreasing_selections_ae_eq q.property.1 hs hts volume measurableSet_Ioo
  have hsub : Ioo (0 : ℝ) a ⊆ Ioo (0 : ℝ) B := fun x hx => ⟨hx.1,hx.2.trans_le ha.2⟩
  have heGa : g =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] geometricPrefixValue t :=
    ae_restrict_of_ae_restrict_of_subset hsub heG
  have heSa : s =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] t :=
    ae_restrict_of_ae_restrict_of_subset hsub heS
  have heL : (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((g x)^r)) =
      ∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((geometricPrefixValue t x)^r) :=
    lintegral_congr_ae (heGa.fun_comp (fun v => ENNReal.ofReal (v^r)))
  have heR : (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((s x)^r)) =
      ∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((t x)^r) :=
    lintegral_congr_ae (heSa.fun_comp (fun v => ENNReal.ofReal (v^r)))
  rw [heL,heR]
  exact polya_knopp_scalar_measurable hq0 ht hts htP hr ha

end ScalarMonotone.EndOfPaper
end
