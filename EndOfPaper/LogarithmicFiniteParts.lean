import EndOfPaper.ExtendedLogZero
import EndOfPaper.LogGeometricDomain

/-!
Finite logarithmic parts on an initial prefix.
Finite negative area rules out earlier zeros, and finite positive
and negative parts yield local logarithmic integrability.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

private theorem ofReal_max_zero (v : ℝ) :
    ENNReal.ofReal (max v 0) = ENNReal.ofReal v := by
  by_cases hv : 0 ≤ v
  · rw [max_eq_left hv]
  · have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hv',ENNReal.ofReal_zero,ENNReal.ofReal_eq_zero.mpr hv']

theorem positive_log_prefix_area_finite {s : ℝ → ℝ} {B p : ℝ} (hm : Measurable s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) :
    (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞ := by
  have hplus : IntegrableOn (fun x => max (Real.log (s x)) 0) (Ioo (0 : ℝ) p) volume :=
    (positive_log_integrable_of_lintegral hm hP).mono_set (fun x hx => ⟨hx.1,hx.2.trans hp.2⟩)
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) p)), 0 ≤ max (Real.log (s x)) 0 :=
    Eventually.of_forall (fun x => le_max_right (Real.log (s x)) 0)
  exact (hasFiniteIntegral_iff_ofReal hnn).mp hplus.hasFiniteIntegral

theorem negative_log_area_finite_of_integrable {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞ := by
  have hi' : Integrable (fun x => Real.log (s x)) (volume.restrict (Ioo (0 : ℝ) p)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mp hi
  have hAbs : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal |Real.log (s x)|) < ∞ := by
    simpa only [Real.norm_eq_abs] using
      (hasFiniteIntegral_iff_norm (fun x => Real.log (s x))).mp hi'.hasFiniteIntegral
  have hNeg : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (-Real.log (s x))) < ∞ :=
    lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal
      (neg_le_abs (Real.log (s x))))) hAbs
  have heq : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) =
      ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (-Real.log (s x)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact negativeLogWithZero_of_pos (hpos x hx)
  rw [heq]
  exact ne_of_lt hNeg

theorem positive_prefix_of_finite_negative_log_area {s : ℝ → ℝ} {B p : ℝ}
    (hanti : AntitoneOn s (Ioo (0 : ℝ) B))
    (hnn : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ s x) (hp : p ∈ Ioo (0 : ℝ) B)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞) :
    ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x := by
  intro x hx
  have hxI : x ∈ Ioo (0 : ℝ) B := ⟨hx.1,hx.2.trans hp.2⟩
  by_contra hn
  have hxzero : s x = 0 := le_antisymm (le_of_not_gt hn) (hnn x hxI)
  have hzero : ∀ y ∈ Ioo x p, s y = 0 := by
    intro y hy
    have hyI : y ∈ Ioo (0 : ℝ) B := ⟨hx.1.trans hy.1,hy.2.trans hp.2⟩
    have hle := hanti hxI hyI hy.1.le
    exact le_antisymm (by simpa only [hxzero] using hle) (hnn y hyI)
  exact hN (negative_log_area_eq_top_of_zero_interval hx.1.le hx.2 le_rfl hzero)

theorem logarithm_integrable_of_finite_log_parts {s : ℝ → ℝ} {p : ℝ}
    (hp : 0 < p) (hm : Measurable s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) :
    IntervalIntegrable (fun x => Real.log (s x)) volume 0 p := by
  have hplus := positive_log_integrable_of_lintegral hm hP
  have hnegMeas : Measurable (fun x => max (-Real.log (s x)) 0) := by fun_prop
  have hN' : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (-Real.log (s x)) 0)) ≠ ∞ := by
    have heq : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (-Real.log (s x)) 0)) =
        ∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [negativeLogWithZero_of_pos (hpos x hx),ofReal_max_zero]
    rwa [heq]
  have hminus : IntegrableOn (fun x => max (-Real.log (s x)) 0) (Ioo (0 : ℝ) p) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hnegMeas.aestronglyMeasurable
      (Eventually.of_forall (fun x => le_max_right (-Real.log (s x)) 0))).mp hN'
  have heq (x : ℝ) : max (Real.log (s x)) 0-max (-Real.log (s x)) 0 = Real.log (s x) := by
    by_cases hx : 0 ≤ Real.log (s x)
    · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),sub_zero]
    · have hx' : Real.log (s x) ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx')]
      ring
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mpr
    ((hplus.sub hminus).congr (Eventually.of_forall heq))

theorem prefix_log_domain_of_finite_negative_area {q : DecGraph} {B p : ℝ}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hp : p ∈ Ioo (0 : ℝ) B)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞) :
    Ioo (0 : ℝ) p ⊆ interior (dom (logOp q.val)) := by
  have hpos := positive_prefix_of_finite_negative_log_area
    (selection_antitoneOn q.property.1 hs) (fun x hx => hq0 x hx (s x) (hs x hx)) hp hN
  intro x hx
  obtain ⟨y,hxy,hyp⟩ := exists_between hx.2
  have hyI : y ∈ Ioo (0 : ℝ) B := ⟨hx.1.trans hxy,hyp.trans hp.2⟩
  have hD := positive_initial_interval_in_log_dom q.property hqi hyI (hs y hyI)
    (hpos y ⟨hx.1.trans hxy,hyp⟩)
  exact isOpen_Ioo.subset_interior_iff.mpr hD ⟨hx.1,hxy⟩

theorem logarithm_prefix_integrable_of_finite_negative_area {q : DecGraph} {B p : ℝ}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞) :
    IntervalIntegrable (fun x => Real.log (s x)) volume 0 p := by
  have hpos := positive_prefix_of_finite_negative_log_area
    (selection_antitoneOn q.property.1 hs) (fun x hx => hq0 x hx (s x) (hs x hx)) hp hN
  have hP' := positive_log_prefix_area_finite hm hP hp
  exact logarithm_integrable_of_finite_log_parts hp.1 hm hP' hN hpos

end ScalarMonotone.EndOfPaper
end
