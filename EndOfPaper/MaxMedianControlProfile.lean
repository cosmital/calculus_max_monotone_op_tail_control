import EndOfPaper.InitialProfileAffine
import EndOfPaper.MaxMedianControlTail
import EndOfPaper.AffinePositiveLogArea
import EndOfPaper.GeometricDilation
import EndOfPaper.QuantileTailCompletion

/-!
The actual half-dilated completed median control profile, its whole quantile bound, nonnegativity and derived positive-log area.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def halfAffineProfile (q : DecGraph) (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (m c : ℝ) (hc : 0 ≤ c) : DecGraph :=
  let r := completedProfileAffine 1 m c q (by norm_num) hqi hc
  completedProfileDilation 1 1 (1/2) r (completedProfileAffine_domain (by norm_num) hqi hc).1
    (by norm_num) (by norm_num) (by norm_num)

theorem halfAffineProfile_selection {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1) {m c : ℝ} (hc : 0 ≤ c)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s) :
    interior (dom (halfAffineProfile q hqi m c hc).val) = Ioo (0 : ℝ) 1 ∧
      SelectionOn (halfAffineProfile q hqi m c hc).val (Ioo (0 : ℝ) 1)
        (fun x => m+c*s (x/2)) := by
  let r := completedProfileAffine 1 m c q (by norm_num) hqi hc
  have hr := completedProfileAffine_domain (m := m) (by norm_num) hqi hc
  have hd := completedProfileDilation_properties hr.1
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ)*1 ≤ 1)
  refine ⟨hd.1,?_⟩
  intro x hx
  have hx2 : x/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  change m+c*s (x/2) ∈ (completedProfileDilation 1 1 (1/2) r hr.1
    (by norm_num) (by norm_num) (by norm_num)).val x
  rw [hd.2 x hx]
  have hh := completedProfileAffine_selection (m := m) (by norm_num) hqi hc hs (x/2) hx2
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm (2 : ℝ)⁻¹ x] using hh

theorem max_median_control_quantile_bound {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ q.val x, 0 ≤ t)
    (hq : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q.val)
    {K : ℝ≥0} (hK : 0 < (K : ℝ)) {f g : E → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g)
    {mf mg : ℝ} (hmf : IsRealMedian (f ∘ Z) μ mf) (hmg : IsRealMedian (g ∘ Z) μ mg)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s) :
    DecLE (tailQuantile (Measure.map (fun ω => max (f (Z ω)) (g (Z ω))) μ))
      (halfAffineProfile q hqi (max mf mg) (K : ℝ) hK.le).val := by
  have hd := halfAffineProfile_selection (m := max mf mg) hqi hK.le hs
  apply tailQuantile_decLE_of_profile_selection_tail_bounds
    ((hf.continuous.measurable.comp hZ).max (hg.continuous.measurable.comp hZ))
    (halfAffineProfile q hqi (max mf mg) (K : ℝ) hK.le).property hd.1 hd.2
  intro x hx
  have hx2 : x/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hh := max_median_control_strict_tail hZ hZ' hi he hq hK hf hg hmf hmg
    (hs (x/2) hx2) (hq0 (x/2) hx2 _ (hs (x/2) hx2))
  have hhalf : 2*(x/2) = x := by ring
  simpa only [Function.comp_apply,hhalf] using hh

theorem halfAffineProfile_nonnegative {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1) {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ q.val x, 0 ≤ t) :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ (halfAffineProfile q hqi m c hc).val x, 0 ≤ t := by
  let r := completedProfileAffine 1 m c q (by norm_num) hqi hc
  have hr := completedProfileAffine_domain (m := m) (by norm_num) hqi hc
  have hd := completedProfileDilation_properties hr.1
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ)*1 ≤ 1)
  intro x hx t ht
  change t ∈ (completedProfileDilation 1 1 (1/2) r hr.1
    (by norm_num) (by norm_num) (by norm_num)).val x at ht
  rw [hd.2 x hx] at ht
  apply completedProfileAffine_nonnegative (by norm_num) hqi hm hc hq0 ((1/2)*x) _ t ht
  constructor <;> linarith [hx.1,hx.2]

theorem half_affine_positive_log_area_finite {s : ℝ → ℝ} (hsm : Measurable s)
    (hs0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ s x)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (m+c*s (x/2))) 0)) < ∞ := by
  have ha := positive_log_area_affine_finite hsm hs0 hP hm hc
  have hd := positive_log_area_dilation_finite (s := fun x => m+c*s x) (by fun_prop) ha
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ)*1 ≤ 1)
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm (2 : ℝ)⁻¹] using hd

end ScalarMonotone.EndOfPaper
end
