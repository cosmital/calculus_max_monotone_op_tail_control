import EndOfPaper.RandomizedLogTail
import EndOfPaper.GeometricLogExcess
import EndOfPaper.ZeroControlTail
import EndOfPaper.ProfileLogAdmissibility
import Mathlib.Data.Fintype.BigOperators

/-!
The exact two-parameter scalar tail estimate from the
original single combined positive-log area and arbitrary
input selections. Internal zeros and zero areas are included.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem randomized_two_parameter_of_individual_areas {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hqΔ : MaximalDecreasing qΔ)
    (hδdom : Ioo (0 : ℝ) 1 ⊆ interior (dom qΔ))
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : ι → Operator} (hq : ∀ i, MaximalDecreasing (q i))
    (hqdom : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (q i))
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    {sq : ι → ℝ → ℝ} (hsqm : ∀ i, Measurable (sq i))
    (hsq : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    (hPi : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p)) 0)) < ∞)
    {h : E → ℝ} (hhm : Measurable h)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {a b t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (ht : t ∈ qΔ a) :
    μ.real {ω | (∏ i, geometricPrefixValue (sq i) b)*t < |h (Z ω)-h (Z' ω)|} ≤ a+2*b := by
  classical
  choose c hcb using fun i => hqdom i hb
  have ht0 : 0 ≤ t := hδ0 a ha t ht
  have hφ0 (i : ι) : 0 ≤ geometricPrefixValue (sq i) b := by
    cases he : extendedLogIntegral (sq i) b <;> simp only [geometricPrefixValue,he]
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  by_cases hc : ∀ i, 0 < c i
  · have hArea (i : ι) :
        (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p/c i)) 0)) < ∞ := by
      have hm : Measurable (fun p => max (Real.log (sq i p/c i)) 0) := by fun_prop
      have hi := (profile_log_excess_integral (hq i).1 (hsqm i) (hsq i) (hq0 i)
        (hPi i) hb (hc i) (hcb i)).1
      exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
        hm.aestronglyMeasurable (Eventually.of_forall (fun p => le_max_right (Real.log (sq i p/c i)) 0))).mpr hi)
    let I : ℝ := ∑ i, ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq i p/c i)) 0
    have hI : 0 ≤ I := Finset.sum_nonneg (fun i _ => integral_nonneg (fun p => le_max_right _ _))
    have hC : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc i)
    have heProd : (∏ i, geometricPrefixValue (sq i) b) = (∏ i, c i)*Real.exp (I/b) := by
      calc
        _ = ∏ i, c i*Real.exp ((∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq i p/c i)) 0)/b) :=
          Finset.prod_congr rfl (fun i _ => geometricPrefixValue_log_excess (hq i).1
            (hsqm i) (hsq i) (hq0 i) (hPi i) hb (hc i) (hcb i))
        _ = _ := by rw [Finset.prod_mul_distrib,← Real.exp_sum,← Finset.sum_div]
    have hX : Measurable (fun ω => |h (Z ω)-h (Z' ω)|) := ((hhm.comp hZ).sub (hhm.comp hZ')).abs
    have hbudget := logarithmic_tail_budget hX hC.le ht0 hb.1 hI
      (fun s hs => randomized_lipschitz_logarithmic_tail hZ hZ' hindep hident hqΔ hδdom hδ0 hδ
        hΛm hΛ0 hq hqdom hq0 hQ hsqm hsq hc hArea hhm hmod ha hs ht)
    simpa only [← heProd] using hbudget
  · obtain ⟨i,hi⟩ := not_forall.mp hc
    have hci0 : c i = 0 := le_antisymm (le_of_not_gt hi) (hq0 i b hb (c i) (hcb i))
    have hzero : (0 : ℝ) ∈ q i b := by simpa only [hci0] using hcb i
    have htail := randomized_zero_cutoff_tail hZ hident hΛm hΛ0 hmod i (hQ i) hzero
      (τ := (∏ j, geometricPrefixValue (sq j) b)*t)
      (mul_nonneg (Finset.prod_nonneg (fun j _ => hφ0 j)) ht0)
    exact htail.trans (by linarith [ha.1])

theorem randomized_lipschitz_two_parameter {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hqΔ : MaximalDecreasing qΔ)
    (hδdom : interior (dom qΔ) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : ι → Operator} (hq : ∀ i, MaximalDecreasing (q i))
    (hqdom : ∀ i, interior (dom (q i)) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q i p, v = 0)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ (Ioo (0 : ℝ) 1) sqΔ)
    {sq : ι → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞)
    {h : E → ℝ} (hhm : Measurable h)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {a b t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (ht : t ∈ qΔ a) :
    μ.real {ω | (∏ i, geometricPrefixValue (sq i) b)*t < |h (Z ω)-h (Z' ω)|} ≤ a+2*b := by
  classical
  let Q : Option ι → Operator := fun j => match j with | none => qΔ | some i => q i
  let S : Option ι → ℝ → ℝ := fun j => match j with | none => sqΔ | some i => sq i
  have hMax (j : Option ι) : MaximalDecreasing (Q j) := by
    cases j with
    | none => exact hqΔ
    | some i => exact hq i
  have hZero (j : Option ι) : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Q j p, 0 ≤ v := by
    cases j with
    | none => exact hδ0
    | some i => exact hq0 i
  have hNonzero (j : Option ι) : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Q j p, v = 0 := by
    cases j with
    | none => exact hnδ
    | some i => exact hnq i
  have hSel (j : Option ι) : SelectionOn (Q j) (Ioo (0 : ℝ) 1) (S j) := by
    cases j with
    | none => exact hsδ
    | some i => exact hsq i
  have hProduct (p : ℝ) : (∏ j : Option ι, S j p) = sqΔ p*(∏ i, sq i p) := by
    rw [Fintype.prod_option]
  have hPAll : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (∏ j : Option ι, S j p)) 0)) < ∞ := by
    simp_rw [hProduct]
    exact hP
  have hAreas := nonzero_profiles_individual_log_areas (by norm_num) hMax hZero hNonzero hSel hPAll
  have hOriginal (i : ι) :
      (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p)) 0)) < ∞ := by
    exact hAreas (some i)
  choose s hsm hss using fun i => exists_global_measurable_selection
    (Or.inr (hq i).1) measurableSet_Ioo
    (fun p hp => interior_subset (show p ∈ interior (dom (q i)) from by rwa [hqdom i]))
  have he (i : ι) : s i =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sq i := by
    apply ae_selections_ae_eq (Or.inr (hq i).1) (volume.restrict (Ioo (0 : ℝ) 1))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
      exact hss i p hp
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
      exact hsq i p hp
  have hPs (i : ι) : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i p)) 0)) < ∞ := by
    have heArea : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i p)) 0)) =
        ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p)) 0) :=
      lintegral_congr_ae ((he i).fun_comp (fun y : ℝ => ENNReal.ofReal (max (Real.log y) 0)))
    rw [heArea]
    exact hOriginal i
  have hbound := randomized_two_parameter_of_individual_areas hZ hZ' hindep hident hqΔ
    (show Ioo (0 : ℝ) 1 ⊆ interior (dom qΔ) from by rw [hδdom]) hδ0 hδ hΛm hΛ0 hq
    (fun i p hp => interior_subset (show p ∈ interior (dom (q i)) from by rwa [hqdom i]))
    hq0 hQ hsm hss hPs hhm hmod ha hb ht
  have hφ : (∏ i, geometricPrefixValue (s i) b) = ∏ i, geometricPrefixValue (sq i) b :=
    Finset.prod_congr rfl (fun i _ => geometricPrefixValue_congr_ae (he i) hb.2.le)
  simpa only [hφ] using hbound

end ScalarMonotone.EndOfPaper
end
