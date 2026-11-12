import EndOfPaper.ProfileLogExcess
import EndOfPaper.LogarithmicExpectations

/-!
Logarithmic excess L1 and expectation comparison for arbitrary profile selections, without extra measurable-selection assumptions.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem profile_log_excess_integrable_of_selection {q : Operator} {sq : ℝ → ℝ}
    (hq : MaximalDecreasing q) (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p)) 0)) < ∞)
    {b c : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hcb : c ∈ q b) :
    IntegrableOn (fun p => max (Real.log (sq p/c)) 0) (Ioo (0 : ℝ) 1) volume := by
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection (Or.inr hq.1)
    measurableSet_Ioo (fun p hp => ⟨sq p,hsq p hp⟩)
  have he := decreasing_selections_ae_eq hq.1 hs hsq volume measurableSet_Ioo
  have hPs : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s p)) 0)) < ∞ := by
    have heArea : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s p)) 0)) =
        ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p)) 0) :=
      lintegral_congr_ae (he.fun_comp (fun x : ℝ => ENNReal.ofReal (max (Real.log x) 0)))
    rw [heArea]
    exact hP
  exact ((profile_log_excess_integral hq.1 hsm hs hq0 hPs hb hc hcb).1).congr
    (he.fun_comp (fun x : ℝ => max (Real.log (x/c)) 0))

theorem logarithmic_excess_mean_bound_of_selection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : 0 ≤ᵐ[μ] X) {q : Operator} (hq : MaximalDecreasing q)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {sq : ℝ → ℝ} (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    {c : ℝ} (hc : 0 < c)
    (hi : IntegrableOn (fun p => max (Real.log (sq p/c)) 0) (Ioo (0 : ℝ) 1) volume) :
    Integrable (fun ω => max (Real.log (X ω/c)) 0) μ ∧
      (∫ ω, max (Real.log (X ω/c)) 0 ∂μ) ≤
        ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq p/c)) 0 := by
  have hn : ∀ᵐ p ∂volume.restrict (Ioo (0 : ℝ) 1), 0 ≤ max (Real.log (sq p/c)) 0 :=
    Eventually.of_forall (fun _ => le_max_right _ _)
  have hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p/c)) 0)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral
  have hd : Ioo (0 : ℝ) 1 ⊆ dom q := fun p hp => ⟨sq p,hsq p hp⟩
  have hXi := logarithmic_excess_integrable μ hX hX0 hq hd hq0 hQ hsq hc hfinite
  refine ⟨hXi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun p => le_max_right (Real.log (sq p/c)) 0))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hXi
      (Eventually.of_forall (fun _ => le_max_right _ _)),
    ofReal_integral_eq_lintegral_ofReal hi hn]
  exact logarithmic_excess_lintegral_bound μ hX hX0 hq hd hq0 hQ hsq hc

end ScalarMonotone.EndOfPaper
end
