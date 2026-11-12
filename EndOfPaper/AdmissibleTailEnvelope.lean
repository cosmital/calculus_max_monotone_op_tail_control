import EndOfPaper.PositiveSurvivalCompletion
import EndOfPaper.ProfileMomentComparison
import MonotoneOperators.OrderGeometry

/-!
Original admissible survival envelopes force inverse-domain coverage, nonnegative inverse fibers and L1, without extra boundedness or integrability hypotheses.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem admissible_tail_inverse_geometry (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) {β : Operator} (hβ : MaximalDecreasing β)
    (hβ1 : DecLE β (ofFun (fun _ => (1 : ℝ)))) (hzero : IsGLB (ran β) 0)
    (hS : DecLE (survival ν) β) :
    (Ioo (0 : ℝ) 1 ⊆ dom (inverse β)) ∧
    interior (dom (inverse β)) = Ioo (0 : ℝ) 1 ∧
    (dom (inverse β) ⊆ Icc (0 : ℝ) 1) ∧
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ inverse β p, 0 ≤ v := by
  have hq := inverse_maximal_decreasing hβ
  have hQ : DecLE (tailQuantile ν) (inverse β) := decLE_inverse_iff.mpr hS
  have hdom : dom (inverse β) ⊆ Icc (0 : ℝ) 1 := by
    rintro p ⟨t,ht⟩
    change p ∈ β t at ht
    refine ⟨hzero.1 ⟨t,ht⟩,?_⟩
    exact hβ1 ht (show (1 : ℝ) ∈ ofFun (fun _ => (1 : ℝ)) (t-1) from rfl) (by linarith)
  have hcover : Ioo (0 : ℝ) 1 ⊆ dom (inverse β) := by
    intro p hp
    have hlow : ∃ z ∈ dom (inverse β), z < p := by
      by_contra hn
      push_neg at hn
      have hp0 : p ≤ 0 := hzero.2 (by
        intro z hz
        exact hn z hz)
      exact (not_lt_of_ge hp0) hp.1
    have hmid : (p+1)/2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hp.1,hp.2]
    obtain ⟨z,hz,hpz⟩ := (decLE_domains (tailQuantile_maximal ν) hq hQ).2
      (mem_lowerHull (tailQuantile_fiber_nonempty ν hmid))
    obtain ⟨a,ha,hap⟩ := hlow
    exact (decreasing_dom_ordConnected hq).out ha hz ⟨hap.le,by linarith [hp.2]⟩
  have hi : interior (dom (inverse β)) = Ioo (0 : ℝ) 1 :=
    domain_interior_of_open_interval isOpen_Ioo ordConnected_Ioo
      (nonempty_Ioo.mpr zero_lt_one) hcover (by
        simpa only [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hdom)
  refine ⟨hcover,hi,hdom,?_⟩
  intro p hp v hv
  obtain ⟨w,hw,hwv⟩ := (decLE_fiber (tailQuantile_maximal ν) hq hQ
    (tailQuantile_fiber_nonempty ν hp) (hcover hp)).1 (mem_upperHull hv)
  exact (nonnegative_law_quantile_nonnegative ν hν hp hw).trans hwv

theorem admissible_tail_integrability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hY0 : 0 ≤ᵐ[μ] Y) {β : Operator} (hβ : MaximalDecreasing β)
    (hβ1 : DecLE β (ofFun (fun _ => (1 : ℝ)))) (hzero : IsGLB (ran β) 0)
    (hS : DecLE (survival (Measure.map Y μ)) β) {b : ℝ → ℝ}
    (hb : SelectionOn (inverse β) (Ioo (0 : ℝ) 1) b)
    (hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b p|) < ∞) :
    Integrable Y μ ∧ Integrable b unitUniform := by
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  have hν : ∀ᵐ x ∂Measure.map Y μ, 0 ≤ x :=
    (ae_map_iff hY.aemeasurable measurableSet_Ici).mpr hY0
  have hg := admissible_tail_inverse_geometry (Measure.map Y μ) hν hβ hβ1 hzero hS
  have hbm : AEMeasurable b unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo
      (selection_antitoneOn (inverse_maximal_decreasing hβ).1 hb)
  have hbn : 0 ≤ᵐ[unitUniform] b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    exact hg.2.2.2 p hp (b p) (hb p hp)
  have hbf : (∫⁻ p, ENNReal.ofReal (b p) ∂unitUniform) < ∞ :=
    (lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (le_abs_self (b p)))).trans_lt hfinite
  have hbi : Integrable b unitUniform :=
    ⟨hbm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hbn).mpr hbf⟩
  have hbound := random_variable_profile_lintegral_bound μ hY
    (inverse_maximal_decreasing hβ) hg.1 (decLE_inverse_iff.mpr hS) hb
    ENNReal.continuous_ofReal.measurable (fun _ _ h => ENNReal.ofReal_le_ofReal h)
  refine ⟨⟨hY.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hY0).mpr (hbound.trans_lt hbf)⟩,hbi⟩

end ScalarMonotone.EndOfPaper
end
