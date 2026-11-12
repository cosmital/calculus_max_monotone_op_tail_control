import EndOfPaper.Moments
import EndOfPaper.PositivePowerArea
import MonotoneOperators.ExtremaExamples
import MonotoneOperators.ProbabilityBounds

/-!
The actual lattice infimum with the constant-one graph, its positive domain, the whole survival bound and the full divergent centered-moment inequality and identity.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem decreasing_inf_min_mem (a b : DecGraph) {t u v : ℝ}
    (hu : u ∈ a.val t) (hv : v ∈ b.val t) : min u v ∈ (a ⊓ b).val t := by
  have hju := (DecGraph.mem_iff_J a).mp hu
  have hjv := (DecGraph.mem_iff_J b).mp hv
  apply (DecGraph.mem_iff_J (a ⊓ b)).mpr
  rcases le_total u v with huv | hvu
  · have hle : t ≤ b.J (t-u) := by
      calc
        t = b.J (t-v) := hjv.symm
        _ ≤ b.J (t-u) := b.monotone_J (sub_le_sub_left huv t)
    rw [min_eq_left huv,DecGraph.J_inf,hju,min_eq_left hle]
  · have hle : t ≤ a.J (t-v) := by
      calc
        t = a.J (t-u) := hju.symm
        _ ≤ a.J (t-v) := a.monotone_J (sub_le_sub_left hvu t)
    rw [min_eq_right hvu,DecGraph.J_inf,hjv,min_eq_right hle]

theorem survival_le_operator_cap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (α : DecGraph) (hα : DecLE (survival ν) α.val) :
    DecLE (survival ν) (α ⊓ DecGraph.constant 1).val := by
  change (⟨survival ν,survival_maximal ν⟩ : DecGraph) ≤ α ⊓ DecGraph.constant 1
  refine le_inf hα ?_
  change DecLE (survival ν) (ofFun (fun _ => (1 : ℝ)))
  apply (survival_comparison_iff ν _).mpr
  intro t v hv
  have hv1 : v = 1 := hv
  rw [hv1]
  exact measureReal_le_one

theorem operator_cap_positive_domain (α : DecGraph) (hαdom : Ioi 0 ⊆ dom α.val) :
    Ioi 0 ⊆ dom (α ⊓ DecGraph.constant 1).val := by
  intro t ht
  obtain ⟨a,ha⟩ := hαdom ht
  exact ⟨min a 1,decreasing_inf_min_mem α (DecGraph.constant 1) ha rfl⟩

theorem centered_moment_operator_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (c : ℝ) (α : DecGraph)
    (hαdom : Ioi 0 ⊆ dom α.val)
    (hα0 : ∀ t > 0, ∀ v ∈ α.val t, 0 ≤ v)
    (hbound : DecLE (survival (Measure.map (fun ω => |X ω-c|) μ)) α.val)
    {b : ℝ → ℝ} (hb : ∀ t > 0, b t ∈ (α ⊓ DecGraph.constant 1).val t)
    {r : ℝ} (hr : 0 < r) :
    DecLE (survival (Measure.map (fun ω => |X ω-c|) μ)) (α ⊓ DecGraph.constant 1).val ∧
    ((∫⁻ ω, ENNReal.ofReal (|X ω-c|^r) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b (t^(1/r)))) ∧
    ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b (t^(1/r)))) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1)*b t)) := by
  let Y : Ω → ℝ := fun ω => |X ω-c|
  have hY : Measurable Y := (hX.sub measurable_const).abs
  letI : IsProbabilityMeasure (Measure.map Y μ) := isProbabilityMeasure_map hY.aemeasurable
  have hcap := survival_le_operator_cap (Measure.map Y μ) α hbound
  have htail := (survival_map_comparison_iff μ hY _).mp hcap
  refine ⟨hcap,?_,?_⟩
  · apply expectation_le_tail_area μ
      ((Real.continuous_rpow_const hr.le).measurable.comp hY).aemeasurable
      (Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg (X ω-c)) r))
    intro t ht
    have ht0 : 0 < t^(1/r) := Real.rpow_pos_of_pos ht _
    have hset : {ω | t < (Y ω)^r} = {ω | t^(1/r) < Y ω} := by
      ext ω
      rw [one_div]
      exact (Real.rpow_inv_lt_iff_of_pos ht.le (abs_nonneg (X ω-c)) hr).symm
    change μ {ω | t < (Y ω)^r} ≤ ENNReal.ofReal (b (t^(1/r)))
    rw [hset,← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (htail (hb _ ht0))
  · rw [positive_power_area_substitution (fun t => ENNReal.ofReal (b t)) hr]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]

end ScalarMonotone.EndOfPaper
end
