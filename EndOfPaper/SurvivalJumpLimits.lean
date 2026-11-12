import EndOfPaper.AggregationOperator
import MonotoneOperators.Survival

/-!
Strict and weak survival jump limits for arbitrary probability laws
and arbitrary real random variables on their original measurable spaces.
No integrability or atomlessness is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem survival_strict_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Antitone (fun t => μ.real (Ioi t)) := by
  intro a b hab
  exact measureReal_mono (fun x hx => hab.trans_lt hx)

theorem survival_full_domain (μ : Measure ℝ) [IsProbabilityMeasure μ] : dom (survival μ) = univ := by
  ext t
  simp only [mem_univ, iff_true]
  exact ⟨μ.real (Ioi t), le_rfl, measureReal_mono Ioi_subset_Ici_self⟩

theorem survival_strict_jump_limits (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    Tendsto (fun t => μ.real (Ioi t)) (𝓝[<] a) (𝓝 (μ.real (Ici a))) ∧
      Tendsto (fun t => μ.real (Ioi t)) (𝓝[>] a) (𝓝 (μ.real (Ioi a))) := by
  have hle (t : ℝ) : μ.real (Ioi t) ≤ μ.real (Ici t) := measureReal_mono Ioi_subset_Ici_self
  have hd : univ ⊆ dom (survival μ) := by rw [survival_full_domain]
  have hs : SelectionOn (survival μ) univ (fun t => μ.real (Ioi t)) :=
    fun t _ => ⟨le_rfl, hle t⟩
  have hu : sSup (survival μ a) = μ.real (Ici a) := csSup_Icc (hle a)
  have hl : sInf (survival μ a) = μ.real (Ioi a) := csInf_Icc (hle a)
  constructor
  · simpa only [hu] using
      decreasing_selection_tendsto_left (survival_maximal μ) isOpen_univ hd hs (mem_univ a)
  · simpa only [hl] using
      decreasing_selection_tendsto_right (survival_maximal μ) isOpen_univ hd hs (mem_univ a)

theorem survival_random_variable_jump_limits {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Tendsto (fun t => ν.real {ω | t < X ω}) (𝓝[<] a) (𝓝 (ν.real {ω | a ≤ X ω})) ∧
      Tendsto (fun t => ν.real {ω | t < X ω}) (𝓝[>] a) (𝓝 (ν.real {ω | a < X ω})) := by
  letI : IsProbabilityMeasure (Measure.map X ν) := isProbabilityMeasure_map hX.aemeasurable
  have htail (t) : (Measure.map X ν).real (Ioi t) = ν.real {ω | t < X ω} := by
    rw [measureReal_def, Measure.map_apply hX measurableSet_Ioi]
    rfl
  have hweak (t) : (Measure.map X ν).real (Ici t) = ν.real {ω | t ≤ X ω} := by
    rw [measureReal_def, Measure.map_apply hX measurableSet_Ici]
    rfl
  simpa only [htail, hweak] using survival_strict_jump_limits (Measure.map X ν) a

end ScalarMonotone.EndOfPaper
end
