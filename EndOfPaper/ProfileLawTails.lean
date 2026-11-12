import EndOfPaper.ProfileChainSample
import EndOfPaper.HalfMixtureCopyTail
import EndOfPaper.ComonotoneQuantiles
import EndOfPaper.QuantileTailCompletion

/-!
The actual prescribed-profile probability law and both original whole completed quantile constraints.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper
section
variable {n : ℕ} {s : Option (Fin n) → ℝ → ℝ}
    (hs : ∀ i, AntitoneOn (s i) (Ioo (0 : ℝ) 1))

local notation "E" => PositiveProductPoint (positiveProfileChain s (Ioo (0 : ℝ) 1))

def positiveProfileHalfOrigin : E := ⟨0,positiveProfileChain_zero s (Ioo (0 : ℝ) 1)⟩

def positiveProfileHalfLaw :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    Measure E := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  exact halfOriginMixture (Measure.map (positiveProfilePointSample s (Ioo (0 : ℝ) 1)) unitUniform)
    positiveProfileHalfOrigin

theorem positiveProfilePoint_coordinate_measurable (j : Option (Fin n)) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    Measurable (fun x : E => x.coords j) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  exact positiveChainMetric_coordinate_measurable (positiveProfileChain_properties hs).1
    (positiveProfileChain_properties hs).2.1 (positiveProfileChain_properties hs).2.2.1
    (positiveProfileChain_zero s (Ioo (0 : ℝ) 1)) j

theorem positiveProfileHalfLaw_probability (hsm : ∀ i, Measurable (s i)) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    IsProbabilityMeasure (positiveProfileHalfLaw hs) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  have hS := positiveProfilePointSample_measurable hs hsm measurableSet_Ioo
  letI : IsProbabilityMeasure (Measure.map (positiveProfilePointSample s (Ioo (0 : ℝ) 1)) unitUniform) :=
    isProbabilityMeasure_map hS.aemeasurable
  exact halfOriginMixture_probability _ _

theorem positiveProfileSample_coordinate_tail (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u) (j : Option (Fin n))
    {t : ℝ} (ht : 0 ≤ t) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    (Measure.map (positiveProfilePointSample s (Ioo (0 : ℝ) 1)) unitUniform)
      {x : E | t < x.coords j} ≤ unitUniform {u | t < s j u} := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  have hS := positiveProfilePointSample_measurable hs hsm measurableSet_Ioo
  have hset : MeasurableSet {x : E | t < x.coords j} :=
    measurableSet_lt measurable_const (positiveProfilePoint_coordinate_measurable hs j)
  rw [Measure.map_apply hS hset]
  apply measure_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  intro htu
  exact htu.trans_le (positiveProfileSampleVector_coordinate_le h0 hu j)

theorem positiveProfileHalfLaw_coordinate_tail (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u) (j : Option (Fin n))
    {t : ℝ} (ht : 0 ≤ t) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    positiveProfileHalfLaw hs {x : E | t < x.coords j} ≤
      (2 : ℝ≥0∞)⁻¹*unitUniform {u | t < s j u} := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  change halfOriginMixture _ positiveProfileHalfOrigin _ ≤ _
  rw [halfOriginMixture_strict_tail _ _ (positiveProfilePoint_coordinate_measurable hs j)
    (by rfl) ht]
  exact mul_le_mul_left' (positiveProfileSample_coordinate_tail hs hsm h0 j ht) _

theorem positiveProfileHalfLaw_marginal (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u) (j : Option (Fin n))
    {q : DecGraph} (hqdom : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hqsel : SelectionOn q.val (Ioo (0 : ℝ) 1) (s j)) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    DecLE (tailQuantile (Measure.map (fun x : E => x.coords j) (positiveProfileHalfLaw hs))) q.val := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  letI : IsProbabilityMeasure (positiveProfileHalfLaw hs) := positiveProfileHalfLaw_probability hs hsm
  apply tailQuantile_decLE_of_profile_selection_tail_bounds
    (positiveProfilePoint_coordinate_measurable hs j) q.property hqdom hqsel
  intro p hp
  have hb := positiveProfileHalfLaw_coordinate_tail hs hsm h0 j (h0 j p hp)
  have hdouble : (2 : ℝ≥0∞)⁻¹*unitUniform {u | s j p < s j u}+
      (2 : ℝ≥0∞)⁻¹*unitUniform {u | s j p < s j u} = unitUniform {u | s j p < s j u} := by
    rw [← add_mul,ENNReal.inv_two_add_inv_two,one_mul]
  have hb' : positiveProfileHalfLaw hs {x : E | s j p < x.coords j} ≤ unitUniform {u | s j p < s j u} := by
    calc
      _ ≤ (2 : ℝ≥0∞)⁻¹*unitUniform {u | s j p < s j u} := hb
      _ ≤ (2 : ℝ≥0∞)⁻¹*unitUniform {u | s j p < s j u}+
          (2 : ℝ≥0∞)⁻¹*unitUniform {u | s j p < s j u} := le_add_of_nonneg_right (zero_le _)
      _ = _ := hdouble
  have hReal := ENNReal.toReal_mono (measure_ne_top unitUniform _) hb'
  have hProfile := (antitone_uniform_quantile_selection (hs j) p hp).1
  have hProfile' : unitUniform.real {u | s j p < s j u} ≤ p := by
    simpa only [measureReal_def,Measure.map_apply (hsm j) measurableSet_Ioi,
      preimage_setOf_eq] using hProfile
  exact hReal.trans hProfile'

theorem positiveProfileHalfLaw_baseline (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u)
    {q : DecGraph} (hqdom : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hqsel : SelectionOn q.val (Ioo (0 : ℝ) 1) (s none))
    (f : E → ℝ) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    LipschitzWith 1 f →
    DecLE (tailQuantile (Measure.map (fun z : E × E => |f z.1-f z.2|)
      ((positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs)))) q.val := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  intro hf
  letI : IsProbabilityMeasure (positiveProfileHalfLaw hs) := positiveProfileHalfLaw_probability hs hsm
  have hS := positiveProfilePointSample_measurable hs hsm measurableSet_Ioo
  let η := Measure.map (positiveProfilePointSample s (Ioo (0 : ℝ) 1)) unitUniform
  letI : IsProbabilityMeasure η := isProbabilityMeasure_map hS.aemeasurable
  have hfm : Measurable f := hf.continuous.measurable
  apply tailQuantile_decLE_of_profile_selection_tail_bounds
    ((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).abs q.property hqdom hqsel
  intro p hp
  have hd (x y : E) : dist x y ≤ max (x.coords none) (y.coords none) :=
    positiveChainMetric_le_max_baseline (positiveProfileChain_properties hs).1
      (positiveProfileChain_properties hs).2.1 (positiveProfileChain_properties hs).2.2.1 x y
  have hb := halfOriginMixture_copy_tail η positiveProfileHalfOrigin
    (positiveProfilePoint_coordinate_measurable hs none) (by rfl) hd hf (h0 none p hp)
  have hTail := positiveProfileSample_coordinate_tail hs hsm h0 none (h0 none p hp)
  have hBound : ((positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs))
      {z : E × E | s none p < |f z.1-f z.2|} ≤ unitUniform {u | s none p < s none u} :=
    hb.trans hTail
  have hReal := ENNReal.toReal_mono (measure_ne_top unitUniform _) hBound
  have hProfile := (antitone_uniform_quantile_selection (hs none) p hp).1
  have hProfile' : unitUniform.real {u | s none p < s none u} ≤ p := by
    simpa only [measureReal_def,Measure.map_apply (hsm none) measurableSet_Ioi,
      preimage_setOf_eq] using hProfile
  exact hReal.trans hProfile'

end
end ScalarMonotone.EndOfPaper
end
