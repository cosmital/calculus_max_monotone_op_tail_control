import EndOfPaper.HalfOriginMixture
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Actual independent product-space copies and their coefficient-one baseline tail estimate.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem product_self_independent_copies {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    IndepFun (Prod.fst : E × E → E) Prod.snd (ν.prod ν) ∧
      IdentDistrib (Prod.fst : E × E → E) Prod.snd (ν.prod ν) (ν.prod ν) := by
  constructor
  · apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    change Measure.map id (ν.prod ν) = (Measure.map Prod.fst (ν.prod ν)).prod (Measure.map Prod.snd (ν.prod ν))
    simp only [Measure.map_id,Measure.map_fst_prod,Measure.map_snd_prod,measure_univ,one_smul]
  · exact ⟨measurable_fst.aemeasurable,measurable_snd.aemeasurable,by
      simp only [Measure.map_fst_prod,Measure.map_snd_prod,measure_univ,one_smul]⟩

theorem halfOriginMixture_copy_tail {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (η : Measure E) [IsProbabilityMeasure η] (o : E)
    {A : E → ℝ} (hA : Measurable A) (hAo : A o = 0)
    (hd : ∀ x y, dist x y ≤ max (A x) (A y))
    {f : E → ℝ} (hf : LipschitzWith 1 f) {t : ℝ} (ht : 0 ≤ t) :
    ((halfOriginMixture η o).prod (halfOriginMixture η o))
      {z : E × E | t < |f z.1-f z.2|} ≤ η {x | t < A x} := by
  let ν := halfOriginMixture η o
  letI : IsProbabilityMeasure ν := halfOriginMixture_probability η o
  have hset : MeasurableSet {x | t < A x} := measurableSet_lt measurable_const hA
  have hfst : (ν.prod ν) {z : E × E | t < A z.1} = ν {x | t < A x} := by
    change (ν.prod ν) (Prod.fst ⁻¹' {x | t < A x}) = _
    rw [← Measure.map_apply measurable_fst hset,Measure.map_fst_prod,measure_univ,one_smul]
  have hsnd : (ν.prod ν) {z : E × E | t < A z.2} = ν {x | t < A x} := by
    change (ν.prod ν) (Prod.snd ⁻¹' {x | t < A x}) = _
    rw [← Measure.map_apply measurable_snd hset,Measure.map_snd_prod,measure_univ,one_smul]
  have hsub : {z : E × E | t < |f z.1-f z.2|} ⊆
      {z | t < A z.1} ∪ {z | t < A z.2} := by
    intro z hz
    have hLip : |f z.1-f z.2| ≤ dist z.1 z.2 := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul z.1 z.2
    exact lt_max_iff.mp (hz.trans_le (hLip.trans (hd z.1 z.2)))
  calc
    _ ≤ (ν.prod ν) {z : E × E | t < A z.1}+(ν.prod ν) {z : E × E | t < A z.2} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = ν {x | t < A x}+ν {x | t < A x} := by rw [hfst,hsnd]
    _ = (2 : ℝ≥0∞)⁻¹*η {x | t < A x}+(2 : ℝ≥0∞)⁻¹*η {x | t < A x} := by
      rw [halfOriginMixture_strict_tail η o hA hAo ht]
    _ = _ := by rw [← add_mul,ENNReal.inv_two_add_inv_two,one_mul]

end ScalarMonotone.EndOfPaper
end
