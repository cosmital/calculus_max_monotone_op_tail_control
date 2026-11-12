import MonotoneOperators.ProbabilityBounds
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Original-space quantile tail tests, positive Lipschitz scaling,
and exchangeability of independent identically distributed copies.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem quantile_comparison_strict_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {q : Operator} (hX : Measurable X)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q) {a t : ℝ} (ht : t ∈ q a) :
    μ.real {ω | t < X ω} ≤ a := by
  have hSur : DecLE (survival (Measure.map X μ)) (inverse q) := by
    simpa only [tailQuantile,inverse_inverse] using decLE_inverse_iff.mpr hQ
  exact ((survival_map_comparison_iff μ hX (inverse q)).mp hSur) ht

theorem scaled_lipschitz_tail_of_quantile_control {Ω E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') {q : Operator}
    (hcontrol : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    {a t : ℝ} (ht : t ∈ q a) {K : ℝ≥0} (hK : 0 < (K : ℝ))
    {f : E → ℝ} (hf : LipschitzWith K f) :
    μ.real {ω | (K : ℝ)*t < |f (Z ω)-f (Z' ω)|} ≤ a := by
  let fn := fun x => f x/(K : ℝ)
  have hfn : LipschitzWith 1 fn := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |f x/(K : ℝ)-f y/(K : ℝ)| ≤ (1 : ℝ)*dist x y
    rw [← sub_div,abs_div,abs_of_pos hK,one_mul]
    apply (div_le_iff₀ hK).mpr
    simpa only [Real.dist_eq,mul_comm] using hf.dist_le_mul x y
  have hfnm : Measurable fn := hfn.continuous.measurable
  have hm := ((hfnm.comp hZ).sub (hfnm.comp hZ')).abs
  have hb := quantile_comparison_strict_tail hm (hcontrol fn hfn) ht
  have hset : {ω | (K : ℝ)*t < |f (Z ω)-f (Z' ω)|} =
      {ω | t < |fn (Z ω)-fn (Z' ω)|} := by
    ext ω
    simp only [mem_setOf_eq,fn,← sub_div,abs_div,abs_of_pos hK,lt_div_iff₀ hK,mul_comm t (K : ℝ)]
  rw [hset]
  exact hb

theorem independent_copy_exchangeable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ) :
    IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ := by
  have hZZ' := (indepFun_iff_map_prod_eq_prod_map_map
    hident.aemeasurable_fst hident.aemeasurable_snd).mp hindep
  have hZ'Z := (indepFun_iff_map_prod_eq_prod_map_map
    hident.aemeasurable_snd hident.aemeasurable_fst).mp hindep.symm
  refine ⟨hident.aemeasurable_fst.prodMk hident.aemeasurable_snd,
    hident.aemeasurable_snd.prodMk hident.aemeasurable_fst,?_⟩
  calc
    _ = (Measure.map Z μ).prod (Measure.map Z' μ) := hZZ'
    _ = (Measure.map Z' μ).prod (Measure.map Z μ) := by rw [hident.map_eq]
    _ = _ := hZ'Z.symm

theorem exchangeable_real_measure {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {Z Z' : Ω → E}
    (hSwap : IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ)
    {S : Set (E × E)} (hS : MeasurableSet S) :
    μ.real {ω | (Z ω,Z' ω) ∈ S} = μ.real {ω | (Z' ω,Z ω) ∈ S} :=
  congrArg ENNReal.toReal (hSwap.measure_mem_eq hS)

end ScalarMonotone.EndOfPaper
end
