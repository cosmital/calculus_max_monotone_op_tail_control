import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
The literal half-origin law: probability normalization, origin mass, exact tails and extended integrals.
-/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def halfOriginMixture {E : Type*} [MeasurableSpace E] (η : Measure E) (o : E) : Measure E :=
  (2 : ℝ≥0∞)⁻¹ • η+(2 : ℝ≥0∞)⁻¹ • Measure.dirac o

theorem halfOriginMixture_probability {E : Type*} [MeasurableSpace E]
    (η : Measure E) [IsProbabilityMeasure η] (o : E) :
    IsProbabilityMeasure (halfOriginMixture η o) := by
  constructor
  simp only [halfOriginMixture,Measure.add_apply,Measure.smul_apply,measure_univ,
    smul_eq_mul,mul_one,ENNReal.inv_two_add_inv_two]

theorem halfOriginMixture_origin_mass {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] (η : Measure E) (o : E) :
    (1/2 : ℝ≥0∞) ≤ halfOriginMixture η o {o} := by
  have he : halfOriginMixture η o {o} = (2 : ℝ≥0∞)⁻¹*η {o}+(2 : ℝ≥0∞)⁻¹ := by
    simp only [halfOriginMixture,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton o),Set.indicator,
      mem_singleton_iff,if_true,Pi.one_apply,mul_one]
  rw [he,one_div]
  calc
    _ = 0+(2 : ℝ≥0∞)⁻¹ := (zero_add _).symm
    _ ≤ _ := add_le_add_right (zero_le _) _

theorem halfOriginMixture_lintegral {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] (η : Measure E) (o : E) (f : E → ℝ≥0∞) (hf0 : f o = 0) :
    (∫⁻ x, f x ∂halfOriginMixture η o) = (2 : ℝ≥0∞)⁻¹*(∫⁻ x, f x ∂η) := by
  rw [halfOriginMixture,lintegral_add_measure,lintegral_smul_measure,
    lintegral_smul_measure,lintegral_dirac,hf0]
  simp only [smul_eq_mul,mul_zero,add_zero]

theorem halfOriginMixture_strict_tail {E : Type*} [MeasurableSpace E]
    (η : Measure E) (o : E) {X : E → ℝ} (hX : Measurable X) (ho : X o = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    halfOriginMixture η o {x | t < X x} = (2 : ℝ≥0∞)⁻¹*η {x | t < X x} := by
  have hset : MeasurableSet {x | t < X x} := measurableSet_lt measurable_const hX
  have hnot : o ∉ {x | t < X x} := by simpa only [mem_setOf_eq,ho] using not_lt.mpr ht
  simp only [halfOriginMixture,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply' _ hset,Set.indicator,if_neg hnot,mul_zero,add_zero]

end ScalarMonotone.EndOfPaper
end
