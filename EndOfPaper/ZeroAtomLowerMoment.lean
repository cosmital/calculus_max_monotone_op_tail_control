import EndOfPaper.NonnegativeMomentNorm
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.IdentDistrib

/-!
The two zero-copy contributions give the extended lower moment, without any finite-moment assumption.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem zero_atom_product_moment_lower (ν : Measure ℝ) [SFinite ν]
    {r : ℝ} (hr : 0 < r) :
    (ν {0}+ν {0})*(∫⁻ x : ℝ, ENNReal.ofReal (|x|^r) ∂ν) ≤
      ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(ν.prod ν) := by
  classical
  let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (|x|^r)
  let a : ℝ → ℝ≥0∞ := ({0} : Set ℝ).indicator (fun _ => 1)
  have hw : Measurable w :=
    ((Real.continuous_rpow_const hr.le).comp continuous_abs).measurable.ennreal_ofReal
  have ha : Measurable a := measurable_const.indicator (measurableSet_singleton 0)
  have hw0 : w 0 = 0 := by simp [w,Real.zero_rpow hr.ne']
  have hf : Measurable (fun z : ℝ × ℝ => w z.1*a z.2) :=
    (hw.comp measurable_fst).mul (ha.comp measurable_snd)
  have hpoint (z : ℝ × ℝ) : w z.1*a z.2+a z.1*w z.2 ≤ ENNReal.ofReal (|z.1-z.2|^r) := by
    by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0
    · simp [hx,hy,hw0,a]
    · simp [hx,hy,hw0,a,w,abs_neg]
    · simp [hx,hy,hw0,a,w]
    · simp [hx,hy,a]
  have hIa : (∫⁻ x : ℝ, a x ∂ν) = ν {0} := by
    simpa only [a,one_mul] using lintegral_indicator_const (μ := ν) (measurableSet_singleton 0) (1 : ℝ≥0∞)
  calc
    _ = (∫⁻ x : ℝ, w x ∂ν)*(∫⁻ x : ℝ, a x ∂ν)+
        (∫⁻ x : ℝ, a x ∂ν)*(∫⁻ x : ℝ, w x ∂ν) := by rw [hIa]; ring
    _ = (∫⁻ z : ℝ × ℝ, w z.1*a z.2 ∂(ν.prod ν))+
        (∫⁻ z : ℝ × ℝ, a z.1*w z.2 ∂(ν.prod ν)) := by
      rw [lintegral_prod_mul hw.aemeasurable ha.aemeasurable,
        lintegral_prod_mul ha.aemeasurable hw.aemeasurable]
    _ = ∫⁻ z : ℝ × ℝ, w z.1*a z.2+a z.1*w z.2 ∂(ν.prod ν) :=
      (lintegral_add_left hf _).symm
    _ ≤ _ := lintegral_mono hpoint

theorem independent_copy_zero_atom_moment_lower {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    (hzero : (1/2 : ℝ≥0∞) ≤ μ {ω | X ω = 0}) {r : ℝ} (hr : 0 < r) :
    (∫⁻ ω, ENNReal.ofReal (|X ω|^r) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal (|X ω-X' ω|^r) ∂μ := by
  let ν := Measure.map X μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hPair := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hX'.aemeasurable).mp hi
  rw [← he.map_eq] at hPair
  have hAtom : ν {0} = μ {ω | X ω = 0} := by
    change (Measure.map X μ) {0} = _
    rw [Measure.map_apply hX (measurableSet_singleton 0)]
    rfl
  have hMass : (1 : ℝ≥0∞) ≤ ν {0}+ν {0} := by
    rw [hAtom]
    calc
      (1 : ℝ≥0∞) = (1/2 : ℝ≥0∞)+(1/2 : ℝ≥0∞) := by
        simpa only [one_div] using ENNReal.inv_two_add_inv_two.symm
      _ ≤ _ := add_le_add hzero hzero
  have hw : Measurable (fun x : ℝ => ENNReal.ofReal (|x|^r)) :=
    ((Real.continuous_rpow_const hr.le).comp continuous_abs).measurable.ennreal_ofReal
  have hDiff : Continuous (fun z : ℝ × ℝ => z.1-z.2) := continuous_fst.sub continuous_snd
  have hF : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (|z.1-z.2|^r)) :=
    ((Real.continuous_rpow_const hr.le).comp hDiff.abs).measurable.ennreal_ofReal
  have hb := zero_atom_product_moment_lower ν hr
  have hLeft : (∫⁻ x : ℝ, ENNReal.ofReal (|x|^r) ∂ν) =
      ∫⁻ ω, ENNReal.ofReal (|X ω|^r) ∂μ := lintegral_map hw hX
  have hRight : (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(ν.prod ν)) =
      ∫⁻ ω, ENNReal.ofReal (|X ω-X' ω|^r) ∂μ := by
    rw [← hPair]
    exact lintegral_map hF (hX.prodMk hX')
  have hM := mul_le_mul_right' hMass (∫⁻ x : ℝ, ENNReal.ofReal (|x|^r) ∂ν)
  rw [one_mul] at hM
  have hAll := hM.trans hb
  rwa [hLeft,hRight] at hAll

end ScalarMonotone.EndOfPaper
end
