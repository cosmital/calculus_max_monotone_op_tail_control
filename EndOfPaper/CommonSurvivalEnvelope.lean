import EndOfPaper.CommonTailAggregation

/-!
The actual zero-aggregation law and full common-envelope survival comparison, including the literal domain-scaled strict-tail infimum and AE-nonnegative original inputs.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem zero_aggregation_law {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) {F : CoordinateVector n → ℝ}
    (hF0 : ∀ a, 0 ≤ a → F a = 0) :
    Measure.map (fun ω => F (X ω)) μ = Measure.dirac (0 : ℝ) := by
  calc
    _ = Measure.map (fun _ : Ω => (0 : ℝ)) μ :=
      Measure.map_congr (hX.mono (fun ω hω => hF0 (X ω) hω))
    _ = _ := by simp

theorem common_envelope_survival_bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {a | 0 ≤ a})
    (hnz : ¬ ∀ a, 0 ≤ a → F a = 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hXm : Measurable X) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {β : Operator} (hβ : MaximalDecreasing β)
    (hβ1 : DecLE β (ofFun (fun _ => (1 : ℝ)))) (hz : IsGLB (ran β) 0)
    (hS : ∀ i, DecLE (survival (Measure.map (fun ω => X ω i) μ)) β)
    {b : ℝ → ℝ} (hb : SelectionOn (inverse β) (Ioo (0 : ℝ) 1) b)
    (hfinite : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal |b p|) < ∞) :
    let C := superadditiveTransform F (fun _ => 1)
    0 < C ∧
    DecLE (survival (Measure.map (fun ω => F (X ω)) μ)) (inputDivide C (hardyTailTransform β)) ∧
    ∀ t ∈ (fun x : ℝ => C*x) '' dom (hardyTailTransform β),
      μ.real {ω | t < F (X ω)} ≤ sInf (hardyTailTransform β (t/C)) := by
  dsimp only
  let C := superadditiveTransform F (fun _ => 1)
  let H := hardyFamilyIntegral (interior (dom (inverse β))) (inverse β)
  have hC : 0 < C := sharp_one_positive_of_nonzero hF hnz
  let Xp : Ω → CoordinateVector n := fun ω i => max (X ω i) 0
  have hXpm : Measurable Xp := measurable_pi_iff.mpr (fun i =>
    (measurable_pi_iff.mp hXm i).max measurable_const)
  have hXp : ∀ ω, 0 ≤ Xp ω := fun ω i => le_max_right _ _
  have hS' (i : Fin n) : DecLE (survival (Measure.map (fun ω => Xp ω i) μ)) β := by
    have he : (fun ω => Xp ω i) =ᵐ[μ] (fun ω => X ω i) :=
      hX.mono (fun ω hω => max_eq_left (hω i))
    rw [Measure.map_congr he]
    exact hS i
  have hQ := common_envelope_quantile_bound_of_nonnegative hn hF hFc hC
    μ hXpm hXp hβ hβ1 hz hS' hb hfinite
  have hinv : inverse (outputScale C H) = inputDivide C (hardyTailTransform β) := by
    simpa only [inverse_inverse] using inverse_outputScale_inverse hC.ne' (inverse H)
  have hSur : DecLE (survival (Measure.map (fun ω => F (Xp ω)) μ))
      (inputDivide C (hardyTailTransform β)) := by
    have hh := decLE_inverse_iff.mpr hQ
    have hh' : DecLE (survival (Measure.map (fun ω => F (Xp ω)) μ))
        (inverse (outputScale C H)) := by
      simpa only [tailQuantile,inverse_inverse] using hh
    rwa [hinv] at hh'
  have hFm : Measurable (fun ω => F (Xp ω)) :=
    (aggregation_positiveExtension_continuous hFc).measurable.comp hXm
  have htclip := (survival_map_comparison_iff μ hFm _).mp hSur
  have heF : (fun ω => F (Xp ω)) =ᵐ[μ] (fun ω => F (X ω)) := by
    filter_upwards [hX] with ω hω
    congr 1
    funext i
    exact max_eq_left (hω i)
  rw [Measure.map_congr heF] at hSur
  refine ⟨hC,hSur,?_⟩
  rintro t ⟨u,hu,rfl⟩
  have he : C*u/C = u := by field_simp [hC.ne']
  change μ.real {ω | C*u < F (X ω)} ≤ sInf (hardyTailTransform β (C*u/C))
  rw [he]
  apply le_csInf hu
  intro v hv
  have hsets : {ω | C*u < F (X ω)} =ᵐ[μ] {ω | C*u < F (Xp ω)} :=
    heF.symm.fun_comp (fun y : ℝ => C*u < y)
  calc
    _ = μ.real {ω | C*u < F (Xp ω)} := congrArg ENNReal.toReal (measure_congr hsets)
    _ ≤ v := htclip (show v ∈ inputDivide C (hardyTailTransform β) (C*u) from by
      change v ∈ hardyTailTransform β (C*u/C)
      rwa [he])

end ScalarMonotone.EndOfPaper
end
