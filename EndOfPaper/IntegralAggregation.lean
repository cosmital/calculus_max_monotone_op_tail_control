import EndOfPaper.Superadditive

/-!
General integral aggregation for finite measures and almost-everywhere
nonnegative integrable vectors. Lower simple approximations preserve the
exact upper mean constraint, so no continuity of the sharp transform at
boundary faces is assumed. Aggregate integrability is derived.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper
local infixr:25 " →ₛ " => SimpleFunc

variable {Ω : Type*} [MeasurableSpace Ω]

theorem simple_aggregation_integral_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Ω →ₛ CoordinateVector n) (hq : ∀ ω, 0 ≤ q ω) :
    (∫ ω, F (q ω) ∂μ) ≤ superadditiveTransform F (∫ ω, q ω ∂μ) := by
  classical
  have hqi := q.integrable_of_isFiniteMeasure (μ := μ)
  have hFi := (q.map F).integrable_of_isFiniteMeasure (μ := μ)
  have hr (x) (hx : x ∈ q.range) : 0 ≤ x := by
    obtain ⟨ω, rfl⟩ := SimpleFunc.mem_range.mp hx
    exact hq ω
  calc
    (∫ ω, F (q ω) ∂μ) = ∑ x ∈ q.range, μ.real (q ⁻¹' {x}) * F x := by
      change (∫ ω, (q.map F) ω ∂μ) = _
      rw [← (q.map F).integral_eq_integral hFi, q.map_integral F hqi (aggregation_zero hF)]
      rfl
    _ = ∑ x ∈ q.range, F (μ.real (q ⁻¹' {x}) • x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (hF.homogeneous _ measureReal_nonneg _ (hr x hx)).symm
    _ ≤ superadditiveTransform F (∑ x ∈ q.range, μ.real (q ⁻¹' {x}) • x) :=
      aggregation_finset_bound hF q.range _ (fun x hx => smul_nonneg measureReal_nonneg (hr x hx))
    _ = superadditiveTransform F (∫ ω, q ω ∂μ) := by rw [q.integral_eq_sum hqi]

def lowerScalarSimple (X : Ω → ℝ) (k : ℕ) : Ω →ₛ ℝ :=
  (SimpleFunc.eapprox (fun ω => ENNReal.ofReal (X ω)) k).map ENNReal.toReal

theorem lowerScalarSimple_bounds {X : Ω → ℝ} (hX : Measurable X)
    (hpos : ∀ ω, 0 ≤ X ω) (k : ℕ) (ω : Ω) :
    0 ≤ lowerScalarSimple X k ω ∧ lowerScalarSimple X k ω ≤ X ω := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have he : SimpleFunc.eapprox (fun ω => ENNReal.ofReal (X ω)) k ω ≤ ENNReal.ofReal (X ω) := by
      rw [← SimpleFunc.iSup_eapprox_apply (hX.ennreal_ofReal) ω]
      exact le_iSup (fun k => SimpleFunc.eapprox (fun ω => ENNReal.ofReal (X ω)) k ω) k
    simpa only [lowerScalarSimple, SimpleFunc.map_apply, ENNReal.toReal_ofReal (hpos ω)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he

theorem lowerScalarSimple_tendsto {X : Ω → ℝ} (hX : Measurable X)
    (hpos : ∀ ω, 0 ≤ X ω) (ω : Ω) :
    Tendsto (fun k => lowerScalarSimple X k ω) atTop (𝓝 (X ω)) := by
  have ht := (ENNReal.continuousAt_toReal (x := ENNReal.ofReal (X ω)) ENNReal.ofReal_ne_top).tendsto.comp
    (SimpleFunc.tendsto_eapprox hX.ennreal_ofReal ω)
  simpa only [lowerScalarSimple, SimpleFunc.map_apply, Function.comp_apply,
    ENNReal.toReal_ofReal (hpos ω)] using ht

def lowerVectorSimple {n : ℕ} (X : Ω → CoordinateVector n) (k : ℕ) : Ω →ₛ CoordinateVector n :=
  ∑ i, (lowerScalarSimple (fun ω => X ω i) k).map (coordinateAxis i)

theorem lowerVectorSimple_apply {n : ℕ} (X : Ω → CoordinateVector n) (k : ℕ) (ω : Ω) :
    lowerVectorSimple X k ω = fun i => lowerScalarSimple (fun ω => X ω i) k ω := by
  classical
  have he (s : Finset (Fin n)) :
      (∑ i ∈ s, (lowerScalarSimple (fun ω => X ω i) k).map (coordinateAxis i)) ω =
        ∑ i ∈ s, coordinateAxis i (lowerScalarSimple (fun ω => X ω i) k ω) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, SimpleFunc.add_apply, SimpleFunc.map_apply, ih]
  change (∑ i ∈ Finset.univ, (lowerScalarSimple (fun ω => X ω i) k).map (coordinateAxis i)) ω = _
  rw [he]
  exact sum_coordinateAxis _

theorem lowerVectorSimple_bounds {n : ℕ} {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω) (k : ℕ) (ω : Ω) :
    0 ≤ lowerVectorSimple X k ω ∧ lowerVectorSimple X k ω ≤ X ω := by
  rw [lowerVectorSimple_apply]
  exact ⟨fun i => (lowerScalarSimple_bounds (measurable_pi_iff.mp hm i) (fun ω => hx ω i) k ω).1,
    fun i => (lowerScalarSimple_bounds (measurable_pi_iff.mp hm i) (fun ω => hx ω i) k ω).2⟩

theorem lowerVectorSimple_tendsto {n : ℕ} {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω) (ω : Ω) :
    Tendsto (fun k => lowerVectorSimple X k ω) atTop (𝓝 (X ω)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [lowerVectorSimple_apply] using
    lowerScalarSimple_tendsto (measurable_pi_iff.mp hm i) (fun ω => hx ω i) ω

theorem simpleVector_integral_apply {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Ω →ₛ CoordinateVector n) (i : Fin n) :
    (∫ ω, q ω ∂μ) i = ∫ ω, q ω i ∂μ := by
  exact ((ContinuousLinearMap.proj i : CoordinateVector n →L[ℝ] ℝ).integral_comp_comm
    (q.integrable_of_isFiniteMeasure (μ := μ))).symm

theorem aggregation_positiveExtension_continuous {n : ℕ} {F : CoordinateVector n → ℝ}
    (hFc : ContinuousOn F {x | 0 ≤ x}) :
    Continuous (fun x : CoordinateVector n => F (fun i => max (x i) 0)) := by
  exact hFc.comp_continuous
    (continuous_pi (fun i => (continuous_apply i).max continuous_const))
    (fun x i => le_max_right (x i) 0)

theorem aggregation_composition_integrable {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    Integrable (fun ω => F (X ω)) μ := by
  have hext := aggregation_positiveExtension_continuous hFc
  have heq : (fun ω => F (fun i => max (X ω i) 0)) = fun ω => F (X ω) := by
    funext ω
    congr 1
    funext i
    exact max_eq_left (hx ω i)
  have hmeas : Measurable (fun ω => F (X ω)) := by
    rw [← heq]
    exact hext.measurable.comp hm
  have hbound : Integrable (fun ω => F (fun _ => 1) * coordinateMass (X ω)) μ :=
    (integrable_finset_sum _ (fun i _ => hi i)).const_mul _
  apply hbound.mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ (hx ω))]
    exact aggregation_linear_bound hF (hx ω))

/-- General finite-measure integral inequality. Lower simple approximations
keep their integrals below the exact mean, so continuity of F-sharp on boundary
faces is neither assumed nor needed. -/
theorem aggregation_integral_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    (∫ ω, F (X ω) ∂μ) ≤ superadditiveTransform F (fun i => ∫ ω, X ω i ∂μ) := by
  let C := F (fun _ => 1)
  let bound : Ω → ℝ := fun ω => C * coordinateMass (X ω)
  have hbi : Integrable bound μ := (integrable_finset_sum _ (fun i _ => hi i)).const_mul C
  have hseq : Tendsto (fun k => ∫ ω, F (lowerVectorSimple X k ω) ∂μ) atTop
      (𝓝 (∫ ω, F (X ω) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence bound
    · intro k
      exact (lowerVectorSimple X k |>.map F).measurable.aestronglyMeasurable
    · exact hbi
    · intro k
      exact Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ (lowerVectorSimple_bounds hm hx k ω).1)]
        exact (hF.mono (lowerVectorSimple_bounds hm hx k ω).1 (lowerVectorSimple_bounds hm hx k ω).2).trans
          (aggregation_linear_bound hF (hx ω)))
    · exact Eventually.of_forall (fun ω => (hFc (X ω) (hx ω)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨lowerVectorSimple_tendsto hm hx ω,
          Eventually.of_forall (fun k => (lowerVectorSimple_bounds hm hx k ω).1)⟩))
  apply le_of_tendsto' hseq
  intro k
  have hs := simple_aggregation_integral_bound hF μ (lowerVectorSimple X k)
    (fun ω => (lowerVectorSimple_bounds hm hx k ω).1)
  apply hs.trans
  apply superadditiveTransform_mono hF
  · intro i
    rw [simpleVector_integral_apply]
    exact integral_nonneg (fun ω => (lowerVectorSimple_bounds hm hx k ω).1 i)
  · intro i
    rw [simpleVector_integral_apply]
    have hqi : Integrable (fun ω => lowerVectorSimple X k ω i) μ := by
      simpa only [SimpleFunc.map_apply] using
        ((lowerVectorSimple X k).map (fun x : CoordinateVector n => x i)).integrable_of_isFiniteMeasure (μ := μ)
    exact integral_mono_ae hqi (hi i)
      (Eventually.of_forall (fun ω => (lowerVectorSimple_bounds hm hx k ω).2 i))

theorem exists_nonnegative_measurable_representative {n : ℕ}
    (μ : Measure Ω) {X : Ω → CoordinateVector n} (hm : AEMeasurable X μ)
    (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    ∃ Y : Ω → CoordinateVector n, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧ X =ᵐ[μ] Y ∧
      ∀ i, Integrable (fun ω => Y ω i) μ := by
  let Y : Ω → CoordinateVector n := fun ω i => max (hm.mk X ω i) 0
  have hYm : Measurable Y := measurable_pi_iff.mpr (fun i =>
    (measurable_pi_iff.mp hm.measurable_mk i).max measurable_const)
  have hYpos : ∀ ω, 0 ≤ Y ω := fun ω i => le_max_right _ _
  have he : X =ᵐ[μ] Y := by
    filter_upwards [hm.ae_eq_mk, hx] with ω hω hp
    funext i
    dsimp [Y]
    rw [← hω]
    exact (max_eq_left (show (0 : ℝ) ≤ X ω i from hp i)).symm
  exact ⟨Y, hYm, hYpos, he, fun i => (hi i).congr (he.mono (fun ω hω => congrArg (fun v => v i) hω))⟩

theorem aggregation_composition_integrable_ae {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) {X : Ω → CoordinateVector n}
    (hm : AEMeasurable X μ) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    Integrable (fun ω => F (X ω)) μ := by
  obtain ⟨Y, hYm, hYpos, he, hYi⟩ := exists_nonnegative_measurable_representative μ hm hx hi
  exact (aggregation_composition_integrable hF hFc μ hYm hYpos hYi).congr (he.symm.fun_comp F)

theorem aggregation_integral_bound_ae {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → CoordinateVector n}
    (hm : AEMeasurable X μ) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    (∫ ω, F (X ω) ∂μ) ≤ superadditiveTransform F (fun i => ∫ ω, X ω i ∂μ) := by
  obtain ⟨Y, hYm, hYpos, he, hYi⟩ := exists_nonnegative_measurable_representative μ hm hx hi
  calc
    (∫ ω, F (X ω) ∂μ) = ∫ ω, F (Y ω) ∂μ := integral_congr_ae (he.fun_comp F)
    _ ≤ superadditiveTransform F (fun i => ∫ ω, Y ω i ∂μ) :=
      aggregation_integral_bound hF hFc μ hYm hYpos hYi
    _ = superadditiveTransform F (fun i => ∫ ω, X ω i ∂μ) := by
      congr 1
      funext i
      exact integral_congr_ae (he.symm.mono (fun ω hω => congrArg (fun v => v i) hω))

end ScalarMonotone.EndOfPaper
end
