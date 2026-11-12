import EndOfPaper.IntegralAggregation
import EndOfPaper.HardyVariational

/-!
The complete Hardy tail-aggregation proposition. Feasible weights live
on the original probability space, aggregate integrability is derived, and
all profile values are fibers of the actual completed Hardy family integral.
Homogeneity at zero is derived from the paper positive-scalar assumption.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The paper assumes homogeneity only for positive scalars. Its zero-scalar
case follows already from the positive identity at the zero vector. -/
theorem aggregationAxioms_of_positive_homogeneity {n : ℕ} {F : CoordinateVector n → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hmono : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x) :
    AggregationAxioms F := by
  have hzero : F 0 = 0 := by
    have he := hhom 2 (by norm_num) 0 le_rfl
    simp only [smul_zero] at he
    linarith
  refine ⟨hn, hmono, ?_⟩
  intro c hc x hx
  rcases eq_or_lt_of_le hc with he | hc
  · subst c
    simp [hzero]
  · exact hhom c hc x hx

theorem weighted_aggregation_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hm : AEMeasurable X μ) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ)
    {Z : Ω → ℝ} (hZ : AEMeasurable Z μ)
    (hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) {p : ℝ} (hp : 0 < p) :
    (∫ ω, F (X ω)*Z ω ∂μ)/p ≤
      superadditiveTransform F (fun i => (∫ ω, X ω i*Z ω ∂μ)/p) := by
  let b : CoordinateVector n := fun i => ∫ ω, X ω i*Z ω ∂μ
  let a : CoordinateVector n := fun i => b i/p
  have hb : 0 ≤ b := by
    intro i
    apply integral_nonneg_of_ae
    filter_upwards [hx, hz] with ω hω hωZ
    exact mul_nonneg (hω i) hωZ.1
  have ha : 0 ≤ a := fun i => div_nonneg (hb i) hp.le
  have hYpos : ∀ᵐ ω ∂μ, 0 ≤ Z ω • X ω := by
    filter_upwards [hx, hz] with ω hω hωZ
    exact smul_nonneg hωZ.1 hω
  have hYi (i) : Integrable (fun ω => (Z ω • X ω) i) μ := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      integrable_mul_unit_weight (hi i) hZ hz
  have hagg := aggregation_integral_bound_ae hF hFc μ (hZ.smul hm) hYpos hYi
  have hleft : (∫ ω, F (Z ω • X ω) ∂μ) = ∫ ω, F (X ω)*Z ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [hx, hz] with ω hω hωZ
    rw [hF.homogeneous (Z ω) hωZ.1 (X ω) hω, mul_comm]
  have hright : (fun i => ∫ ω, (Z ω • X ω) i ∂μ) = p • a := by
    funext i
    dsimp [a, b]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm (Z _) (X _ _)]
    field_simp [hp.ne']
  rw [hleft, hright, superadditiveTransform_smul hF ha hp.le] at hagg
  exact (div_le_iff₀ hp).mpr (hagg.trans_eq (mul_comm _ _))

/-- Every random variable and feasible weight lives on the original space.
The profile values are fibers of the actual completed Hardy family integrals. -/
theorem hardy_tail_aggregation {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : CoordinateVector n, ∃ v : ℝ,
      (∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a i}) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => F (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => F (X ω)) μ)) p = {v} ∧
      v ≤ superadditiveTransform F a := by
  classical
  have hFi := aggregation_composition_integrable hF hFc μ hm hx hi
  have hFm : Measurable (fun ω => F (X ω)) := by
    have he : (fun ω => F (fun i => max (X ω i) 0)) = fun ω => F (X ω) := by
      funext ω
      congr 1
      funext i
      exact max_eq_left (hx ω i)
    rw [← he]
    exact (aggregation_positiveExtension_continuous hFc).measurable.comp hm
  obtain ⟨v, hvfiber, _, hvdual, _, _, _⟩ := hardy_quantile_original_variational hFm hFi hp
  have hc (i : Fin n) : ∃ a : ℝ,
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a} ∧
      IsGreatest (dualCandidates μ (fun ω => X ω i) p) a := by
    obtain ⟨a, haf, _, had, _, _, _⟩ :=
      hardy_quantile_original_variational (measurable_pi_iff.mp hm i) (hi i) hp
    exact ⟨a, haf, had⟩
  choose a haf had using hc
  refine ⟨a, v, haf, hvfiber, ?_⟩
  obtain ⟨Z, hZ, hz, hmean, hval⟩ := hvdual.1
  rw [hval]
  apply (weighted_aggregation_bound hF hFc μ hm.aemeasurable
    (Eventually.of_forall hx) hi hZ hz hp.1).trans
  apply superadditiveTransform_mono hF
  · intro i
    apply div_nonneg _ hp.1.le
    apply integral_nonneg_of_ae
    filter_upwards [hz] with ω hωZ
    exact mul_nonneg (hx ω i) hωZ.1
  · intro i
    exact (had i).2 (show (∫ ω, X ω i*Z ω ∂μ)/p ∈ dualCandidates μ (fun ω => X ω i) p from
      ⟨Z, hZ, hz, hmean, rfl⟩)

theorem hardy_tail_aggregation_of_positive_homogeneity {n : ℕ} {F : CoordinateVector n → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hmono : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x)
    (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → CoordinateVector n}
    (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : CoordinateVector n, ∃ v : ℝ,
      (∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a i}) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => F (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => F (X ω)) μ)) p = {v} ∧
      v ≤ superadditiveTransform F a :=
  hardy_tail_aggregation (aggregationAxioms_of_positive_homogeneity hn hmono hhom) hFc μ hm hx hi hp

end ScalarMonotone.EndOfPaper
end
