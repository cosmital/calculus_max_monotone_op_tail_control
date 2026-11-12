import EndOfPaper.IntegralAggregation
import EndOfPaper.AggregationOperator
import EndOfPaper.ScalarIntegralConventions

/-!
The full aggregation-area lemma for the actual completed operator.
Finite extended nonnegative input areas imply L1 and the area inequality,
for arbitrary selections, including a finite upper boundary endpoint.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem aggregation_area_bound_on {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJI : J ⊆ I)
    [IsFiniteMeasure (volume.restrict J)]
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) I (s i))
    (hi : ∀ i, Integrable (s i) (volume.restrict J))
    {t : ℝ → ℝ} (ht : SelectionOn (aggregationOperator F I f) I t) :
    Integrable t (volume.restrict J) ∧
      (∫ x in J, t x) ≤ superadditiveTransform F (fun i => ∫ x in J, s i x) := by
  let μ := volume.restrict J
  have hsm (i) : AEMeasurable (s i) μ := aemeasurable_restrict_of_antitoneOn hJ
    ((selection_antitoneOn (hf i).1 (hs i)).mono hJI)
  let Y : ℝ → CoordinateVector n := fun x i => (hsm i).mk (s i) x
  have hYm : Measurable Y := measurable_pi_iff.mpr (fun i => (hsm i).measurable_mk)
  have he : (fun x i => s i x) =ᵐ[μ] Y := by
    filter_upwards [ae_all_iff.mpr (fun i => (hsm i).ae_eq_mk)] with x hx
    exact funext hx
  have hvm : AEMeasurable (fun x i => s i x) μ := hYm.aemeasurable.congr he.symm
  have hvpos : ∀ᵐ x ∂μ, 0 ≤ (fun i => s i x) := by
    filter_upwards [ae_restrict_mem hJ] with x hx
    exact fun i => hpos i x (hJI hx) _ (hs i x (hJI hx))
  have hcomp := aggregationOperator_selection hF hFc hI hord hne hf hdom hpos hs
  have hA := aggregationOperator_properties hF hFc hI hord hne hf hdom hpos
  have hts : t =ᵐ[μ] (fun x => F (fun i => s i x)) :=
    decreasing_selections_ae_eq hA.1.1 (fun x hx => ht x (hJI hx))
      (fun x hx => hcomp x (hJI hx)) volume hJ
  have hci := aggregation_composition_integrable_ae hF hFc μ hvm hvpos hi
  refine ⟨hci.congr hts.symm, ?_⟩
  calc
    (∫ x in J, t x) = ∫ x, F (fun i => s i x) ∂μ := integral_congr_ae hts
    _ ≤ superadditiveTransform F (fun i => ∫ x in J, s i x) :=
      aggregation_integral_bound_ae hF hFc μ hvm hvpos hi

/-- Full area statement, including b at a finite upper endpoint of I.
All selections are arbitrary, and the aggregate is the completed graph. -/
theorem aggregation_area_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {b : ℝ} (hb : 0 < b) (hbI : Ioo (0 : ℝ) b ⊆ I)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) I (s i))
    (hi : ∀ i, Integrable (s i) (volume.restrict (Ioo (0 : ℝ) b)))
    {t : ℝ → ℝ} (ht : SelectionOn (aggregationOperator F I f) I t) :
    Integrable t (volume.restrict (Ioo (0 : ℝ) b)) ∧
      (∫ x in Ioo (0 : ℝ) b, t x) ≤
        superadditiveTransform F (fun i => ∫ x in Ioo (0 : ℝ) b, s i x) := by
  letI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) b)) :=
    ⟨by simp [Measure.restrict_apply, Real.volume_Ioo]⟩
  exact aggregation_area_bound_on hF hFc hI hord hne hf hdom hpos measurableSet_Ioo hbI hs hi ht

theorem aggregation_area_finite_nonnegative {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {b : ℝ} (hb : 0 < b) (hbI : Ioo (0 : ℝ) b ⊆ I)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) I (s i))
    (hfinite : ∀ i, (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)) < ∞)
    {t : ℝ → ℝ} (ht : SelectionOn (aggregationOperator F I f) I t) :
    Integrable t (volume.restrict (Ioo (0 : ℝ) b)) ∧
      (∫ x in Ioo (0 : ℝ) b, t x) ≤ superadditiveTransform F
        (fun i => (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)).toReal) := by
  have hn (i) : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) b)), 0 ≤ s i x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hpos i x (hbI hx) _ (hs i x (hbI hx))
  have hi (i) : Integrable (s i) (volume.restrict (Ioo (0 : ℝ) b)) := by
    apply (selection_integrable_iff_absolute_area_finite (Or.inr (hf i).1)
      measurableSet_Ioo (fun x hx => hs i x (hbI hx)) volume).mpr
    rw [lintegral_congr_ae ((hn i).mono (fun x hx => congrArg ENNReal.ofReal (abs_of_nonneg hx)))]
    exact hfinite i
  have harea (i) : (∫ x in Ioo (0 : ℝ) b, s i x) =
      (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (hn i) (hi i).aestronglyMeasurable
  have h := aggregation_area_bound hF hFc hI hord hne hf hdom hpos hb hbI hs hi ht
  refine ⟨h.1, ?_⟩
  simpa only [harea] using h.2

end ScalarMonotone.EndOfPaper
end
