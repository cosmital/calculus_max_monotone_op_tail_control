import EndOfPaper.AggregationArea
import EndOfPaper.HardyIntegral
import EndOfPaper.ScalarIntegralConventions

/-!
The deterministic completed-operator Hardy aggregation inequality.
The actual common initial interval permits a finite or infinite upper
endpoint. One finite nonnegative prefix area implies every prefix L1
condition, and all completed Hardy graph values are identified.
-/

open Set Filter MeasureTheory
open scoped Topology Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveInitialInterval (L : EReal) : Set ℝ := {p | 0 < p ∧ (p : EReal) < L}

theorem positiveInitialInterval_geometry {L : EReal} (hL : 0 < L) :
    IsOpen (positiveInitialInterval L) ∧ (positiveInitialInterval L).OrdConnected ∧
      (positiveInitialInterval L).Nonempty ∧
      (∀ p ∈ positiveInitialInterval L, 0 < p) ∧
      ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ positiveInitialInterval L, c*p ∈ positiveInitialInterval L := by
  induction L with
  | bot => exact (not_lt_bot hL).elim
  | coe L =>
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have he : positiveInitialInterval (L : EReal) = Ioo (0 : ℝ) L := by
      ext p
      simp [positiveInitialInterval]
    rw [he]
    refine ⟨isOpen_Ioo, ordConnected_Ioo, nonempty_Ioo.mpr hLr, fun _ hp => hp.1, ?_⟩
    intro c hc p hp
    exact ⟨mul_pos hc.1 hp.1, (mul_le_of_le_one_left hp.1.le hc.2).trans_lt hp.2⟩
  | top =>
    have he : positiveInitialInterval ⊤ = Ioi (0 : ℝ) := by
      ext p
      simp [positiveInitialInterval]
    rw [he]
    exact ⟨isOpen_Ioi, ordConnected_Ioi, ⟨(1 : ℝ), by norm_num⟩, fun _ hp => hp,
      fun c hc p hp => mul_pos hc.1 hp⟩

theorem hardy_operator_aggregation_on {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hpositive : ∀ p ∈ I, 0 < p)
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hIeq : ∀ i, interior (dom (f i)) = I)
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) I (s i))
    (hi : ∀ i, ∀ p ∈ I, IntervalIntegrable (s i) volume 0 p) :
    MaximalDecreasing (hardyFamilyIntegral I (aggregationOperator F I f)) ∧
      interior (dom (hardyFamilyIntegral I (aggregationOperator F I f))) = I ∧
      ∀ p ∈ I, ∃ a : CoordinateVector n, ∃ v : ℝ,
        (∀ i, hardyFamilyIntegral I (f i) p = {a i}) ∧
        hardyFamilyIntegral I (aggregationOperator F I f) p = {v} ∧
        v ≤ superadditiveTransform F a := by
  have hdi (i) : I ⊆ interior (dom (f i)) := by
    intro p hp
    rwa [hIeq i]
  have hd (i) : I ⊆ dom (f i) := fun _ hp => interior_subset (hdi i hp)
  have hprefix (p) (hp : p ∈ I) : Ioo (0 : ℝ) p ⊆ I := by
    intro x hx
    have hp0 := hpositive p hp
    have hc : x/p ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos hx.1 hp0, (div_le_one hp0).mpr hx.2.le⟩
    have ht := hscale (x/p) hc p hp
    have he : (x/p)*p = x := by field_simp [hp0.ne']
    rwa [he] at ht
  have hA := aggregationOperator_properties hF hFc hI hord hne hf hd hpos
  have hsA := aggregationOperator_selection hF hFc hI hord hne hf hd hpos hs
  have hinput (p) (hp : p ∈ I) (i) : Integrable (s i) (volume.restrict (Ioo (0 : ℝ) p)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpositive p hp).le).mp (hi i p hp)
  have harea (p) (hp : p ∈ I) := aggregation_area_bound hF hFc hI hord hne hf hd hpos
    (hpositive p hp) (hprefix p hp) hs (hinput p hp) hsA
  have hiA (p) (hp : p ∈ I) : IntervalIntegrable (fun x => F (fun i => s i x)) volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpositive p hp).le).mpr (harea p hp).1
  have hAdom : I ⊆ interior (dom (aggregationOperator F I f)) := by
    intro p hp
    rwa [hA.2.1]
  have hHA := hardyFamilyIntegral_well_defined hA.1 hI hord hne hAdom hpositive hscale hsA hiA
  have hHi (i) := hardyFamilyIntegral_well_defined (hf i) hI hord hne (hdi i) hpositive hscale (hs i) (hi i)
  refine ⟨hHA.1, hHA.2.1, ?_⟩
  intro p hp
  let a : CoordinateVector n := fun i => hardyScalar (s i) p
  let v : ℝ := hardyScalar (fun x => F (fun i => s i x)) p
  refine ⟨a, v, fun i => (hHi i).2.2.2.1 p hp, hHA.2.2.2.1 p hp, ?_⟩
  have he (q : ℝ → ℝ) : hardyScalar q p = (∫ x in Ioo (0 : ℝ) p, q x)/p := by
    rw [hardyScalar, intervalIntegral.integral_of_le (hpositive p hp).le, integral_Ioc_eq_integral_Ioo]
  have ha : 0 ≤ a := by
    intro i
    dsimp [a]
    rw [he]
    apply div_nonneg _ (hpositive p hp).le
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hpos i x (hprefix p hp hx) _ (hs i x (hprefix p hp hx))
  have hevec : (fun i => ∫ x in Ioo (0 : ℝ) p, s i x) = p • a := by
    funext i
    dsimp [a]
    rw [he]
    change _ = p * (_/p)
    field_simp [(hpositive p hp).ne']
  have hb := (harea p hp).2
  rw [hevec, superadditiveTransform_smul hF ha (hpositive p hp).le] at hb
  dsimp [v]
  rw [he]
  exact (div_le_iff₀ (hpositive p hp)).mpr (hb.trans_eq (mul_comm _ _))

/-- The manuscript common initial interval, with L finite or infinite.
Every geometric premise of the generic completion theorem is discharged. -/
theorem hardy_operator_aggregation {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {L : EReal} (hL : 0 < L) {f : Fin n → Operator}
    (hf : ∀ i, MaximalDecreasing (f i))
    (hIeq : ∀ i, interior (dom (f i)) = positiveInitialInterval L)
    (hpos : ∀ i, ∀ x ∈ positiveInitialInterval L, ∀ v ∈ f i x, 0 ≤ v)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) (positiveInitialInterval L) (s i))
    (hi : ∀ i, ∀ p ∈ positiveInitialInterval L, IntervalIntegrable (s i) volume 0 p) :
    MaximalDecreasing (hardyFamilyIntegral (positiveInitialInterval L)
      (aggregationOperator F (positiveInitialInterval L) f)) ∧
      interior (dom (hardyFamilyIntegral (positiveInitialInterval L)
        (aggregationOperator F (positiveInitialInterval L) f))) = positiveInitialInterval L ∧
      ∀ p ∈ positiveInitialInterval L, ∃ a : CoordinateVector n, ∃ v : ℝ,
        (∀ i, hardyFamilyIntegral (positiveInitialInterval L) (f i) p = {a i}) ∧
        hardyFamilyIntegral (positiveInitialInterval L) (aggregationOperator F (positiveInitialInterval L) f) p = {v} ∧
        v ≤ superadditiveTransform F a := by
  obtain ⟨hI, hord, hne, hposI, hscale⟩ := positiveInitialInterval_geometry hL
  exact hardy_operator_aggregation_on hF hFc hI hord hne hposI hscale hf hIeq hpos hs hi

theorem antitone_prefix_integrable_all {I : Set ℝ} (hord : I.OrdConnected)
    (hpositive : ∀ p ∈ I, 0 < p)
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    {s : ℝ → ℝ} (hs : AntitoneOn s I) {b : ℝ} (hb : 0 < b)
    (hi : Integrable s (volume.restrict (Ioo (0 : ℝ) b))) :
    ∀ p ∈ I, IntervalIntegrable s volume 0 p := by
  intro p hp
  by_cases hpb : p ≤ b
  · apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpositive p hp).le).mpr
    apply hi.mono_measure
    apply Measure.restrict_mono _ le_rfl
    exact fun x hx => ⟨hx.1, hx.2.trans_le hpb⟩
  · have hbp : b < p := lt_of_not_ge hpb
    have hc : b/p ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos hb (hpositive p hp), (div_le_one (hpositive p hp)).mpr hbp.le⟩
    have hbI := hscale (b/p) hc p hp
    have he : (b/p)*p = b := by field_simp [(hpositive p hp).ne']
    rw [he] at hbI
    have hsub : uIcc b p ⊆ I := by
      rw [uIcc_of_le hbp.le]
      exact fun x hx => hord.out hbI hp hx
    have hlocal : IntervalIntegrable s volume b p := (hs.mono hsub).intervalIntegrable
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr hi).trans hlocal

/-- The finite-area hypothesis of the preceding manuscript lemma suffices
for every Hardy level, even on an unbounded initial domain. -/
theorem hardy_operator_aggregation_of_finite_area {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {L : EReal} (hL : 0 < L) {f : Fin n → Operator}
    (hf : ∀ i, MaximalDecreasing (f i))
    (hIeq : ∀ i, interior (dom (f i)) = positiveInitialInterval L)
    (hpos : ∀ i, ∀ x ∈ positiveInitialInterval L, ∀ v ∈ f i x, 0 ≤ v)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) (positiveInitialInterval L) (s i))
    {b : ℝ} (hb : 0 < b) (hbI : Ioo (0 : ℝ) b ⊆ positiveInitialInterval L)
    (hfinite : ∀ i, (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)) < ∞) :
    MaximalDecreasing (hardyFamilyIntegral (positiveInitialInterval L)
      (aggregationOperator F (positiveInitialInterval L) f)) ∧
      interior (dom (hardyFamilyIntegral (positiveInitialInterval L)
        (aggregationOperator F (positiveInitialInterval L) f))) = positiveInitialInterval L ∧
      ∀ p ∈ positiveInitialInterval L, ∃ a : CoordinateVector n, ∃ v : ℝ,
        (∀ i, hardyFamilyIntegral (positiveInitialInterval L) (f i) p = {a i}) ∧
        hardyFamilyIntegral (positiveInitialInterval L) (aggregationOperator F (positiveInitialInterval L) f) p = {v} ∧
        v ≤ superadditiveTransform F a := by
  have hi (i) : Integrable (s i) (volume.restrict (Ioo (0 : ℝ) b)) := by
    apply (selection_integrable_iff_absolute_area_finite (Or.inr (hf i).1)
      measurableSet_Ioo (fun x hx => hs i x (hbI hx)) volume).mpr
    have hnn : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) b)), 0 ≤ s i x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpos i x (hbI hx) _ (hs i x (hbI hx))
    rw [lintegral_congr_ae (hnn.mono (fun x hx => congrArg ENNReal.ofReal (abs_of_nonneg hx)))]
    exact hfinite i
  obtain ⟨_, hord, _, hpositive, hscale⟩ := positiveInitialInterval_geometry hL
  have hiAll (i) := antitone_prefix_integrable_all hord hpositive hscale
    (selection_antitoneOn (hf i).1 (hs i)) hb (hi i)
  exact hardy_operator_aggregation hF hFc hL hf hIeq hpos hs hiAll

end ScalarMonotone.EndOfPaper
end
