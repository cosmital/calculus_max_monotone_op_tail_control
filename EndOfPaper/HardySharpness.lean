import EndOfPaper.FiniteStepProfiles
import EndOfPaper.GeometricBands
import EndOfPaper.HardyTailAggregation

/-!
The full sharpness theorem for Hardy tail aggregation. Literal
admissible classes quantify over all original probability spaces in an
arbitrary universe, allow almost-sure nonnegativity, and use actual
completed Hardy quantile graphs. Explicit finite-valued comonotone models
have prescribed marginal averages and the geometric-band lower bound.
The epsilon limit proves both exact suprema without asserting attainment.
-/

open Set Filter MeasureTheory
open scoped BigOperators Interval Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- An abbreviation for the actual completed Hardy integral of a tail quantile. -/
def quantileHardy (μ : Measure ℝ) : Operator :=
  hardyFamilyIntegral (interior (dom (tailQuantile μ))) (tailQuantile μ)

theorem finite_vector_steps_prescribed {n m : ℕ} {p : ℝ} (hp : p ∈ Ioo 0 1)
    {v : Fin m → CoordinateVector n} (hv : ∀ j, 0 ≤ v j)
    {a : CoordinateVector n} (hva : (∑ j, v j) ≤ a)
    {s : Fin m → ℝ} (hs : ∀ j, 0 < s j ∧ s j ≤ p) :
    ∃ q : Fin n → ℝ → ℝ, (∀ i, Measurable (q i)) ∧ (∀ i, Antitone (q i)) ∧
      (∀ i, (Set.range (q i)).Finite) ∧ (∀ i u, 0 ≤ q i u) ∧
      (∀ i, quantileHardy (Measure.map (q i) unitUniform) p = {a i}) ∧
      ∀ i j u, u ≤ s j → p*v j i/s j ≤ q i u := by
  classical
  have heach (i : Fin n) : ∃ q : ℝ → ℝ, Measurable q ∧ Antitone q ∧
      (Set.range q).Finite ∧ (∀ u, 0 ≤ q u) ∧
      quantileHardy (Measure.map q unitUniform) p = {a i} ∧
      ∀ j u, u ≤ s j → p*v j i/s j ≤ q u := by
    have hi : (∑ j, v j i) ≤ a i := by simpa only [Finset.sum_apply] using hva i
    exact finite_steps_prescribed_hardy hp (fun j => hv j i) hi hs
  choose q hqm hanti hfin hpos hH hstep using heach
  exact ⟨q, hqm, hanti, hfin, hpos, hH, hstep⟩

theorem finite_profile_aggregation_properties {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hqm : ∀ i, Measurable (q i)) (hanti : ∀ i, Antitone (q i))
    (hfin : ∀ i, (Set.range (q i)).Finite) (hpos : ∀ i u, 0 ≤ q i u) :
    Measurable (fun u => F (fun i => q i u)) ∧ Antitone (fun u => F (fun i => q i u)) ∧
      Integrable (fun u => F (fun i => q i u)) unitUniform := by
  have hQm : Measurable (fun u i => q i u) := measurable_pi_iff.mpr hqm
  have hi (i) : Integrable (q i) unitUniform :=
    finite_nonnegative_range_integrable (hqm i).aemeasurable (hpos i) (hfin i)
  have hFint := aggregation_composition_integrable hF hFc unitUniform hQm
    (fun u i => hpos i u) hi
  have he : (fun u => F (fun i => max (q i u) 0)) = (fun u => F (fun i => q i u)) := by
    funext u
    congr 1
    funext i
    exact max_eq_left (hpos i u)
  have hFm : Measurable (fun u => F (fun i => q i u)) := by
    rw [← he]
    exact (aggregation_positiveExtension_continuous hFc).measurable.comp hQm
  have hFa : Antitone (fun u => F (fun i => q i u)) := by
    intro x y hxy
    exact hF.mono (fun i => hpos i y) (fun i => hanti i hxy)
  exact ⟨hFm, hFa, hFint⟩

theorem geometric_scaled_band_mass {p ε : ℝ} (hp : 0 < p) (hε : ε ∈ Ioo 0 1)
    {m j : ℕ} (hj : j < m) :
    (1-ε)*p ≤ (geometricScale p ε m j-geometricScale p ε m (j+1)) *
      (p/geometricScale p ε m j) := by
  have hs := geometricScale_positive hp hε.1 hj
  have ht := mul_le_mul_of_nonneg_right
    (geometricBand_length_lower hp.le hε.1.le hε.2.le m j).2 (div_nonneg hp.le hs.le)
  have he : ((1-ε)*geometricScale p ε m j)*(p/geometricScale p ε m j) = (1-ε)*p := by
    field_simp [hs.ne'] <;> ring
  rwa [he] at ht

theorem geometric_step_hardy_lower_model {n m : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p ε : ℝ} (hp : p ∈ Ioo 0 1) (hε : ε ∈ Ioo 0 1)
    {v : Fin m → CoordinateVector n} (hv : ∀ j, 0 ≤ v j)
    {a : CoordinateVector n} (hva : (∑ j, v j) ≤ a) :
    ∃ q : Fin n → ℝ → ℝ, ∃ z : ℝ,
      (∀ i, Measurable (q i)) ∧ (∀ i, Antitone (q i)) ∧
      (∀ i, (Set.range (q i)).Finite) ∧ (∀ i u, 0 ≤ q i u) ∧
      (∀ i, quantileHardy (Measure.map (q i) unitUniform) p = {a i}) ∧
      quantileHardy (Measure.map (fun u => F (fun i => q i u)) unitUniform) p = {z} ∧
      (1-ε)*(∑ j, F (v j)) ≤ z := by
  classical
  let s : Fin m → ℝ := fun j => geometricScale p ε m j.val
  have hs (j : Fin m) : 0 < s j ∧ s j ≤ p :=
    ⟨geometricScale_positive hp.1 hε.1 j.isLt,
      geometricScale_le_initial hp.1.le hε.1.le hε.2.le m j.val⟩
  obtain ⟨q, hqm, hanti, hfin, hpos, hH, hstep⟩ := finite_vector_steps_prescribed hp hv hva hs
  obtain ⟨hFm, hFa, hFi⟩ := finite_profile_aggregation_properties hF hFc hqm hanti hfin hpos
  let φ : ℝ → ℝ := fun u => F (fun i => q i u)
  let w : Fin m → ℝ := fun j => (p/s j)*F (v j)
  have hφpos (u : ℝ) : 0 ≤ φ u := hF.nonneg _ (fun i => hpos i u)
  have hband (j : Fin m) (u : ℝ) (hu : u ∈ geometricBand p ε m j.val) : w j ≤ φ u := by
    have hscalar : 0 ≤ p/s j := div_nonneg hp.1.le (hs j).1.le
    have hnon : 0 ≤ (p/s j) • v j := smul_nonneg hscalar (hv j)
    have hle : (p/s j) • v j ≤ (fun i => q i u) := by
      intro i
      change (p/s j)*v j i ≤ q i u
      rw [show (p/s j)*v j i = p*v j i/s j by ring]
      exact hstep i j u hu.2
    have ht := hF.mono hnon hle
    rw [hF.homogeneous (p/s j) hscalar (v j) (hv j)] at ht
    exact ht
  have hφinterval : IntervalIntegrable φ volume 0 p := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.1.le).mpr
    have hi : IntegrableOn φ (Ioo (0 : ℝ) 1) volume := hFi
    exact hi.mono_set (fun u hu => ⟨hu.1, hu.2.trans hp.2⟩)
  have hbandint (j : Fin m) : IntervalIntegrable
      ((geometricBand p ε m j.val).indicator (fun _ => w j)) volume 0 p :=
    interval_indicator_band_integrable _ _ _ _
  have hsumint : IntervalIntegrable
      (fun u => ∑ j : Fin m, (geometricBand p ε m j.val).indicator (fun _ => w j) u) volume 0 p := by
    simpa only [← Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun j _ => hbandint j)
  have harea := intervalIntegral.integral_mono_on_of_le_Ioo hp.1.le hsumint hφinterval
    (fun u _ => geometricBand_sum_lower hp.1.le hε.1.le hε.2.le m w hφpos hband u)
  rw [intervalIntegral.integral_finset_sum (fun j _ => hbandint j)] at harea
  have hbandvalue (j : Fin m) :
      (∫ u in (0 : ℝ)..p, (geometricBand p ε m j.val).indicator (fun _ => w j) u) =
      (s j-geometricScale p ε m (j.val+1))*w j :=
    interval_indicator_band_integral
      (geometricScale_nonnegative hp.1.le hε.1.le m (j.val+1))
      (geometricScale_antitone hp.1.le hε.1.le hε.2.le m (Nat.le_succ j.val))
      (geometricScale_le_initial hp.1.le hε.1.le hε.2.le m j.val) (w j)
  simp_rw [hbandvalue] at harea
  have hterm (j : Fin m) : ((1-ε)*p)*F (v j) ≤
      (s j-geometricScale p ε m (j.val+1))*w j := by
    have ht := mul_le_mul_of_nonneg_right (geometric_scaled_band_mass hp.1 hε j.isLt)
      (hF.nonneg (v j) (hv j))
    convert ht using 1 <;> dsimp [s, w] <;> ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hterm j)
  rw [← Finset.mul_sum] at hsum
  have hlower : (1-ε)*(∑ j, F (v j)) ≤ hardyScalar φ p := by
    unfold hardyScalar
    apply (le_div_iff₀ hp.1).mpr
    convert hsum.trans harea using 1 <;> ring
  letI : IsProbabilityMeasure (Measure.map φ unitUniform) := isProbabilityMeasure_map hFm.aemeasurable
  have hidentity : Integrable (fun x : ℝ => x) (Measure.map φ unitUniform) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hFm.aemeasurable).mpr hFi
  have hsel := antitone_uniform_quantile_selection
    (show AntitoneOn φ (Ioo 0 1) from fun _ _ _ _ hxy => hFa hxy)
  have hactual := hardy_tailQuantile_fiber _ hidentity hFm hsel hp
  exact ⟨q, hardyScalar φ p, hqm, hanti, hfin, hpos, hH, hactual, hlower⟩

universe u

/-- Values from all nonnegative finite-valued tuples on all probability spaces
in the chosen arbitrary universe. The constraints use actual completed graphs. -/
def hardyTailValues {n : ℕ} (F : CoordinateVector n → ℝ) (p : ℝ)
    (a : CoordinateVector n) : Set ℝ :=
  {z | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∃ (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ) (X : Ω → CoordinateVector n),
      Measurable X ∧ (∀ᵐ ω ∂μ, 0 ≤ X ω) ∧
      (∀ i, (Set.range (fun ω => X ω i)).Finite) ∧
      (∀ i, quantileHardy (Measure.map (fun ω => X ω i) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => F (X ω)) μ) p = {z}}

/-- The same class with a common-uniform representation in joint law.
The original sample space may be atomic and need not carry that uniform input. -/
def comonotoneHardyTailValues {n : ℕ} (F : CoordinateVector n → ℝ) (p : ℝ)
    (a : CoordinateVector n) : Set ℝ :=
  {z | ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∃ (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ) (X : Ω → CoordinateVector n),
      Measurable X ∧ (∀ᵐ ω ∂μ, 0 ≤ X ω) ∧
      (∀ i, (Set.range (fun ω => X ω i)).Finite) ∧
      ∃ q : Fin n → ℝ → ℝ, (∀ i, AntitoneOn (q i) (Ioo 0 1)) ∧
      Measure.map X μ = Measure.map (fun r i => q i r) unitUniform ∧
      (∀ i, quantileHardy (Measure.map (fun ω => X ω i) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => F (X ω)) μ) p = {z}}

theorem comonotoneHardyTailValues_subset {n : ℕ} (F : CoordinateVector n → ℝ)
    (p : ℝ) (a : CoordinateVector n) :
    comonotoneHardyTailValues.{u} F p a ⊆ hardyTailValues.{u} F p a := by
  rintro z ⟨Ω, mΩ, μ, hμ, X, hm, hn, hfin, q, hq, hlaw, hMarg, hAgg⟩
  exact ⟨Ω, mΩ, μ, hμ, X, hm, hn, hfin, hMarg, hAgg⟩

theorem hardyTailValues_le {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) (a : CoordinateVector n) :
    ∀ z ∈ hardyTailValues.{u} F p a, z ≤ superadditiveTransform F a := by
  rintro z ⟨Ω, mΩ, μ, hμ, X, hm, hn, hfin, hMarg, hAgg⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hμ
  let Y : Ω → CoordinateVector n := fun ω i => max (X ω i) 0
  have hYm : Measurable Y := measurable_pi_iff.mpr
    (fun i => (measurable_pi_iff.mp hm i).max measurable_const)
  have hYn (ω) (i) : 0 ≤ Y ω i := le_max_right _ _
  have hYfin (i) : (Set.range (fun ω => Y ω i)).Finite := by
    apply ((hfin i).image (fun r : ℝ => max r 0)).subset
    rintro _ ⟨ω, rfl⟩
    exact ⟨X ω i, Set.mem_range_self ω, rfl⟩
  have hXY : X =ᵐ[μ] Y := hn.mono
    (fun ω hω => funext (fun i => (max_eq_left (hω i)).symm))
  have hMargLaw (i) : Measure.map (fun ω => X ω i) μ = Measure.map (fun ω => Y ω i) μ :=
    Measure.map_congr (hXY.mono (fun ω he => congrArg (fun x => x i) he))
  have hAggLaw : Measure.map (fun ω => F (X ω)) μ = Measure.map (fun ω => F (Y ω)) μ :=
    Measure.map_congr (hXY.mono (fun ω he => congrArg F he))
  have hi (i) : Integrable (fun ω => Y ω i) μ :=
    finite_nonnegative_range_integrable (measurable_pi_iff.mp hYm i).aemeasurable
      (fun ω => hYn ω i) (hYfin i)
  obtain ⟨b, t, hb, ht, hle⟩ := hardy_tail_aggregation hF hFc μ hYm hYn hi hp
  have hMargY (i) : quantileHardy (Measure.map (fun ω => Y ω i) μ) p = {a i} := by
    rw [← hMargLaw i]
    exact hMarg i
  have hAggY : quantileHardy (Measure.map (fun ω => F (Y ω)) μ) p = {z} := by
    rw [← hAggLaw]
    exact hAgg
  have hba : b = a := by
    funext i
    exact Set.singleton_injective ((hb i).symm.trans (hMargY i))
  have htz : t = z := Set.singleton_injective (ht.symm.trans hAggY)
  simpa only [hba, htz] using hle

theorem hardyTailValues_bddAbove {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) (a : CoordinateVector n) :
    BddAbove (hardyTailValues.{u} F p a) :=
  ⟨superadditiveTransform F a, hardyTailValues_le hF hFc hp a⟩

theorem comonotoneHardyTailValues_bddAbove {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) (a : CoordinateVector n) :
    BddAbove (comonotoneHardyTailValues.{u} F p a) :=
  ⟨superadditiveTransform F a, fun _ hz =>
    hardyTailValues_le hF hFc hp a _ (comonotoneHardyTailValues_subset F p a hz)⟩

/-- Universe lifting changes no law and lets the lower construction inhabit
the same arbitrary universe as the competing original probability spaces. -/
theorem uniform_lift_profile_law {A : Type*} [MeasurableSpace A] {f : ℝ → A}
    (hf : Measurable f) :
    Measure.map (fun ω : ULift.{u} ℝ => f ω.down)
      (Measure.map (ULift.up : ℝ → ULift.{u} ℝ) unitUniform) = Measure.map f unitUniform := by
  change Measure.map (f ∘ ULift.down)
    (Measure.map (ULift.up : ℝ → ULift.{u} ℝ) unitUniform) = Measure.map f unitUniform
  rw [Measure.map_map (hf.comp measurable_down) measurable_up]
  rfl

theorem uniform_profiles_mem_comonotone_values {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p z : ℝ} {a : CoordinateVector n} {q : Fin n → ℝ → ℝ}
    (hqm : ∀ i, Measurable (q i)) (hanti : ∀ i, Antitone (q i))
    (hfin : ∀ i, (Set.range (q i)).Finite) (hpos : ∀ i r, 0 ≤ q i r)
    (hMarg : ∀ i, quantileHardy (Measure.map (q i) unitUniform) p = {a i})
    (hAgg : quantileHardy (Measure.map (fun r => F (fun i => q i r)) unitUniform) p = {z}) :
    z ∈ comonotoneHardyTailValues.{u} F p a := by
  let Ω := ULift.{u} ℝ
  let μ : Measure Ω := Measure.map (ULift.up : ℝ → Ω) unitUniform
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_map measurable_up.aemeasurable
  let X : Ω → CoordinateVector n := fun ω i => q i ω.down
  have hQm : Measurable (fun r i => q i r) := measurable_pi_iff.mpr hqm
  have hXm : Measurable X := hQm.comp measurable_down
  have hXn (ω : Ω) (i) : 0 ≤ X ω i := hpos i ω.down
  have hXf (i) : (Set.range (fun ω => X ω i)).Finite := by
    apply (hfin i).subset
    rintro _ ⟨ω, rfl⟩
    exact Set.mem_range_self ω.down
  obtain ⟨hFm, _, _⟩ := finite_profile_aggregation_properties hF hFc hqm hanti hfin hpos
  refine ⟨Ω, inferInstance, μ, hμ, X, hXm, Eventually.of_forall hXn, hXf, q,
    (fun i _ _ _ _ hxy => hanti i hxy), ?_, ?_, ?_⟩
  · exact uniform_lift_profile_law hQm
  · intro i
    change quantileHardy (Measure.map (fun ω : Ω => q i ω.down) μ) p = {a i}
    rw [uniform_lift_profile_law (hqm i)]
    exact hMarg i
  · change quantileHardy (Measure.map (fun ω : Ω => F (fun i => q i ω.down)) μ) p = {z}
    rw [uniform_lift_profile_law hFm]
    exact hAgg

theorem finite_decomposition_comonotone_model {n m : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p ε : ℝ} (hp : p ∈ Ioo 0 1) (hε : ε ∈ Ioo 0 1)
    {v : Fin m → CoordinateVector n} (hv : ∀ j, 0 ≤ v j)
    {a : CoordinateVector n} (hva : (∑ j, v j) ≤ a) :
    ∃ z ∈ comonotoneHardyTailValues.{u} F p a, (1-ε)*(∑ j, F (v j)) ≤ z := by
  obtain ⟨q, z, hm, hanti, hfin, hpos, hMarg, hAgg, hbound⟩ :=
    geometric_step_hardy_lower_model hF hFc hp hε hv hva
  exact ⟨z, uniform_profiles_mem_comonotone_values hF hFc hm hanti hfin hpos hMarg hAgg, hbound⟩

theorem comonotoneHardyTailValues_nonempty {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    (comonotoneHardyTailValues.{u} F p a).Nonempty := by
  let v : Fin 0 → CoordinateVector n := fun j => Fin.elim0 j
  have hv : ∀ j, 0 ≤ v j := fun j => Fin.elim0 j
  have hva : (∑ j, v j) ≤ a := by simpa only [Fin.sum_univ_zero] using ha
  obtain ⟨z, hz, _⟩ := finite_decomposition_comonotone_model hF hFc hp
    (show (1/2 : ℝ) ∈ Ioo 0 1 by norm_num) hv hva
  exact ⟨z, hz⟩

theorem superadditiveTransform_le_comonotone_values {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a ≤ sSup (comonotoneHardyTailValues.{u} F p a) := by
  change sSup (sharpValues F a) ≤ _
  apply csSup_le (sharpValues_nonempty F ha)
  rintro _ ⟨v, hv, rfl⟩
  have hvsum : (∑ j : Fin v.length, v.get j) = v.sum := by
    simpa only [List.ofFn_get] using (List.sum_ofFn (f := v.get)).symm
  have hFsum : (∑ j : Fin v.length, F (v.get j)) = (v.map F).sum := by
    rw [← List.sum_ofFn]
    congr 1
    change List.ofFn (F ∘ v.get) = List.map F v
    rw [← List.map_ofFn, List.ofFn_get]
  have hvj (j : Fin v.length) : 0 ≤ v.get j := hv.1 _ (List.get_mem v j)
  have hva : (∑ j : Fin v.length, v.get j) ≤ a := by rw [hvsum]; exact hv.2
  have ht0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have ht1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have ht : Tendsto (fun ε : ℝ => (1-ε)*(v.map F).sum) (𝓝[>] (0 : ℝ)) (𝓝 (v.map F).sum) := by
    simpa only [sub_zero, one_mul] using (ht1.sub ht0).mul_const (v.map F).sum
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  obtain ⟨z, hz, hbound⟩ := finite_decomposition_comonotone_model hF hFc hp hε hvj hva
  rw [hFsum] at hbound
  exact hbound.trans (le_csSup (comonotoneHardyTailValues_bddAbove hF hFc hp a) hz)

/-- The full sharpness theorem for all original probability spaces and every
fixed p and a. It asserts suprema, without asserting general attainment or a
single extremizing tuple simultaneously for every p. -/
theorem hardy_tail_aggregation_sharp {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a = sSup (hardyTailValues.{u} F p a) ∧
      superadditiveTransform F a = sSup (comonotoneHardyTailValues.{u} F p a) := by
  have hcN : (comonotoneHardyTailValues.{u} F p a).Nonempty :=
    comonotoneHardyTailValues_nonempty hF hFc hp ha
  have hgN : (hardyTailValues.{u} F p a).Nonempty :=
    hcN.mono (comonotoneHardyTailValues_subset F p a)
  have hgB : BddAbove (hardyTailValues.{u} F p a) := hardyTailValues_bddAbove hF hFc hp a
  have hclower : superadditiveTransform F a ≤ sSup (comonotoneHardyTailValues.{u} F p a) :=
    superadditiveTransform_le_comonotone_values hF hFc hp ha
  have hcupper : sSup (comonotoneHardyTailValues.{u} F p a) ≤ superadditiveTransform F a :=
    csSup_le hcN (fun z hz => hardyTailValues_le hF hFc hp a z
      (comonotoneHardyTailValues_subset F p a hz))
  have hgupper : sSup (hardyTailValues.{u} F p a) ≤ superadditiveTransform F a :=
    csSup_le hgN (hardyTailValues_le hF hFc hp a)
  have hglower : superadditiveTransform F a ≤ sSup (hardyTailValues.{u} F p a) :=
    hclower.trans (csSup_le_csSup hgB hcN (comonotoneHardyTailValues_subset F p a))
  exact ⟨le_antisymm hglower hgupper, le_antisymm hclower hcupper⟩

end ScalarMonotone.EndOfPaper
end
