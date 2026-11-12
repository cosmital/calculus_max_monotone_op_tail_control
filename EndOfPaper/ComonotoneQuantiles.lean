import EndOfPaper.AggregationOperator
import EndOfPaper.HardyVariational
import EndOfPaper.ContinuousSelections

/-!
Actual completed quantiles of monotone uniform profiles and their
aggregation, including arbitrary original spaces carrying the common
uniform variable. Nonnegativity is discharged from the actual variables.
Fixed singleton quantiles force the aggregate singleton; constants attain
the exact finite-valued comonotone supremum.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem antitone_uniform_quantile_selection {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioo 0 1)) :
    SelectionOn (tailQuantile (Measure.map q unitUniform)) (Ioo 0 1) q := by
  have hqm : AEMeasurable q unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo hq
  intro p hp
  change (Measure.map q unitUniform).real (Ioi (q p)) ≤ p ∧
    p ≤ (Measure.map q unitUniform).real (Ici (q p))
  simp only [measureReal_def, Measure.map_apply_of_aemeasurable hqm measurableSet_Ioi,
    Measure.map_apply_of_aemeasurable hqm measurableSet_Ici]
  have hu : unitUniform (q ⁻¹' Ioi (q p)) ≤ volume (Ioo 0 p) := by
    rw [unitUniform, Measure.restrict_apply₀' measurableSet_Ioo.nullMeasurableSet]
    apply measure_mono
    rintro u ⟨hu, huI⟩
    refine ⟨huI.1, ?_⟩
    by_contra hn
    exact not_lt_of_ge (hq hp huI (le_of_not_gt hn)) hu
  have hl : volume (Ioo 0 p) ≤ unitUniform (q ⁻¹' Ici (q p)) := by
    rw [unitUniform, Measure.restrict_apply₀' measurableSet_Ioo.nullMeasurableSet]
    apply measure_mono
    intro u hu
    have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hp.2⟩
    exact ⟨hq huI hp hu.2.le, huI⟩
  constructor
  · have h := ENNReal.toReal_mono (show volume (Ioo 0 p) ≠ ∞ by simp) hu
    simpa only [Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hp.1.le] using h
  · have h := ENNReal.toReal_mono (measure_ne_top unitUniform _) hl
    simpa only [Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hp.1.le] using h

theorem antitone_uniform_quantile_unique {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioo 0 1)) {g : Operator} (hg : MaximalDecreasing g)
    (hgd : dom g ⊆ closure (Ioo (0 : ℝ) 1))
    (hs : SelectionOn g (Ioo 0 1) q) :
    g = tailQuantile (Measure.map q unitUniform) := by
  have hqm : AEMeasurable q unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo hq
  letI : IsProbabilityMeasure (Measure.map q unitUniform) := isProbabilityMeasure_map hqm
  obtain ⟨c, hc, huniq⟩ := antitoneOn_unique_completion hq ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one)
  have hsel := antitone_uniform_quantile_selection hq
  have hQd : dom (tailQuantile (Measure.map q unitUniform)) ⊆ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    rintro p ⟨t, ht⟩
    change (Measure.map q unitUniform).real (Ioi t) ≤ p ∧
      p ≤ (Measure.map q unitUniform).real (Ici t) at ht
    exact ⟨measureReal_nonneg.trans ht.1, ht.2.trans measureReal_le_one⟩
  have hG : restrictOperator (ofFun q) (Ioo 0 1) ≤ g := by
    intro p t ht
    rcases ht with ⟨hp, ht⟩
    change t = q p at ht
    simpa only [ht] using hs p hp
  have hQ : restrictOperator (ofFun q) (Ioo 0 1) ≤ tailQuantile (Measure.map q unitUniform) := by
    intro p t ht
    rcases ht with ⟨hp, ht⟩
    change t = q p at ht
    simpa only [ht] using hsel p hp
  exact (huniq g ⟨hg, hG, hgd⟩).trans
    (huniq _ ⟨tailQuantile_maximal _, hQ, hQd⟩).symm

theorem antitone_uniform_quantile_nonnegative {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioo 0 1)) (hn : ∀ p ∈ Ioo 0 1, 0 ≤ q p)
    {p t : ℝ} (hp : p ∈ Ioo 0 1) (ht : t ∈ tailQuantile (Measure.map q unitUniform) p) :
    0 ≤ t := by
  have hqm : AEMeasurable q unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo hq
  letI : IsProbabilityMeasure (Measure.map q unitUniform) := isProbabilityMeasure_map hqm
  let u : ℝ := (p+1)/2
  have hpu : p < u := by dsimp [u]; linarith [hp.2]
  have hu : u ∈ Ioo (0 : ℝ) 1 := by dsimp [u]; constructor <;> linarith [hp.1, hp.2]
  have hs := antitone_uniform_quantile_selection hq u hu
  have hle := negOut_increasing_iff.mp (tailQuantile_maximal (Measure.map q unitUniform)).1 ht hs
  have hqt : q u ≤ t := by nlinarith
  exact (hn u hu).trans hqt

theorem comonotone_aggregation_quantile {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hn : ∀ i, ∀ p ∈ Ioo 0 1, 0 ≤ q i p) :
    tailQuantile (Measure.map (fun u => F (fun i => q i u)) unitUniform) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (q i) unitUniform)) := by
  have hqm (i) : AEMeasurable (q i) unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo (hq i)
  letI (i : Fin n) : IsProbabilityMeasure (Measure.map (q i) unitUniform) :=
    isProbabilityMeasure_map (hqm i)
  have hf (i) : MaximalDecreasing (tailQuantile (Measure.map (q i) unitUniform)) :=
    tailQuantile_maximal _
  have hd (i) : Ioo (0 : ℝ) 1 ⊆ dom (tailQuantile (Measure.map (q i) unitUniform)) :=
    fun _ hp => tailQuantile_fiber_nonempty _ hp
  have hpos (i) (p) (hp : p ∈ Ioo (0 : ℝ) 1) (v)
      (hv : v ∈ tailQuantile (Measure.map (q i) unitUniform) p) : 0 ≤ v :=
    antitone_uniform_quantile_nonnegative (hq i) (hn i) hp hv
  have hA := aggregationOperator_properties hF hFc isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one) hf hd hpos
  have hs := aggregationOperator_selection hF hFc isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one) hf hd hpos
    (fun i => antitone_uniform_quantile_selection (hq i))
  have hanti : AntitoneOn (fun u => F (fun i => q i u)) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact hF.mono (fun i => hn i y hy) (fun i => hq i hx hy hxy)
  exact (antitone_uniform_quantile_unique hanti hA.1 hA.2.2.1 hs).symm

theorem uniform_profile_law_original_space {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → ℝ} (hU : AEMeasurable U μ)
    (hUlaw : Measure.map U μ = unitUniform) {q : ℝ → ℝ}
    (hq : AntitoneOn q (Ioo 0 1)) :
    Measure.map (fun ω => q (U ω)) μ = Measure.map q unitUniform := by
  have hqm : AEMeasurable q unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo hq
  rw [← hUlaw] at hqm
  simpa only [hUlaw, Function.comp_def] using
    (AEMeasurable.map_map_of_aemeasurable hqm hU).symm

theorem comonotone_aggregation_quantile_original_space {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → ℝ} (hU : AEMeasurable U μ)
    (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hn : ∀ i, ∀ p ∈ Ioo 0 1, 0 ≤ q i p) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (fun ω => q i (U ω)) μ)) := by
  have hmarg (i) := uniform_profile_law_original_space hU hUlaw (hq i)
  have hanti : AntitoneOn (fun u => F (fun i => q i u)) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact hF.mono (fun i => hn i y hy) (fun i => hq i hx hy hxy)
  rw [uniform_profile_law_original_space hU hUlaw hanti]
  simp_rw [hmarg]
  exact comonotone_aggregation_quantile hF hFc hq hn

theorem constant_uniform_quantile (c : ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    tailQuantile (Measure.map (fun _ : ℝ => c) unitUniform) p = {c} := by
  have hq : AntitoneOn (fun _ : ℝ => c) (Ioo 0 1) := fun _ _ _ _ _ => le_rfl
  letI : IsProbabilityMeasure (Measure.map (fun _ : ℝ => c) unitUniform) :=
    isProbabilityMeasure_map measurable_const.aemeasurable
  exact fiber_of_continuous_selection (Or.inr (tailQuantile_maximal _)) isOpen_Ioo
    (fun _ hx => tailQuantile_fiber_nonempty _ hx)
    (antitone_uniform_quantile_selection hq) continuousOn_const hp

theorem comonotone_quantile_fiber {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hn : ∀ i, ∀ u ∈ Ioo 0 1, 0 ≤ q i u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n}
    (hQa : ∀ i, tailQuantile (Measure.map (q i) unitUniform) p = {a i}) :
    tailQuantile (Measure.map (fun u => F (fun i => q i u)) unitUniform) p = {F a} := by
  have hqm (i) : AEMeasurable (q i) unitUniform :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo (hq i)
  letI (i : Fin n) : IsProbabilityMeasure (Measure.map (q i) unitUniform) :=
    isProbabilityMeasure_map (hqm i)
  have hf (i) : MaximalDecreasing (tailQuantile (Measure.map (q i) unitUniform)) :=
    tailQuantile_maximal _
  have hd (i) : Ioo (0 : ℝ) 1 ⊆ dom (tailQuantile (Measure.map (q i) unitUniform)) :=
    fun _ hu => tailQuantile_fiber_nonempty _ hu
  have hpos (i) (u) (hu : u ∈ Ioo (0 : ℝ) 1) (v)
      (hv : v ∈ tailQuantile (Measure.map (q i) unitUniform) u) : 0 ≤ v :=
    antitone_uniform_quantile_nonnegative (hq i) (hn i) hu hv
  have hA := aggregationOperator_properties hF hFc isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one) hf hd hpos
  rw [comonotone_aggregation_quantile hF hFc hq hn, hA.2.2.2 p hp]
  simp only [hQa, csInf_singleton, csSup_singleton, Icc_self]

theorem comonotone_quantile_fiber_original_space {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → ℝ} (hU : AEMeasurable U μ)
    (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hn : ∀ i, ∀ u ∈ Ioo 0 1, 0 ≤ q i u)
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n}
    (hQa : ∀ i, tailQuantile (Measure.map (fun ω => q i (U ω)) μ) p = {a i}) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) p = {F a} := by
  have hmarg (i) := uniform_profile_law_original_space hU hUlaw (hq i)
  have hsingle (i) : tailQuantile (Measure.map (q i) unitUniform) p = {a i} := by
    simpa only [hmarg] using hQa i
  have hanti : AntitoneOn (fun u => F (fun i => q i u)) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact hF.mono (fun i => hn i y hy) (fun i => hq i hx hy hxy)
  rw [uniform_profile_law_original_space hU hUlaw hanti]
  exact comonotone_quantile_fiber hF hFc hq hn hp hsingle

def comonotoneQuantileValues {n : ℕ} (F : CoordinateVector n → ℝ)
    (p : ℝ) (a : CoordinateVector n) : Set ℝ :=
  {b | ∃ q : Fin n → ℝ → ℝ,
    (∀ i, AntitoneOn (q i) (Ioo 0 1)) ∧ (∀ i u, 0 ≤ q i u) ∧
    (∀ i, (Set.range (q i)).Finite) ∧
    (∀ i, tailQuantile (Measure.map (q i) unitUniform) p = {a i}) ∧
    b ∈ tailQuantile (Measure.map (fun u => F (fun i => q i u)) unitUniform) p}

theorem comonotone_quantile_sharp_isGreatest {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    IsGreatest (comonotoneQuantileValues F p a) (F a) := by
  refine ⟨?_, ?_⟩
  · refine ⟨(fun i _ => a i), (fun _ _ _ _ _ _ => le_rfl), (fun i _ => ha i), ?_, ?_, ?_⟩
    · intro i
      simpa only [Set.range_const] using Set.finite_singleton (a i)
    · exact fun i => constant_uniform_quantile (a i) hp
    · simpa only [constant_uniform_quantile (F a) hp] using mem_singleton (F a)
  · rintro b ⟨q, hq, hn, _, hQa, hb⟩
    rw [comonotone_quantile_fiber hF hFc hq (fun i u _ => hn i u) hp hQa] at hb
    exact (mem_singleton_iff.mp hb).le

theorem comonotone_quantile_sharp {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n} (ha : 0 ≤ a) :
    sSup (comonotoneQuantileValues F p a) = F a :=
  (comonotone_quantile_sharp_isGreatest hF hFc hp ha).csSup_eq


/-- Nonnegativity is assumed only for the actual original-space variables.
Replacing the uniform profiles by their positive parts changes none of those
variables and discharges nonnegativity at every uniform level. -/
theorem comonotone_aggregation_nonnegative_original_space {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → ℝ} (hU : AEMeasurable U μ)
    (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hX : ∀ ω i, 0 ≤ q i (U ω)) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (fun ω => q i (U ω)) μ)) := by
  let r : Fin n → ℝ → ℝ := fun i u => max (q i u) 0
  have hr (i) : (fun ω => r i (U ω)) = (fun ω => q i (U ω)) := by
    funext ω
    exact max_eq_left (hX ω i)
  have hranti (i) : AntitoneOn (r i) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact max_le_max (hq i hx hy hxy) le_rfl
  have hrn (i) (u) (_ : u ∈ Ioo (0 : ℝ) 1) : 0 ≤ r i u := le_max_right _ _
  have hagg : (fun ω => F (fun i => r i (U ω))) =
      (fun ω => F (fun i => q i (U ω))) := by
    funext ω
    congr 1
    funext i
    exact congrFun (hr i) ω
  have ht := comonotone_aggregation_quantile_original_space hU hUlaw hF hFc hranti hrn
  rw [hagg] at ht
  simpa only [hr] using ht

theorem comonotone_fixed_quantile_original_space {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → ℝ} (hU : AEMeasurable U μ)
    (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hX : ∀ ω i, 0 ≤ q i (U ω))
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : CoordinateVector n}
    (hQa : ∀ i, tailQuantile (Measure.map (fun ω => q i (U ω)) μ) p = {a i}) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) p = {F a} := by
  let r : Fin n → ℝ → ℝ := fun i u => max (q i u) 0
  have hr (i) : (fun ω => r i (U ω)) = (fun ω => q i (U ω)) := by
    funext ω
    exact max_eq_left (hX ω i)
  have hranti (i) : AntitoneOn (r i) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact max_le_max (hq i hx hy hxy) le_rfl
  have hrn (i) (u) (_ : u ∈ Ioo (0 : ℝ) 1) : 0 ≤ r i u := le_max_right _ _
  have hQaR (i) : tailQuantile (Measure.map (fun ω => r i (U ω)) μ) p = {a i} := by
    rw [hr i]
    exact hQa i
  have hagg : (fun ω => F (fun i => r i (U ω))) =
      (fun ω => F (fun i => q i (U ω))) := by
    funext ω
    congr 1
    funext i
    exact congrFun (hr i) ω
  have ht := comonotone_quantile_fiber_original_space hU hUlaw hF hFc hranti hrn hp hQaR
  rwa [hagg] at ht

end ScalarMonotone.EndOfPaper
end
