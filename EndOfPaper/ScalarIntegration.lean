import EndOfPaper.Area
import EndOfPaper.Aumann

/-!
# Selection-based scalar integration (current Definition `def:area`)

Selections exist on every subset of the domain. Monotonicity makes their
restrictions measurable. All selections agree for atomless measures, so this
also treats infinite nonnegative integrals and both parts of signed integrals.
The Aumann integral is a singleton when an integrable selection exists.
-/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- Completing the restriction of a maximal graph preserves every interior
value, including the entire value at a jump. -/
theorem completion_restriction_value {f : Operator} (hf : MaximalIncreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f) {x : ℝ} (hx : x ∈ I) :
    completion I (restrictOperator f I) x = f x := by
  ext u
  constructor
  · intro hu
    obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hx)
    have hb := compatible_iff_bounds.mp hu.2
    apply hf.2
    apply compatible_iff_bounds.mpr
    constructor
    · intro y v hv hyx
      obtain ⟨z, hzlo, hzx⟩ := exists_between (max_lt hax hyx)
      have hzI : z ∈ I := hab ⟨(le_max_left a y).trans_lt hzlo, hzx.trans hxb⟩
      obtain ⟨w, hw⟩ := hdom hzI
      exact (hf.1.le_of_lt hv hw ((le_max_right a y).trans_lt hzlo)).trans
        (hb.1 (show w ∈ restrictOperator f I z from ⟨hzI, hw⟩) hzx)
    · intro y v hv hxy
      obtain ⟨z, hxz, hzhi⟩ := exists_between (lt_min hxb hxy)
      have hzI : z ∈ I := hab ⟨hax.trans hxz, hzhi.trans_le (min_le_left b y)⟩
      obtain ⟨w, hw⟩ := hdom hzI
      exact (hb.2 (show w ∈ restrictOperator f I z from ⟨hzI, hw⟩) hxz).trans
        (hf.1.le_of_lt hw hv (hzhi.trans_le (min_le_right b y)))
  · intro hu
    exact le_completion (restrictOperator_increasing hf.1 I) (dom_restrictOperator hdom)
      x (show u ∈ restrictOperator f I x from ⟨hx, hu⟩)

/-- The manuscript's completed restriction with exact interior values. -/
theorem unique_completed_restriction_values {f : Operator} (hf : MaximalIncreasing f)
    {I : Set ℝ} (hI : I.OrdConnected) (hopen : IsOpen I) (hne : I.Nonempty)
    (hdom : I ⊆ dom f) :
    ∃! g : Operator, MaximalIncreasing g ∧ (∀ x ∈ I, g x = f x) ∧ dom g ⊆ closure I := by
  let c := completion I (restrictOperator f I)
  have hc : MaximalIncreasing c := completion_maximal hI hne
    (restrictOperator_increasing hf.1 I) (dom_restrictOperator hdom)
  refine ⟨c, ⟨hc, fun x hx => completion_restriction_value hf hopen hdom hx,
    completion_dom_subset I (restrictOperator f I)⟩, ?_⟩
  rintro g ⟨hg, heq, hgd⟩
  have hgc : restrictOperator f I ≤ g := by
    intro x u hu
    rw [heq x hu.1]
    exact hu.2
  have hcc : restrictOperator f I ≤ c :=
    le_completion (restrictOperator_increasing hf.1 I) (dom_restrictOperator hdom)
  exact (unique_completed_restriction hf hI hne hdom).unique ⟨hg, hgc, hgd⟩
    ⟨hc, hcc, completion_dom_subset I (restrictOperator f I)⟩

/-- Exact completed restriction for decreasing graphs, with boundary-domain control. -/
theorem unique_completed_decreasing_restriction_values {f : Operator}
    (hf : MaximalDecreasing f) {I : Set ℝ} (hI : I.OrdConnected) (hopen : IsOpen I)
    (hne : I.Nonempty) (hdom : I ⊆ dom f) :
    ∃! g : Operator, MaximalDecreasing g ∧ (∀ x ∈ I, g x = f x) ∧ dom g ⊆ closure I := by
  have hnegdom : I ⊆ dom (negOut f) := by
    intro x hx
    obtain ⟨u, hu⟩ := hdom hx
    exact ⟨-u, by simpa only [negOut, mem_setOf_eq, neg_neg] using hu⟩
  obtain ⟨g, hg, huniq⟩ := unique_completed_restriction_values hf hI hopen hne hnegdom
  refine ⟨negOut g, ⟨?_, ?_, ?_⟩, ?_⟩
  · change MaximalIncreasing (negOut (negOut g))
    simpa only [negOut_negOut] using hg.1
  · intro x hx
    change (fun u => -u ∈ g x) = _
    rw [hg.2.1 x hx]
    exact congrFun (negOut_negOut f) x
  · rintro x ⟨u, hu⟩
    exact hg.2.2 ⟨-u, hu⟩
  · rintro k ⟨hk, heq, hkd⟩
    have hkeq : ∀ x ∈ I, negOut k x = negOut f x := by
      intro x hx
      simp only [negOut, heq x hx]
    have hnegkd : dom (negOut k) ⊆ closure I := by
      rintro x ⟨u, hu⟩
      exact hkd ⟨-u, hu⟩
    have heqg := huniq (negOut k) ⟨hk, hkeq, hnegkd⟩
    have := congrArg negOut heqg
    simpa only [negOut_negOut] using this

/-- Choose a value wherever the graph is defined, and use zero elsewhere. -/
def scalarSelection (f : Operator) : ℝ → ℝ := by
  classical
  exact fun x => if hx : (f x).Nonempty then hx.choose else 0

theorem scalarSelection_mem {f : Operator} {x : ℝ} (hx : x ∈ dom f) :
    scalarSelection f x ∈ f x := by
  classical
  have hne : (f x).Nonempty := hx
  simpa only [scalarSelection, dif_pos hne] using hne.choose_spec

theorem scalarSelection_on {f : Operator} {I : Set ℝ} (hI : I ⊆ dom f) :
    SelectionOn f I (scalarSelection f) :=
  fun _ hx => scalarSelection_mem (hI hx)

theorem selection_antitoneOn {f : Operator} (hf : Decreasing f)
    {I : Set ℝ} {s : ℝ → ℝ} (hs : SelectionOn f I s) : AntitoneOn s I := by
  have hneg : SelectionOn (negOut f) I (fun x => -s x) := by
    intro x hx
    change -(-s x) ∈ f x
    simpa only [neg_neg] using hs x hx
  have hmono := selection_monotoneOn hf hneg
  intro x hx y hy hxy
  have := hmono hx hy hxy
  change -s x ≤ -s y at this
  linarith

/-- A measurable selection on the actual domain, for either orientation. -/
theorem exists_measurable_selection {f : Operator}
    (hf : Increasing f ∨ Decreasing f) {I : Set ℝ} (hI : I ⊆ dom f) :
    ∃ s : ℝ → ℝ, SelectionOn f I s ∧ Measurable (fun x : I => s x) := by
  refine ⟨scalarSelection f, scalarSelection_on hI, ?_⟩
  rcases hf with hf | hf
  · have hmono : Monotone (fun x : I => scalarSelection f x) :=
      fun x y hxy => selection_monotoneOn hf (scalarSelection_on hI)
        x.property y.property hxy
    exact hmono.measurable
  · have hanti : Antitone (fun x : I => scalarSelection f x) :=
      fun x y hxy => selection_antitoneOn hf (scalarSelection_on hI)
        x.property y.property hxy
    exact hanti.measurable

/-- A globally measurable representative, set to zero outside the integration set. -/
theorem exists_global_measurable_selection {f : Operator}
    (hf : Increasing f ∨ Decreasing f) {I : Set ℝ}
    (hI : MeasurableSet I) (hdom : I ⊆ dom f) :
    ∃ s : ℝ → ℝ, Measurable s ∧ SelectionOn f I s := by
  classical
  obtain ⟨s, hsel, hsm⟩ := exists_measurable_selection hf hdom
  refine ⟨fun x => if hx : x ∈ I then (fun y : I => s y) ⟨x, hx⟩ else 0, ?_, ?_⟩
  · exact hsm.dite measurable_const hI
  · intro x hx
    simpa only [dif_pos hx] using hsel x hx

/-- An almost-everywhere version also permits null-set changes of selections. -/
theorem ae_selections_ae_eq {f : Operator} (hf : Increasing f ∨ Decreasing f)
    (μ : Measure ℝ) [NoAtoms μ] {s t : ℝ → ℝ}
    (hs : ∀ᵐ x ∂μ, s x ∈ f x) (ht : ∀ᵐ x ∂μ, t x ∈ f x) : s =ᵐ[μ] t := by
  rcases hf with hf | hf
  · filter_upwards [(countable_jumpInputs hf).ae_not_mem μ, hs, ht] with x hx hs ht
    exact fiber_subsingleton_off_jumps f hx hs ht
  · have hs' : ∀ᵐ x ∂μ, -s x ∈ negOut f x := by
      filter_upwards [hs] with x hx
      change -(-s x) ∈ f x
      simpa only [neg_neg] using hx
    have ht' : ∀ᵐ x ∂μ, -t x ∈ negOut f x := by
      filter_upwards [ht] with x hx
      change -(-t x) ∈ f x
      simpa only [neg_neg] using hx
    filter_upwards [(countable_jumpInputs hf).ae_not_mem μ, hs', ht'] with x hx hs ht
    exact neg_injective (fiber_subsingleton_off_jumps (negOut f) hx hs ht)

/-- Every nonnegative scalar expression is independent of selection, including
when its integral is infinite. No finiteness is imposed. -/
theorem selection_lintegral_comp_eq {f : Operator} (hf : Increasing f ∨ Decreasing f)
    {I : Set ℝ} (hI : MeasurableSet I) {s t : ℝ → ℝ}
    (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (ψ : ℝ → ℝ≥0∞) :
    (∫⁻ x in I, ψ (s x) ∂μ) = ∫⁻ x in I, ψ (t x) ∂μ := by
  have heq : s =ᵐ[μ.restrict I] t := by
    rcases hf with hf | hf
    · exact selections_ae_eq hf hs ht μ hI
    · exact decreasing_selections_ae_eq hf hs ht μ hI
  exact lintegral_congr_ae (heq.mono fun _ hx => congrArg ψ hx)

/-- The two extended parts of a signed scalar expression agree separately.
The paper's signed integral is defined when these are not both infinite. -/
theorem selection_signed_parts_eq {f : Operator} (hf : Increasing f ∨ Decreasing f)
    {I : Set ℝ} (hI : MeasurableSet I) {s t : ℝ → ℝ}
    (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (ψ : ℝ → ℝ) :
    (∫⁻ x in I, ENNReal.ofReal (ψ (s x)) ∂μ) =
      (∫⁻ x in I, ENNReal.ofReal (ψ (t x)) ∂μ) ∧
    (∫⁻ x in I, ENNReal.ofReal (-ψ (s x)) ∂μ) =
      (∫⁻ x in I, ENNReal.ofReal (-ψ (t x)) ∂μ) :=
  ⟨selection_lintegral_comp_eq hf hI hs ht μ (fun v => ENNReal.ofReal (ψ v)),
   selection_lintegral_comp_eq hf hI hs ht μ (fun v => ENNReal.ofReal (-ψ v))⟩

/-- The scalar integral is the unique element of its Aumann integral. -/
theorem aumannIntegral_monotone_singleton {f : Operator}
    (hf : Increasing f ∨ Decreasing f) (μ : Measure ℝ) [NoAtoms μ]
    {s : ℝ → ℝ} (hs : Integrable s μ) (hsel : ∀ᵐ x ∂μ, s x ∈ f x) :
    aumannIntegral μ f = {∫ x, s x ∂μ} := by
  ext v
  constructor
  · rintro ⟨t, ht, htsel, rfl⟩
    exact integral_congr_ae (ae_selections_ae_eq hf μ htsel hsel)
  · intro hv
    exact ⟨s, hs, hsel, hv⟩

end ScalarMonotone.EndOfPaper
end
