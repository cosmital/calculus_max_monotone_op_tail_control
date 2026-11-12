import EndOfPaper.HardyEndpoints
import MonotoneOperators.ProbabilityInterface

/-!
The actual completed Hardy dilation-family integral (def:hardytransform,
eq:hardy and lem:hardyconvexity). Positive initial-interval geometry and
endpoint integrability are derived; no finite upper endpoint is imposed.
The construction has exact singleton interior fibers, whole-operator
uniqueness, convexity/concavity preservation, and compatible smaller
completed restrictions in the locally integrable setting.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveInputDilation (c : ℝ) (f : Operator) : Operator := fun x => f (c*x)

theorem positiveInputDilation_maximal {f : Operator} (hf : MaximalDecreasing f)
    {c : ℝ} (hc : 0 < c) : MaximalDecreasing (positiveInputDilation c f) := by
  refine ⟨increasing_iff_order.mpr ?_, ?_⟩
  · intro x u y v hu hv hxy
    exact hf.1.le_of_lt hu hv (mul_lt_mul_of_pos_left hxy hc)
  · intro x u hxu
    apply hf.2
    have hb := compatible_iff_bounds.mp hxu
    apply compatible_iff_bounds.mpr
    constructor
    · intro y v hv hyx
      have hv' : v ∈ negOut (positiveInputDilation c f) (y/c) := by
        change -v ∈ f (c*(y/c))
        have he : c*(y/c) = y := by field_simp [hc.ne']
        rw [he]
        exact hv
      apply hb.1 hv'
      exact (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using hyx)
    · intro y v hv hxy
      have hv' : v ∈ negOut (positiveInputDilation c f) (y/c) := by
        change -v ∈ f (c*(y/c))
        have he : c*(y/c) = y := by field_simp [hc.ne']
        rw [he]
        exact hv
      apply hb.2 hv'
      exact (lt_div_iff₀ hc).mpr (by simpa only [mul_comm] using hxy)

def completedDecreasingRestriction (I : Set ℝ) (f : Operator) : Operator :=
  negOut (completion I (restrictOperator (negOut f) I))

theorem completedDecreasingRestriction_value {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f) {x : ℝ} (hx : x ∈ I) :
    completedDecreasingRestriction I f x = f x := by
  have hndom : I ⊆ dom (negOut f) := by simpa only [dom_negOut] using hdom
  have he := completion_restriction_value hf hI hndom hx
  ext v
  change -v ∈ completion I (restrictOperator (negOut f) I) x ↔ v ∈ f x
  rw [he]
  change -(-v) ∈ f x ↔ v ∈ f x
  simp only [neg_neg]

theorem completedDecreasingRestriction_maximal {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hord : I.OrdConnected) (hne : I.Nonempty) (hdom : I ⊆ dom f) :
    MaximalDecreasing (completedDecreasingRestriction I f) := by
  have hndom : I ⊆ dom (negOut f) := by simpa only [dom_negOut] using hdom
  have hm := completion_maximal hord hne (restrictOperator_increasing hf.1 I)
    (dom_restrictOperator hndom)
  change MaximalIncreasing (negOut (negOut (completion I (restrictOperator (negOut f) I))))
  simpa only [negOut_negOut] using hm

theorem completedDecreasingRestriction_domain {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : I ⊆ dom f) :
    interior (dom (completedDecreasingRestriction I f)) = I ∧
      dom (completedDecreasingRestriction I f) ⊆ closure I := by
  have hc : dom (completedDecreasingRestriction I f) ⊆ closure I := by
    simpa only [completedDecreasingRestriction, dom_negOut] using
      completion_dom_subset I (restrictOperator (negOut f) I)
  refine ⟨domain_interior_of_open_interval hI hord hne ?_ hc, hc⟩
  intro x hx
  change (completedDecreasingRestriction I f x).Nonempty
  rw [show completedDecreasingRestriction I f x = f x from
    completedDecreasingRestriction_value hf hI hdom hx]
  exact hdom hx

/-- The values outside the averaging interval are harmless positive parameters.
The measure is exactly Lebesgue restricted to (0,1). -/
def hardyParameter (r : ℝ) : ℝ := if r ∈ Ioo (0 : ℝ) 1 then r else 1

theorem hardyParameter_bounds (r : ℝ) : 0 < hardyParameter r ∧ hardyParameter r ≤ 1 := by
  classical
  by_cases hr : r ∈ Ioo (0 : ℝ) 1
  · simpa only [hardyParameter, if_pos hr] using (show 0 < r ∧ r ≤ 1 from ⟨hr.1, hr.2.le⟩)
  · simp only [hardyParameter, if_neg hr, zero_lt_one, le_refl, and_self]

def hardyDilationFamily (I : Set ℝ) (f : Operator) (r : ℝ) : Operator :=
  completedDecreasingRestriction I (positiveInputDilation (hardyParameter r) f)

theorem hardyDilationFamily_properties {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : I ⊆ interior (dom f))
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I) (r : ℝ) :
    MaximalDecreasing (hardyDilationFamily I f r) ∧
      interior (dom (hardyDilationFamily I f r)) = I ∧
      dom (hardyDilationFamily I f r) ⊆ closure I ∧
      ∀ p ∈ I, hardyDilationFamily I f r p = f (hardyParameter r*p) := by
  have hr := hardyParameter_bounds r
  have hD := positiveInputDilation_maximal hf hr.1
  have hd : I ⊆ dom (positiveInputDilation (hardyParameter r) f) := by
    intro p hp
    change hardyParameter r*p ∈ dom f
    exact interior_subset (hdom (hscale _ hr p hp))
  obtain ⟨hdi, hdc⟩ := completedDecreasingRestriction_domain hD hI hord hne hd
  exact ⟨completedDecreasingRestriction_maximal hD hord hne hd, hdi, hdc,
    fun p hp => completedDecreasingRestriction_value hD hI hd hp⟩

def hardyFamilyIntegral (I : Set ℝ) (f : Operator) : Operator :=
  decreasingFamilyIntegral unitUniform I (hardyDilationFamily I f)

/-- Ae equality of parameter families preserves the whole completed integral,
not just its interior values. -/
theorem decreasingFamilyIntegral_congr_ae {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) {f g : Θ → Operator} (he : f =ᵐ[μ] g) :
    decreasingFamilyIntegral μ I f = decreasingFamilyIntegral μ I g := by
  unfold decreasingFamilyIntegral increasingFamilyIntegral
  apply congrArg negOut
  apply congrArg (completion I)
  funext x
  have hl := integral_congr_ae (he.fun_comp (fun F : Operator => sInf (negOut F x)))
  have hu := integral_congr_ae (he.fun_comp (fun F : Operator => sSup (negOut F x)))
  simp only [Function.comp_def] at hl hu
  simp only [integratedFiberGraph, hl, hu]

/-- The construction is literally the completed family integral of the
paper's restricted positive dilations on (0,1). -/
theorem hardyFamilyIntegral_eq_actual_dilations (I : Set ℝ) (f : Operator) :
    hardyFamilyIntegral I f = decreasingFamilyIntegral unitUniform I
      (fun r => completedDecreasingRestriction I (positiveInputDilation r f)) := by
  apply decreasingFamilyIntegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  simp only [hardyDilationFamily, hardyParameter, if_pos hr]

/-- The paper's zero lower domain endpoint and a positive domain point imply
all initial-interval geometry, without imposing a finite upper endpoint. -/
theorem decreasing_zero_inf_domain_geometry {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a) :
    (interior (dom f)).OrdConnected ∧ (interior (dom f)).Nonempty ∧
      (∀ p ∈ interior (dom f), 0 < p) ∧
      (∀ p ∈ interior (dom f), Ioo 0 p ⊆ interior (dom f)) ∧
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ interior (dom f), c*p ∈ interior (dom f)) := by
  have ho := decreasing_dom_ordConnected hf
  have hn : dom f ⊆ Ici 0 := fun _ hx => hzero.1 hx
  have hp0 (p) (hp : p ∈ interior (dom f)) : 0 < p := by
    have h := interior_mono hn hp
    simpa only [interior_Ici, mem_Ioi] using h
  have hprefix (p) (hp : p ∈ interior (dom f)) : Ioo 0 p ⊆ interior (dom f) := by
    intro u hu
    obtain ⟨b, hb, _, hbu⟩ := hzero.exists_between hu.1
    have hsub : Ioo b p ⊆ dom f := fun y hy =>
      ho.out hb (interior_subset hp) ⟨hy.1.le, hy.2.le⟩
    exact isOpen_Ioo.subset_interior_iff.mpr hsub ⟨hbu, hu.2⟩
  have hne : (interior (dom f)).Nonempty := by
    obtain ⟨a, ha, ha0⟩ := hpositive
    obtain ⟨b, hb, _, hba⟩ := hzero.exists_between ha0
    have hsub : Ioo b a ⊆ dom f := fun y hy => ho.out hb ha ⟨hy.1.le, hy.2.le⟩
    exact ⟨(b+a)/2, isOpen_Ioo.subset_interior_iff.mpr hsub ⟨by linarith, by linarith⟩⟩
  have hord : (interior (dom f)).OrdConnected := by
    apply ordConnected_def.mpr
    intro a ha b hb z hz
    by_cases he : z = b
    · simpa only [he] using hb
    exact hprefix b hb ⟨(hp0 a ha).trans_le hz.1, lt_of_le_of_ne hz.2 he⟩
  refine ⟨hord, hne, hp0, hprefix, ?_⟩
  intro c hc p hp
  by_cases hc1 : c = 1
  · simpa only [hc1, one_mul] using hp
  exact hprefix p hp ⟨mul_pos hc.1 (hp0 p hp),
    mul_lt_of_lt_one_left (hp0 p hp) (lt_of_le_of_ne hc.2 hc1)⟩

theorem hardyDilationFamily_endpoint_areas {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : I ⊆ interior (dom f))
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) {p : ℝ} (hp : p ∈ I) (hp0 : 0 < p)
    (hi : IntervalIntegrable s volume 0 p) :
    Integrable (fun r => sInf (hardyDilationFamily I f r p)) unitUniform ∧
    Integrable (fun r => sSup (hardyDilationFamily I f r p)) unitUniform ∧
    (∫ r, sInf (hardyDilationFamily I f r p) ∂unitUniform) = hardyScalar s p ∧
    (∫ r, sSup (hardyDilationFamily I f r p) ∂unitUniform) = hardyScalar s p := by
  obtain ⟨hl, hu, hal, hau⟩ := hardy_dilation_endpoint_areas hf hdom hs hp0
    (fun r hr => hscale r ⟨hr.1, hr.2.le⟩ p hp) hi
  have he : ∀ᵐ r ∂unitUniform, hardyDilationFamily I f r p = f (r*p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [(hardyDilationFamily_properties hf hI hord hne hdom hscale r).2.2.2 p hp]
    simp only [hardyParameter, if_pos hr]
  have hel : (fun r => sInf (hardyDilationFamily I f r p)) =ᵐ[unitUniform]
      (fun r => sInf (f (r*p))) := he.mono (fun r hr => congrArg sInf hr)
  have heu : (fun r => sSup (hardyDilationFamily I f r p)) =ᵐ[unitUniform]
      (fun r => sSup (f (r*p))) := he.mono (fun r hr => congrArg sSup hr)
  exact ⟨hl.congr hel.symm, hu.congr heu.symm,
    (integral_congr_ae hel).trans hal, (integral_congr_ae heu).trans hau⟩

/-- The actual Aumann family integral is maximal with the exact common domain
interior and singleton scalar Hardy fibers. Uniqueness concerns entire completed
operators, including endpoint fibers, rather than only interior scalar values. -/
theorem hardyFamilyIntegral_well_defined {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : I ⊆ interior (dom f)) (hpos : ∀ p ∈ I, 0 < p)
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    {s : ℝ → ℝ} (hs : SelectionOn f I s)
    (hi : ∀ p ∈ I, IntervalIntegrable s volume 0 p) :
    MaximalDecreasing (hardyFamilyIntegral I f) ∧
      interior (dom (hardyFamilyIntegral I f)) = I ∧
      dom (hardyFamilyIntegral I f) ⊆ closure I ∧
      (∀ p ∈ I, hardyFamilyIntegral I f p = {hardyScalar s p}) ∧
      ∀ g : Operator, MaximalDecreasing g → dom g ⊆ closure I →
        (∀ p ∈ I, g p = {hardyScalar s p}) → g = hardyFamilyIntegral I f := by
  have hprops := hardyDilationFamily_properties hf hI hord hne hdom hscale
  have hm (r) : MaximalDecreasing (hardyDilationFamily I f r) := (hprops r).1
  have hd (r) : I ⊆ dom (hardyDilationFamily I f r) := by
    intro p hp
    apply interior_subset
    rw [(hprops r).2.1]
    exact hp
  have ha (p) (hp : p ∈ I) :=
    hardyDilationFamily_endpoint_areas hf hI hord hne hdom hscale hs hp (hpos p hp) (hi p hp)
  have hl (p) (hp : p ∈ I) : Integrable (fun r => sInf (hardyDilationFamily I f r p)) unitUniform :=
    (ha p hp).1
  have hu (p) (hp : p ∈ I) : Integrable (fun r => sSup (hardyDilationFamily I f r p)) unitUniform :=
    (ha p hp).2.1
  have hvalue (p) (hp : p ∈ I) : hardyFamilyIntegral I f p = {hardyScalar s p} := by
    rw [hardyFamilyIntegral, decreasingFamilyIntegral_value unitUniform hm hI hd hl hu hp,
      (ha p hp).2.2.1, (ha p hp).2.2.2, Icc_self]
  obtain ⟨hmax, hcl, huniq⟩ := decreasingFamilyIntegral_unique unitUniform hm hI hord hne hd hl hu
  refine ⟨hmax, decreasingFamilyIntegral_domain_interior unitUniform hm hI hord hne hd hl hu,
    hcl, hvalue, ?_⟩
  intro g hg hgd hgv
  apply huniq g hg hgd
  intro p hp
  calc
    g p = {hardyScalar s p} := hgv p hp
    _ = hardyFamilyIntegral I f p := (hvalue p hp).symm
    _ = aumannIntegral unitUniform (fun r => hardyDilationFamily I f r p) :=
      decreasingFamilyIntegral_aumann unitUniform hm hI hd hl hu hp

/-- Manuscript-facing integrable case: zero lower domain endpoint and a
positive domain point imply all geometry and local integrability obligations.
No finite upper endpoint or integrability of endpoint maps is assumed. -/
theorem hardyFamilyIntegral_of_integrable {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hsi : Integrable s (volume.restrict (interior (dom f)))) :
    let I := interior (dom f)
    MaximalDecreasing (hardyFamilyIntegral I f) ∧
      interior (dom (hardyFamilyIntegral I f)) = I ∧
      dom (hardyFamilyIntegral I f) ⊆ closure I ∧
      (∀ p ∈ I, hardyFamilyIntegral I f p = {hardyScalar s p}) ∧
      ∀ g : Operator, MaximalDecreasing g → dom g ⊆ closure I →
        (∀ p ∈ I, g p = {hardyScalar s p}) → g = hardyFamilyIntegral I f := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ :=
    decreasing_zero_inf_domain_geometry hf hzero hpositive
  apply hardyFamilyIntegral_well_defined hf isOpen_interior hord hne Subset.rfl hpos hscale hs
  intro p hp
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
  exact IntegrableOn.mono_set hsi (hprefix p hp)

/-- Convexity of scalar Hardy averages on any positive initial interval,
including intervals with no finite upper endpoint. -/
theorem hardyScalar_convexOn_initial {φ : ℝ → ℝ} {I : Set ℝ}
    (hφ : ConvexOn ℝ I φ) (hpos : ∀ p ∈ I, 0 < p)
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    (hi : ∀ p ∈ I, IntervalIntegrable φ volume 0 p) :
    ConvexOn ℝ I (hardyScalar φ) := by
  refine ⟨hφ.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x+b • y ∈ I := hφ.1 hx hy ha hb hab
  have hxint := hardyScalar_dilation_integrable (hpos x hx) (hi x hx)
  have hyint := hardyScalar_dilation_integrable (hpos y hy) (hi y hy)
  rw [hardyScalar_dilation φ (hpos _ hz), hardyScalar_dilation φ (hpos x hx),
    hardyScalar_dilation φ (hpos y hy)]
  calc
    (∫ r in (0 : ℝ)..1, φ (r*(a • x+b • y))) ≤
        ∫ r in (0 : ℝ)..1, a*φ (r*x)+b*φ (r*y) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
        (hardyScalar_dilation_integrable (hpos _ hz) (hi _ hz))
        ((hxint.const_mul a).add (hyint.const_mul b))
      intro r hr
      have hc := hφ.2 (hscale r ⟨hr.1, hr.2.le⟩ x hx)
        (hscale r ⟨hr.1, hr.2.le⟩ y hy) ha hb hab
      have he : r*(a*x+b*y) = a*(r*x)+b*(r*y) := by ring
      simpa only [smul_eq_mul, he] using hc
    _ = a • (∫ r in (0 : ℝ)..1, φ (r*x)) +
        b • (∫ r in (0 : ℝ)..1, φ (r*y)) := by
      rw [intervalIntegral.integral_add (hxint.const_mul _) (hyint.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]

theorem hardyScalar_concaveOn_initial {φ : ℝ → ℝ} {I : Set ℝ}
    (hφ : ConcaveOn ℝ I φ) (hpos : ∀ p ∈ I, 0 < p)
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    (hi : ∀ p ∈ I, IntervalIntegrable φ volume 0 p) :
    ConcaveOn ℝ I (hardyScalar φ) := by
  have hn := (hardyScalar_convexOn_initial hφ.neg hpos hscale
    (fun p hp => (hi p hp).neg)).neg
  have he : hardyScalar (-φ) = -hardyScalar φ := funext (fun p => hardyScalar_neg φ p)
  rwa [he, neg_neg] at hn

/-- Convexity in the manuscript's sense, expressed as existence of a convex
selection on the actual interior domain of the completed Hardy operator. -/
theorem hardyFamilyIntegral_preserves_convexity {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hsi : Integrable s (volume.restrict (interior (dom f))))
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (interior (dom f)) φ)
    (hφsel : SelectionOn f (interior (dom f)) φ) :
    ∃ ψ : ℝ → ℝ,
      ConvexOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      SelectionOn (hardyFamilyIntegral (interior (dom f)) f)
        (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ := by
  obtain ⟨_, _, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hzero hpositive
  have hφi : Integrable φ (volume.restrict (interior (dom f))) := hsi.congr
    (decreasing_selections_ae_eq hf.1 hs hφsel volume isOpen_interior.measurableSet)
  obtain ⟨_, hd, _, hv, _⟩ := hardyFamilyIntegral_of_integrable hf hzero hpositive hφsel hφi
  have hi (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable φ volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
      (IntegrableOn.mono_set hφi (hprefix p hp))
  refine ⟨hardyScalar φ, ?_, ?_⟩
  · rw [hd]
    exact hardyScalar_convexOn_initial hφ hpos hscale hi
  · intro p hp
    have hpI : p ∈ interior (dom f) := by simpa only [hd] using hp
    rw [hv p hpI]
    exact mem_singleton _

theorem hardyFamilyIntegral_preserves_concavity {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hsi : Integrable s (volume.restrict (interior (dom f))))
    {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (interior (dom f)) φ)
    (hφsel : SelectionOn f (interior (dom f)) φ) :
    ∃ ψ : ℝ → ℝ,
      ConcaveOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      SelectionOn (hardyFamilyIntegral (interior (dom f)) f)
        (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ := by
  obtain ⟨_, _, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hzero hpositive
  have hφi : Integrable φ (volume.restrict (interior (dom f))) := hsi.congr
    (decreasing_selections_ae_eq hf.1 hs hφsel volume isOpen_interior.measurableSet)
  obtain ⟨_, hd, _, hv, _⟩ := hardyFamilyIntegral_of_integrable hf hzero hpositive hφsel hφi
  have hi (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable φ volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
      (IntegrableOn.mono_set hφi (hprefix p hp))
  refine ⟨hardyScalar φ, ?_, ?_⟩
  · rw [hd]
    exact hardyScalar_concaveOn_initial hφ hpos hscale hi
  · intro p hp
    have hpI : p ∈ interior (dom f) := by simpa only [hd] using hp
    rw [hv p hpI]
    exact mem_singleton _


/-- The local construction using a smaller completed restriction has exactly
the same Hardy fibers wherever that restriction is used. -/
theorem hardyFamilyIntegral_restriction_compatible {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {b : ℝ} (hb : b ∈ interior (dom f)) :
    ∀ p ∈ Ioo (0 : ℝ) b,
      hardyFamilyIntegral (Ioo 0 b) (completedDecreasingRestriction (Ioo 0 b) f) p =
        hardyFamilyIntegral (interior (dom f)) f p := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hzero hpositive
  let Ib := Ioo (0 : ℝ) b
  let C := completedDecreasingRestriction Ib f
  change ∀ p ∈ Ib, hardyFamilyIntegral Ib C p = hardyFamilyIntegral (interior (dom f)) f p
  have hneIb : Ib.Nonempty := nonempty_Ioo.mpr (hpos b hb)
  have hdIb : Ib ⊆ dom f := fun p hp => interior_subset (hprefix b hb hp)
  have hC : MaximalDecreasing C :=
    completedDecreasingRestriction_maximal hf ordConnected_Ioo hneIb hdIb
  have hCI : interior (dom C) = Ib :=
    (completedDecreasingRestriction_domain hf isOpen_Ioo ordConnected_Ioo hneIb hdIb).1
  have hdC : Ib ⊆ interior (dom C) := by
    intro p hp
    simpa only [hCI] using hp
  have hsC : SelectionOn C Ib s := by
    intro p hp
    change s p ∈ completedDecreasingRestriction Ib f p
    rw [completedDecreasingRestriction_value hf isOpen_Ioo hdIb hp]
    exact hs p (hprefix b hb hp)
  have hscaleIb : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ Ib, c*p ∈ Ib := by
    intro c hc p hp
    refine ⟨mul_pos hc.1 hp.1, ?_⟩
    exact (show c*p ≤ p from by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc.2 hp.1.le).trans_lt hp.2
  have hlocal := hardyFamilyIntegral_well_defined hC isOpen_Ioo ordConnected_Ioo hneIb hdC
    (fun p hp => hp.1) hscaleIb hsC (fun p hp => hi p (hprefix b hb hp))
  have hglobal := hardyFamilyIntegral_well_defined hf isOpen_interior hord hne Subset.rfl
    hpos hscale hs hi
  intro p hp
  rw [hlocal.2.2.2.1 p hp, hglobal.2.2.2.1 p (hprefix b hb hp)]

theorem hardyFamilyIntegral_local_independence {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {p b₁ b₂ : ℝ} (hb₁ : b₁ ∈ interior (dom f)) (hb₂ : b₂ ∈ interior (dom f))
    (hp₁ : p ∈ Ioo 0 b₁) (hp₂ : p ∈ Ioo 0 b₂) :
    hardyFamilyIntegral (Ioo 0 b₁) (completedDecreasingRestriction (Ioo 0 b₁) f) p =
      hardyFamilyIntegral (Ioo 0 b₂) (completedDecreasingRestriction (Ioo 0 b₂) f) p :=
  (hardyFamilyIntegral_restriction_compatible hf hzero hpositive hs hi hb₁ p hp₁).trans
    (hardyFamilyIntegral_restriction_compatible hf hzero hpositive hs hi hb₂ p hp₂).symm

end ScalarMonotone.EndOfPaper
end
