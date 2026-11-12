import EndOfPaper.ScalarIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Interior endpoints and one-sided convergence for family integration

The real infimum and supremum below are used only at interior domain points,
where their membership and boundedness are proved. They retain both ends of a
jump. No atomlessness assumption is made on the family parameter measure.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem maximal_interior_fiber_bounded {f : Operator} (hf : MaximalIncreasing f)
    {x : ℝ} (hx : x ∈ interior (dom f)) : BddBelow (f x) ∧ BddAbove (f x) := by
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hx)
  obtain ⟨y, hay, hyx⟩ := exists_between hax
  obtain ⟨z, hxz, hzb⟩ := exists_between hxb
  obtain ⟨v, hv⟩ := interior_subset (hab ⟨hay, hyx.trans hxb⟩)
  obtain ⟨w, hw⟩ := interior_subset (hab ⟨hax.trans hxz, hzb⟩)
  exact ⟨⟨v, fun _ hu => hf.1.le_of_lt hv hu hyx⟩,
    ⟨w, fun _ hu => hf.1.le_of_lt hu hw hxz⟩⟩

theorem maximal_interior_fiber_endpoints_mem {f : Operator} (hf : MaximalIncreasing f)
    {x : ℝ} (hx : x ∈ interior (dom f)) :
    sInf (f x) ∈ f x ∧ sSup (f x) ∈ f x := by
  have hn : (f x).Nonempty := (show x ∈ dom f from interior_subset hx)
  have hb := maximal_interior_fiber_bounded hf hx
  exact ⟨(maximal_fiber_closed hf x).csInf_mem hn hb.1,
    (maximal_fiber_closed hf x).csSup_mem hn hb.2⟩

theorem maximal_interior_fiber_eq_Icc {f : Operator} (hf : MaximalIncreasing f)
    {x : ℝ} (hx : x ∈ interior (dom f)) : f x = Icc (sInf (f x)) (sSup (f x)) := by
  have hb := maximal_interior_fiber_bounded hf hx
  have he := maximal_interior_fiber_endpoints_mem hf hx
  ext v
  exact ⟨fun hv => ⟨csInf_le hb.1 hv, le_csSup hb.2 hv⟩,
    fun hv => (maximal_fiber_ordConnected hf x).out he.1 he.2 hv⟩

/-- Every selection tends to the lower endpoint from the left, including at jumps. -/
theorem selection_tendsto_left {f : Operator} (hf : MaximalIncreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) {x : ℝ} (hx : x ∈ I) :
    Tendsto s (𝓝[<] x) (𝓝 (sInf (f x))) := by
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hx)
  have hsub : Ioo a x ⊆ I := fun _ hy => hab ⟨hy.1, hy.2.trans hxb⟩
  have hn : (s '' Ioo a x).Nonempty := (nonempty_Ioo.mpr hax).image s
  have hb : BddAbove (s '' Ioo a x) := by
    refine ⟨s x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hf.1.le_of_lt (hs y (hsub hy)) (hs x hx) hy.2
  have hlim := MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hax)
    ((selection_monotoneOn hf.1 hs).mono hsub) hb
  have hp : Tendsto (fun y => (y, s y)) (𝓝[<] x)
      (𝓝 (x, sSup (s '' Ioo a x))) :=
    (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds hlim
  have hmem : sSup (s '' Ioo a x) ∈ f x := (graph_closed hf).mem_of_tendsto hp (by
    filter_upwards [Ioo_mem_nhdsLT hax] with y hy
    exact hs y (hsub hy))
  have hxi : x ∈ interior (dom f) := hI.subset_interior_iff.mpr hdom hx
  have hfb := maximal_interior_fiber_bounded hf hxi
  have hem := (maximal_interior_fiber_endpoints_mem hf hxi).1
  have heq : sSup (s '' Ioo a x) = sInf (f x) := by
    apply le_antisymm
    · apply csSup_le hn
      rintro _ ⟨y, hy, rfl⟩
      exact hf.1.le_of_lt (hs y (hsub hy)) hem hy.2
    · exact csInf_le hfb.1 hmem
  simpa only [heq] using hlim

/-- Every selection tends to the upper endpoint from the right. -/
theorem selection_tendsto_right {f : Operator} (hf : MaximalIncreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) {x : ℝ} (hx : x ∈ I) :
    Tendsto s (𝓝[>] x) (𝓝 (sSup (f x))) := by
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hx)
  have hsub : Ioo x b ⊆ I := fun _ hy => hab ⟨hax.trans hy.1, hy.2⟩
  have hn : (s '' Ioo x b).Nonempty := (nonempty_Ioo.mpr hxb).image s
  have hb : BddBelow (s '' Ioo x b) := by
    refine ⟨s x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hf.1.le_of_lt (hs x hx) (hs y (hsub hy)) hy.1
  have hlim := MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hxb)
    ((selection_monotoneOn hf.1 hs).mono hsub) hb
  have hp : Tendsto (fun y => (y, s y)) (𝓝[>] x)
      (𝓝 (x, sInf (s '' Ioo x b))) :=
    (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds hlim
  have hmem : sInf (s '' Ioo x b) ∈ f x := (graph_closed hf).mem_of_tendsto hp (by
    filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
    exact hs y (hsub hy))
  have hxi : x ∈ interior (dom f) := hI.subset_interior_iff.mpr hdom hx
  have hfb := maximal_interior_fiber_bounded hf hxi
  have hem := (maximal_interior_fiber_endpoints_mem hf hxi).2
  have heq : sInf (s '' Ioo x b) = sSup (f x) := by
    apply le_antisymm
    · exact le_csSup hfb.2 hmem
    · apply le_csInf hn
      rintro _ ⟨y, hy, rfl⟩
      exact hf.1.le_of_lt hem (hs y (hsub hy)) hy.1
  simpa only [heq] using hlim

/-- The local integrable domination in the manuscript's family-integral proof. -/
theorem interior_fiber_abs_bound {f : Operator} (hf : MaximalIncreasing f)
    {a b y v : ℝ} (ha : a ∈ interior (dom f)) (hb : b ∈ interior (dom f))
    (hy : y ∈ Ioo a b) (hv : v ∈ f y) :
    |v| ≤ |sInf (f a)| + |sSup (f b)| := by
  have hlo := hf.1.le_of_lt (maximal_interior_fiber_endpoints_mem hf ha).1 hv hy.1
  have hhi := hf.1.le_of_lt hv (maximal_interior_fiber_endpoints_mem hf hb).2 hy.2
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (sInf (f a)), abs_nonneg (sSup (f b))]
  · linarith [le_abs_self (sSup (f b)), abs_nonneg (sInf (f a))]

/-- Dominated convergence preserves both one-sided endpoint identities.
The parameter measure can have atoms; integrability is exactly pointwise in x. -/
theorem family_integral_endpoint_limits {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {x : ℝ} (hx : x ∈ I) :
    Tendsto (fun y => ∫ θ, sSup (f θ y) ∂μ) (𝓝[<] x)
      (𝓝 (∫ θ, sInf (f θ x) ∂μ)) ∧
    Tendsto (fun y => ∫ θ, sInf (f θ y) ∂μ) (𝓝[>] x)
      (𝓝 (∫ θ, sSup (f θ x) ∂μ)) := by
  have hinside (θ) {y} (hy : y ∈ I) : y ∈ interior (dom (f θ)) :=
    hI.subset_interior_iff.mpr (hdom θ) hy
  obtain ⟨a₀, b₀, ⟨hax₀, hxb₀⟩, hab₀⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hx)
  obtain ⟨a, ha₀, hax⟩ := exists_between hax₀
  obtain ⟨b, hxb, hb₀⟩ := exists_between hxb₀
  have haI : a ∈ I := hab₀ ⟨ha₀, hax.trans hxb₀⟩
  have hbI : b ∈ I := hab₀ ⟨hax₀.trans hxb, hb₀⟩
  have hab : Ioo a b ⊆ I := fun _ hy => hab₀ ⟨ha₀.trans hy.1, hy.2.trans hb₀⟩
  let bound : Θ → ℝ := fun θ => |sInf (f θ a)| + |sSup (f θ b)|
  have hbound : Integrable bound μ := (hl a haI).abs.add (hu b hbI).abs
  have hlowSel (θ) : SelectionOn (f θ) I (fun y => sInf (f θ y)) :=
    fun y hy => (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hy)).1
  have huppSel (θ) : SelectionOn (f θ) I (fun y => sSup (f θ y)) :=
    fun y hy => (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hy)).2
  constructor
  · apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [Ioo_mem_nhdsLT hax] with y hy
      exact (hu y (hab ⟨hy.1, hy.2.trans hxb⟩)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsLT hax] with y hy
      exact Eventually.of_forall (fun θ => by
        rw [Real.norm_eq_abs]
        exact interior_fiber_abs_bound (hf θ) (hinside θ haI) (hinside θ hbI)
          ⟨hy.1, hy.2.trans hxb⟩ (huppSel θ y (hab ⟨hy.1, hy.2.trans hxb⟩)))
    · exact hbound
    · exact Eventually.of_forall (fun θ => selection_tendsto_left (hf θ) hI
        (hdom θ) (huppSel θ) hx)
  · apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
      exact (hl y (hab ⟨hax.trans hy.1, hy.2⟩)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
      exact Eventually.of_forall (fun θ => by
        rw [Real.norm_eq_abs]
        exact interior_fiber_abs_bound (hf θ) (hinside θ haI) (hinside θ hbI)
          ⟨hax.trans hy.1, hy.2⟩ (hlowSel θ y (hab ⟨hax.trans hy.1, hy.2⟩)))
    · exact hbound
    · exact Eventually.of_forall (fun θ => selection_tendsto_right (hf θ) hI
        (hdom θ) (hlowSel θ) hx)

/-- The paper's increasing family integral: Aumann interior fibers, then completion. -/
def increasingFamilyIntegral {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) (f : Θ → Operator) : Operator :=
  completion I (integratedFiberGraph μ I
    (fun θ x => sInf (f θ x)) (fun θ x => sSup (f θ x)))

/-- Maximal completion preserves the full Aumann interval at every interior point.
This includes jump fibers, arbitrary parameter measures, and unbounded domains. -/
theorem increasingFamilyIntegral_value {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {x : ℝ} (hx : x ∈ I) :
    increasingFamilyIntegral μ I f x =
      Icc (∫ θ, sInf (f θ x) ∂μ) (∫ θ, sSup (f θ x) ∂μ) := by
  have hinside (θ) {y} (hy : y ∈ I) : y ∈ interior (dom (f θ)) :=
    hI.subset_interior_iff.mpr (hdom θ) hy
  have hle (y) (hy : y ∈ I) : ∀ᵐ θ ∂μ, sInf (f θ y) ≤ sSup (f θ y) :=
    Eventually.of_forall (fun θ => csInf_le
      (maximal_interior_fiber_bounded (hf θ) (hinside θ hy)).1
      (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hy)).2)
  have hsep (y) (hy : y ∈ I) (z) (hz : z ∈ I) (hyz : y < z) :
      ∀ᵐ θ ∂μ, sSup (f θ y) ≤ sInf (f θ z) :=
    Eventually.of_forall (fun θ => (hf θ).1.le_of_lt
      (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hy)).2
      (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hz)).1 hyz)
  let G := integratedFiberGraph μ I (fun θ y => sInf (f θ y)) (fun θ y => sSup (f θ y))
  have hG : Increasing G := integratedFiberGraph_increasing μ I _ _ hl hu hsep
  have hGdom : dom G = I := integratedFiberGraph_dom μ I _ _ hl hu hle
  have hends (y) (hy : y ∈ I) :
      (∫ θ, sInf (f θ y) ∂μ) ∈ G y ∧ (∫ θ, sSup (f θ y) ∂μ) ∈ G y := by
    have hab := integral_mono_ae (hl y hy) (hu y hy) (hle y hy)
    simpa only [G, integratedFiberGraph, if_pos hy, mem_Icc] using
      (show ((∫ θ, sInf (f θ y) ∂μ) ≤ (∫ θ, sInf (f θ y) ∂μ) ∧
        (∫ θ, sInf (f θ y) ∂μ) ≤ (∫ θ, sSup (f θ y) ∂μ)) ∧
        ((∫ θ, sInf (f θ y) ∂μ) ≤ (∫ θ, sSup (f θ y) ∂μ) ∧
        (∫ θ, sSup (f θ y) ∂μ) ≤ (∫ θ, sSup (f θ y) ∂μ)) from
        ⟨⟨le_rfl, hab⟩, ⟨hab, le_rfl⟩⟩)
  have hlim := family_integral_endpoint_limits μ hf hI hdom hl hu hx
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hx)
  ext v
  constructor
  · intro hv
    have hc : Compatible G x v := hv.2
    have hb := compatible_iff_bounds.mp hc
    constructor
    · apply le_of_tendsto hlim.1
      filter_upwards [Ioo_mem_nhdsLT hax] with y hy
      exact hb.1 (hends y (hab ⟨hy.1, hy.2.trans hxb⟩)).2 hy.2
    · apply ge_of_tendsto hlim.2
      filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
      exact hb.2 (hends y (hab ⟨hax.trans hy.1, hy.2⟩)).1 hy.1
  · intro hv
    apply le_completion hG hGdom x
    simpa only [G, integratedFiberGraph, if_pos hx] using hv

/-- Exact Aumann identification on the common interior, with all selections. -/
theorem increasingFamilyIntegral_aumann {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {x : ℝ} (hx : x ∈ I) :
    increasingFamilyIntegral μ I f x = aumannIntegral μ (fun θ => f θ x) := by
  have heq : (fun θ => f θ x) =
      (fun θ => Icc (sInf (f θ x)) (sSup (f θ x))) := by
    funext θ
    exact maximal_interior_fiber_eq_Icc (hf θ) (hI.subset_interior_iff.mpr (hdom θ) hx)
  rw [increasingFamilyIntegral_value μ hf hI hdom hl hu hx, heq,
    aumannIntegral_interval, aumannInterval_eq μ (hl x hx) (hu x hx)]
  exact Eventually.of_forall (fun θ => csInf_le
    (maximal_interior_fiber_bounded (hf θ) (hI.subset_interior_iff.mpr (hdom θ) hx)).1
    (maximal_interior_fiber_endpoints_mem (hf θ)
      (hI.subset_interior_iff.mpr (hdom θ) hx)).2)

/-- The increasing family integral is the unique maximal operator with the
prescribed full interior fibers and domain contained in the common closure. -/
theorem increasingFamilyIntegral_unique {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ) :
    MaximalIncreasing (increasingFamilyIntegral μ I f) ∧
      dom (increasingFamilyIntegral μ I f) ⊆ closure I ∧
      ∀ g : Operator, MaximalIncreasing g → dom g ⊆ closure I →
        (∀ x ∈ I, g x = aumannIntegral μ (fun θ => f θ x)) →
        g = increasingFamilyIntegral μ I f := by
  have hinside (θ) {x} (hx : x ∈ I) : x ∈ interior (dom (f θ)) :=
    hI.subset_interior_iff.mpr (hdom θ) hx
  have hle (x) (hx : x ∈ I) : ∀ᵐ θ ∂μ, sInf (f θ x) ≤ sSup (f θ x) :=
    Eventually.of_forall (fun θ => csInf_le
      (maximal_interior_fiber_bounded (hf θ) (hinside θ hx)).1
      (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hx)).2)
  have hsep (x) (hx : x ∈ I) (y) (hy : y ∈ I) (hxy : x < y) :
      ∀ᵐ θ ∂μ, sSup (f θ x) ≤ sInf (f θ y) :=
    Eventually.of_forall (fun θ => (hf θ).1.le_of_lt
      (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hx)).2
      (maximal_interior_fiber_endpoints_mem (hf θ) (hinside θ hy)).1 hxy)
  have hG := integratedFiberGraph_increasing μ I _ _ hl hu hsep
  have hGdom := integratedFiberGraph_dom μ I _ _ hl hu hle
  have hmax : MaximalIncreasing (increasingFamilyIntegral μ I f) :=
    completion_maximal hord hne hG hGdom
  refine ⟨hmax, completion_dom_subset I _, ?_⟩
  intro g hg hgd hvals
  apply hg.eq_of_le hmax.1
  intro x v hv
  refine ⟨hgd ⟨v, hv⟩, ?_⟩
  intro y w hw
  have hy : y ∈ I := by
    by_contra hy
    simpa [integratedFiberGraph, hy] using hw
  have hw' : w ∈ g y := by
    rw [hvals y hy, ← increasingFamilyIntegral_aumann μ hf hI hdom hl hu hy,
      increasingFamilyIntegral_value μ hf hI hdom hl hu hy]
    simpa only [integratedFiberGraph, if_pos hy] using hw
  exact hg.1 hv hw'

/-- Negation exchanges the two finite interior endpoints of a decreasing graph. -/
theorem decreasing_interior_neg_endpoints {f : Operator} (hf : MaximalDecreasing f)
    {x : ℝ} (hx : x ∈ interior (dom f)) :
    sInf (negOut f x) = -sSup (f x) ∧ sSup (negOut f x) = -sInf (f x) := by
  have hxi : x ∈ interior (dom (negOut f)) := by simpa only [dom_negOut] using hx
  have he := maximal_interior_fiber_endpoints_mem hf hxi
  have hb := maximal_interior_fiber_bounded hf hxi
  have hn : (f x).Nonempty := (show x ∈ dom f from interior_subset hx)
  have hlo' (v) (hv : v ∈ f x) : -sSup (negOut f x) ≤ v := by
    have hv' : -v ∈ negOut f x := by simpa only [negOut, mem_setOf_eq, neg_neg] using hv
    have := le_csSup hb.2 hv'
    linarith
  have hhi' (v) (hv : v ∈ f x) : v ≤ -sInf (negOut f x) := by
    have hv' : -v ∈ negOut f x := by simpa only [negOut, mem_setOf_eq, neg_neg] using hv
    have := csInf_le hb.1 hv'
    linarith
  have hlo : BddBelow (f x) := ⟨_, hlo'⟩
  have hhi : BddAbove (f x) := ⟨_, hhi'⟩
  have hsup : sSup (f x) = -sInf (negOut f x) :=
    le_antisymm (csSup_le hn hhi') (le_csSup hhi he.1)
  have hinf : sInf (f x) = -sSup (negOut f x) :=
    le_antisymm (csInf_le hlo he.2) (le_csInf hn hlo')
  constructor <;> linarith

theorem aumannIntegral_neg {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (h : Θ → Set ℝ) :
    aumannIntegral μ (fun θ => {v | -v ∈ h θ}) =
      {v | -v ∈ aumannIntegral μ h} := by
  ext v
  constructor
  · rintro ⟨s, hs, hsel, hv⟩
    refine ⟨fun θ => -s θ, hs.neg, hsel, ?_⟩
    simpa only [integral_neg] using congrArg Neg.neg hv
  · rintro ⟨s, hs, hsel, hv⟩
    refine ⟨fun θ => -s θ, hs.neg, ?_, ?_⟩
    · filter_upwards [hsel] with θ hθ
      simpa only [mem_setOf_eq, neg_neg] using hθ
    · rw [integral_neg, ← hv, neg_neg]

/-- Decreasing family integration is the orientation reversal of the increasing construction. -/
def decreasingFamilyIntegral {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (I : Set ℝ) (f : Θ → Operator) : Operator :=
  negOut (increasingFamilyIntegral μ I (fun θ => negOut (f θ)))

theorem decreasingFamilyIntegral_value {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalDecreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {x : ℝ} (hx : x ∈ I) :
    decreasingFamilyIntegral μ I f x =
      Icc (∫ θ, sInf (f θ x) ∂μ) (∫ θ, sSup (f θ x) ∂μ) := by
  have hndom (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdom θ
  have he (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdom θ) hy)
  have hnl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).1] using (hu y hy).neg
  have hnu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).2] using (hl y hy).neg
  have hval := increasingFamilyIntegral_value μ hf hI hndom hnl hnu hx
  ext v
  change -v ∈ increasingFamilyIntegral μ I (fun θ => negOut (f θ)) x ↔ _
  rw [hval]
  simp only [fun θ => (he θ hx).1, fun θ => (he θ hx).2, integral_neg, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem decreasingFamilyIntegral_aumann {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalDecreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {x : ℝ} (hx : x ∈ I) :
    decreasingFamilyIntegral μ I f x = aumannIntegral μ (fun θ => f θ x) := by
  have hndom (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdom θ
  have he (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdom θ) hy)
  have hnl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).1] using (hu y hy).neg
  have hnu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).2] using (hl y hy).neg
  have hval := increasingFamilyIntegral_aumann μ hf hI hndom hnl hnu hx
  ext v
  change -v ∈ increasingFamilyIntegral μ I (fun θ => negOut (f θ)) x ↔ _
  rw [hval]
  change -v ∈ aumannIntegral μ (fun θ => {w | -w ∈ f θ x}) ↔ _
  rw [aumannIntegral_neg]
  simp only [mem_setOf_eq, neg_neg]

theorem decreasingFamilyIntegral_unique {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalDecreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ) :
    MaximalDecreasing (decreasingFamilyIntegral μ I f) ∧
      dom (decreasingFamilyIntegral μ I f) ⊆ closure I ∧
      ∀ g : Operator, MaximalDecreasing g → dom g ⊆ closure I →
        (∀ x ∈ I, g x = aumannIntegral μ (fun θ => f θ x)) →
        g = decreasingFamilyIntegral μ I f := by
  have hndom (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdom θ
  have he (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdom θ) hy)
  have hnl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).1] using (hu y hy).neg
  have hnu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).2] using (hl y hy).neg
  obtain ⟨hmax, hd, huniq⟩ := increasingFamilyIntegral_unique μ hf hI hord hne hndom hnl hnu
  refine ⟨?_, ?_, ?_⟩
  · change MaximalIncreasing (negOut (negOut (increasingFamilyIntegral μ I
      (fun θ => negOut (f θ)))))
    simpa only [negOut_negOut] using hmax
  · simpa only [decreasingFamilyIntegral, dom_negOut] using hd
  · intro g hg hgd hvals
    have heq := huniq (negOut g) hg (by simpa only [dom_negOut] using hgd) (by
      intro x hx
      ext v
      change -v ∈ g x ↔ v ∈ aumannIntegral μ (fun θ => {w | -w ∈ f θ x})
      rw [hvals x hx, aumannIntegral_neg]
      rfl)
    simpa only [negOut_negOut, decreasingFamilyIntegral] using congrArg negOut heq

theorem increasingFamilyIntegral_endpoints_mem {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {x : ℝ} (hx : x ∈ I) :
    (∫ θ, sInf (f θ x) ∂μ) ∈ increasingFamilyIntegral μ I f x ∧
      (∫ θ, sSup (f θ x) ∂μ) ∈ increasingFamilyIntegral μ I f x := by
  have hle : (∫ θ, sInf (f θ x) ∂μ) ≤ ∫ θ, sSup (f θ x) ∂μ := by
    apply integral_mono_ae (hl x hx) (hu x hx)
    exact Eventually.of_forall (fun θ => csInf_le
      (maximal_interior_fiber_bounded (hf θ) (hI.subset_interior_iff.mpr (hdom θ) hx)).1
      (maximal_interior_fiber_endpoints_mem (hf θ)
        (hI.subset_interior_iff.mpr (hdom θ) hx)).2)
  rw [increasingFamilyIntegral_value μ hf hI hdom hl hu hx]
  exact ⟨⟨le_rfl, hle⟩, ⟨hle, le_rfl⟩⟩

/-- Integration preserves the resolvent order on the entire completed graphs,
including boundary fibers. This is separated-graph comparison, not inclusion. -/
theorem increasingFamilyIntegral_mono {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f g : Θ → Operator}
    (hf : ∀ θ, MaximalIncreasing (f θ)) (hg : ∀ θ, MaximalIncreasing (g θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdf : ∀ θ, I ⊆ dom (f θ)) (hdg : ∀ θ, I ⊆ dom (g θ))
    (hfl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hfu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    (hgl : ∀ x ∈ I, Integrable (fun θ => sInf (g θ x)) μ)
    (hgu : ∀ x ∈ I, Integrable (fun θ => sSup (g θ x)) μ)
    (hfg : ∀ θ, IncLE (f θ) (g θ)) :
    IncLE (increasingFamilyIntegral μ I f) (increasingFamilyIntegral μ I g) := by
  obtain ⟨hfm, hfd, _⟩ := increasingFamilyIntegral_unique μ hf hI hord hne hdf hfl hfu
  obtain ⟨hgm, hgd, _⟩ := increasingFamilyIntegral_unique μ hg hI hord hne hdg hgl hgu
  intro x u y v hux hvy hxy
  have hx : x ∈ closure I := hfd ⟨u, hux⟩
  have hy : y ∈ closure I := hgd ⟨v, hvy⟩
  obtain ⟨a, hxa, hay⟩ := exists_between hxy
  obtain ⟨b, hab, hby⟩ := exists_between hay
  have haI : a ∈ I := between_closure_mem hord hx hy hxa hay
  have hbI : b ∈ I := between_closure_mem hord hx hy (hxa.trans hab) hby
  have hfa := (increasingFamilyIntegral_endpoints_mem μ hf hI hdf hfl hfu haI).2
  have hgb := (increasingFamilyIntegral_endpoints_mem μ hg hI hdg hgl hgu hbI).1
  have hmid : (∫ θ, sSup (f θ a) ∂μ) ≤ ∫ θ, sInf (g θ b) ∂μ := by
    apply integral_mono_ae (hfu a haI) (hgl b hbI)
    exact Eventually.of_forall (fun θ => hfg θ
      (maximal_interior_fiber_endpoints_mem (hf θ)
        (hI.subset_interior_iff.mpr (hdf θ) haI)).2
      (maximal_interior_fiber_endpoints_mem (hg θ)
        (hI.subset_interior_iff.mpr (hdg θ) hbI)).1 hab)
  exact (hfm.1.le_of_lt hux hfa hxa).trans (hmid.trans (hgm.1.le_of_lt hgb hvy hby))

/-- For an open interval, interior coverage and closure containment determine
the domain interior. Boundary points need not belong to the domain. -/
theorem domain_interior_of_open_interval {g : Operator} {I : Set ℝ}
    (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hsub : I ⊆ dom g) (hcl : dom g ⊆ closure I) : interior (dom g) = I := by
  have hconv : Convex ℝ I := hord.convex
  have hnint : (interior I).Nonempty := by simpa only [hI.interior_eq] using hne
  have heq : interior (closure I) = I := by
    simpa only [hI.interior_eq] using hconv.interior_closure_eq_interior_of_nonempty_interior hnint
  exact subset_antisymm ((interior_mono hcl).trans (by rw [heq]))
    (hI.subset_interior_iff.mpr hsub)

theorem increasingFamilyIntegral_domain_interior {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ) :
    interior (dom (increasingFamilyIntegral μ I f)) = I :=
  domain_interior_of_open_interval hI hord hne
    (fun x hx => ⟨_, (increasingFamilyIntegral_endpoints_mem μ hf hI hdom hl hu hx).1⟩)
    (completion_dom_subset I _)

theorem decreasingFamilyIntegral_mono {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f g : Θ → Operator}
    (hf : ∀ θ, MaximalDecreasing (f θ)) (hg : ∀ θ, MaximalDecreasing (g θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdf : ∀ θ, I ⊆ dom (f θ)) (hdg : ∀ θ, I ⊆ dom (g θ))
    (hfl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hfu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    (hgl : ∀ x ∈ I, Integrable (fun θ => sInf (g θ x)) μ)
    (hgu : ∀ x ∈ I, Integrable (fun θ => sSup (g θ x)) μ)
    (hfg : ∀ θ, DecLE (f θ) (g θ)) :
    DecLE (decreasingFamilyIntegral μ I f) (decreasingFamilyIntegral μ I g) := by
  have hndf (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdf θ
  have hndg (θ) : I ⊆ dom (negOut (g θ)) := by simpa only [dom_negOut] using hdg θ
  have hef (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdf θ) hy)
  have heg (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hg θ)
    (hI.subset_interior_iff.mpr (hdg θ) hy)
  have hnfl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (hef θ hy).1] using (hfu y hy).neg
  have hnfu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (hef θ hy).2] using (hfl y hy).neg
  have hngl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (g θ) y)) μ := by
    simpa only [fun θ => (heg θ hy).1] using (hgu y hy).neg
  have hngu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (g θ) y)) μ := by
    simpa only [fun θ => (heg θ hy).2] using (hgl y hy).neg
  rw [decLE_iff_negOut]
  simpa only [decreasingFamilyIntegral, negOut_negOut] using
    increasingFamilyIntegral_mono μ hg hf hI hord hne hndg hndf hngl hngu hnfl hnfu
      (fun θ => decLE_iff_negOut.mp (hfg θ))

theorem interior_endpoints_add {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g) {x : ℝ}
    (hxf : x ∈ interior (dom f)) (hxg : x ∈ interior (dom g)) :
    sInf (add f g x) = sInf (f x) + sInf (g x) ∧
      sSup (add f g x) = sSup (f x) + sSup (g x) := by
  have hbf := maximal_interior_fiber_bounded hf hxf
  have hbg := maximal_interior_fiber_bounded hg hxg
  have hef := maximal_interior_fiber_endpoints_mem hf hxf
  have heg := maximal_interior_fiber_endpoints_mem hg hxg
  constructor
  · apply IsLeast.csInf_eq
    refine ⟨⟨_, hef.1, _, heg.1, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact add_le_add (csInf_le hbf.1 hu) (csInf_le hbg.1 hv)
  · apply IsGreatest.csSup_eq
    refine ⟨⟨_, hef.2, _, heg.2, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact add_le_add (le_csSup hbf.2 hu) (le_csSup hbg.2 hv)

theorem setAdd_Icc_real {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    setAdd (Icc a b) (Icc c d) = Icc (a+c) (b+d) := by
  ext v
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨add_le_add hs.1 ht.1, add_le_add hs.2 ht.2⟩
  · intro hv
    let s := max a (v-d)
    have hs : s ∈ Icc a b := ⟨le_max_left _ _, max_le hab (by linarith [hv.2])⟩
    have hsc : s ≤ v-c := max_le (by linarith [hv.1]) (by linarith)
    refine ⟨s, hs, v-s, ⟨by linarith, ?_⟩, by ring⟩
    have := le_max_right a (v-d)
    change v-d ≤ s at this
    linarith

/-- Additivity as equality of completed operators, with boundary fibers. -/
theorem increasingFamilyIntegral_add {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f g : Θ → Operator}
    (hf : ∀ θ, MaximalIncreasing (f θ)) (hg : ∀ θ, MaximalIncreasing (g θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdf : ∀ θ, I ⊆ dom (f θ)) (hdg : ∀ θ, I ⊆ dom (g θ))
    (hfl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hfu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    (hgl : ∀ x ∈ I, Integrable (fun θ => sInf (g θ x)) μ)
    (hgu : ∀ x ∈ I, Integrable (fun θ => sSup (g θ x)) μ) :
    increasingFamilyIntegral μ I (fun θ => add (f θ) (g θ)) =
      add (increasingFamilyIntegral μ I f) (increasingFamilyIntegral μ I g) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hsmax (θ) : MaximalIncreasing (add (f θ) (g θ)) :=
    add_maximal (hf θ) (hg θ) ⟨x₀, hdf θ hx₀, hdg θ hx₀⟩
  have hsdom (θ) : I ⊆ dom (add (f θ) (g θ)) := by
    rw [dom_add]
    exact fun _ hx => ⟨hdf θ hx, hdg θ hx⟩
  have he (θ) {x} (hx : x ∈ I) := interior_endpoints_add (hf θ) (hg θ)
    (hI.subset_interior_iff.mpr (hdf θ) hx) (hI.subset_interior_iff.mpr (hdg θ) hx)
  have hsl (x) (hx : x ∈ I) : Integrable (fun θ => sInf (add (f θ) (g θ) x)) μ := by
    simpa only [fun θ => (he θ hx).1] using (hfl x hx).add (hgl x hx)
  have hsu (x) (hx : x ∈ I) : Integrable (fun θ => sSup (add (f θ) (g θ) x)) μ := by
    simpa only [fun θ => (he θ hx).2] using (hfu x hx).add (hgu x hx)
  obtain ⟨hfm, hfd, _⟩ := increasingFamilyIntegral_unique μ hf hI hord ⟨x₀, hx₀⟩ hdf hfl hfu
  obtain ⟨hgm, hgd, _⟩ := increasingFamilyIntegral_unique μ hg hI hord ⟨x₀, hx₀⟩ hdg hgl hgu
  have hfsub : I ⊆ dom (increasingFamilyIntegral μ I f) :=
    fun x hx => ⟨_, (increasingFamilyIntegral_endpoints_mem μ hf hI hdf hfl hfu hx).1⟩
  have hgsub : I ⊆ dom (increasingFamilyIntegral μ I g) :=
    fun x hx => ⟨_, (increasingFamilyIntegral_endpoints_mem μ hg hI hdg hgl hgu hx).1⟩
  apply Eq.symm
  apply (increasingFamilyIntegral_unique μ hsmax hI hord ⟨x₀, hx₀⟩ hsdom hsl hsu).2.2
  · exact add_maximal hfm hgm ⟨x₀, hfsub hx₀, hgsub hx₀⟩
  · rw [dom_add]
    exact fun x hx => hfd hx.1
  · intro x hx
    rw [← increasingFamilyIntegral_aumann μ hsmax hI hsdom hsl hsu hx,
      increasingFamilyIntegral_value μ hsmax hI hsdom hsl hsu hx]
    change setAdd (increasingFamilyIntegral μ I f x) (increasingFamilyIntegral μ I g x) = _
    rw [increasingFamilyIntegral_value μ hf hI hdf hfl hfu hx,
      increasingFamilyIntegral_value μ hg hI hdg hgl hgu hx]
    have hlef := (increasingFamilyIntegral_endpoints_mem μ hf hI hdf hfl hfu hx).1
    have hleg := (increasingFamilyIntegral_endpoints_mem μ hg hI hdg hgl hgu hx).1
    rw [increasingFamilyIntegral_value μ hf hI hdf hfl hfu hx] at hlef
    rw [increasingFamilyIntegral_value μ hg hI hdg hgl hgu hx] at hleg
    rw [setAdd_Icc_real hlef.2 hleg.2]
    simp only [fun θ => (he θ hx).1, fun θ => (he θ hx).2,
      integral_add (hfl x hx) (hgl x hx), integral_add (hfu x hx) (hgu x hx)]

theorem interior_endpoints_outputScale {f : Operator} (hf : MaximalIncreasing f)
    {c x : ℝ} (hc : 0 ≤ c) (hx : x ∈ interior (dom f)) :
    sInf (outputScale c f x) = c * sInf (f x) ∧
      sSup (outputScale c f x) = c * sSup (f x) := by
  have hb := maximal_interior_fiber_bounded hf hx
  have he := maximal_interior_fiber_endpoints_mem hf hx
  constructor
  · apply IsLeast.csInf_eq
    refine ⟨⟨_, he.1, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hb.1 hv) hc
  · apply IsGreatest.csSup_eq
    refine ⟨⟨_, he.2, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup hb.2 hv) hc

theorem increasingFamilyIntegral_outputScale {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalIncreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {c : ℝ} (hc : 0 < c) :
    increasingFamilyIntegral μ I (fun θ => outputScale c (f θ)) =
      outputScale c (increasingFamilyIntegral μ I f) := by
  have hsm (θ) := outputScale_maximal hc (hf θ)
  have hsd (θ) : I ⊆ dom (outputScale c (f θ)) := by
    simpa only [dom_outputScale] using hdom θ
  have he (θ) {x} (hx : x ∈ I) := interior_endpoints_outputScale (hf θ) hc.le
    (hI.subset_interior_iff.mpr (hdom θ) hx)
  have hsl (x) (hx : x ∈ I) : Integrable (fun θ => sInf (outputScale c (f θ) x)) μ := by
    simpa only [fun θ => (he θ hx).1] using (hl x hx).const_mul c
  have hsu (x) (hx : x ∈ I) : Integrable (fun θ => sSup (outputScale c (f θ) x)) μ := by
    simpa only [fun θ => (he θ hx).2] using (hu x hx).const_mul c
  obtain ⟨hfm, hfd, _⟩ := increasingFamilyIntegral_unique μ hf hI hord hne hdom hl hu
  apply Eq.symm
  apply (increasingFamilyIntegral_unique μ hsm hI hord hne hsd hsl hsu).2.2
  · exact outputScale_maximal hc hfm
  · simpa only [dom_outputScale] using hfd
  · intro x hx
    rw [← increasingFamilyIntegral_aumann μ hsm hI hsd hsl hsu hx,
      increasingFamilyIntegral_value μ hsm hI hsd hsl hsu hx]
    ext v
    rw [outputScale_mem_iff hc.ne', increasingFamilyIntegral_value μ hf hI hdom hl hu hx]
    simp only [fun θ => (he θ hx).1, fun θ => (he θ hx).2,
      integral_const_mul, mem_Icc, le_div_iff₀ hc, div_le_iff₀ hc, mul_comm]

theorem decreasingFamilyIntegral_add {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f g : Θ → Operator}
    (hf : ∀ θ, MaximalDecreasing (f θ)) (hg : ∀ θ, MaximalDecreasing (g θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdf : ∀ θ, I ⊆ dom (f θ)) (hdg : ∀ θ, I ⊆ dom (g θ))
    (hfl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hfu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    (hgl : ∀ x ∈ I, Integrable (fun θ => sInf (g θ x)) μ)
    (hgu : ∀ x ∈ I, Integrable (fun θ => sSup (g θ x)) μ) :
    decreasingFamilyIntegral μ I (fun θ => add (f θ) (g θ)) =
      add (decreasingFamilyIntegral μ I f) (decreasingFamilyIntegral μ I g) := by
  have hndf (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdf θ
  have hndg (θ) : I ⊆ dom (negOut (g θ)) := by simpa only [dom_negOut] using hdg θ
  have hef (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdf θ) hy)
  have heg (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hg θ)
    (hI.subset_interior_iff.mpr (hdg θ) hy)
  have hnfl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (hef θ hy).1] using (hfu y hy).neg
  have hnfu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (hef θ hy).2] using (hfl y hy).neg
  have hngl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (g θ) y)) μ := by
    simpa only [fun θ => (heg θ hy).1] using (hgu y hy).neg
  have hngu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (g θ) y)) μ := by
    simpa only [fun θ => (heg θ hy).2] using (hgl y hy).neg
  have hneg : (fun θ => negOut (add (f θ) (g θ))) =
      (fun θ => add (negOut (f θ)) (negOut (g θ))) :=
    funext (fun θ => negOut_add (f θ) (g θ))
  simp only [decreasingFamilyIntegral, hneg,
    increasingFamilyIntegral_add μ hf hg hI hord hne hndf hndg hnfl hnfu hngl hngu,
    negOut_add]

theorem decreasingFamilyIntegral_outputScale {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalDecreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ)
    {c : ℝ} (hc : 0 < c) :
    decreasingFamilyIntegral μ I (fun θ => outputScale c (f θ)) =
      outputScale c (decreasingFamilyIntegral μ I f) := by
  have hndom (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdom θ
  have he (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdom θ) hy)
  have hnl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).1] using (hu y hy).neg
  have hnu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).2] using (hl y hy).neg
  have hneg : (fun θ => negOut (outputScale c (f θ))) =
      (fun θ => outputScale c (negOut (f θ))) :=
    funext (fun θ => negOut_outputScale c (f θ))
  simp only [decreasingFamilyIntegral, hneg,
    increasingFamilyIntegral_outputScale μ hf hI hord hne hndom hnl hnu hc,
    negOut_outputScale]

theorem decreasingFamilyIntegral_domain_interior {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) {f : Θ → Operator} (hf : ∀ θ, MaximalDecreasing (f θ))
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hdom : ∀ θ, I ⊆ dom (f θ))
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ) :
    interior (dom (decreasingFamilyIntegral μ I f)) = I := by
  have hndom (θ) : I ⊆ dom (negOut (f θ)) := by simpa only [dom_negOut] using hdom θ
  have he (θ) {y} (hy : y ∈ I) := decreasing_interior_neg_endpoints (hf θ)
    (hI.subset_interior_iff.mpr (hdom θ) hy)
  have hnl (y) (hy : y ∈ I) : Integrable (fun θ => sInf (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).1] using (hu y hy).neg
  have hnu (y) (hy : y ∈ I) : Integrable (fun θ => sSup (negOut (f θ) y)) μ := by
    simpa only [fun θ => (he θ hy).2] using (hl y hy).neg
  simpa only [decreasingFamilyIntegral, dom_negOut] using
    increasingFamilyIntegral_domain_interior μ hf hI hord hne hndom hnl hnu

end ScalarMonotone.EndOfPaper
end
