import EndOfPaper.HardyEndpoints
import EndOfPaper.Superadditive

/-!
Continuous monotone aggregation of maximal decreasing graphs, with
exact full jump intervals, the original common interior, closure containment,
whole-operator uniqueness and the scalar-selection correspondence.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def intervalGraphOn (I : Set ℝ) (l u : ℝ → ℝ) : Operator := by
  classical
  exact fun x => if x ∈ I then Icc (l x) (u x) else ∅

def intervalCompletionI (I : Set ℝ) (l u : ℝ → ℝ) : Operator := completion I (intervalGraphOn I l u)

theorem intervalCompletionI_properties {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) (hne : I.Nonempty) {l u : ℝ → ℝ}
    (hle : ∀ x ∈ I, l x ≤ u x)
    (hsep : ∀ x ∈ I, ∀ y ∈ I, x < y → u x ≤ l y)
    (hlim : ∀ x ∈ I, Tendsto u (𝓝[<] x) (𝓝 (l x)) ∧
      Tendsto l (𝓝[>] x) (𝓝 (u x))) :
    MaximalIncreasing (intervalCompletionI I l u) ∧
      interior (dom (intervalCompletionI I l u)) = I ∧
      dom (intervalCompletionI I l u) ⊆ closure I ∧
      (∀ x ∈ I, intervalCompletionI I l u x = Icc (l x) (u x)) ∧
      ∀ g : Operator, MaximalIncreasing g → dom g ⊆ closure I →
        (∀ x ∈ I, g x = Icc (l x) (u x)) → g = intervalCompletionI I l u := by
  let G := intervalGraphOn I l u
  have hG : Increasing G := by
    apply increasing_iff_order.mpr
    intro x v y w hv hw hxy
    have hx : x ∈ I := by
      by_contra hx
      simpa [G, intervalGraphOn, hx] using hv
    have hy : y ∈ I := by
      by_contra hy
      simpa [G, intervalGraphOn, hy] using hw
    have hv' : v ∈ Icc (l x) (u x) := by simpa only [G, intervalGraphOn, if_pos hx] using hv
    have hw' : w ∈ Icc (l y) (u y) := by simpa only [G, intervalGraphOn, if_pos hy] using hw
    exact hv'.2.trans ((hsep x hx y hy hxy).trans hw'.1)
  have hGdom : dom G = I := by
    ext x
    by_cases hx : x ∈ I
    · exact iff_of_true ⟨l x, by simp [G, intervalGraphOn, hx, hle x hx]⟩ hx
    · simp [dom, G, intervalGraphOn, hx]
  have hends (x) (hx : x ∈ I) : l x ∈ G x ∧ u x ∈ G x := by
    simp [G, intervalGraphOn, hx, hle x hx]
  have hmax : MaximalIncreasing (intervalCompletionI I l u) := completion_maximal hord hne hG hGdom
  have hcl : dom (intervalCompletionI I l u) ⊆ closure I := completion_dom_subset I G
  have hval (x) (hx : x ∈ I) : intervalCompletionI I l u x = Icc (l x) (u x) := by
    obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hx)
    ext v
    constructor
    · intro hv
      have hc : Compatible G x v := hv.2
      have hb := compatible_iff_bounds.mp hc
      constructor
      · apply le_of_tendsto (hlim x hx).1
        filter_upwards [Ioo_mem_nhdsLT hax] with y hy
        exact hb.1 (hends y (hab ⟨hy.1, hy.2.trans hxb⟩)).2 hy.2
      · apply ge_of_tendsto (hlim x hx).2
        filter_upwards [Ioo_mem_nhdsGT hxb] with y hy
        exact hb.2 (hends y (hab ⟨hax.trans hy.1, hy.2⟩)).1 hy.1
    · intro hv
      apply le_completion hG hGdom x
      simpa only [G, intervalGraphOn, if_pos hx] using hv
  have hcover : I ⊆ dom (intervalCompletionI I l u) := by
    intro x hx
    refine ⟨l x, ?_⟩
    rw [hval x hx]
    exact ⟨le_rfl, hle x hx⟩
  refine ⟨hmax, domain_interior_of_open_interval hI hord hne hcover hcl, hcl, hval, ?_⟩
  intro g hg hgd hgv
  apply hg.eq_of_le hmax.1
  intro x v hv
  refine ⟨hgd ⟨v, hv⟩, ?_⟩
  intro y w hw
  have hy : y ∈ I := by
    by_contra hy
    simpa [G, intervalGraphOn, hy] using hw
  have hwg : w ∈ g y := by
    rw [hgv y hy]
    simpa only [G, intervalGraphOn, if_pos hy] using hw
  exact hg.1 hv hwg

theorem decreasing_selection_tendsto_left {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) {x : ℝ} (hx : x ∈ I) :
    Tendsto s (𝓝[<] x) (𝓝 (sSup (f x))) := by
  have hn : SelectionOn (negOut f) I (fun y => -s y) := by
    intro y hy
    change -(-s y) ∈ f y
    simpa only [neg_neg] using hs y hy
  have hd : I ⊆ dom (negOut f) := by simpa only [dom_negOut] using hdom
  have ht := (selection_tendsto_left hf hI hd hn hx).neg
  have he := (decreasing_interior_neg_endpoints hf (hI.subset_interior_iff.mpr hdom hx)).1
  simpa only [he, neg_neg] using ht

theorem decreasing_selection_tendsto_right {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : IsOpen I) (hdom : I ⊆ dom f)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) {x : ℝ} (hx : x ∈ I) :
    Tendsto s (𝓝[>] x) (𝓝 (sInf (f x))) := by
  have hn : SelectionOn (negOut f) I (fun y => -s y) := by
    intro y hy
    change -(-s y) ∈ f y
    simpa only [neg_neg] using hs y hy
  have hd : I ⊆ dom (negOut f) := by simpa only [dom_negOut] using hdom
  have ht := (selection_tendsto_right hf hI hd hn hx).neg
  have he := (decreasing_interior_neg_endpoints hf (hI.subset_interior_iff.mpr hdom hx)).2
  simpa only [he, neg_neg] using ht

def aggregationOperator {n : ℕ} (F : CoordinateVector n → ℝ)
    (I : Set ℝ) (f : Fin n → Operator) : Operator :=
  negOut (intervalCompletionI I
    (fun x => -F (fun i => sSup (f i x))) (fun x => -F (fun i => sInf (f i x))))

theorem aggregationOperator_properties {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v) :
    MaximalDecreasing (aggregationOperator F I f) ∧
      interior (dom (aggregationOperator F I f)) = I ∧
      dom (aggregationOperator F I f) ⊆ closure I ∧
      ∀ x ∈ I, aggregationOperator F I f x =
        Icc (F (fun i => sInf (f i x))) (F (fun i => sSup (f i x))) := by
  have hinside (i) {x} (hx : x ∈ I) : x ∈ interior (dom (f i)) :=
    hI.subset_interior_iff.mpr (hdom i) hx
  have hl (i) : SelectionOn (f i) I (fun x => sInf (f i x)) :=
    fun x hx => (maximal_decreasing_interior_endpoints_mem (hf i) (hinside i hx)).1
  have hu (i) : SelectionOn (f i) I (fun x => sSup (f i x)) :=
    fun x hx => (maximal_decreasing_interior_endpoints_mem (hf i) (hinside i hx)).2
  have hlpos (x) (hx : x ∈ I) : 0 ≤ (fun i => sInf (f i x)) :=
    fun i => hpos i x hx _ (hl i x hx)
  have hupos (x) (hx : x ∈ I) : 0 ≤ (fun i => sSup (f i x)) :=
    fun i => hpos i x hx _ (hu i x hx)
  have hlu (x) (hx : x ∈ I) : (fun i => sInf (f i x)) ≤ (fun i => sSup (f i x)) := by
    intro i
    have he := decreasing_interior_neg_endpoints (hf i) (hinside i hx)
    have hb := maximal_interior_fiber_bounded (hf i)
      (show x ∈ interior (dom (negOut (f i))) by simpa only [dom_negOut] using hinside i hx)
    have h := csInf_le hb.1 (maximal_interior_fiber_endpoints_mem (hf i)
      (show x ∈ interior (dom (negOut (f i))) by simpa only [dom_negOut] using hinside i hx)).2
    rw [he.1, he.2] at h
    linarith
  have hle (x) (hx : x ∈ I) : -F (fun i => sSup (f i x)) ≤ -F (fun i => sInf (f i x)) :=
    neg_le_neg (hF.mono (hlpos x hx) (hlu x hx))
  have hsep (x) (hx : x ∈ I) (y) (hy : y ∈ I) (hxy : x < y) :
      -F (fun i => sInf (f i x)) ≤ -F (fun i => sSup (f i y)) :=
    neg_le_neg (hF.mono (hupos y hy) (fun i => Decreasing.le_of_lt (hf i).1 (hl i x hx) (hu i y hy) hxy))
  have hlim (x) (hx : x ∈ I) :
      Tendsto (fun y => -F (fun i => sInf (f i y))) (𝓝[<] x)
        (𝓝 (-F (fun i => sSup (f i x)))) ∧
      Tendsto (fun y => -F (fun i => sSup (f i y))) (𝓝[>] x)
        (𝓝 (-F (fun i => sInf (f i x)))) := by
    have heL : ∀ᶠ y in 𝓝[<] x, y ∈ I := nhdsWithin_le_nhds (hI.mem_nhds hx)
    have heR : ∀ᶠ y in 𝓝[>] x, y ∈ I := nhdsWithin_le_nhds (hI.mem_nhds hx)
    constructor
    · apply Tendsto.neg
      apply (hFc _ (hupos x hx)).tendsto.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr (fun i =>
        decreasing_selection_tendsto_left (hf i) hI (hdom i) (hl i) hx),
        heL.mono (fun y hy => hlpos y hy)⟩
    · apply Tendsto.neg
      apply (hFc _ (hlpos x hx)).tendsto.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr (fun i =>
        decreasing_selection_tendsto_right (hf i) hI (hdom i) (hu i) hx),
        heR.mono (fun y hy => hupos y hy)⟩
  have hC := intervalCompletionI_properties hI hord hne hle hsep hlim
  refine ⟨?_, ?_, ?_, ?_⟩
  · change MaximalIncreasing (negOut (negOut _))
    simpa only [negOut_negOut] using hC.1
  · simpa only [aggregationOperator, dom_negOut] using hC.2.1
  · simpa only [aggregationOperator, dom_negOut] using hC.2.2.1
  · intro x hx
    ext v
    change -v ∈ intervalCompletionI I _ _ x ↔ _
    rw [hC.2.2.2.1 x hx]
    simp only [mem_Icc]
    constructor <;> intro hv <;> constructor <;> linarith [hv.1, hv.2]

theorem aggregationOperator_unique {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {g : Operator} (hg : MaximalDecreasing g) (hgd : dom g ⊆ closure I)
    (hgv : ∀ x ∈ I, g x = Icc (F (fun i => sInf (f i x))) (F (fun i => sSup (f i x)))) :
    g = aggregationOperator F I f := by
  have hA := aggregationOperator_properties hF hFc hI hord hne hf hdom hpos
  have hcover : I ⊆ dom (aggregationOperator F I f) := by
    intro x hx
    apply interior_subset
    rw [hA.2.1]
    exact hx
  obtain ⟨c, _, huniq⟩ := unique_completed_decreasing_restriction_values hA.1 hord hI hne hcover
  have hg' : MaximalDecreasing g ∧ (∀ x ∈ I, g x = aggregationOperator F I f x) ∧ dom g ⊆ closure I :=
    ⟨hg, fun x hx => (hgv x hx).trans (hA.2.2.2 x hx).symm, hgd⟩
  have hself : MaximalDecreasing (aggregationOperator F I f) ∧
      (∀ x ∈ I, aggregationOperator F I f x = aggregationOperator F I f x) ∧
      dom (aggregationOperator F I f) ⊆ closure I := ⟨hA.1, fun _ _ => rfl, hA.2.2.1⟩
  exact (huniq g hg').trans (huniq _ hself).symm

theorem decreasing_interior_value_bounds {f : Operator} (hf : MaximalDecreasing f)
    {x v : ℝ} (hx : x ∈ interior (dom f)) (hv : v ∈ f x) :
    sInf (f x) ≤ v ∧ v ≤ sSup (f x) := by
  have hx' : x ∈ interior (dom (negOut f)) := by simpa only [dom_negOut] using hx
  have hb := maximal_interior_fiber_bounded hf hx'
  have he := decreasing_interior_neg_endpoints hf hx
  have hv' : -v ∈ negOut f x := by simpa only [negOut, mem_setOf_eq, neg_neg] using hv
  have hl := csInf_le hb.1 hv'
  have hu := le_csSup hb.2 hv'
  rw [he.1] at hl
  rw [he.2] at hu
  constructor <;> linarith

theorem aggregationOperator_selection {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i))
    (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (f i) I (s i)) :
    SelectionOn (aggregationOperator F I f) I (fun x => F (fun i => s i x)) := by
  have hA := aggregationOperator_properties hF hFc hI hord hne hf hdom hpos
  intro x hx
  rw [hA.2.2.2 x hx]
  have hxi (i) : x ∈ interior (dom (f i)) := hI.subset_interior_iff.mpr (hdom i) hx
  have hb (i) := decreasing_interior_value_bounds (hf i) (hxi i) (hs i x hx)
  have hln : 0 ≤ (fun i => sInf (f i x)) := fun i => hpos i x hx _
    (maximal_decreasing_interior_endpoints_mem (hf i) (hxi i)).1
  have hsn : 0 ≤ (fun i => s i x) := fun i => hpos i x hx _ (hs i x hx)
  exact ⟨hF.mono hln (fun i => (hb i).1), hF.mono hsn (fun i => (hb i).2)⟩

end ScalarMonotone.EndOfPaper
end
