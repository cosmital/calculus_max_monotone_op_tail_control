import MonotoneOperators.ProbabilityBounds
import MonotoneOperators.ExtremaFinite
import MonotoneOperators.ExtremaIdentities
import MonotoneOperators.OrderGeometry

/-!
# Parallel-sum envelopes

Strictly positive weights form an actual indexing type. The optimized
identities are genuine lattice extrema over all such weights. Their proof
uses a common positive fiber selection at an intermediate domain point.
-/

open Set
open scoped BigOperators

noncomputable section

namespace ScalarMonotone

structure PositiveWeights (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  positive : ∀ i, 0 < weight i
  sum_one : ∑ i, weight i = 1

instance {ι : Type*} [Fintype ι] : CoeFun (PositiveWeights ι) (fun _ => ι → ℝ) :=
  ⟨PositiveWeights.weight⟩

instance {ι : Type*} [Fintype ι] [Nonempty ι] : Nonempty (PositiveWeights ι) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨⟨fun _ => (Fintype.card ι : ℝ)⁻¹, fun _ => inv_pos.2 hc, ?_⟩⟩
  simp [hc.ne']

def IncGraph.normalized {ι : Type*} [Fintype ι]
    (q : ι → IncGraph) (θ : PositiveWeights ι) (i : ι) : IncGraph :=
  ⟨outputScale (θ i)⁻¹ (q i).val,
    outputScale_maximal (inv_pos.2 (θ.positive i)) (q i).property⟩

def DecGraph.normalized {ι : Type*} [Fintype ι]
    (q : ι → DecGraph) (θ : PositiveWeights ι) (i : ι) : DecGraph :=
  ⟨outputScale (θ i)⁻¹ (q i).val,
    outputScale_maximal_decreasing (inv_pos.2 (θ.positive i)) (q i).property⟩

theorem finiteSum_reflect {ι : Type*} [Fintype ι] (f : ι → Operator) :
    finiteSum (fun i => reflect (f i)) = reflect (finiteSum f) := rfl

theorem finiteSum_maximal {ι : Type*} [Fintype ι]
    (f : ι → Operator) (hf : ∀ i, MaximalIncreasing (f i))
    (hc : ∃ c, ∀ i, (f i c).Nonempty) : MaximalIncreasing (finiteSum f) := by
  have hr : ∃ c, ∀ i, (reflect (f i) c).Nonempty := by
    obtain ⟨c, hc⟩ := hc
    exact ⟨-c, by simpa [reflect] using hc⟩
  have hm := finiteSum_maximal_decreasing (fun i => reflect (f i))
    (fun i => reflect_maximal_iff.mp (by simpa using hf i)) hr
  rw [finiteSum_reflect] at hm
  simpa only [reflect_reflect] using reflect_maximal_iff.mpr hm

private theorem weighted_sum_const {ι : Type*} [Fintype ι]
    (θ : PositiveWeights ι) (u : ℝ) : ∑ i, θ i * u = u := by
  rw [← Finset.sum_mul, θ.sum_one, one_mul]

private theorem weight_mul_inverse (θ r : ℝ) (hθ : 0 < θ) :
    θ * (θ⁻¹ * r) = r := by field_simp

section Finite

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The inverse-level weighted envelope bound, without any common-domain qualification. -/
theorem DecGraph.finiteSum_between_envelopes (q : ι → DecGraph) (θ : PositiveWeights ι) :
    DecLE (⨅ i, normalized q θ i).val (finiteSum fun i => (q i).val) ∧
      DecLE (finiteSum fun i => (q i).val) (⨆ i, normalized q θ i).val := by
  constructor
  · intro x u y v hu hv hyx
    rcases hv with ⟨r, hr, rfl⟩
    have hle : ∀ i, θ i * u ≤ r i := by
      intro i
      have hi : (⨅ j, normalized q θ j) ≤ normalized q θ i :=
        ciInf_le (finite_range _).bddBelow i
      have h := hi hu (show (θ i)⁻¹ * r i ∈ (normalized q θ i).val y from
        ⟨r i, hr i, rfl⟩) hyx
      have h' := mul_le_mul_of_nonneg_left h (θ.positive i).le
      simpa only [weight_mul_inverse _ _ (θ.positive i)] using h'
    rw [← weighted_sum_const θ u]
    exact Finset.sum_le_sum (fun i _ => hle i)
  · intro x u y v hu hv hyx
    rcases hu with ⟨r, hr, rfl⟩
    have hle : ∀ i, r i ≤ θ i * v := by
      intro i
      have hi : normalized q θ i ≤ (⨆ j, normalized q θ j) :=
        le_ciSup (finite_range _).bddAbove i
      have h := hi (show (θ i)⁻¹ * r i ∈ (normalized q θ i).val x from
        ⟨r i, hr i, rfl⟩) hv hyx
      have h' := mul_le_mul_of_nonneg_left h (θ.positive i).le
      simpa only [weight_mul_inverse _ _ (θ.positive i)] using h'
    rw [← weighted_sum_const θ v]
    exact Finset.sum_le_sum (fun i _ => hle i)

theorem IncGraph.finiteSum_between_envelopes (q : ι → IncGraph) (θ : PositiveWeights ι) :
    IncLE (⨅ i, normalized q θ i).val (finiteSum fun i => (q i).val) ∧
      IncLE (finiteSum fun i => (q i).val) (⨆ i, normalized q θ i).val := by
  have h := DecGraph.finiteSum_between_envelopes (fun i => (q i).reflect) θ
  have heq : (fun i => DecGraph.normalized (fun j => (q j).reflect) θ i) =
      fun i => (normalized q θ i).reflect := by
    funext i
    apply DecGraph.ext_val
    rfl
  rw [heq, ← IncGraph.reflect_iInf, ← IncGraph.reflect_iSup] at h
  exact ⟨decLE_reflect_iff.1 h.1, decLE_reflect_iff.1 h.2⟩

/-- A common point of all fibers belongs to both finite lattice envelopes. -/
theorem DecGraph.mem_finite_extrema_of_forall (f : ι → DecGraph) {x u : ℝ}
    (hu : ∀ i, u ∈ (f i).val x) :
    u ∈ (⨅ i, f i).val x ∧ u ∈ (⨆ i, f i).val x := by
  have hJ : ∀ i, (f i).J (x-u) = x := fun i => (mem_iff_J _).1 (hu i)
  constructor
  · rw [mem_iff_J, J_iInf_finite]
    simp only [hJ, ciInf_const]
  · rw [mem_iff_J, J_iSup_finite]
    simp only [hJ, ciSup_const]

omit [Fintype ι] in
private theorem intervalInf_const (D : Set ℝ) (hD : D.OrdConnected) :
    intervalInf (fun _ : ι => D) = D := by
  rw [intervalInf, iUnion_const, iInter_const, hull_inter_eq hD]

omit [Fintype ι] in
private theorem intervalSup_const (D : Set ℝ) (hD : D.OrdConnected) :
    intervalSup (fun _ : ι => D) = D := by
  rw [intervalSup, iUnion_const, iInter_const, inter_comm, hull_inter_eq hD]

private theorem finiteSum_dom_common (q : ι → Operator) {D : Set ℝ}
    (hdom : ∀ i, dom (q i) = D) : dom (finiteSum q) = D := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  ext x
  constructor
  · rintro ⟨w, r, hr, hw⟩
    have hx : x ∈ dom (q i₀) := ⟨r i₀, hr i₀⟩
    simpa only [hdom i₀] using hx
  · intro hx
    have h : ∀ i, (q i x).Nonempty := by
      intro i
      change x ∈ dom (q i)
      simpa only [hdom i] using hx
    choose r hr using h
    exact ⟨∑ i, r i, r, hr, rfl⟩

omit [Fintype ι] in
private theorem DecGraph.common_domain_nonempty (q : ι → DecGraph) {D : Set ℝ}
    (hdom : ∀ i, dom (q i).val = D) : ∃ c, ∀ i, ((q i).val c).Nonempty := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨c, u, hu⟩ := maximal_nonempty (q i₀).property
  have hc : c ∈ D := by
    rw [← hdom i₀]
    exact ⟨-u, hu⟩
  refine ⟨c, fun i => ?_⟩
  change c ∈ dom (q i).val
  simpa only [hdom i] using hc

private theorem DecGraph.normalized_extrema_dom (q : ι → DecGraph) {D : Set ℝ}
    (hdom : ∀ i, dom (q i).val = D) (θ : PositiveWeights ι) :
    dom (⨅ i, normalized q θ i).val = D ∧ dom (⨆ i, normalized q θ i).val = D := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hD : D.OrdConnected := by
    rw [← hdom i₀]
    exact decreasing_dom_ordConnected (q i₀).property
  have hnorm : ∀ i, dom (normalized q θ i).val = D := by
    intro i
    change dom (outputScale _ _) = D
    rw [dom_outputScale, hdom]
  constructor
  · rw [dom_iInf]
    simp_rw [hnorm]
    exact intervalInf_const D hD
  · rw [dom_iSup]
    simp_rw [hnorm]
    exact intervalSup_const D hD

/-- Two distinct domain points enclose an interior point of an interval. -/
theorem exists_interior_between {D : Set ℝ} (hD : D.OrdConnected)
    {x y : ℝ} (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) :
    ∃ z ∈ interior D, x < z ∧ z < y := by
  obtain ⟨z, hxz, hzy⟩ := exists_between hxy
  have hs : Ioo x y ⊆ D := fun r hr => hD.out hx hy ⟨hr.1.le, hr.2.le⟩
  exact ⟨z, interior_maximal hs isOpen_Ioo ⟨hxz, hzy⟩, hxz, hzy⟩

/-- Balancing any positive common-level selection produces one point of both envelopes. -/
theorem DecGraph.exists_balanced_weights (q : ι → DecGraph) {x : ℝ}
    (hx : ∀ i, x ∈ dom (q i).val)
    (hpos : ∀ i, (q i).val x ⊆ Ioi 0) :
    ∃ θ : PositiveWeights ι, ∃ u,
      u ∈ finiteSum (fun i => (q i).val) x ∧
      u ∈ (⨅ i, normalized q θ i).val x ∧ u ∈ (⨆ i, normalized q θ i).val x := by
  classical
  choose r hr using hx
  have hrpos : ∀ i, 0 < r i := fun i => hpos i (hr i)
  let u := ∑ i, r i
  have hu : 0 < u := Finset.sum_pos (fun i _ => hrpos i) Finset.univ_nonempty
  let θ : PositiveWeights ι :=
    ⟨fun i => r i / u, fun i => div_pos (hrpos i) hu, by
      rw [← Finset.sum_div]
      exact div_self hu.ne'⟩
  have hmem : ∀ i, u ∈ (normalized q θ i).val x := by
    intro i
    refine ⟨r i, hr i, ?_⟩
    change u = (r i / u)⁻¹ * r i
    field_simp [(hrpos i).ne', hu.ne']
  obtain ⟨hlo, hup⟩ := mem_finite_extrema_of_forall _ hmem
  exact ⟨θ, u, ⟨r, hr, rfl⟩, hlo, hup⟩

/-- Optimizing all positive weights recovers the entire common-domain sum,
including every endpoint fiber. -/
theorem DecGraph.optimized_sum_envelopes (q : ι → DecGraph) (Q : DecGraph)
    (hQ : Q.val = finiteSum fun i => (q i).val) {D : Set ℝ}
    (hdom : ∀ i, dom (q i).val = D)
    (hpos : ∀ x ∈ interior D, ∀ i, (q i).val x ⊆ Ioi 0) :
    (⨆ θ : PositiveWeights ι, ⨅ i, normalized q θ i) = Q ∧
      (⨅ θ : PositiveWeights ι, ⨆ i, normalized q θ i) = Q := by
  classical
  let A : PositiveWeights ι → DecGraph := fun θ => ⨅ i, normalized q θ i
  let B : PositiveWeights ι → DecGraph := fun θ => ⨆ i, normalized q θ i
  let L : DecGraph := ⨆ θ, A θ
  let U : DecGraph := ⨅ θ, B θ
  have hA : ∀ θ, A θ ≤ Q := by
    intro θ
    change DecLE (A θ).val Q.val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).1
  have hB : ∀ θ, Q ≤ B θ := by
    intro θ
    change DecLE Q.val (B θ).val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).2
  have hAbdd : BddAbove (range A) := ⟨Q, by rintro _ ⟨θ, rfl⟩; exact hA θ⟩
  have hBbdd : BddBelow (range B) := ⟨Q, by rintro _ ⟨θ, rfl⟩; exact hB θ⟩
  have hAL : ∀ θ, A θ ≤ L := fun θ => le_ciSup hAbdd θ
  have hLQ : L ≤ Q := ciSup_le hA
  have hQU : Q ≤ U := le_ciInf hB
  have hUB : ∀ θ, U ≤ B θ := fun θ => ciInf_le hBbdd θ
  have hQdom : dom Q.val = D := hQ ▸ finiteSum_dom_common _ hdom
  have hD : D.OrdConnected := by
    rw [← hQdom]
    exact decreasing_dom_ordConnected Q.property
  let θ₀ : PositiveWeights ι := Classical.choice inferInstance
  have hAdom : dom (A θ₀).val = D := (normalized_extrema_dom q hdom θ₀).1
  have hBdom : dom (B θ₀).val = D := (normalized_extrema_dom q hdom θ₀).2
  have hLdom : dom L.val = D := by
    apply intervalLE_antisymm (decreasing_dom_ordConnected L.property) hD
    · simpa only [hQdom] using decLE_domains L.property Q.property hLQ
    · simpa only [hAdom] using decLE_domains (A θ₀).property L.property (hAL θ₀)
  have hUdom : dom U.val = D := by
    apply intervalLE_antisymm (decreasing_dom_ordConnected U.property) hD
    · simpa only [hBdom] using decLE_domains U.property (B θ₀).property (hUB θ₀)
    · simpa only [hQdom] using decLE_domains Q.property U.property hQU
  have hQL : Q ≤ L := by
    intro x u y v hu hv hyx
    have hx : x ∈ D := by rw [← hQdom]; exact ⟨u, hu⟩
    have hy : y ∈ D := by rw [← hLdom]; exact ⟨v, hv⟩
    obtain ⟨z, hz, hyz, hzx⟩ := exists_interior_between hD hy hx hyx
    have hzi : ∀ i, z ∈ dom (q i).val := by
      intro i
      rw [hdom]
      exact interior_subset hz
    obtain ⟨θ, w, hwQ, hwA, hwB⟩ := exists_balanced_weights q hzi (hpos z hz)
    have hwQ' : w ∈ Q.val z := by rw [hQ]; exact hwQ
    exact (decLE_refl Q.property.1 hu hwQ' hzx).trans ((hAL θ) hwA hv hyz)
  have hUQ : U ≤ Q := by
    intro x u y v hu hv hyx
    have hx : x ∈ D := by rw [← hUdom]; exact ⟨u, hu⟩
    have hy : y ∈ D := by rw [← hQdom]; exact ⟨v, hv⟩
    obtain ⟨z, hz, hyz, hzx⟩ := exists_interior_between hD hy hx hyx
    have hzi : ∀ i, z ∈ dom (q i).val := by
      intro i
      rw [hdom]
      exact interior_subset hz
    obtain ⟨θ, w, hwQ, hwA, hwB⟩ := exists_balanced_weights q hzi (hpos z hz)
    have hwQ' : w ∈ Q.val z := by rw [hQ]; exact hwQ
    exact ((hUB θ) hu hwB hzx).trans (decLE_refl Q.property.1 hwQ' hv hyz)
  exact ⟨le_antisymm hLQ hQL, le_antisymm hUQ hQU⟩

theorem interior_setNeg (D : Set ℝ) : interior (setNeg D) = setNeg (interior D) :=
  ((Homeomorph.neg ℝ).preimage_interior D).symm

/-- The increasing version is transported by input reflection, which preserves
the pointwise resolvent order. -/
theorem IncGraph.optimized_sum_envelopes (q : ι → IncGraph) (Q : IncGraph)
    (hQ : Q.val = finiteSum fun i => (q i).val) {D : Set ℝ}
    (hdom : ∀ i, dom (q i).val = D)
    (hpos : ∀ x ∈ interior D, ∀ i, (q i).val x ⊆ Ioi 0) :
    (⨆ θ : PositiveWeights ι, ⨅ i, normalized q θ i) = Q ∧
      (⨅ θ : PositiveWeights ι, ⨆ i, normalized q θ i) = Q := by
  let A : PositiveWeights ι → IncGraph := fun θ => ⨅ i, normalized q θ i
  let B : PositiveWeights ι → IncGraph := fun θ => ⨆ i, normalized q θ i
  have hA : ∀ θ, A θ ≤ Q := by
    intro θ
    change IncLE (A θ).val Q.val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).1
  have hB : ∀ θ, Q ≤ B θ := by
    intro θ
    change IncLE Q.val (B θ).val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).2
  have hAbdd : BddAbove (range A) := ⟨Q, by rintro _ ⟨θ, rfl⟩; exact hA θ⟩
  have hBbdd : BddBelow (range B) := ⟨Q, by rintro _ ⟨θ, rfl⟩; exact hB θ⟩
  have hdom' : ∀ i, dom (q i).reflect.val = setNeg D := by
    intro i
    change dom (ScalarMonotone.reflect (q i).val) = setNeg D
    rw [dom_reflect, hdom]
  have hpos' : ∀ x ∈ interior (setNeg D), ∀ i, (q i).reflect.val x ⊆ Ioi 0 := by
    intro x hx i
    rw [interior_setNeg] at hx
    exact hpos (-x) hx i
  have hQ' : Q.reflect.val = finiteSum fun i => (q i).reflect.val := by
    change ScalarMonotone.reflect Q.val = ScalarMonotone.reflect (finiteSum fun i => (q i).val)
    rw [hQ]
  have h := DecGraph.optimized_sum_envelopes (fun i => (q i).reflect) Q.reflect
    hQ' hdom' hpos'
  have heq : ∀ θ : PositiveWeights ι,
      (fun i => DecGraph.normalized (fun j => (q j).reflect) θ i) =
        fun i => (normalized q θ i).reflect := by
    intro θ
    funext i
    apply DecGraph.ext_val
    rfl
  have hAr : ∀ θ, (A θ).reflect = ⨅ i, DecGraph.normalized (fun j => (q j).reflect) θ i := by
    intro θ
    rw [heq θ]
    exact reflect_iInf _
  have hBr : ∀ θ, (B θ).reflect = ⨆ i, DecGraph.normalized (fun j => (q j).reflect) θ i := by
    intro θ
    rw [heq θ]
    exact reflect_iSup _
  constructor
  · apply IncGraph.reflectionOrderIso.injective
    change IncGraph.reflectionOrderIso (⨆ θ, A θ) = Q.reflect
    rw [IncGraph.reflectionOrderIso.map_ciSup hAbdd]
    change (⨆ θ, (A θ).reflect) = Q.reflect
    simpa only [hAr] using h.1
  · apply IncGraph.reflectionOrderIso.injective
    change IncGraph.reflectionOrderIso (⨅ θ, B θ) = Q.reflect
    rw [IncGraph.reflectionOrderIso.map_ciInf hBbdd]
    change (⨅ θ, (B θ).reflect) = Q.reflect
    simpa only [hBr] using h.2

omit [Fintype ι] in
private theorem IncGraph.common_domain_nonempty (q : ι → IncGraph) {D : Set ℝ}
    (hdom : ∀ i, dom (q i).val = D) : ∃ c, ∀ i, ((q i).val c).Nonempty := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨c, u, hu⟩ := maximal_nonempty (q i₀).property
  have hc : c ∈ D := by
    rw [← hdom i₀]
    exact ⟨u, hu⟩
  refine ⟨c, fun i => ?_⟩
  change c ∈ dom (q i).val
  simpa only [hdom i] using hc

/-- The maximal finite parallel sum constructed from the common-range hypothesis. -/
def DecGraph.parallelSumGraph (α : ι → DecGraph) {D : Set ℝ}
    (hD : ∀ i, ran (α i).val = D) : DecGraph :=
  ⟨finiteParallelAdd (fun i => (α i).val),
    finiteParallelAdd_maximal_decreasing _ (fun i => (α i).property)
      (common_domain_nonempty (fun i => (α i).inv) hD)⟩

def IncGraph.parallelSumGraph (α : ι → IncGraph) {D : Set ℝ}
    (hD : ∀ i, ran (α i).val = D) : IncGraph :=
  ⟨finiteParallelAdd (fun i => (α i).val), inverse_maximal
    (finiteSum_maximal _ (fun i => (α i).inv.property)
      (common_domain_nonempty (fun i => (α i).inv) hD))⟩

/-- The graph `αᵢ ∘ (θᵢ id)`, constructed through inverse output scaling. -/
def DecGraph.weightedProfile (α : ι → DecGraph) (θ : PositiveWeights ι) (i : ι) : DecGraph :=
  (normalized (fun j => (α j).inv) θ i).inv

def IncGraph.weightedProfile (α : ι → IncGraph) (θ : PositiveWeights ι) (i : ι) : IncGraph :=
  (normalized (fun j => (α j).inv) θ i).inv

omit [Nonempty ι] in
theorem DecGraph.weightedProfile_val (α : ι → DecGraph) (θ : PositiveWeights ι) (i : ι) :
    (weightedProfile α θ i).val = comp (α i).val (ofFun fun t => θ i * t) := by
  change inverse (outputScale (θ i)⁻¹ (inverse (α i).val)) = _
  rw [inverse_outputScale_inverse (inv_ne_zero (θ.positive i).ne')]
  ext t u
  simp [inputDivide, comp, ofFun, div_inv_eq_mul, mul_comm]

omit [Nonempty ι] in
theorem IncGraph.weightedProfile_val (α : ι → IncGraph) (θ : PositiveWeights ι) (i : ι) :
    (weightedProfile α θ i).val = comp (α i).val (ofFun fun t => θ i * t) := by
  change inverse (outputScale (θ i)⁻¹ (inverse (α i).val)) = _
  rw [inverse_outputScale_inverse (inv_ne_zero (θ.positive i).ne')]
  ext t u
  simp [inputDivide, comp, ofFun, div_inv_eq_mul, mul_comm]

/-- Literal parallel-profile envelopes in the decreasing orientation. -/
theorem DecGraph.parallelSum_envelopes (α : ι → DecGraph) {D : Set ℝ}
    (hD : ∀ i, ran (α i).val = D) (θ : PositiveWeights ι) :
    (⨅ i, weightedProfile α θ i) ≤ parallelSumGraph α hD ∧
      parallelSumGraph α hD ≤ (⨆ i, weightedProfile α θ i) := by
  have h := finiteSum_between_envelopes (fun i => (α i).inv) θ
  have hlo : (⨅ i, normalized (fun j => (α j).inv) θ i).inv ≤ parallelSumGraph α hD :=
    decLE_inverse_iff.2 h.1
  have hup : parallelSumGraph α hD ≤ (⨆ i, normalized (fun j => (α j).inv) θ i).inv :=
    decLE_inverse_iff.2 h.2
  rw [inv_iInf _ (finite_range _).bddBelow] at hlo
  rw [inv_iSup _ (finite_range _).bddAbove] at hup
  exact ⟨hlo, hup⟩

/-- Literal parallel-profile envelopes in the increasing orientation. -/
theorem IncGraph.parallelSum_envelopes (α : ι → IncGraph) {D : Set ℝ}
    (hD : ∀ i, ran (α i).val = D) (θ : PositiveWeights ι) :
    (⨅ i, weightedProfile α θ i) ≤ parallelSumGraph α hD ∧
      parallelSumGraph α hD ≤ (⨆ i, weightedProfile α θ i) := by
  have h := finiteSum_between_envelopes (fun i => (α i).inv) θ
  have hlo : (⨆ i, normalized (fun j => (α j).inv) θ i).inv ≤ parallelSumGraph α hD :=
    incLE_inverse_iff.2 h.2
  have hup : parallelSumGraph α hD ≤ (⨅ i, normalized (fun j => (α j).inv) θ i).inv :=
    incLE_inverse_iff.2 h.1
  rw [inv_iSup _ (finite_range _).bddAbove] at hlo
  rw [inv_iInf _ (finite_range _).bddBelow] at hup
  exact ⟨hlo, hup⟩

/-- Optimized parallel-sum envelopes, with the manuscript's common range and
interior positivity hypotheses and no additional maximality assumption. -/
theorem DecGraph.optimized_parallelSum_envelopes (α : ι → DecGraph) {D : Set ℝ}
    (hD : ∀ i, ran (α i).val = D)
    (hpos : ∀ u ∈ interior D, ∀ i, inverse (α i).val u ⊆ Ioi 0) :
    (⨆ θ : PositiveWeights ι, ⨅ i, weightedProfile α θ i) = parallelSumGraph α hD ∧
      (⨅ θ : PositiveWeights ι, ⨆ i, weightedProfile α θ i) = parallelSumGraph α hD := by
  let q : ι → DecGraph := fun i => (α i).inv
  let P := parallelSumGraph α hD
  have hQ : P.inv.val = finiteSum fun i => (q i).val := by
    change inverse (inverse (finiteSum fun i => inverse (α i).val)) = _
    rw [inverse_inverse]
    rfl
  have h := optimized_sum_envelopes q P.inv hQ hD hpos
  let A : PositiveWeights ι → DecGraph := fun θ => ⨅ i, normalized q θ i
  let B : PositiveWeights ι → DecGraph := fun θ => ⨆ i, normalized q θ i
  have hAbdd : BddAbove (range A) := by
    refine ⟨P.inv, ?_⟩
    rintro _ ⟨θ, rfl⟩
    change DecLE (A θ).val P.inv.val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).1
  have hBbdd : BddBelow (range B) := by
    refine ⟨P.inv, ?_⟩
    rintro _ ⟨θ, rfl⟩
    change DecLE P.inv.val (B θ).val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).2
  have hAi : ∀ θ, (A θ).inv = ⨅ i, weightedProfile α θ i := by
    intro θ
    exact inv_iInf _ (finite_range _).bddBelow
  have hBi : ∀ θ, (B θ).inv = ⨆ i, weightedProfile α θ i := by
    intro θ
    exact inv_iSup _ (finite_range _).bddAbove
  have hL : (⨆ θ, A θ).inv = P := by rw [h.1, inv_inv]
  have hU : (⨅ θ, B θ).inv = P := by rw [h.2, inv_inv]
  rw [inv_iSup A hAbdd] at hL
  rw [inv_iInf B hBbdd] at hU
  exact ⟨by simpa only [hAi] using hL, by simpa only [hBi] using hU⟩

theorem IncGraph.optimized_parallelSum_envelopes (α : ι → IncGraph) {D : Set ℝ}
    (hD : ∀ i, ran (α i).val = D)
    (hpos : ∀ u ∈ interior D, ∀ i, inverse (α i).val u ⊆ Ioi 0) :
    (⨆ θ : PositiveWeights ι, ⨅ i, weightedProfile α θ i) = parallelSumGraph α hD ∧
      (⨅ θ : PositiveWeights ι, ⨆ i, weightedProfile α θ i) = parallelSumGraph α hD := by
  let q : ι → IncGraph := fun i => (α i).inv
  let P := parallelSumGraph α hD
  have hQ : P.inv.val = finiteSum fun i => (q i).val := by
    change inverse (inverse (finiteSum fun i => inverse (α i).val)) = _
    rw [inverse_inverse]
    rfl
  have h := optimized_sum_envelopes q P.inv hQ hD hpos
  let A : PositiveWeights ι → IncGraph := fun θ => ⨅ i, normalized q θ i
  let B : PositiveWeights ι → IncGraph := fun θ => ⨆ i, normalized q θ i
  have hAbdd : BddAbove (range A) := by
    refine ⟨P.inv, ?_⟩
    rintro _ ⟨θ, rfl⟩
    change IncLE (A θ).val P.inv.val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).1
  have hBbdd : BddBelow (range B) := by
    refine ⟨P.inv, ?_⟩
    rintro _ ⟨θ, rfl⟩
    change IncLE P.inv.val (B θ).val
    rw [hQ]
    exact (finiteSum_between_envelopes q θ).2
  have hAi : ∀ θ, (A θ).inv = ⨆ i, weightedProfile α θ i := by
    intro θ
    exact inv_iInf _ (finite_range _).bddBelow
  have hBi : ∀ θ, (B θ).inv = ⨅ i, weightedProfile α θ i := by
    intro θ
    exact inv_iSup _ (finite_range _).bddAbove
  have hL : (⨆ θ, A θ).inv = P := by rw [h.1, inv_inv]
  have hU : (⨅ θ, B θ).inv = P := by rw [h.2, inv_inv]
  rw [inv_iSup A hAbdd] at hL
  rw [inv_iInf B hBbdd] at hU
  exact ⟨by simpa only [hBi] using hU, by simpa only [hAi] using hL⟩

end Finite

end ScalarMonotone
