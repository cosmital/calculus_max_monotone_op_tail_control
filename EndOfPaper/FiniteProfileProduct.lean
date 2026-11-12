import EndOfPaper.GeometricScalarCompletion

/-!
The literal finite interior graph product and its
unique maximal completion. Domain, nonnegativity, every
scalar selection and all endpoint/jump fibers are retained.
-/

open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def interiorFiniteProfileProduct {ι : Type*} [Fintype ι] (B : ℝ) (q : ι → Operator) : Operator :=
  fun x => {v | x ∈ Ioo (0 : ℝ) B ∧ ∃ a : ι → ℝ, (∀ i, a i ∈ q i x) ∧ v = ∏ i, a i}

theorem interiorFiniteProfileProduct_decreasing {ι : Type*} [Fintype ι]
    {q : ι → Operator} {B : ℝ} (hq : ∀ i, Decreasing (q i))
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ q i x, 0 ≤ v) :
    Decreasing (interiorFiniteProfileProduct B q) := by
  classical
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  change -u ∈ interiorFiniteProfileProduct B q x at hu
  change -v ∈ interiorFiniteProfileProduct B q y at hv
  rcases hu with ⟨hx,a,ha,heu⟩
  rcases hv with ⟨hy,b,hb,hev⟩
  have hprod : (∏ i, b i) ≤ ∏ i, a i := Finset.prod_le_prod
    (fun i _ => hq0 i y hy (b i) (hb i))
    (fun i _ => Decreasing.le_of_lt (hq i) (ha i) (hb i) hxy)
  linarith

theorem interiorFiniteProfileProduct_domain {ι : Type*} [Fintype ι]
    {q : ι → Operator} {B : ℝ}
    (hqi : ∀ i, interior (dom (q i)) = Ioo (0 : ℝ) B) :
    dom (interiorFiniteProfileProduct B q) = Ioo (0 : ℝ) B := by
  classical
  ext x
  constructor
  · rintro ⟨v,hx,_⟩
    exact hx
  · intro hx
    have hd (i : ι) : x ∈ dom (q i) := interior_subset (by rwa [hqi i])
    choose a ha using hd
    exact ⟨∏ i, a i,hx,a,ha,rfl⟩

def completedFiniteProfileProduct {ι : Type*} [Fintype ι] (B : ℝ) (q : ι → DecGraph)
    (hB : 0 < B) (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v) : DecGraph := by
  let P := interiorFiniteProfileProduct B (fun i => (q i).val)
  refine ⟨negOut (completion (Ioo (0 : ℝ) B) (negOut P)),?_⟩
  change MaximalIncreasing (negOut (negOut (completion (Ioo (0 : ℝ) B) (negOut P))))
  rw [negOut_negOut]
  apply completion_maximal ordConnected_Ioo (nonempty_Ioo.mpr hB)
    (interiorFiniteProfileProduct_decreasing (fun i => (q i).property.1) hq0)
  rw [dom_negOut]
  exact interiorFiniteProfileProduct_domain hqi

theorem completedFiniteProfileProduct_raw_inclusion {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v) :
    interiorFiniteProfileProduct B (fun i => (q i).val) ≤
      (completedFiniteProfileProduct B q hB hqi hq0).val := by
  let P := interiorFiniteProfileProduct B (fun i => (q i).val)
  have hP : Increasing (negOut P) := interiorFiniteProfileProduct_decreasing
    (fun i => (q i).property.1) hq0
  have hd : dom (negOut P) = Ioo (0 : ℝ) B := by
    rw [dom_negOut]
    exact interiorFiniteProfileProduct_domain hqi
  intro x v hv
  change -v ∈ completion (Ioo (0 : ℝ) B) (negOut P) x
  apply le_completion hP hd x
  change -(-v) ∈ P x
  simpa only [neg_neg] using hv

theorem completedFiniteProfileProduct_domain {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v) :
    let P := completedFiniteProfileProduct B q hB hqi hq0
    interior (dom P.val) = Ioo (0 : ℝ) B ∧ dom P.val ⊆ closure (Ioo (0 : ℝ) B) := by
  let P := completedFiniteProfileProduct B q hB hqi hq0
  have hd : dom P.val ⊆ closure (Ioo (0 : ℝ) B) := by
    change dom (negOut (completion (Ioo (0 : ℝ) B)
      (negOut (interiorFiniteProfileProduct B (fun i => (q i).val))))) ⊆ _
    simpa only [dom_negOut] using completion_dom_subset (Ioo (0 : ℝ) B)
      (negOut (interiorFiniteProfileProduct B (fun i => (q i).val)))
  have hc : Ioo (0 : ℝ) B ⊆ dom P.val := by
    intro x hx
    have hxP : x ∈ dom (interiorFiniteProfileProduct B (fun i => (q i).val)) := by
      rwa [interiorFiniteProfileProduct_domain hqi]
    obtain ⟨v,hv⟩ := hxP
    exact ⟨v,completedFiniteProfileProduct_raw_inclusion hB hqi hq0 x hv⟩
  exact ⟨domain_interior_of_open_interval isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr hB) hc hd,hd⟩

theorem completedFiniteProfileProduct_nonnegative {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v) :
    ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ (completedFiniteProfileProduct B q hB hqi hq0).val x, 0 ≤ v := by
  classical
  intro x hx v hv
  let y := (x+B)/2
  have hy : y ∈ Ioo (0 : ℝ) B := ⟨by dsimp [y]; linarith [hx.1,hx.2],by dsimp [y]; linarith [hx.2]⟩
  have hxy : x < y := by dsimp [y]; linarith [hx.2]
  have hdy (i : ι) : y ∈ dom (q i).val := interior_subset (by rwa [hqi i])
  choose a ha using hdy
  have hw : (∏ i, a i) ∈ (completedFiniteProfileProduct B q hB hqi hq0).val y :=
    completedFiniteProfileProduct_raw_inclusion hB hqi hq0 y ⟨hy,a,ha,rfl⟩
  exact (Finset.prod_nonneg (fun i _ => hq0 i y hy (a i) (ha i))).trans
    (Decreasing.le_of_lt (completedFiniteProfileProduct B q hB hqi hq0).property.1 hv hw hxy)

theorem completedFiniteProfileProduct_selection {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v)
    {s : ι → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) B) (s i)) :
    SelectionOn (completedFiniteProfileProduct B q hB hqi hq0).val
      (Ioo (0 : ℝ) B) (fun x => ∏ i, s i x) := by
  intro x hx
  exact completedFiniteProfileProduct_raw_inclusion hB hqi hq0 x
    ⟨hx,(fun i => s i x),(fun i => hs i x hx),rfl⟩

theorem completedFiniteProfileProduct_unique {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v)
    {f : Operator} (hf : MaximalDecreasing f)
    (hpf : interiorFiniteProfileProduct B (fun i => (q i).val) ≤ f)
    (hfd : dom f ⊆ closure (Ioo (0 : ℝ) B)) :
    f = (completedFiniteProfileProduct B q hB hqi hq0).val := by
  apply (unique_maximal_decreasing_completion ordConnected_Ioo (nonempty_Ioo.mpr hB)
    (interiorFiniteProfileProduct_decreasing (fun i => (q i).property.1) hq0)
    (interiorFiniteProfileProduct_domain hqi)).unique
  · exact ⟨hf,hpf,hfd⟩
  · exact ⟨(completedFiniteProfileProduct B q hB hqi hq0).property,
      completedFiniteProfileProduct_raw_inclusion hB hqi hq0,
      (completedFiniteProfileProduct_domain hB hqi hq0).2⟩

end ScalarMonotone.EndOfPaper
end
