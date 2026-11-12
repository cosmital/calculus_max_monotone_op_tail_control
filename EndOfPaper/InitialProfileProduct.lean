import EndOfPaper.GeometricScalarCompletion

/-!
The actual interior graph product and its unique maximal
completion, with exact domain, nonnegativity and scalar selections.
Products are formed on the interior before endpoint completion.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

def interiorProfileProduct (B : ℝ) (q r : Operator) : Operator := fun x =>
  {v | x ∈ Ioo (0 : ℝ) B ∧ ∃ a ∈ q x, ∃ b ∈ r x, v = a*b}

theorem interiorProfileProduct_decreasing {q r : Operator} {B : ℝ}
    (hq : Decreasing q) (hr : Decreasing r)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r x, 0 ≤ v) :
    Decreasing (interiorProfileProduct B q r) := by
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  change -u ∈ interiorProfileProduct B q r x at hu
  change -v ∈ interiorProfileProduct B q r y at hv
  rcases hu with ⟨hx,a,ha,b,hb,heu⟩
  rcases hv with ⟨hy,c,hc,d,hd,hev⟩
  have hca := Decreasing.le_of_lt hq ha hc hxy
  have hdb := Decreasing.le_of_lt hr hb hd hxy
  have hmul := mul_le_mul hca hdb (hr0 y hy d hd) (hq0 x hx a ha)
  linarith

theorem interiorProfileProduct_domain {q r : Operator} {B : ℝ}
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (hri : interior (dom r) = Ioo (0 : ℝ) B) :
    dom (interiorProfileProduct B q r) = Ioo (0 : ℝ) B := by
  ext x
  constructor
  · rintro ⟨v,hx,_⟩
    exact hx
  · intro hx
    have hxq : x ∈ dom q := interior_subset (by rwa [hqi])
    have hxr : x ∈ dom r := interior_subset (by rwa [hri])
    obtain ⟨a,ha⟩ := hxq
    obtain ⟨b,hb⟩ := hxr
    exact ⟨a*b,hx,a,ha,b,hb,rfl⟩

def completedProfileProduct (B : ℝ) (q r : DecGraph)
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v) : DecGraph := by
  let P := interiorProfileProduct B q.val r.val
  refine ⟨negOut (completion (Ioo (0 : ℝ) B) (negOut P)),?_⟩
  change MaximalIncreasing (negOut (negOut (completion (Ioo (0 : ℝ) B) (negOut P))))
  rw [negOut_negOut]
  apply completion_maximal ordConnected_Ioo (nonempty_Ioo.mpr hB)
    (interiorProfileProduct_decreasing q.property.1 r.property.1 hq0 hr0)
  rw [dom_negOut]
  exact interiorProfileProduct_domain hqi hri

theorem completedProfileProduct_raw_inclusion {q r : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v) :
    interiorProfileProduct B q.val r.val ≤ (completedProfileProduct B q r hB hqi hri hq0 hr0).val := by
  let P := interiorProfileProduct B q.val r.val
  have hP : Increasing (negOut P) := interiorProfileProduct_decreasing q.property.1 r.property.1 hq0 hr0
  have hd : dom (negOut P) = Ioo (0 : ℝ) B := by
    rw [dom_negOut]
    exact interiorProfileProduct_domain hqi hri
  intro x v hv
  change -v ∈ completion (Ioo (0 : ℝ) B) (negOut P) x
  apply le_completion hP hd x
  change -(-v) ∈ P x
  simpa only [neg_neg] using hv

theorem completedProfileProduct_domain {q r : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v) :
    let P := completedProfileProduct B q r hB hqi hri hq0 hr0
    interior (dom P.val) = Ioo (0 : ℝ) B ∧ dom P.val ⊆ closure (Ioo (0 : ℝ) B) := by
  let P := completedProfileProduct B q r hB hqi hri hq0 hr0
  have hd : dom P.val ⊆ closure (Ioo (0 : ℝ) B) := by
    change dom (negOut (completion (Ioo (0 : ℝ) B) (negOut (interiorProfileProduct B q.val r.val)))) ⊆ _
    simpa only [dom_negOut] using completion_dom_subset (Ioo (0 : ℝ) B) (negOut (interiorProfileProduct B q.val r.val))
  have hc : Ioo (0 : ℝ) B ⊆ dom P.val := by
    intro x hx
    have hxP : x ∈ dom (interiorProfileProduct B q.val r.val) := by
      rwa [interiorProfileProduct_domain hqi hri]
    obtain ⟨v,hv⟩ := hxP
    exact ⟨v,completedProfileProduct_raw_inclusion hB hqi hri hq0 hr0 x hv⟩
  exact ⟨domain_interior_of_open_interval isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr hB) hc hd,hd⟩

theorem completedProfileProduct_nonnegative {q r : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v) :
    ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ (completedProfileProduct B q r hB hqi hri hq0 hr0).val x, 0 ≤ v := by
  intro x hx v hv
  let y := (x+B)/2
  have hy : y ∈ Ioo (0 : ℝ) B := ⟨by dsimp [y]; linarith [hx.1,hx.2],by dsimp [y]; linarith [hx.2]⟩
  have hxy : x < y := by dsimp [y]; linarith [hx.2]
  have hyq : y ∈ dom q.val := interior_subset (by rwa [hqi])
  have hyr : y ∈ dom r.val := interior_subset (by rwa [hri])
  obtain ⟨a,ha⟩ := hyq
  obtain ⟨b,hb⟩ := hyr
  have hw : a*b ∈ (completedProfileProduct B q r hB hqi hri hq0 hr0).val y :=
    completedProfileProduct_raw_inclusion hB hqi hri hq0 hr0 y ⟨hy,a,ha,b,hb,rfl⟩
  exact (mul_nonneg (hq0 y hy a ha) (hr0 y hy b hb)).trans
    (Decreasing.le_of_lt (completedProfileProduct B q r hB hqi hri hq0 hr0).property.1 hv hw hxy)

theorem completedProfileProduct_selection {q r : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {s t : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (ht : SelectionOn r.val (Ioo (0 : ℝ) B) t) :
    SelectionOn (completedProfileProduct B q r hB hqi hri hq0 hr0).val
      (Ioo (0 : ℝ) B) (fun x => s x*t x) := by
  intro x hx
  exact completedProfileProduct_raw_inclusion hB hqi hri hq0 hr0 x ⟨hx,s x,hs x hx,t x,ht x hx,rfl⟩

theorem completedProfileProduct_unique {q r : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {f : Operator} (hf : MaximalDecreasing f)
    (hpf : interiorProfileProduct B q.val r.val ≤ f)
    (hfd : dom f ⊆ closure (Ioo (0 : ℝ) B)) :
    f = (completedProfileProduct B q r hB hqi hri hq0 hr0).val := by
  apply (unique_maximal_decreasing_completion ordConnected_Ioo (nonempty_Ioo.mpr hB)
    (interiorProfileProduct_decreasing q.property.1 r.property.1 hq0 hr0)
    (interiorProfileProduct_domain hqi hri)).unique
  · exact ⟨hf,hpf,hfd⟩
  · exact ⟨(completedProfileProduct B q r hB hqi hri hq0 hr0).property,
      completedProfileProduct_raw_inclusion hB hqi hri hq0 hr0,
      (completedProfileProduct_domain hB hqi hri hq0 hr0).2⟩

end ScalarMonotone.EndOfPaper
end
