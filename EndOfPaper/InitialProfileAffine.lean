import EndOfPaper.GeometricScalarCompletion

/-!
Literal affine images of whole interior graph fibers and their unique maximal completion, including zero scales.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

def interiorProfileAffine (B m c : ℝ) (q : Operator) : Operator := fun x =>
  {v | x ∈ Ioo (0 : ℝ) B ∧ ∃ a ∈ q x, v = m+c*a}

theorem interiorProfileAffine_decreasing {B m c : ℝ} {q : Operator}
    (hq : Decreasing q) (hc : 0 ≤ c) : Decreasing (interiorProfileAffine B m c q) := by
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  change -u ∈ interiorProfileAffine B m c q x at hu
  change -v ∈ interiorProfileAffine B m c q y at hv
  rcases hu with ⟨_, a, ha, heu⟩
  rcases hv with ⟨_, b, hb, hev⟩
  have hh := mul_le_mul_of_nonneg_left (Decreasing.le_of_lt hq ha hb hxy) hc
  linarith

theorem interiorProfileAffine_domain {B m c : ℝ} {q : Operator}
    (hqi : interior (dom q) = Ioo (0 : ℝ) B) :
    dom (interiorProfileAffine B m c q) = Ioo (0 : ℝ) B := by
  ext x
  constructor
  · rintro ⟨v,hx,_⟩
    exact hx
  · intro hx
    obtain ⟨a,ha⟩ := interior_subset (show x ∈ interior (dom q) from by rwa [hqi])
    exact ⟨m+c*a,hx,a,ha,rfl⟩

def completedProfileAffine (B m c : ℝ) (q : DecGraph)
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B) (hc : 0 ≤ c) : DecGraph := by
  let A := interiorProfileAffine B m c q.val
  refine ⟨negOut (completion (Ioo (0 : ℝ) B) (negOut A)),?_⟩
  change MaximalIncreasing (negOut (negOut (completion (Ioo (0 : ℝ) B) (negOut A))))
  rw [negOut_negOut]
  apply completion_maximal ordConnected_Ioo (nonempty_Ioo.mpr hB)
    (interiorProfileAffine_decreasing q.property.1 hc)
  rw [dom_negOut]
  exact interiorProfileAffine_domain hqi

theorem completedProfileAffine_raw_inclusion {B m c : ℝ} {q : DecGraph}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B) (hc : 0 ≤ c) :
    interiorProfileAffine B m c q.val ≤ (completedProfileAffine B m c q hB hqi hc).val := by
  let A := interiorProfileAffine B m c q.val
  have hA : Increasing (negOut A) := interiorProfileAffine_decreasing q.property.1 hc
  have hd : dom (negOut A) = Ioo (0 : ℝ) B := by
    rw [dom_negOut]
    exact interiorProfileAffine_domain hqi
  intro x v hv
  change -v ∈ completion (Ioo (0 : ℝ) B) (negOut A) x
  apply le_completion hA hd x
  change -(-v) ∈ A x
  simpa only [neg_neg] using hv

theorem completedProfileAffine_domain {B m c : ℝ} {q : DecGraph}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B) (hc : 0 ≤ c) :
    let A := completedProfileAffine B m c q hB hqi hc
    interior (dom A.val) = Ioo (0 : ℝ) B ∧ dom A.val ⊆ closure (Ioo (0 : ℝ) B) := by
  let A := completedProfileAffine B m c q hB hqi hc
  have hd : dom A.val ⊆ closure (Ioo (0 : ℝ) B) := by
    change dom (negOut (completion (Ioo (0 : ℝ) B) (negOut (interiorProfileAffine B m c q.val)))) ⊆ _
    simpa only [dom_negOut] using completion_dom_subset (Ioo (0 : ℝ) B) (negOut (interiorProfileAffine B m c q.val))
  have hi : Ioo (0 : ℝ) B ⊆ dom A.val := by
    intro x hx
    obtain ⟨v,hv⟩ := (show x ∈ dom (interiorProfileAffine B m c q.val) from by
      rwa [interiorProfileAffine_domain hqi])
    exact ⟨v,completedProfileAffine_raw_inclusion hB hqi hc x hv⟩
  exact ⟨domain_interior_of_open_interval isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr hB) hi hd,hd⟩

theorem completedProfileAffine_nonnegative {B m c : ℝ} {q : DecGraph}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ a ∈ q.val x, 0 ≤ a) :
    ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ (completedProfileAffine B m c q hB hqi hc).val x, 0 ≤ v := by
  intro x hx v hv
  let y := (x+B)/2
  have hy : y ∈ Ioo (0 : ℝ) B := ⟨by dsimp [y]; linarith [hx.1],by dsimp [y]; linarith [hx.2]⟩
  have hxy : x < y := by dsimp [y]; linarith [hx.2]
  obtain ⟨a,ha⟩ := interior_subset (show y ∈ interior (dom q.val) from by rwa [hqi])
  have hw : m+c*a ∈ (completedProfileAffine B m c q hB hqi hc).val y :=
    completedProfileAffine_raw_inclusion hB hqi hc y ⟨hy,a,ha,rfl⟩
  exact (add_nonneg hm (mul_nonneg hc (hq0 y hy a ha))).trans
    (Decreasing.le_of_lt (completedProfileAffine B m c q hB hqi hc).property.1 hv hw hxy)

theorem completedProfileAffine_selection {B m c : ℝ} {q : DecGraph}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B) (hc : 0 ≤ c)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s) :
    SelectionOn (completedProfileAffine B m c q hB hqi hc).val (Ioo (0 : ℝ) B) (fun x => m+c*s x) := by
  intro x hx
  exact completedProfileAffine_raw_inclusion hB hqi hc x ⟨hx,s x,hs x hx,rfl⟩

theorem completedProfileAffine_unique {B m c : ℝ} {q : DecGraph}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B) (hc : 0 ≤ c)
    {f : Operator} (hf : MaximalDecreasing f)
    (haf : interiorProfileAffine B m c q.val ≤ f) (hfd : dom f ⊆ closure (Ioo (0 : ℝ) B)) :
    f = (completedProfileAffine B m c q hB hqi hc).val := by
  apply (unique_maximal_decreasing_completion ordConnected_Ioo (nonempty_Ioo.mpr hB)
    (interiorProfileAffine_decreasing q.property.1 hc) (interiorProfileAffine_domain hqi)).unique
  · exact ⟨hf,haf,hfd⟩
  · exact ⟨(completedProfileAffine B m c q hB hqi hc).property,
      completedProfileAffine_raw_inclusion hB hqi hc,(completedProfileAffine_domain hB hqi hc).2⟩

end ScalarMonotone.EndOfPaper
end
