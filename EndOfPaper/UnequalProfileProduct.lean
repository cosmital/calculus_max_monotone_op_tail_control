import EndOfPaper.GeometricProduct

/-!
Literal completed products at unequal probability levels.
All selected jump values, exact domains and the whole
equal-level dilation identity are retained.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem completedProfileDilation_nonnegative {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈
      (completedProfileDilation 1 1 c q hqi (by norm_num) hc.1 (by simpa using hc.2)).val x,
      0 ≤ v := by
  intro x hx v hv
  have he := (completedProfileDilation_properties (q := q) hqi
    (by norm_num : (0 : ℝ) < 1) hc.1 (by simpa using hc.2)).2 x hx
  rw [he] at hv
  exact hq0 _ (initial_dilation_mapsTo hc.1 (by simpa using hc.2) hx) v hv

def completedUnequalProfileProduct (q r : DecGraph)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ r.val x, 0 ≤ v)
    {α β : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) (hβ : β ∈ Ioc (0 : ℝ) 1) : DecGraph :=
  let dq := completedProfileDilation 1 1 α q hqi (by norm_num) hα.1 (by simpa using hα.2)
  let dr := completedProfileDilation 1 1 β r hri (by norm_num) hβ.1 (by simpa using hβ.2)
  completedProfileProduct 1 dq dr (by norm_num)
    (completedProfileDilation_properties (q := q) hqi (by norm_num) hα.1 (by simpa using hα.2)).1
    (completedProfileDilation_properties (q := r) hri (by norm_num) hβ.1 (by simpa using hβ.2)).1
    (completedProfileDilation_nonnegative hqi hq0 hα)
    (completedProfileDilation_nonnegative hri hr0 hβ)

theorem completedUnequalProfileProduct_properties {q r : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ r.val x, 0 ≤ v)
    {α β : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    let R := completedUnequalProfileProduct q r hqi hri hq0 hr0 hα hβ
    interior (dom R.val) = Ioo (0 : ℝ) 1 ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ R.val x, 0 ≤ v) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ a ∈ q.val (α*x), ∀ b ∈ r.val (β*x), a*b ∈ R.val x) := by
  let dq := completedProfileDilation 1 1 α q hqi (by norm_num) hα.1 (by simpa using hα.2)
  let dr := completedProfileDilation 1 1 β r hri (by norm_num) hβ.1 (by simpa using hβ.2)
  have hDP := completedProfileDilation_properties (q := q) hqi
    (by norm_num : (0 : ℝ) < 1) hα.1 (by simpa using hα.2)
  have hDR := completedProfileDilation_properties (q := r) hri
    (by norm_num : (0 : ℝ) < 1) hβ.1 (by simpa using hβ.2)
  have hD0 := completedProfileDilation_nonnegative hqi hq0 hα
  have hR0 := completedProfileDilation_nonnegative hri hr0 hβ
  change interior (dom (completedProfileProduct 1 dq dr (by norm_num) hDP.1 hDR.1 hD0 hR0).val) = _ ∧ _
  refine ⟨(completedProfileProduct_domain (by norm_num) hDP.1 hDR.1 hD0 hR0).1,
    completedProfileProduct_nonnegative (by norm_num) hDP.1 hDR.1 hD0 hR0,?_⟩
  intro x hx a ha b hb
  have ha' : a ∈ dq.val x := by rw [hDP.2 x hx]; exact ha
  have hb' : b ∈ dr.val x := by rw [hDR.2 x hx]; exact hb
  exact completedProfileProduct_raw_inclusion (by norm_num) hDP.1 hDR.1 hD0 hR0 x
    ⟨hx,a,ha',b,hb',rfl⟩

theorem completedUnequalProfileProduct_selection {q r : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ r.val x, 0 ≤ v)
    {α β : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) (hβ : β ∈ Ioc (0 : ℝ) 1)
    {s t : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (ht : SelectionOn r.val (Ioo (0 : ℝ) 1) t) :
    SelectionOn (completedUnequalProfileProduct q r hqi hri hq0 hr0 hα hβ).val
      (Ioo (0 : ℝ) 1) (fun x => s (α*x)*t (β*x)) := by
  intro x hx
  exact (completedUnequalProfileProduct_properties hqi hri hq0 hr0 hα hβ).2.2 x hx _
    (hs _ (initial_dilation_mapsTo hα.1 (by simpa using hα.2) hx)) _
    (ht _ (initial_dilation_mapsTo hβ.1 (by simpa using hβ.2) hx))

theorem completedUnequalProfileProduct_equal_dilation {q r : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ r.val x, 0 ≤ v)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    {s t : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (ht : SelectionOn r.val (Ioo (0 : ℝ) 1) t) :
    (completedUnequalProfileProduct q r hqi hri hq0 hr0 hc hc).val =
      completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation c (completedProfileProduct 1 q r (by norm_num) hqi hri hq0 hr0).val) := by
  let P := completedProfileProduct 1 q r (by norm_num) hqi hri hq0 hr0
  have hPD := (completedProfileProduct_domain (by norm_num) hqi hri hq0 hr0).1
  let D := completedProfileDilation 1 1 c P hPD (by norm_num) hc.1 (by simpa using hc.2)
  have hDP := completedProfileDilation_properties (q := P) hPD
    (by norm_num : (0 : ℝ) < 1) hc.1 (by simpa using hc.2)
  have hS := completedProfileProduct_selection (by norm_num) hqi hri hq0 hr0 hs ht
  have hDS : SelectionOn D.val (Ioo (0 : ℝ) 1) (fun x => s (c*x)*t (c*x)) := by
    intro x hx
    rw [hDP.2 x hx]
    exact hS _ (initial_dilation_mapsTo hc.1 (by simpa using hc.2) hx)
  exact initial_profile_eq_of_selection_ae_eq (by norm_num)
    (completedUnequalProfileProduct q r hqi hri hq0 hr0 hc hc).property D.property
    (completedUnequalProfileProduct_properties hqi hri hq0 hr0 hc hc).1 hDP.1
    (completedUnequalProfileProduct_selection hqi hri hq0 hr0 hc hc hs ht) hDS
    (Eventually.of_forall (fun _ => rfl))

end ScalarMonotone.EndOfPaper
end
