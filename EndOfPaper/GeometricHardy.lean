import EndOfPaper.ExponentialCompletion
import EndOfPaper.LogGeometricDomain

/-!
The actual lattice-floor/logarithm/Hardy/exponential
construction and its unique nonnegative maximal extension. The
zero convention is literal; logarithmic prefix L1 is derived.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem raw_exponential_le_iff {f g : Operator} :
    comp (ofFun Real.exp) f ≤ g ↔ ∀ x w, w ∈ f x → Real.exp w ∈ g x := by
  constructor
  · intro h x w hw
    exact h x ⟨w,hw,rfl⟩
  · rintro h x v ⟨w,hw,hv⟩
    change v = Real.exp w at hv
    simpa only [hv] using h x w hw

/-- The manuscript's literal logarithm/Hardy/exponential construction, with
all logarithmic prefix L1 and domain obligations derived from log-plus L1. -/
theorem positive_geometric_hardy_extension {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (hpositive : ∃ a ∈ Ioo (0 : ℝ) B, ∃ v ∈ q a, 0 < v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    let L := logOp (nonnegativeFloorGraph (⟨q,hq⟩ : DecGraph)).val
    let H := hardyFamilyIntegral (interior (dom L)) L
    ∃! g : Operator, MaximalDecreasing g ∧
      interior (dom g) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
      comp (ofFun Real.exp) H ≤ g := by
  dsimp only
  rw [logarithm_nonnegative_floor]
  obtain ⟨hL,hLd,hLz,hLp⟩ := logarithm_initial_domain hB hq hqi hpositive
  obtain ⟨hsel,hprefix⟩ := logarithmic_prefix_integrability hB hq hqi hm hs hi
  let H := hardyFamilyIntegral (interior (dom (logOp q))) (logOp q)
  have hH := hardyFamilyIntegral_of_locally_integrable hL hLz hLp hsel hprefix
  have hHd : dom H ⊆ Icc (0 : ℝ) B := by
    apply hH.2.2.1.trans
    exact closure_minimal (interior_subset.trans hLd) isClosed_Icc
  have hne : (interior (dom (logOp q))).Nonempty :=
    (decreasing_zero_inf_domain_geometry hL hLz hLp).2.1
  have hzero : (0 : ℝ) ∈ closure (interior (dom (logOp q))) :=
    zero_mem_closure_decreasing_domain_interior hL hLz hne
  have hI : interior (dom (logOp q)) ⊆ dom H := by
    intro x hx
    apply interior_subset
    rwa [hH.2.1]
  have hzeroH : (0 : ℝ) ∈ closure (dom H) := closure_mono hI hzero
  have hHz : IsGLB (dom H) 0 := by
    refine ⟨fun x hx => (hHd hx).1, ?_⟩
    intro b hb
    exact closure_minimal (show dom H ⊆ Ici b from hb) isClosed_Ici hzeroH
  simpa only [raw_exponential_le_iff] using
    unique_initial_exponential_completion hB hH.1 hHd hHz

theorem geometric_hardy_extension_of_nonzero {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, 0 ≤ v)
    (hnonzero : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    let L := logOp (nonnegativeFloorGraph (⟨q,hq⟩ : DecGraph)).val
    let H := hardyFamilyIntegral (interior (dom L)) L
    ∃! g : Operator, MaximalDecreasing g ∧
      interior (dom g) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
      comp (ofFun Real.exp) H ≤ g := by
  classical
  push_neg at hnonzero
  obtain ⟨a,ha,v,hv,hvn⟩ := hnonzero
  have hvpos : 0 < v := lt_of_le_of_ne (hq0 a ha v hv) (Ne.symm hvn)
  exact positive_geometric_hardy_extension hB hq hqi ⟨a,ha,v,hv,hvpos⟩ hm hs hi

def geometricHardyExtensionPredicate (B : ℝ) (q : DecGraph) (g : Operator) : Prop :=
  let L := logOp (nonnegativeFloorGraph q).val
  MaximalDecreasing g ∧ interior (dom g) = Ioo (0 : ℝ) B ∧
    (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
    comp (ofFun Real.exp) (hardyFamilyIntegral (interior (dom L)) L) ≤ g

/-- The zero convention is literal. On the manuscript's admissible class,
the existence theorem discharges the conditional choice in the second branch. -/
def geometricHardyTransform (B : ℝ) (q : DecGraph) : Operator := by
  classical
  exact if ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0 then q.val
    else if h : ∃! g, geometricHardyExtensionPredicate B q g then h.choose else q.val

theorem geometricHardyTransform_zero {B : ℝ} {q : DecGraph}
    (hz : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0) :
    geometricHardyTransform B q = q.val := by
  simp only [geometricHardyTransform, if_pos hz]

theorem geometricHardyTransform_well_defined {B : ℝ} {q : DecGraph}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    MaximalDecreasing (geometricHardyTransform B q) ∧
      interior (dom (geometricHardyTransform B q)) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ geometricHardyTransform B q x, 0 ≤ v) ∧
      ((∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0) ∨
        (geometricHardyExtensionPredicate B q (geometricHardyTransform B q) ∧
          ∀ g, geometricHardyExtensionPredicate B q g → g = geometricHardyTransform B q)) := by
  classical
  by_cases hz : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0
  · rw [geometricHardyTransform_zero hz]
    exact ⟨q.property,hqi,hq0,Or.inl hz⟩
  · have hex : ∃! g, geometricHardyExtensionPredicate B q g :=
      geometric_hardy_extension_of_nonzero hB q.property hqi hq0 hz hm hs hi
    have hchoice := hex.choose_spec
    have hG : geometricHardyTransform B q = hex.choose := by
      simp only [geometricHardyTransform, if_neg hz, dif_pos hex]
    rw [hG]
    exact ⟨hchoice.1.1,hchoice.1.2.1,hchoice.1.2.2.1,Or.inr hchoice⟩


end ScalarMonotone.EndOfPaper
end
