import EndOfPaper.ScalarIntegration
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Tactic

/-!
Full scalar integration conventions (def:area): selection independence,
infinite endpoints, endpoint addition/deletion, signed orientation and
equal limits. The extended signed integral is Option EReal: none means
precisely that both nonnegative signed parts are infinite. Its finite
integrable value is proved equal to the ordinary Bochner integral.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- `none` is precisely the undefined infinity-minus-infinity case. -/
def signedExtendedIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Ω → ℝ) : Option EReal :=
  let P := ∫⁻ x, ENNReal.ofReal (s x) ∂μ
  let N := ∫⁻ x, ENNReal.ofReal (-s x) ∂μ
  if P = ∞ ∧ N = ∞ then none else some ((P : EReal)-(N : EReal))

theorem signedExtendedIntegral_eq_none_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Ω → ℝ) :
    signedExtendedIntegral μ s = none ↔
      (∫⁻ x, ENNReal.ofReal (s x) ∂μ) = ∞ ∧
        (∫⁻ x, ENNReal.ofReal (-s x) ∂μ) = ∞ := by
  simp [signedExtendedIntegral]

theorem signedExtendedIntegral_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s t : Ω → ℝ} (hst : s =ᵐ[μ] t) :
    signedExtendedIntegral μ s = signedExtendedIntegral μ t := by
  have hp := lintegral_congr_ae (hst.fun_comp ENNReal.ofReal)
  have hn := lintegral_congr_ae (hst.fun_comp (fun v => ENNReal.ofReal (-v)))
  simp only [Function.comp_apply] at hp hn
  simp only [signedExtendedIntegral, hp, hn]

theorem signedExtendedIntegral_neg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Ω → ℝ) :
    signedExtendedIntegral μ (fun x => -s x) =
      (signedExtendedIntegral μ s).map (fun v => -v) := by
  let P := ∫⁻ x, ENNReal.ofReal (s x) ∂μ
  let N := ∫⁻ x, ENNReal.ofReal (-s x) ∂μ
  simp only [signedExtendedIntegral, neg_neg]
  change (if N = ∞ ∧ P = ∞ then none else some ((N : EReal)-(P : EReal))) =
    (if P = ∞ ∧ N = ∞ then none else some ((P : EReal)-(N : EReal))).map (fun v => -v)
  by_cases h : P = ∞ ∧ N = ∞
  · simp [h.1, h.2]
  · have h' : ¬ (N = ∞ ∧ P = ∞) := fun hh => h hh.symm
    simp only [if_neg h, if_neg h']
    change some ((N : EReal)-(P : EReal)) = some (-((P : EReal)-(N : EReal)))
    congr 1
    have ht : (P : EReal) ≠ ⊤ ∨ (N : EReal) ≠ ⊤ := by
      rcases not_and_or.mp h with hP | hN
      · exact Or.inl (fun he => hP (EReal.coe_ennreal_eq_top_iff.mp he))
      · exact Or.inr (fun he => hN (EReal.coe_ennreal_eq_top_iff.mp he))
    rw [EReal.neg_sub (Or.inl (EReal.coe_ennreal_ne_bot P)) ht]
    simp only [sub_eq_add_neg, add_comm]

theorem signedExtendedIntegral_zero_measure {Ω : Type*} [MeasurableSpace Ω]
    (s : Ω → ℝ) : signedExtendedIntegral (0 : Measure Ω) s = some 0 := by
  simp [signedExtendedIntegral]

theorem signedExtendedIntegral_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Ω → ℝ} (hs : Integrable s μ) :
    signedExtendedIntegral μ s = some (Real.toEReal (∫ x, s x ∂μ)) := by
  have hi : (∫⁻ x, ENNReal.ofReal |s x| ∂μ) < ∞ := by
    simpa only [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm s).mp hs.hasFiniteIntegral
  have hp : (∫⁻ x, ENNReal.ofReal (s x) ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (le_abs_self (s x))))
      hi
  have hn : (∫⁻ x, ENNReal.ofReal (-s x) ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (neg_le_abs (s x))))
      hi
  simp only [signedExtendedIntegral, hp, false_and, ↓reduceIte, Option.some.injEq]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hs, EReal.coe_sub,
    EReal.coe_ennreal_toReal hp, EReal.coe_ennreal_toReal hn]

theorem selection_aemeasurable {f : Operator} (hf : Increasing f ∨ Decreasing f)
    {I : Set ℝ} (hI : MeasurableSet I) {s : ℝ → ℝ} (hs : SelectionOn f I s)
    (μ : Measure ℝ) : AEMeasurable s (μ.restrict I) := by
  rcases hf with hf | hf
  · exact aemeasurable_restrict_of_monotoneOn hI (selection_monotoneOn hf hs)
  · exact aemeasurable_restrict_of_antitoneOn hI (selection_antitoneOn hf hs)

theorem selection_integrable_iff_absolute_area_finite {f : Operator}
    (hf : Increasing f ∨ Decreasing f) {I : Set ℝ} (hI : MeasurableSet I)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) (μ : Measure ℝ) :
    Integrable s (μ.restrict I) ↔
      (∫⁻ x in I, ENNReal.ofReal |s x| ∂μ) < ∞ := by
  rw [Integrable, hasFiniteIntegral_iff_norm]
  simp only [(selection_aemeasurable hf hI hs μ).aestronglyMeasurable,
    true_and, Real.norm_eq_abs]

theorem selection_signedExtendedIntegral_eq {f : Operator}
    (hf : Increasing f ∨ Decreasing f) {I : Set ℝ} (hI : MeasurableSet I)
    {s t : ℝ → ℝ} (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (ψ : ℝ → ℝ) :
    signedExtendedIntegral (μ.restrict I) (fun x => ψ (s x)) =
      signedExtendedIntegral (μ.restrict I) (fun x => ψ (t x)) := by
  have he := selection_signed_parts_eq hf hI hs ht μ ψ
  simp only [signedExtendedIntegral, he.1, he.2]

def extendedOpenInterval (a b : EReal) : Set ℝ := {x | a < (x : EReal) ∧ (x : EReal) < b}

theorem extendedOpenInterval_measurable (a b : EReal) : MeasurableSet (extendedOpenInterval a b) :=
  measurableSet_Ioo.preimage measurable_coe_real_ereal

theorem extended_endpoint_ae_ne (μ : Measure ℝ) [NoAtoms μ] (a : EReal) :
    ∀ᵐ (x : ℝ) ∂μ, (x : EReal) ≠ a := by
  induction a with
  | bot => exact Eventually.of_forall (fun x => EReal.coe_ne_bot x)
  | coe a =>
    filter_upwards [(Set.countable_singleton a).ae_not_mem μ] with x hx
    intro he
    apply hx
    exact EReal.coe_injective he
  | top => exact Eventually.of_forall (fun x => EReal.coe_ne_top x)

theorem extendedInterval_restrict_endpoints (μ : Measure ℝ) [NoAtoms μ] (a b : EReal) :
    μ.restrict (extendedOpenInterval a b) =
      μ.restrict {x : ℝ | a ≤ (x : EReal) ∧ (x : EReal) ≤ b} := by
  apply Measure.restrict_congr_set
  filter_upwards [extended_endpoint_ae_ne μ a, extended_endpoint_ae_ne μ b] with x hxa hxb
  apply propext
  change (a < (x : EReal) ∧ (x : EReal) < b) ↔ (a ≤ (x : EReal) ∧ (x : EReal) ≤ b)
  constructor
  · intro hx
    exact ⟨hx.1.le, hx.2.le⟩
  · intro hx
    exact ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩

/-- Signed integral with finite or infinite limits and the stated orientation. -/
def orientedExtendedIntegral (a b : EReal) (s : ℝ → ℝ) : Option EReal :=
  if a ≤ b then signedExtendedIntegral (volume.restrict (extendedOpenInterval a b)) s
  else (signedExtendedIntegral (volume.restrict (extendedOpenInterval b a)) s).map (fun v => -v)

theorem orientedExtendedIntegral_self (a : EReal) (s : ℝ → ℝ) :
    orientedExtendedIntegral a a s = some 0 := by
  have he : extendedOpenInterval a a = ∅ := by
    ext x
    simp only [extendedOpenInterval, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun ha => not_lt_of_ge ha.le
  simp [orientedExtendedIntegral, he, signedExtendedIntegral_zero_measure]

theorem orientedExtendedIntegral_reverse (a b : EReal) (s : ℝ → ℝ) :
    orientedExtendedIntegral b a s = (orientedExtendedIntegral a b s).map (fun v => -v) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp [orientedExtendedIntegral, hab.le, not_le_of_gt hab]
  · simp [orientedExtendedIntegral_self]
  · simp only [orientedExtendedIntegral, hba.le, not_le_of_gt hba, ↓reduceIte]
    cases signedExtendedIntegral (volume.restrict (extendedOpenInterval b a)) s <;> simp

theorem orientedExtendedIntegral_selection_eq {f : Operator}
    (hf : Increasing f ∨ Decreasing f) (a b : EReal) {s t : ℝ → ℝ}
    (hs : SelectionOn f (extendedOpenInterval (min a b) (max a b)) s)
    (ht : SelectionOn f (extendedOpenInterval (min a b) (max a b)) t)
    (ψ : ℝ → ℝ) :
    orientedExtendedIntegral a b (fun x => ψ (s x)) =
      orientedExtendedIntegral a b (fun x => ψ (t x)) := by
  rcases le_total a b with hab | hba
  · simp only [min_eq_left hab, max_eq_right hab] at hs ht
    simp only [orientedExtendedIntegral, if_pos hab]
    exact selection_signedExtendedIntegral_eq hf (extendedOpenInterval_measurable a b) hs ht volume ψ
  · simp only [min_eq_right hba, max_eq_left hba] at hs ht
    by_cases hab : a ≤ b
    · have he : a = b := le_antisymm hab hba
      subst b
      simp only [orientedExtendedIntegral_self]
    · simp only [orientedExtendedIntegral, if_neg hab]
      rw [selection_signedExtendedIntegral_eq hf (extendedOpenInterval_measurable b a) hs ht volume ψ]

theorem orientedExtendedIntegral_finite_of_integrable {a b : ℝ} (hab : a ≤ b)
    {s : ℝ → ℝ} (hs : Integrable s (volume.restrict (Ioo a b))) :
    orientedExtendedIntegral (a : EReal) (b : EReal) s =
      some (Real.toEReal (∫ x in Ioo a b, s x)) := by
  have he : extendedOpenInterval (a : EReal) (b : EReal) = Ioo a b := by
    ext x
    simp [extendedOpenInterval]
  rw [orientedExtendedIntegral, if_pos (by exact_mod_cast hab), he]
  exact signedExtendedIntegral_of_integrable hs

theorem extendedInterval_restrict_between_endpoints (μ : Measure ℝ) [NoAtoms μ]
    (a b : EReal) {J : Set ℝ} (hlo : extendedOpenInterval a b ⊆ J)
    (hhi : J ⊆ {x : ℝ | a ≤ (x : EReal) ∧ (x : EReal) ≤ b}) :
    μ.restrict (extendedOpenInterval a b) = μ.restrict J := by
  apply Measure.restrict_congr_set
  filter_upwards [extended_endpoint_ae_ne μ a, extended_endpoint_ae_ne μ b] with x hxa hxb
  apply propext
  constructor
  · exact fun hx => hlo hx
  · intro hx
    exact ⟨lt_of_le_of_ne (hhi hx).1 hxa.symm, lt_of_le_of_ne (hhi hx).2 hxb⟩

theorem selection_borel_expression_aemeasurable {f : Operator}
    (hf : Increasing f ∨ Decreasing f) {I : Set ℝ} (hI : MeasurableSet I)
    {s : ℝ → ℝ} (hs : SelectionOn f I s) (μ : Measure ℝ)
    {ψ : ℝ → ℝ} (hψ : Measurable ψ) :
    AEMeasurable (fun x => ψ (s x)) (μ.restrict I) :=
  hψ.comp_aemeasurable (selection_aemeasurable hf hI hs μ)

/-- All scalar expressions are well defined by measurable selections;
integrability is exactly finiteness of absolute area, with no finite interval
or finite signed-integral restriction. -/
theorem scalar_integration_well_defined {f : Operator}
    (hf : Increasing f ∨ Decreasing f) {I : Set ℝ} (hI : MeasurableSet I)
    (hdom : I ⊆ dom f) :
    ∃ s : ℝ → ℝ, Measurable s ∧ SelectionOn f I s ∧
      ∀ t : ℝ → ℝ, SelectionOn f I t →
        (Integrable t (volume.restrict I) ↔ (∫⁻ x in I, ENNReal.ofReal |s x|) < ∞) ∧
        (∀ ψ : ℝ → ℝ≥0∞, (∫⁻ x in I, ψ (s x)) = ∫⁻ x in I, ψ (t x)) ∧
        (∀ ψ : ℝ → ℝ, signedExtendedIntegral (volume.restrict I) (fun x => ψ (s x)) =
          signedExtendedIntegral (volume.restrict I) (fun x => ψ (t x))) ∧
        (Integrable s (volume.restrict I) →
          aumannIntegral (volume.restrict I) f = {∫ x in I, s x}) := by
  obtain ⟨s, hsm, hs⟩ := exists_global_measurable_selection hf hI hdom
  refine ⟨s, hsm, hs, fun t ht => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [selection_integrable_iff_absolute_area_finite hf hI ht volume,
      selection_lintegral_comp_eq hf hI ht hs volume (fun v => ENNReal.ofReal |v|)]
  · exact fun ψ => selection_lintegral_comp_eq hf hI hs ht volume ψ
  · exact fun ψ => selection_signedExtendedIntegral_eq hf hI hs ht volume ψ
  · intro hi
    apply aumannIntegral_monotone_singleton hf _ hi
    filter_upwards [ae_restrict_mem hI] with x hx
    exact hs x hx

end ScalarMonotone.EndOfPaper
end
