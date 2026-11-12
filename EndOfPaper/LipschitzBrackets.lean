import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
The actual two extremal Lipschitz extensions and their
two-sublevel bracketing property. The exact pointwise two-tail
indicator inequality is proved for logarithmic endpoint control.
-/

open Set
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def upperLipschitzExtension {E : Type*} [PseudoMetricSpace E]
    (A : Set E) (h : E → ℝ) (K : ℝ≥0) (x : E) : ℝ :=
  ⨅ z : A, h z+(K : ℝ)*dist x z

theorem upperLipschitzExtension_properties {E : Type*} [PseudoMetricSpace E]
    {A : Set E} {h : E → ℝ} {K : ℝ≥0} (hA : A.Nonempty) (hf : LipschitzOnWith K h A) :
    LipschitzWith K (upperLipschitzExtension A h K) ∧
      EqOn h (upperLipschitzExtension A h K) A ∧
      ∀ y, (∀ z ∈ A, h y ≤ h z+(K : ℝ)*dist y z) → h y ≤ upperLipschitzExtension A h K y := by
  have : Nonempty A := by rwa [nonempty_coe_sort]
  have B (y : E) : BddBelow (range (fun z : A => h z+(K : ℝ)*dist y z)) := by
    obtain ⟨z,hz⟩ := hA
    refine ⟨h z-K*dist y z,?_⟩
    rintro w ⟨t,rfl⟩
    dsimp
    rw [sub_le_iff_le_add,add_assoc,← mul_add,add_comm (dist y t)]
    calc
      h z ≤ h t+K*dist z t := hf.le_add_mul hz t.2
      _ ≤ h t+K*(dist y z+dist y t) := by gcongr; apply dist_triangle_left
  refine ⟨LipschitzWith.of_le_add_mul K (fun x y => ?_),?_,?_⟩
  · rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro z
    rw [sub_le_iff_le_add]
    calc
      upperLipschitzExtension A h K x ≤ h z+K*dist x z := ciInf_le (B x) z
      _ ≤ h z+K*dist y z+K*dist x y := by
        rw [add_assoc,← mul_add,add_comm (dist y z)]
        gcongr
        apply dist_triangle
  · intro x hx
    apply le_antisymm (le_ciInf (fun z : A => hf.le_add_mul hx z.2))
    simpa only [upperLipschitzExtension,Subtype.coe_mk,dist_self,mul_zero,add_zero] using
      ciInf_le (B x) ⟨x,hx⟩
  · intro y hy
    exact le_ciInf (fun z : A => hy z z.2)

theorem lipschitz_extremal_brackets {E : Type*} [PseudoMetricSpace E]
    {A : Set E} {h : E → ℝ} {K : ℝ≥0} (hA : A.Nonempty) (hf : LipschitzOnWith K h A) :
    ∃ l u : E → ℝ, LipschitzWith K l ∧ LipschitzWith K u ∧ EqOn h l A ∧ EqOn h u A ∧
      ∀ y, (∀ z ∈ A, |h y-h z| ≤ (K : ℝ)*dist y z) → l y ≤ h y ∧ h y ≤ u y := by
  have hn : LipschitzOnWith K (fun x => -h x) A :=
    LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
      simpa only [dist_neg_neg] using hf.dist_le_mul x hx y hy)
  have hU := upperLipschitzExtension_properties hA hf
  have hN := upperLipschitzExtension_properties hA hn
  let l := fun x => -upperLipschitzExtension A (fun z => -h z) K x
  let u := upperLipschitzExtension A h K
  refine ⟨l,u,?_,hU.1,?_,hU.2.1,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [l,dist_neg_neg] using hN.1.dist_le_mul x y
  · intro x hx
    have he := hN.2.1 hx
    change -h x = upperLipschitzExtension A (fun z => -h z) K x at he
    change h x = -upperLipschitzExtension A (fun z => -h z) K x
    rw [← he,neg_neg]
  · intro y hy
    constructor
    · have he := hN.2.2 y (fun z hz => by
        have hbound := (abs_le.mp (hy z hz)).1
        linarith)
      change -upperLipschitzExtension A (fun z => -h z) K y ≤ h y
      simpa only [neg_neg] using neg_le_neg he
    · exact hU.2.2 y (fun z hz => by
        have hbound := (abs_le.mp (hy z hz)).2
        linarith)

theorem multiplicative_control_lipschitz_on_sublevel {E : Type*} [PseudoMetricSpace E]
    {h U : E → ℝ} {C r s : ℝ} (hC : 0 ≤ C) (hrs : 2*r ≤ s)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y) :
    LipschitzOnWith ⟨C*Real.exp s,mul_nonneg hC (Real.exp_pos s).le⟩ h {x | U x ≤ r} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change U x ≤ r at hx
  change U y ≤ r at hy
  rw [Real.dist_eq]
  have hsum : U x+U y ≤ s := by linarith
  have hcoef := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) hC
  exact (hmod x y).trans (mul_le_mul_of_nonneg_right hcoef dist_nonneg)

theorem two_level_lipschitz_brackets {E : Type*} [PseudoMetricSpace E]
    {h U : E → ℝ} {C r s : ℝ} (hC : 0 ≤ C) (hrs : 2*r ≤ s)
    (hA : {x | U x ≤ r}.Nonempty)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y) :
    ∃ l u : E → ℝ,
      LipschitzWith ⟨C*Real.exp s,mul_nonneg hC (Real.exp_pos s).le⟩ l ∧
      LipschitzWith ⟨C*Real.exp s,mul_nonneg hC (Real.exp_pos s).le⟩ u ∧
      EqOn h l {x | U x ≤ r} ∧ EqOn h u {x | U x ≤ r} ∧
      ∀ y, U y ≤ s-r → l y ≤ h y ∧ h y ≤ u y := by
  obtain ⟨l,u,hLl,hLu,heL,heU,hbr⟩ := lipschitz_extremal_brackets hA
    (multiplicative_control_lipschitz_on_sublevel hC hrs hmod)
  refine ⟨l,u,hLl,hLu,heL,heU,?_⟩
  intro y hy
  apply hbr y
  intro z hz
  have hsum : U y+U z ≤ s := by change U z ≤ r at hz; linarith
  exact (hmod y z).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) hC) dist_nonneg)

theorem bracket_tail_implication {E : Type*} {A B : Set E} {h l u : E → ℝ}
    (hL : EqOn h l A) (hU : EqOn h u A)
    (hbr : ∀ y ∈ B, l y ≤ h y ∧ h y ≤ u y)
    {x y : E} (hx : x ∈ A) (hy : y ∈ B) {τ : ℝ} (hD : τ < |h x-h y|) :
    τ < |l x-l y| ∨ τ < |u x-u y| := by
  have heL := hL hx
  have heU := hU hx
  have hby := hbr y hy
  rcases lt_abs.mp hD with hpos | hneg
  · left
    exact (show τ < l x-l y by linarith [hby.1]).trans_le (le_abs_self _)
  · right
    exact (show τ < -(u x-u y) by linarith [hby.2]).trans_le (neg_le_abs _)

open scoped Classical ENNReal in
theorem bracket_two_tail_indicator_bound {E : Type*} {A B : Set E} {h l u : E → ℝ}
    (hAB : A ⊆ B) (hL : EqOn h l A) (hU : EqOn h u A)
    (hbr : ∀ y ∈ B, l y ≤ h y ∧ h y ≤ u y) (x y : E) (τ : ℝ) :
    ((if τ < |h x-h y| ∧ x ∈ A ∧ y ∈ B then 1 else 0)+
        (if τ < |h x-h y| ∧ y ∈ A ∧ x ∈ B then 1 else 0) : ℝ≥0∞) ≤
      (if τ < |l x-l y| then 1 else 0)+(if τ < |u x-u y| then 1 else 0) := by
  by_cases hD : τ < |h x-h y|
  · by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · have hDl : τ < |l x-l y| := by simpa only [← hL hxA,← hL hyA] using hD
        have hDu : τ < |u x-u y| := by simpa only [← hU hxA,← hU hyA] using hD
        simp [hD,hxA,hyA,hAB hxA,hAB hyA,hDl,hDu]
      · by_cases hyB : y ∈ B
        · rcases bracket_tail_implication hL hU hbr hxA hyB hD with hl | hu
          all_goals split_ifs <;> simp_all
        · simp [hD,hxA,hyA,hyB]
    · by_cases hyA : y ∈ A
      · by_cases hxB : x ∈ B
        · have hDyx : τ < |h y-h x| := by simpa only [abs_sub_comm] using hD
          have hor : τ < |l x-l y| ∨ τ < |u x-u y| := by
            simpa only [abs_sub_comm] using bracket_tail_implication hL hU hbr hyA hxB hDyx
          rcases hor with hl | hu
          all_goals split_ifs <;> simp_all
        · simp [hD,hxA,hyA,hxB]
      · simp [hxA,hyA]
  · simp [hD]

end ScalarMonotone.EndOfPaper
end
