import EndOfPaper.NetworkTailProfileDefinition
import EndOfPaper.NetworkProfileGeometry
import EndOfPaper.NetworkObservation

/-!
Maximality, exact probability domain and an actual geometric product selection for the literal network target, with all areas derived.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_tail_profile_geometry {L N : ℕ} {p : ℕ → ℕ} (hpL : 0 < p L)
    {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {mx : ℝ} {mw : Fin L → ℝ} (hmx : 0 ≤ mx) (hmw : ∀ i, 0 ≤ mw i) :
    MaximalDecreasing (networkTailProfile N p q hqi mx mw) ∧
      interior (dom (networkTailProfile N p q hqi mx mw)) = Ioo (0 : ℝ) 1 ∧
      SelectionOn (networkTailProfile N p q hqi mx mw) (Ioo (0 : ℝ) 1)
        (fun u => networkPrefactor L N p*s (u/6)*
          (∏ i, geometricPrefixValue
            (fun x => max mx (mw i)+networkInverseDimension N p i*s x) (u/12))) := by
  classical
  let r := networkAffineInputProfile N p q hqi mx mw
  let sr := fun i : Fin L => fun x : ℝ => max mx (mw i)+networkInverseDimension N p i*s x
  have hm (i : Fin L) : 0 ≤ max mx (mw i) := hmx.trans (le_max_left _ _)
  have hc (i : Fin L) : 0 ≤ networkInverseDimension N p i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hrdom (i : Fin L) : interior (dom (r i).val) = Ioo (0 : ℝ) 1 :=
    (completedProfileAffine_domain (m := max mx (mw i)) (by norm_num) hqi (hc i)).1
  have hr0 (i : Fin L) : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (r i).val x, 0 ≤ v :=
    completedProfileAffine_nonnegative (by norm_num) hqi (hm i) (hc i) hq0
  have hrs (i : Fin L) : SelectionOn (r i).val (Ioo (0 : ℝ) 1) (sr i) :=
    completedProfileAffine_selection (by norm_num) hqi (hc i) hs
  have hrsm (i : Fin L) : Measurable (sr i) := by dsimp only [sr]; fun_prop
  have hrP (i : Fin L) : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sr i x)) 0)) < ∞ :=
    positive_log_area_affine_finite hsm (fun x hx => hq0 x hx _ (hs x hx)) hP (hm i) (hc i)
  have hGi := fun i : Fin L => geometricHardyTransform_well_defined (by norm_num)
    (hrdom i) (hr0 i) (hrsm i) (hrs i) (hrP i)
  let Gi : Fin L → DecGraph := fun i => ⟨geometricHardyTransform 1 (r i),(hGi i).1⟩
  have hGiSel (i : Fin L) : SelectionOn (Gi i).val (Ioo (0 : ℝ) 1) (geometricPrefixValue (sr i)) :=
    geometric_hardy_scalar_selection (by norm_num) (hrdom i) (hr0 i) (hrs i) (hrP i)
  let Q : Option (Fin L) → DecGraph := fun j => match j with
    | none => completedProfileDilation 1 1 (1/6) q hqi (by norm_num) (by norm_num) (by norm_num)
    | some i => completedProfileDilation 1 1 (1/12) (Gi i) (hGi i).2.1
        (by norm_num) (by norm_num) (by norm_num)
  have hQ (j : Option (Fin L)) : interior (dom (Q j).val) = Ioo (0 : ℝ) 1 ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, (Q j).val x = networkTailComponent N p q hqi mx mw j x := by
    cases j with
    | none =>
      have hd : interior (dom (Q none).val) = Ioo (0 : ℝ) 1 ∧
          ∀ x ∈ Ioo (0 : ℝ) 1, (Q none).val x = q.val ((1/6)*x) :=
        completedProfileDilation_properties hqi (by norm_num : (0 : ℝ) < 1)
          (by norm_num : (0 : ℝ) < 1/6) (by norm_num : (1/6 : ℝ)*1 ≤ 1)
      refine ⟨hd.1,?_⟩
      intro x hx
      rw [hd.2 x hx]
      change q.val ((1/6)*x) = q.val (x/6)
      congr 1
      ring
    | some i =>
      have hd : interior (dom (Q (some i)).val) = Ioo (0 : ℝ) 1 ∧
          ∀ x ∈ Ioo (0 : ℝ) 1, (Q (some i)).val x = (Gi i).val ((1/12)*x) :=
        completedProfileDilation_properties (hGi i).2.1 (by norm_num : (0 : ℝ) < 1)
          (by norm_num : (0 : ℝ) < 1/12) (by norm_num : (1/12 : ℝ)*1 ≤ 1)
      refine ⟨hd.1,?_⟩
      intro x hx
      rw [hd.2 x hx]
      change (Gi i).val ((1/12)*x) = (Gi i).val (x/12)
      congr 1
      ring
  have hQ0 (j : Option (Fin L)) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
      (v : ℝ) (hv : v ∈ (Q j).val x) : 0 ≤ v := by
    rw [(hQ j).2 x hx] at hv
    cases j with
    | none => exact hq0 (x/6) ⟨by linarith [hx.1],by linarith [hx.2]⟩ v hv
    | some i => exact (hGi i).2.2.1 (x/12) ⟨by linarith [hx.1],by linarith [hx.2]⟩ v hv
  let S : Option (Fin L) → ℝ → ℝ := fun j => match j with
    | none => fun x => s (x/6)
    | some i => fun x => geometricPrefixValue (sr i) (x/12)
  have hQS (j : Option (Fin L)) : SelectionOn (Q j).val (Ioo (0 : ℝ) 1) (S j) := by
    intro x hx
    rw [(hQ j).2 x hx]
    cases j with
    | none => exact hs (x/6) ⟨by linarith [hx.1],by linarith [hx.2]⟩
    | some i => exact hGiSel i (x/12) ⟨by linarith [hx.1],by linarith [hx.2]⟩
  let P := completedFiniteProfileProduct 1 Q (by norm_num) (fun j => (hQ j).1) hQ0
  have hPD := (completedFiniteProfileProduct_domain (by norm_num) (fun j => (hQ j).1) hQ0).1
  have hPS : SelectionOn P.val (Ioo (0 : ℝ) 1)
      (fun x => s (x/6)*(∏ i, geometricPrefixValue (sr i) (x/12))) := by
    have hh := completedFiniteProfileProduct_selection (by norm_num) (fun j => (hQ j).1) hQ0 hQS
    intro x hx
    have he : (∏ j : Option (Fin L), S j x) = s (x/6)*(∏ i, geometricPrefixValue (sr i) (x/12)) := by
      rw [Fintype.prod_option]
    change s (x/6)*(∏ i, geometricPrefixValue (sr i) (x/12)) ∈ P.val x
    rw [← he]
    exact hh x hx
  have hraw := interiorFiniteProfileProduct_congr_on (fun j x hx => (hQ j).2 x hx)
  have hrawP : P.val = negOut (completion (Ioo (0 : ℝ) 1)
      (negOut (interiorFiniteProfileProduct 1 (networkTailComponent N p q hqi mx mw)))) := by
    change negOut (completion (Ioo (0 : ℝ) 1)
      (negOut (interiorFiniteProfileProduct 1 (fun j => (Q j).val)))) = _
    rw [hraw]
  have hTarget : networkTailProfile N p q hqi mx mw = outputScale (networkPrefactor L N p) P.val := by
    rw [hrawP]
    rfl
  have hD := network_prefactor_pos (N := N) hpL
  refine ⟨?_,?_,?_⟩
  · rw [hTarget]
    exact outputScale_maximal_decreasing hD P.property
  · rw [hTarget,dom_outputScale]
    exact hPD
  · intro x hx
    rw [hTarget]
    exact ⟨_,hPS x hx,by dsimp only [sr]; ring⟩

end ScalarMonotone.EndOfPaper
end
