import EndOfPaper.FiniteGeometricProduct
import EndOfPaper.ProfileLogAdmissibility

/-!
Derived individual logarithmic areas and the actual
geometric finite control-product profile from the original
single combined area, without additional final hypotheses.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem randomized_individual_log_areas {n : ℕ} {qΔ : DecGraph} {q : Fin n → DecGraph}
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞) :
    (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sqΔ p)) 0)) < ∞ ∧
      ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p)) 0)) < ∞ := by
  classical
  let Q : Option (Fin n) → DecGraph := fun j => match j with | none => qΔ | some i => q i
  let S : Option (Fin n) → ℝ → ℝ := fun j => match j with | none => sqΔ | some i => sq i
  have h0 (j : Option (Fin n)) : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (Q j).val p, 0 ≤ v := by
    cases j with
    | none => exact hδ0
    | some i => exact hq0 i
  have hn (j : Option (Fin n)) : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (Q j).val p, v = 0 := by
    cases j with
    | none => exact hnδ
    | some i => exact hnq i
  have hSel (j : Option (Fin n)) : SelectionOn (Q j).val (Ioo (0 : ℝ) 1) (S j) := by
    cases j with
    | none => exact hsδ
    | some i => exact hsq i
  have he (p : ℝ) : (∏ j : Option (Fin n), S j p) = sqΔ p*(∏ i, sq i p) := by
    rw [Fintype.prod_option]
  have hAll : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (∏ j : Option (Fin n), S j p)) 0)) < ∞ := by
    simp_rw [he]
    exact hP
  have hAreas := nonzero_profiles_individual_log_areas (by norm_num)
    (fun j => (Q j).property) h0 hn hSel hAll
  exact ⟨hAreas none,fun i => hAreas (some i)⟩

def geometricFiniteProfileProduct {ι : Type*} [Fintype ι] (q : ι → DecGraph)
    (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val x, 0 ≤ v)
    {s : ι → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hPi : ∀ i, (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞) : DecGraph := by
  classical
  let P := completedFiniteProfileProduct 1 q (by norm_num) hqi hq0
  refine ⟨geometricHardyTransform 1 P,?_⟩
  have he := geometric_hardy_finite_product (by norm_num) hqi hq0 hs hPi
  rw [he]
  exact (completedFiniteProfileProduct 1
    (fun i => ⟨geometricHardyTransform 1 (q i),
      (geometricHardyTransform_well_defined_any_selection (by norm_num) (hqi i) (hq0 i) (hs i) (hPi i)).1⟩)
    (by norm_num)
    (fun i => (geometricHardyTransform_well_defined_any_selection (by norm_num) (hqi i) (hq0 i) (hs i) (hPi i)).2.1)
    (fun i => (geometricHardyTransform_well_defined_any_selection (by norm_num) (hqi i) (hq0 i) (hs i) (hPi i)).2.2.1)).property

theorem geometricFiniteProfileProduct_properties {ι : Type*} [Fintype ι] {q : ι → DecGraph}
    (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val x, 0 ≤ v)
    {s : ι → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hPi : ∀ i, (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞) :
    let G := geometricFiniteProfileProduct q hqi hq0 hs hPi
    interior (dom G.val) = Ioo (0 : ℝ) 1 ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ G.val x, 0 ≤ v) ∧
      SelectionOn G.val (Ioo (0 : ℝ) 1) (fun x => ∏ i, geometricPrefixValue (s i) x) := by
  classical
  let hGi := fun i => geometricHardyTransform_well_defined_any_selection (by norm_num) (hqi i) (hq0 i) (hs i) (hPi i)
  let Gi : ι → DecGraph := fun i => ⟨geometricHardyTransform 1 (q i),(hGi i).1⟩
  let R := completedFiniteProfileProduct 1 Gi (by norm_num) (fun i => (hGi i).2.1) (fun i => (hGi i).2.2.1)
  have he : (geometricFiniteProfileProduct q hqi hq0 hs hPi).val = R.val :=
    geometric_hardy_finite_product (by norm_num) hqi hq0 hs hPi
  dsimp only
  rw [he]
  refine ⟨(completedFiniteProfileProduct_domain (by norm_num) (fun i => (hGi i).2.1) (fun i => (hGi i).2.2.1)).1,
    completedFiniteProfileProduct_nonnegative (by norm_num) (fun i => (hGi i).2.1) (fun i => (hGi i).2.2.1),?_⟩
  exact completedFiniteProfileProduct_selection (by norm_num) (fun i => (hGi i).2.1)
    (fun i => (hGi i).2.2.1)
    (fun i => geometric_hardy_scalar_selection (by norm_num) (hqi i) (hq0 i) (hs i) (hPi i))

end ScalarMonotone.EndOfPaper
end
