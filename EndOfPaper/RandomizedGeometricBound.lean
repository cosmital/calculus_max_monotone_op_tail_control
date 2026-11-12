import EndOfPaper.FiniteGeometricProduct
import EndOfPaper.RandomizedTwoParameter
import EndOfPaper.GeometricPrefixLower
import EndOfPaper.QuantileTailCompletion
import Mathlib.Data.Fintype.BigOperators

/-!
The original completed geometric graph bound for randomized
Lipschitz control. The literal combined input product, exact
probability dilation and every endpoint and jump fiber are retained.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def randomizedInputProduct {n : ℕ} (qΔ : DecGraph) (q : Fin n → DecGraph)
    (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v) : DecGraph :=
  let Q : Option (Fin n) → DecGraph := fun j => match j with | none => qΔ | some i => q i
  let hD : ∀ j, interior (dom (Q j).val) = Ioo (0 : ℝ) 1 := fun j => by
    cases j with
    | none => exact hδdom
    | some i => exact hqdom i
  let h0 : ∀ j p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (Q j).val p, 0 ≤ v := fun j => by
    cases j with
    | none => exact hδ0
    | some i => exact hq0 i
  completedFiniteProfileProduct 1 Q (by norm_num) hD h0

theorem randomizedInputProduct_properties {n : ℕ} {qΔ : DecGraph} {q : Fin n → DecGraph}
    (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i)) :
    let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
    interior (dom P.val) = Ioo (0 : ℝ) 1 ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ P.val p, 0 ≤ v) ∧
      SelectionOn P.val (Ioo (0 : ℝ) 1) (fun p => sqΔ p*(∏ i, sq i p)) := by
  let Q : Option (Fin n) → DecGraph := fun j => match j with | none => qΔ | some i => q i
  let S : Option (Fin n) → ℝ → ℝ := fun j => match j with | none => sqΔ | some i => sq i
  have hD (j : Option (Fin n)) : interior (dom (Q j).val) = Ioo (0 : ℝ) 1 := by
    cases j with
    | none => exact hδdom
    | some i => exact hqdom i
  have h0 (j : Option (Fin n)) : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (Q j).val p, 0 ≤ v := by
    cases j with
    | none => exact hδ0
    | some i => exact hq0 i
  let P := completedFiniteProfileProduct 1 Q (by norm_num) hD h0
  change interior (dom P.val) = Ioo (0 : ℝ) 1 ∧ _
  refine ⟨(completedFiniteProfileProduct_domain (by norm_num) hD h0).1,
    completedFiniteProfileProduct_nonnegative (by norm_num) hD h0,?_⟩
  have hSel (j : Option (Fin n)) : SelectionOn (Q j).val (Ioo (0 : ℝ) 1) (S j) := by
    cases j with
    | none => exact hsδ
    | some i => exact hsq i
  intro p hp
  have hmem := completedFiniteProfileProduct_selection (by norm_num) hD h0 hSel p hp
  change (∏ j : Option (Fin n), S j p) ∈ P.val p at hmem
  have he : (∏ j : Option (Fin n), S j p) = sqΔ p*(∏ i, sq i p) := by rw [Fintype.prod_option]
  rw [he] at hmem
  exact hmem

theorem randomized_lipschitz_geometric_bound {n : ℕ} (_hn : 0 < n)
    {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {g : F → ℝ} (hg : LipschitzWith 1 g) :
    let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/3) (geometricHardyTransform 1 P))) := by
  classical
  dsimp only
  let Q : Option (Fin n) → DecGraph := fun j => match j with | none => qΔ | some i => q i
  let S : Option (Fin n) → ℝ → ℝ := fun j => match j with | none => sqΔ | some i => sq i
  have hD (j : Option (Fin n)) : interior (dom (Q j).val) = Ioo (0 : ℝ) 1 := by
    cases j with
    | none => exact hδdom
    | some i => exact hqdom i
  have h0 (j : Option (Fin n)) : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (Q j).val p, 0 ≤ v := by
    cases j with
    | none => exact hδ0
    | some i => exact hq0 i
  have hnAll (j : Option (Fin n)) : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (Q j).val p, v = 0 := by
    cases j with
    | none => exact hnδ
    | some i => exact hnq i
  have hSel (j : Option (Fin n)) : SelectionOn (Q j).val (Ioo (0 : ℝ) 1) (S j) := by
    cases j with
    | none => exact hsδ
    | some i => exact hsq i
  have hProduct (p : ℝ) : (∏ j : Option (Fin n), S j p) = sqΔ p*(∏ i, sq i p) := by
    rw [Fintype.prod_option]
  let σ := fun p => sqΔ p*(∏ i, sq i p)
  let P := completedFiniteProfileProduct 1 Q (by norm_num) hD h0
  have hPD : interior (dom P.val) = Ioo (0 : ℝ) 1 :=
    (completedFiniteProfileProduct_domain (by norm_num) hD h0).1
  have hP0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ P.val p, 0 ≤ v :=
    completedFiniteProfileProduct_nonnegative (by norm_num) hD h0
  have hSelP : SelectionOn P.val (Ioo (0 : ℝ) 1) σ := by
    intro p hp
    have hmem := completedFiniteProfileProduct_selection (by norm_num) hD h0 hSel p hp
    change (∏ j : Option (Fin n), S j p) ∈ P.val p at hmem
    rw [hProduct] at hmem
    exact hmem
  have hGP := geometricHardyTransform_well_defined_any_selection (by norm_num) hPD hP0 hSelP hP
  let G : DecGraph := ⟨geometricHardyTransform 1 P,hGP.1⟩
  let D := completedProfileDilation 1 1 (1/3) G hGP.2.1 (by norm_num) (by norm_num) (by norm_num)
  have hDP : interior (dom D.val) = Ioo (0 : ℝ) 1 ∧
      ∀ p ∈ Ioo (0 : ℝ) 1, D.val p = G.val ((1/3)*p) :=
    completedProfileDilation_properties (q := G) (B := 1) (C := 1) (c := (1/3 : ℝ))
      hGP.2.1 (by norm_num) (by norm_num) (by norm_num)
  have hGsel := geometric_hardy_scalar_selection (by norm_num) hPD hP0 hSelP hP
  have hDsel : SelectionOn D.val (Ioo (0 : ℝ) 1) (fun p => geometricPrefixValue σ ((1/3)*p)) := by
    intro p hp
    rw [hDP.2 p hp]
    exact hGsel _ (initial_dilation_mapsTo (B := 1) (C := 1) (c := (1/3 : ℝ))
      (by norm_num) (by norm_num) hp)
  have hscalar : ∀ x y, |g (Φ x)-g (Φ y)| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)) := by
    intro x y
    exact (show |g (Φ x)-g (Φ y)| ≤ dist (Φ x) (Φ y) from by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hg.dist_le_mul (Φ x) (Φ y)).trans (hmod x y)
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hX : Measurable (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) := ((hhm.comp hZ).sub (hhm.comp hZ')).abs
  have hPAll : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (∏ j : Option (Fin n), S j p)) 0)) < ∞ := by
    simp_rw [hProduct]
    exact hP
  have hAreas := nonzero_profiles_individual_log_areas (by norm_num)
    (fun j => (Q j).property) h0 hnAll hSel hPAll
  change DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ)) D.val
  apply tailQuantile_decLE_of_profile_selection_tail_bounds hX D.property hDP.1 hDsel
  intro u hu
  let a : ℝ := (1/3)*u
  have ha : a ∈ Ioo (0 : ℝ) 1 := initial_dilation_mapsTo (B := 1) (C := 1) (c := (1/3 : ℝ))
    (by norm_num) (by norm_num) hu
  have ht := hsδ a ha
  have htwo := randomized_lipschitz_two_parameter hZ hZ' hindep hident qΔ.property hδdom hδ0 hδ
    hΛm hΛ0 (fun i => (q i).property) hqdom hq0 hQ hnδ hnq hsδ hsq hP hhm hscalar ha ha ht
  have hδle : sqΔ a ≤ geometricPrefixValue sqΔ a :=
    profile_value_le_geometricPrefixValue hδdom hδ0 hsδ (hAreas none) ha ht
  have hphi : geometricPrefixValue σ a = geometricPrefixValue sqΔ a*(∏ i, geometricPrefixValue (sq i) a) := by
    have he := geometricPrefixValue_finite_product (by norm_num) hD h0 hSel hAreas ha
    simpa only [Fintype.prod_option] using he
  have hτ : (∏ i, geometricPrefixValue (sq i) a)*sqΔ a ≤ geometricPrefixValue σ a := by
    calc
      _ = sqΔ a*(∏ i, geometricPrefixValue (sq i) a) := mul_comm _ _
      _ ≤ geometricPrefixValue sqΔ a*(∏ i, geometricPrefixValue (sq i) a) :=
        mul_le_mul_of_nonneg_right hδle (Finset.prod_nonneg (fun i _ => geometricPrefixValue_nonnegative _ _))
      _ = _ := hphi.symm
  have hprob : μ.real {ω | geometricPrefixValue σ a < |g (Φ (Z ω))-g (Φ (Z' ω))|} ≤ a+2*a :=
    (measureReal_mono (show {ω | geometricPrefixValue σ a < |g (Φ (Z ω))-g (Φ (Z' ω))|} ⊆
      {ω | (∏ i, geometricPrefixValue (sq i) a)*sqΔ a < |g (Φ (Z ω))-g (Φ (Z' ω))|}
      from fun _ hω => hτ.trans_lt hω)).trans htwo
  have hbudget : a+2*a = u := by dsimp [a]; ring
  simpa only [hbudget] using hprob

end ScalarMonotone.EndOfPaper
end
