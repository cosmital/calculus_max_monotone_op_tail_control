import EndOfPaper.ProfileLawMoments

/-!
The full original lower-model existence theorem, with every metric, probability, measurability, marginal and simultaneous-moment obligation discharged.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem randomized_lipschitz_moment_lower {n : ℕ} (hn : 0 < n)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞) :
    ∃ E : Type, ∃ instMetric : MetricSpace E,
      letI := instMetric
      ∃ instMeasurable : MeasurableSpace E,
      letI := instMeasurable
      OpensMeasurableSpace E ∧
      ∃ ν : Measure E, IsProbabilityMeasure ν ∧
      ∃ Λ : Fin n → E → ℝ, ∃ Φ : E → ℝ,
        (∀ i, Measurable (Λ i)) ∧ (∀ i z, 0 ≤ Λ i z) ∧ Measurable Φ ∧
        (∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y))) ∧
        (IndepFun (Prod.fst : E × E → E) Prod.snd (ν.prod ν) ∧
          IdentDistrib (Prod.fst : E × E → E) Prod.snd (ν.prod ν) (ν.prod ν)) ∧
        (∀ f : E → ℝ, LipschitzWith 1 f →
          DecLE (tailQuantile (Measure.map (fun z : E × E => |f z.1-f z.2|) (ν.prod ν))) qΔ.val) ∧
        (∀ i, DecLE (tailQuantile (Measure.map (fun z : E × E => Λ i z.1) (ν.prod ν))) (q i).val) ∧
        (∀ r : ℝ, 0 < r →
          ENNReal.ofReal ((2 : ℝ)^(-1/r))*
            eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform ≤
          eLpNorm (fun z : E × E => Φ z.1-Φ z.2) (ENNReal.ofReal r) (ν.prod ν)) := by
  classical
  let Q : Option (Fin n) → DecGraph := fun j => match j with
    | none => qΔ
    | some i => q i
  let τ : Option (Fin n) → ℝ → ℝ := fun j => match j with
    | none => sqΔ
    | some i => sq i
  have hdom (j : Option (Fin n)) : interior (dom (Q j).val) = Ioo (0 : ℝ) 1 := by
    cases j with
    | none => exact hδdom
    | some i => exact hqdom i
  have hNN (j : Option (Fin n)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
      (v : ℝ) (hv : v ∈ (Q j).val p) : 0 ≤ v := by
    cases j with
    | none => exact hδ0 p hp v hv
    | some i => exact hq0 i p hp v hv
  have hτ (j : Option (Fin n)) : SelectionOn (Q j).val (Ioo (0 : ℝ) 1) (τ j) := by
    cases j with
    | none => exact hsδ
    | some i => exact hsq i
  have hRep (j : Option (Fin n)) : ∃ s : ℝ → ℝ,
      Measurable s ∧ SelectionOn (Q j).val (Ioo (0 : ℝ) 1) s :=
    exists_global_measurable_selection (Or.inr (Q j).property.1) measurableSet_Ioo
      (fun p hp => interior_subset (show p ∈ interior (dom (Q j).val) from by rwa [hdom j]))
  choose s hm hs using hRep
  have hAnti (j : Option (Fin n)) : AntitoneOn (s j) (Ioo (0 : ℝ) 1) :=
    selection_antitoneOn (Q j).property.1 (hs j)
  have h0 (j : Option (Fin n)) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : 0 ≤ s j u :=
    hNN j u hu (s j u) (hs j u hu)
  have hAE (j : Option (Fin n)) : s j =ᵐ[unitUniform] τ j :=
    decreasing_selections_ae_eq (Q j).property.1 (hs j) (hτ j) volume measurableSet_Ioo
  have hProductAE : (fun u => ∏ j, s j u) =ᵐ[unitUniform] (fun u => sqΔ u*(∏ i, sq i u)) := by
    filter_upwards [ae_all_iff.mpr hAE] with u hu
    calc
      _ = ∏ j, τ j u := Finset.prod_congr rfl (fun j _ => hu j)
      _ = _ := by simp only [Fintype.prod_option,τ]
  let E := PositiveProductPoint (positiveProfileChain s (Ioo (0 : ℝ) 1))
  letI : MetricSpace E := positiveProfileChainMetric hAnti
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let ν := positiveProfileHalfLaw hAnti
  letI : IsProbabilityMeasure ν := positiveProfileHalfLaw_probability hAnti hm
  let Λ : Fin n → E → ℝ := fun i x => x.coords (some i)
  let Φ : E → ℝ := positiveProfileProductMap
  have hΛm (i : Fin n) : Measurable (Λ i) := positiveProfilePoint_coordinate_measurable hAnti (some i)
  have hΛ0 (i : Fin n) (x : E) : 0 ≤ Λ i x :=
    positiveProfileChain_nonnegative x.coords_mem (some i)
  have hΦ : Measurable Φ := positiveProfileProductMap_measurable hAnti
  refine ⟨E,inferInstance,inferInstance,inferInstance,ν,inferInstance,Λ,Φ,hΛm,hΛ0,hΦ,?_,
    product_self_independent_copies ν,?_,?_,?_⟩
  · intro x y
    exact (show |Φ x-Φ y| = dist x y*(∏ i, max (Λ i x) (Λ i y)) from
      positiveProfileProductMap_modulus hAnti x y).le
  · intro f hf
    exact positiveProfileHalfLaw_baseline hAnti hm h0 hδdom (hs none) f hf
  · intro i
    have hMap : Measure.map (fun z : E × E => Λ i z.1) (ν.prod ν) = Measure.map (Λ i) ν := by
      change Measure.map ((Λ i) ∘ Prod.fst) (ν.prod ν) = _
      rw [← Measure.map_map (hΛm i) measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]
    rw [hMap]
    exact positiveProfileHalfLaw_marginal hAnti hm h0 (some i) (hqdom i) (hs (some i))
  · intro r hr
    have hb := positiveProfileHalfLaw_lower_norm hAnti hm h0 hr
    have he : eLpNorm (fun u => ∏ j, s j u) (ENNReal.ofReal r) unitUniform =
        eLpNorm (fun u => sqΔ u*(∏ i, sq i u)) (ENNReal.ofReal r) unitUniform :=
      eLpNorm_congr_ae hProductAE
    rwa [he] at hb

end ScalarMonotone.EndOfPaper
end
