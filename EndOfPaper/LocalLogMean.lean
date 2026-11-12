import EndOfPaper.LogExcessProductArea
import EndOfPaper.ProfileLogAdmissibility
import Mathlib.Data.Fintype.BigOperators

/-!
The local logarithmic-mean identity from the single original combined positive-log area, with all random and profile L1 derived.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem local_logarithmic_mean {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Λ : ι → Ω → ℝ} (hΛm : ∀ i, Measurable (Λ i))
    (hΛ0 : ∀ i, 0 ≤ᵐ[μ] Λ i)
    {q : Option ι → Operator} (hq : ∀ j, MaximalDecreasing (q j))
    (hqpos : ∀ j p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q j p, 0 < v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (Λ i) μ)) (q (some i)))
    {sq : Option ι → ℝ → ℝ}
    (hsq : ∀ j, SelectionOn (q j) (Ioo (0 : ℝ) 1) (sq j))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (∏ j : Option ι, sq j p)) 0)) < ∞)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {c : ι → ℝ}
    (hcb : ∀ i, c i ∈ q (some i) b) :
    (∀ i, Integrable (fun ω => max (Real.log (Λ i ω/c i)) 0) μ) ∧
    Integrable (fun ω => ∑ i, max (Real.log (Λ i ω/c i)) 0) μ ∧
    ((∫ ω, ∑ i, max (Real.log (Λ i ω/c i)) 0 ∂μ) =
      ∑ i, ∫ ω, max (Real.log (Λ i ω/c i)) 0 ∂μ) ∧
    ((∑ i, ∫ ω, max (Real.log (Λ i ω/c i)) 0 ∂μ) ≤
      ∑ i, ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq (some i) p/c i)) 0) ∧
    ((∑ i, ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq (some i) p/c i)) 0) =
      ∫ p in Ioo (0 : ℝ) b, Real.log ((∏ i, sq (some i) p)/(∏ i, c i))) := by
  have hq0 (j : Option ι) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (v : ℝ) (hv : v ∈ q j p) :
      0 ≤ v := (hqpos j p hp v hv).le
  have hn (j : Option ι) : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q j p, v = 0 := by
    intro hz
    have hh : (1/2 : ℝ) ∈ Ioo 0 1 := by norm_num
    have hp := hqpos j (1/2) hh (sq j (1/2)) (hsq j (1/2) hh)
    rw [hz (1/2) hh (sq j (1/2)) (hsq j (1/2) hh)] at hp
    exact lt_irrefl _ hp
  have hAreas := nonzero_profiles_individual_log_areas zero_lt_one hq hq0 hn hsq hP
  have hc (i : ι) : 0 < c i := hqpos (some i) b hb (c i) (hcb i)
  have hi (i : ι) := profile_log_excess_integrable_of_selection (hq (some i))
    (hsq (some i)) (hq0 (some i)) (hAreas (some i)) hb (hc i) (hcb i)
  have hm (i : ι) := logarithmic_excess_mean_bound_of_selection μ (hΛm i) (hΛ0 i)
    (hq (some i)) (hq0 (some i)) (hQ i) (hsq (some i)) (hc i) (hi i)
  refine ⟨(fun i => (hm i).1),integrable_finset_sum Finset.univ (fun i _ => (hm i).1),
    integral_finset_sum _ (fun i _ => (hm i).1),?_,?_⟩
  · exact Finset.sum_le_sum (fun i _ => (hm i).2)
  · exact finite_log_excess_product_area (fun i => hq (some i))
      (fun i => hsq (some i)) (fun i => hq0 (some i)) (fun i => hAreas (some i)) hb hc hcb

end ScalarMonotone.EndOfPaper
end
