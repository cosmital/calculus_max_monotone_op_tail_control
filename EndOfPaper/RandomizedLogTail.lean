import EndOfPaper.EndpointControl
import EndOfPaper.LogarithmicModulus
import EndOfPaper.LogarithmicExpectations
import EndOfPaper.StrictTailLimits

/-!
Apply the actual endpoint theorem to the finite random
control family. All random logarithmic L1 and mean bounds are
derived from the marginal comparisons and normalized profile areas.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem randomized_lipschitz_logarithmic_tail {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hqΔ : MaximalDecreasing qΔ)
    (hδdom : Ioo (0 : ℝ) 1 ⊆ interior (dom qΔ))
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : ι → Operator} (hq : ∀ i, MaximalDecreasing (q i))
    (hqdom : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (q i))
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    {sq : ι → ℝ → ℝ} (hsqm : ∀ i, Measurable (sq i))
    (hsq : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hPi : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p/c i)) 0)) < ∞)
    {h : E → ℝ} (hhm : Measurable h)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {a s t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (ht : t ∈ qΔ a) :
    μ.real {ω | (∏ i, c i)*Real.exp s*t < |h (Z ω)-h (Z' ω)|} ≤
      a+2*(∑ i, ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq i p/c i)) 0)/s := by
  classical
  let U := fun z => ∑ i, max (Real.log (Λ i z/c i)) 0
  have hUm : Measurable U := logarithmic_control_measurable hΛm c
  have hU0 : ∀ z, 0 ≤ U z := fun z => Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hXi (i : ι) : Integrable (fun ω => max (Real.log (Λ i (Z ω)/c i)) 0) μ :=
    logarithmic_excess_integrable μ ((hΛm i).comp hZ)
      (Eventually.of_forall (fun ω => hΛ0 i (Z ω))) (hq i) (hqdom i) (hq0 i) (hQ i) (hsq i) (hc i) (hPi i)
  have hUi : Integrable (fun ω => U (Z ω)) μ :=
    integrable_finset_sum Finset.univ (fun i _ => hXi i)
  have hmean : (∫ ω, U (Z ω) ∂μ) ≤
      ∑ i, ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq i p/c i)) 0 := by
    change (∫ ω, ∑ i, max (Real.log (Λ i (Z ω)/c i)) 0 ∂μ) ≤ _
    rw [integral_finset_sum _ (fun i _ => hXi i)]
    apply Finset.sum_le_sum
    intro i _hi
    exact logarithmic_excess_mean_bound μ ((hΛm i).comp hZ)
      (Eventually.of_forall (fun ω => hΛ0 i (Z ω))) (hq i) (hqdom i) (hq0 i) (hQ i)
      (hsqm i) (hsq i) (hc i) (hPi i)
  have hfinite : (∫⁻ ω, ENNReal.ofReal (U (Z ω)) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun ω => hU0 (Z ω)))).mp hUi.hasFiniteIntegral
  have hC : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc i)
  have hmodU : ∀ x y, |h x-h y| ≤ (∏ i, c i)*Real.exp (U x+U y)*dist x y :=
    randomized_modulus_logarithmic_form hc hΛ0 hmod
  have hb := logarithmic_endpoint_control hZ hZ' hindep hident hqΔ hδdom hδ0 hδ
    hhm hUm hU0 hfinite hC hmodU ha hs ht
  apply hb.trans
  apply add_le_add_left
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmean (by norm_num)) hs.le

end ScalarMonotone.EndOfPaper
end
