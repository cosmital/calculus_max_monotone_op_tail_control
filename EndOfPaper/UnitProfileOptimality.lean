import EndOfPaper.UnitProfileMomentUpper
import EndOfPaper.UnitProfileBernoulli

/-!
The complete universal upper bound and an actual admissible Bernoulli attainer for the original lower coefficient.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem unit_profile_product_norm_one (n : ℕ) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun _ : ℝ => (1 : ℝ)*(∏ _i : Fin n, (1 : ℝ))) (ENNReal.ofReal r) unitUniform = 1 := by
  have he : (fun _ : ℝ => (1 : ℝ)*(∏ _i : Fin n, (1 : ℝ))) = (fun _ : ℝ => (1 : ℝ)) := by
    funext u
    simp
  rw [he,eLpNorm_nonnegative_eq_moment
    (Eventually.of_forall (fun _ : ℝ => (zero_le_one : (0 : ℝ) ≤ 1))) hr]
  simp

theorem unit_profile_moment_optimality {n : ℕ} (hn : 0 < n)
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) unitQuantileProfile.val)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) unitQuantileProfile.val)
    {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {r : ℝ} (hr : 1 ≤ r) :
    ((∫⁻ ω, ENNReal.ofReal (|Φ (Z ω)-Φ (Z' ω)|^r) ∂μ) ≤ ENNReal.ofReal (1/2 : ℝ) ∧
      eLpNorm (fun ω => Φ (Z ω)-Φ (Z' ω)) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal ((2 : ℝ)^(-1/r))) ∧
    Measurable (id : ℝ → ℝ) ∧ (∀ _i : Fin n, Measurable (fun _ : ℝ => (1 : ℝ))) ∧
    (∀ (_i : Fin n) (_x : ℝ), (0 : ℝ) ≤ 1) ∧
    (∀ x y : ℝ, dist x y ≤ dist x y*(∏ _i : Fin n, max (1 : ℝ) 1)) ∧
    (IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (symmetricBernoulli.prod symmetricBernoulli) ∧
      IdentDistrib (Prod.fst : ℝ × ℝ → ℝ) Prod.snd
        (symmetricBernoulli.prod symmetricBernoulli) (symmetricBernoulli.prod symmetricBernoulli)) ∧
    (∀ f : ℝ → ℝ, LipschitzWith 1 f → DecLE
      (tailQuantile (Measure.map (fun z : ℝ × ℝ => |f z.1-f z.2|)
        (symmetricBernoulli.prod symmetricBernoulli))) unitQuantileProfile.val) ∧
    (∀ _i : Fin n, DecLE (tailQuantile (Measure.map (fun _ : ℝ × ℝ => (1 : ℝ))
      (symmetricBernoulli.prod symmetricBernoulli))) unitQuantileProfile.val) ∧
    ((∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(symmetricBernoulli.prod symmetricBernoulli)) =
      ENNReal.ofReal (1/2 : ℝ) ∧
      eLpNorm (fun z : ℝ × ℝ => z.1-z.2) (ENNReal.ofReal r)
        (symmetricBernoulli.prod symmetricBernoulli) = ENNReal.ofReal ((2 : ℝ)^(-1/r))) := by
  have hScalar : ∀ x y, |Φ x-Φ y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)) := by
    simpa only [Real.dist_eq] using hmod
  have hUpper := unit_profile_universal_moment_upper hZ hZ' hi he hΛm hΛ0 hQ
    (fun i p hp => unitQuantileProfile_one_mem hp) hδ (fun p hp => unitQuantileProfile_one_mem hp)
    hΦ hScalar hr
  exact ⟨hUpper,measurable_id,(fun _ => measurable_const),(fun _ _ => zero_le_one),
    bernoulli_unit_profile_modulus n,product_self_independent_copies symmetricBernoulli,
    bernoulli_unit_profile_baseline,(fun _ => unit_profile_constant_control _),
    symmetricBernoulli_copy_moment (zero_lt_one.trans_le hr),symmetricBernoulli_copy_norm (zero_lt_one.trans_le hr)⟩

end ScalarMonotone.EndOfPaper
end
