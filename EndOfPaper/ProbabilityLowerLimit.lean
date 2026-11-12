import MonotoneOperators.Survival
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Almost-sure convergence to a constant yields strict-tail probability
convergence to one and a finite positive sample size attaining any
prescribed smaller probability.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem strict_tail_probability_tendsto_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hm : ∀ m, Measurable (Y m)) {a b : ℝ} (hab : a < b)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ => Y m ω) atTop (𝓝 b)) :
    Tendsto (fun m : ℕ => μ.real {ω | a < Y m ω}) atTop (𝓝 (1 : ℝ)) := by
  let f : ℕ → Ω → ℝ := fun m => {ω | a < Y m ω}.indicator (fun _ => 1)
  have hE (m) : MeasurableSet {ω | a < Y m ω} := (hm m) measurableSet_Ioi
  have hfm (m) : AEStronglyMeasurable (f m) μ :=
    (measurable_const.indicator (hE m)).aestronglyMeasurable
  have hbound (m) : ∀ᵐ ω ∂μ, ‖f m ω‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro ω
    by_cases h : a < Y m ω <;> simp [f, h]
  have hflim : ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ => f m ω) atTop (𝓝 (1 : ℝ)) := by
    apply hlim.mono
    intro ω hω
    have hevent : ∀ᶠ m : ℕ in atTop, a < Y m ω := hω.eventually (isOpen_Ioi.mem_nhds hab)
    have heq : (fun m : ℕ => f m ω) =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
      hevent.mono (fun m hm => by simp [f, hm])
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' heq.symm
  have hInt := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    hfm (integrable_const (1 : ℝ)) hbound hflim
  have heq (m : ℕ) : (∫ ω, f m ω ∂μ) = μ.real {ω | a < Y m ω} := by
    change (∫ ω, {ω | a < Y m ω}.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
    rw [integral_indicator (hE m), setIntegral_const]
    simp only [smul_eq_mul, mul_one]
  simp_rw [heq] at hInt
  simpa using hInt

theorem exists_strict_tail_probability_of_ae_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ}
    (hm : ∀ m, Measurable (Y m)) {a b q : ℝ} (hab : a < b) (hq : q < 1)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ => Y m ω) atTop (𝓝 b)) :
    ∃ m : ℕ, 1 ≤ m ∧ q < μ.real {ω | a < Y m ω} := by
  have hT := strict_tail_probability_tendsto_one μ hm hab hlim
  have hevent : ∀ᶠ m : ℕ in atTop, q < μ.real {ω | a < Y m ω} :=
    hT.eventually (isOpen_Ioi.mem_nhds hq)
  exact ((eventually_ge_atTop (1 : ℕ)).and hevent).exists

end ScalarMonotone.EndOfPaper
end
