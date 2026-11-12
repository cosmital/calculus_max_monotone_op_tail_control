import EndOfPaper.IIDUniformAverage
import EndOfPaper.ProbabilityLowerLimit
import EndOfPaper.TwoBranchProbability
import EndOfPaper.UniformTailMixture
import EndOfPaper.QuantileSegmentIntegrals

/-!
Actual repeated-coordinate couplings with every prescribed
quantile marginal law, derived integrability, and finite-replication
strict-tail witnesses from the explicitly constructed L1 strong law.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def quantileReplica {n : ℕ} (q : Fin n → ℝ → ℝ) (p : ℝ) (i : Fin n)
    (j : ℕ) : ℝ × (ℕ → ℝ) → ℝ :=
  twoBranchFunction (fun ω => q i (p*ω j)) (fun ω => q i (p+(1-p)*ω j))

def replicaAverage {n : ℕ} (q : Fin n → ℝ → ℝ) (p : ℝ) (m : ℕ)
    (z : ℝ × (ℕ → ℝ)) : ℝ :=
  (∑ i, ∑ j ∈ Finset.range m, quantileReplica q p i j z)/((n : ℝ)*(m : ℝ))

theorem quantileReplica_measurable {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hm : ∀ i, Measurable (q i)) (p : ℝ) (i : Fin n) (j : ℕ) :
    Measurable (quantileReplica q p i j) := by
  apply twoBranchFunction_measurable
  · exact (hm i).comp (measurable_const.mul (measurable_pi_apply j))
  · exact (hm i).comp (measurable_const.add (measurable_const.mul (measurable_pi_apply j)))

theorem quantileReplica_law {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hm : ∀ i, Measurable (q i)) {p : ℝ} (hp : p ∈ Ioo 0 1)
    (i : Fin n) (j : ℕ) :
    Measure.map (quantileReplica q p i j) (twoBranchMeasure p iidUniformMeasure) =
      Measure.map (q i) unitUniform := by
  have ht : Measurable (fun u : ℝ => q i (p*u)) :=
    (hm i).comp (measurable_const.mul measurable_id)
  have hb : Measurable (fun u : ℝ => q i (p+(1-p)*u)) :=
    (hm i).comp (measurable_const.add (measurable_const.mul measurable_id))
  have hbranch := twoBranchFunction_law iidUniformMeasure p
    (F := fun ω : ℕ → ℝ => q i (p*ω j))
    (G := fun ω : ℕ → ℝ => q i (p+(1-p)*ω j))
    (ht.comp (measurable_pi_apply j)) (hb.comp (measurable_pi_apply j))
  rw [quantileReplica]
  apply hbranch.trans
  change ENNReal.ofReal p • Measure.map
      ((fun u : ℝ => q i (p*u)) ∘ (fun ω : ℕ → ℝ => ω j)) iidUniformMeasure +
    ENNReal.ofReal (1-p) • Measure.map
      ((fun u : ℝ => q i (p+(1-p)*u)) ∘ (fun ω : ℕ → ℝ => ω j)) iidUniformMeasure = _
  rw [← Measure.map_map ht (measurable_pi_apply j),
    ← Measure.map_map hb (measurable_pi_apply j), iid_uniform_eval_law j,
    quantile_law_split hp (hm i)]

theorem quantileReplica_integrable {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hm : ∀ i, Measurable (q i)) (hi : ∀ i, Integrable (q i) unitUniform)
    {p : ℝ} (hp : p ∈ Ioo 0 1) (i : Fin n) (j : ℕ) :
    Integrable (quantileReplica q p i j) (twoBranchMeasure p iidUniformMeasure) := by
  have hid : Integrable id (Measure.map (q i) unitUniform) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable (hm i).aemeasurable).mpr (hi i)
  rw [← quantileReplica_law hm hp i j] at hid
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (quantileReplica_measurable hm p i j).aemeasurable).mp hid

theorem replicaAverage_measurable {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hm : ∀ i, Measurable (q i)) (p : ℝ) (m : ℕ) :
    Measurable (replicaAverage q p m) :=
  (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
    (fun j _ => quantileReplica_measurable hm p i j))).div_const _

theorem replicaAverage_true {n : ℕ} (q : Fin n → ℝ → ℝ) (p : ℝ)
    (m : ℕ) (ω : ℕ → ℝ) :
    replicaAverage q p m ((0 : ℝ), ω) =
      (∑ j ∈ Finset.range m, (∑ i, q i (p*ω j))/(n : ℝ))/(m : ℝ) := by
  simp only [replicaAverage, quantileReplica, twoBranchFunction, Prod.fst, Prod.snd, ite_true]
  rw [← Finset.sum_div, div_div]
  congr 1
  exact Finset.sum_comm

theorem replicaAverage_true_limit {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hm : ∀ i, Measurable (q i)) (hi : ∀ i, Integrable (q i) unitUniform)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∀ᵐ ω ∂iidUniformMeasure,
      Tendsto (fun m : ℕ => replicaAverage q p m ((0 : ℝ), ω)) atTop
        (𝓝 ((∑ i, hardyScalar (q i) p)/(n : ℝ))) := by
  have hF : Measurable (fun u : ℝ => (∑ i, q i (p*u))/(n : ℝ)) :=
    (Finset.measurable_sum _ (fun i _ =>
      (hm i).comp (measurable_const.mul measurable_id))).div_const _
  have hlim := iid_uniform_average_ae hF (uniform_top_average_integrable hi hp)
  simpa only [replicaAverage_true, uniform_top_average_mean hi hp] using hlim

theorem replicaAverage_near_mean {n : ℕ} {q : Fin n → ℝ → ℝ}
    (hm : ∀ i, Measurable (q i)) (hi : ∀ i, Integrable (q i) unitUniform)
    {p : ℝ} (hp : p ∈ Ioo 0 1) {t r : ℝ}
    (ht : t < (∑ i, hardyScalar (q i) p)/(n : ℝ)) (hr : r ∈ Ioo 0 p) :
    ∃ m : ℕ, 1 ≤ m ∧
      r < (twoBranchMeasure p iidUniformMeasure).real {z | t < replicaAverage q p m z} := by
  letI : IsProbabilityMeasure iidUniformMeasure := iidUniformMeasure_probability
  have hMeas (m : ℕ) : Measurable (fun ω : ℕ → ℝ =>
      replicaAverage q p m ((0 : ℝ), ω)) :=
    (replicaAverage_measurable hm p m).comp (by fun_prop)
  obtain ⟨m, hmpos, hprob⟩ := exists_strict_tail_probability_of_ae_limit iidUniformMeasure
    hMeas ht ((div_lt_one hp.1).mpr hr.2) (replicaAverage_true_limit hm hi hp)
  have hE : MeasurableSet {z | t < replicaAverage q p m z} :=
    (replicaAverage_measurable hm p m) measurableSet_Ioi
  have hlow := twoBranchMeasure_lower iidUniformMeasure hp hE
  refine ⟨m, hmpos, ?_⟩
  have hstrict : r < p*iidUniformMeasure.real {ω | t < replicaAverage q p m ((0 : ℝ), ω)} := by
    have h := (div_lt_iff₀ hp.1).mp hprob
    simpa only [mul_comm] using h
  exact hstrict.trans_le hlow

end ScalarMonotone.EndOfPaper
end
