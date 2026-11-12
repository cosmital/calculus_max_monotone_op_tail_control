import MonotoneOperators.Survival
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw

/-!
An actual infinite product of uniform measures, its coordinate laws
and independence, and the strong law for any integrable observable.
These are ingredients for the replicated quantile-envelope construction.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def iidUniformMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => unitUniform)

theorem iidUniformMeasure_probability : IsProbabilityMeasure iidUniformMeasure := by
  unfold iidUniformMeasure
  infer_instance

theorem iid_uniform_eval_law (j : ℕ) :
    Measure.map (fun ω : ℕ → ℝ => ω j) iidUniformMeasure = unitUniform := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply j) hs]
  have he : (fun ω : ℕ → ℝ => ω j) ⁻¹' s =
      Set.pi ({j} : Finset ℕ) (fun _ : ℕ => s) := by
    ext ω
    simp [Set.mem_pi]
  rw [he, iidUniformMeasure, Measure.infinitePi_pi]
  · simp
  · intro i hi
    exact hs

theorem iid_uniform_coordinates_independent :
    iIndepFun (fun j : ℕ => fun ω : ℕ → ℝ => ω j) iidUniformMeasure := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hsets
  have he : (⋂ i ∈ S, (fun ω : ℕ → ℝ => ω i) ⁻¹' sets i) = Set.pi S sets := by
    ext ω
    simp [Set.mem_pi]
  rw [he, iidUniformMeasure, Measure.infinitePi_pi]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [← Measure.map_apply (measurable_pi_apply j) (hsets j hj)]
    change unitUniform (sets j) =
      (Measure.map (fun ω : ℕ → ℝ => ω j) iidUniformMeasure) (sets j)
    rw [iid_uniform_eval_law j]
  · exact hsets

theorem iid_uniform_average_ae {F : ℝ → ℝ} (hm : Measurable F)
    (hi : Integrable F unitUniform) :
    ∀ᵐ ω ∂iidUniformMeasure,
      Tendsto (fun m : ℕ => (∑ j ∈ Finset.range m, F (ω j))/(m : ℝ)) atTop
        (𝓝 (∫ u, F u ∂unitUniform)) := by
  letI : IsProbabilityMeasure iidUniformMeasure := iidUniformMeasure_probability
  have hId (j : ℕ) : IdentDistrib (fun ω : ℕ → ℝ => ω j) id iidUniformMeasure unitUniform :=
    ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id,
      by rw [iid_uniform_eval_law j, Measure.map_id]⟩
  have hFId (j : ℕ) : IdentDistrib (fun ω : ℕ → ℝ => F (ω j)) F
      iidUniformMeasure unitUniform := (hId j).comp hm
  have hFi : Integrable (fun ω : ℕ → ℝ => F (ω 0)) iidUniformMeasure :=
    (hFId 0).integrable_iff.mpr hi
  have hInd : iIndepFun (fun j : ℕ => fun ω : ℕ → ℝ => F (ω j)) iidUniformMeasure :=
    iid_uniform_coordinates_independent.comp (fun _ => F) (fun _ => hm)
  have hLaw := strong_law_ae (fun j : ℕ => fun ω : ℕ → ℝ => F (ω j)) hFi
    (fun i j hij => hInd.indepFun hij) (fun j => (hFId j).trans (hFId 0).symm)
  simpa only [(hFId 0).integral_eq, smul_eq_mul, div_eq_mul_inv, mul_comm] using hLaw

end ScalarMonotone.EndOfPaper
end
