import EndOfPaper.GaussianNormMedian
import EndOfPaper.HSMatrixBasic

/-!
The exact manuscript data HS-norm median constant, from actual independent standard Gaussian entries on the original probability space.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_hs_normalized_median {Ω : Type*} [MeasurableSpace Ω] {N d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix (Fin d) (Fin N)}
    (hN : 0 < N) (hd : 0 < d)
    (hi : iIndepFun (fun i : Fin d × Fin N => fun ω => X ω i) μ)
    (hm : ∀ i : Fin d × Fin N, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : Fin d × Fin N, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {m : ℝ} (hmed : IsRealMedian (fun ω => ‖X ω‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ m) :
    m ≤ 1+Real.sqrt (2*Real.log 2/((N*d : ℕ) : ℝ)) := by
  have hcard : 0 < Fintype.card (Fin d × Fin N) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Nat.mul_pos hd hN
  have hmed' : IsRealMedian (fun ω => ‖X ω‖/Real.sqrt (Fintype.card (Fin d × Fin N) : ℝ)) μ m := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm d N] using hmed
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm d N] using
    gaussian_euclidean_normalized_norm_median hi hm hLaw hcard hmed'

end ScalarMonotone.EndOfPaper
end
