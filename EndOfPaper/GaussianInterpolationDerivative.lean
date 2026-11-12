import EndOfPaper.GaussianInterpolationContinuity
import EndOfPaper.GaussianSoftmaxDirectional
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
The actual pointwise derivative of the Gaussian comparison interpolation and the local interval estimates needed to justify its integral derivative.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianInterpolationVelocity {ι : Type*} {n : ℕ} (A B : ι → Fin n → ℝ)
    (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : ι) : ℝ :=
  gaussianLinearProcess A z i/(2*Real.sqrt t)-gaussianLinearProcess B z i/(2*Real.sqrt (1-t))

def gaussianInterpolationDerivative {ι : Type*} [Fintype ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a β t : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t z) i*
    gaussianInterpolationVelocity A B t z i

theorem gaussian_interpolated_softmax_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (A B : ι → Fin n → ℝ) (a : ℝ) {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Ioo (0 : ℝ) 1)
    (z : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B s z))
      (gaussianInterpolationDerivative A B a β t z) t := by
  exact gaussian_softmax_moment_path_derivative
    (fun i => gaussian_interpolated_process_hasDerivAt A B z i ht) a hβ

theorem gaussian_interpolation_neighborhood {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let ε := min (t/2) ((1-t)/2)
    0 < ε ∧ ∀ s ∈ Metric.ball t ε,
      s ∈ Ioo (0 : ℝ) 1 ∧ t/2 ≤ s ∧ (1-t)/2 ≤ 1-s := by
  dsimp only
  have hT : 0 < t/2 := div_pos ht.1 (by norm_num)
  have hU : 0 < (1-t)/2 := div_pos (sub_pos.mpr ht.2) (by norm_num)
  refine ⟨lt_min hT hU,?_⟩
  intro s hs
  have hdist : |s-t| < min (t/2) ((1-t)/2) := by simpa only [Metric.mem_ball,Real.dist_eq] using hs
  have hlow := (abs_lt.mp hdist).1
  have hhigh := (abs_lt.mp hdist).2
  have hminT := min_le_left (t/2) ((1-t)/2)
  have hminU := min_le_right (t/2) ((1-t)/2)
  refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> linarith only [ht.1,ht.2,hlow,hhigh,hminT,hminU]

end ScalarMonotone.EndOfPaper
end
