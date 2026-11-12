import EndOfPaper.GaussianCoordinatePermutation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
Actual linear Gaussian process coefficients, deterministic growth and the derivatives of the Gaussian comparison interpolation.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianLinearProcess {ι : Type*} {n : ℕ} (A : ι → Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (i : ι) : ℝ := ∑ k, A i k*z k

def gaussianLinearCovariance {ι : Type*} {n : ℕ} (A : ι → Fin n → ℝ) (i j : ι) : ℝ :=
  ∑ k, A i k*A j k

def gaussianInterpolatedProcess {ι : Type*} {n : ℕ} (A B : ι → Fin n → ℝ)
    (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : ι) : ℝ :=
  Real.sqrt t*gaussianLinearProcess A z i+Real.sqrt (1-t)*gaussianLinearProcess B z i

theorem gaussian_linear_process_abs_le {ι : Type*} {n : ℕ} (A : ι → Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (i : ι) :
    |gaussianLinearProcess A z i| ≤ (∑ k, |A i k|)*‖z‖ := by
  calc
    _ ≤ ∑ k, |A i k*z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |A i k| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z k
    _ = _ := (Finset.sum_mul ..).symm

theorem gaussian_linear_process_continuous {ι : Type*} {n : ℕ}
    (A : ι → Fin n → ℝ) (i : ι) : Continuous (fun z : EuclideanSpace ℝ (Fin n) => gaussianLinearProcess A z i) := by
  unfold gaussianLinearProcess
  fun_prop

theorem gaussian_linear_process_hasDerivAt {ι : Type*} {n : ℕ} (A : ι → Fin n → ℝ)
    {z : ℝ → EuclideanSpace ℝ (Fin n)} {d : Fin n → ℝ} {x : ℝ}
    (hz : ∀ k, HasDerivAt (fun t => z t k) (d k) x) (i : ι) :
    HasDerivAt (fun t => gaussianLinearProcess A (z t) i) (∑ k, A i k*d k) x := by
  simpa only [gaussianLinearProcess] using
    HasDerivAt.sum (u := Finset.univ) (fun k _ => (hz k).const_mul (A i k))

theorem gaussian_linear_process_replace_derivative {ι : Type*} {n : ℕ}
    (A : ι → Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) (i : ι) (x : ℝ) :
    HasDerivAt (fun t => gaussianLinearProcess A (gaussianReplace z k t) i) (A i k) x := by
  have hz (j : Fin n) : HasDerivAt (fun t => gaussianReplace z k t j) (if j = k then 1 else 0) x := by
    by_cases hj : j = k
    · subst j
      simpa only [gaussian_replace_apply,Function.update_self,if_pos rfl] using hasDerivAt_id x
    · simpa only [gaussian_replace_apply,Function.update_of_ne hj,if_neg hj] using hasDerivAt_const x (z j)
  simpa using gaussian_linear_process_hasDerivAt A hz i

theorem gaussian_interpolated_process_hasDerivAt {ι : Type*} {n : ℕ}
    (A B : ι → Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : ι) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => gaussianInterpolatedProcess A B s z i)
      (gaussianLinearProcess A z i/(2*Real.sqrt t)-gaussianLinearProcess B z i/(2*Real.sqrt (1-t))) t := by
  have hA := (Real.hasDerivAt_sqrt ht.1.ne').mul_const (gaussianLinearProcess A z i)
  have hB := (((hasDerivAt_id t).const_sub 1).sqrt (sub_pos.mpr ht.2).ne').mul_const
    (gaussianLinearProcess B z i)
  convert hA.add hB using 1 <;> dsimp only [gaussianInterpolatedProcess,id_eq] <;> ring

theorem gaussian_interpolated_process_replace_derivative {ι : Type*} {n : ℕ}
    (A B : ι → Fin n → ℝ) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) (i : ι) (x : ℝ) :
    HasDerivAt (fun s => gaussianInterpolatedProcess A B t (gaussianReplace z k s) i)
      (Real.sqrt t*A i k+Real.sqrt (1-t)*B i k) x :=
  ((gaussian_linear_process_replace_derivative A z k i x).const_mul (Real.sqrt t)).add
    ((gaussian_linear_process_replace_derivative B z k i x).const_mul (Real.sqrt (1-t)))

end ScalarMonotone.EndOfPaper
end
