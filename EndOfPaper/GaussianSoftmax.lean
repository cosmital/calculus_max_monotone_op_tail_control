import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Field

/-!
The actual smooth exponential approximation of a finite Gaussian maximum, with its probability weights and first derivatives.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianExpSum {ι : Type*} [Fintype ι] (β : ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (β*z i)

def gaussianSoftmax {ι : Type*} [Fintype ι] (β : ℝ) (z : ι → ℝ) : ℝ :=
  Real.log (gaussianExpSum β z)/β

def gaussianSoftmaxWeight {ι : Type*} [Fintype ι] (β : ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (β*z i)/gaussianExpSum β z

def gaussianSoftmaxMoment {ι : Type*} [Fintype ι] (a β : ℝ) (z : ι → ℝ) : ℝ :=
  Real.exp (a*gaussianSoftmax β z)

theorem gaussian_exp_sum_positive {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (z : ι → ℝ) :
    0 < gaussianExpSum β z :=
  Finset.sum_pos (fun i _ => Real.exp_pos (β*z i)) Finset.univ_nonempty

theorem gaussian_softmax_weight_positive {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (z : ι → ℝ) (i : ι) : 0 < gaussianSoftmaxWeight β z i :=
  div_pos (Real.exp_pos _) (gaussian_exp_sum_positive β z)

theorem gaussian_softmax_weight_sum {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (z : ι → ℝ) :
    ∑ i, gaussianSoftmaxWeight β z i = 1 := by
  simp only [gaussianSoftmaxWeight,← Finset.sum_div]
  exact div_self (gaussian_exp_sum_positive β z).ne'

theorem gaussian_exp_sum_hasDerivAt {ι : Type*} [Fintype ι]
    {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ} (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x) (β : ℝ) :
    HasDerivAt (fun t => gaussianExpSum β (z t))
      (β*∑ i, Real.exp (β*z x i)*d i) x := by
  have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ => ((hz i).const_mul β).exp)
  convert hh using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gaussian_softmax_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι]
    {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ} (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x)
    {β : ℝ} (hβ : β ≠ 0) :
    HasDerivAt (fun t => gaussianSoftmax β (z t))
      (∑ i, gaussianSoftmaxWeight β (z x) i*d i) x := by
  have hh := ((gaussian_exp_sum_hasDerivAt hz β).log (gaussian_exp_sum_positive β (z x)).ne').div_const β
  convert hh using 1
  simp only [gaussianSoftmaxWeight,div_mul_eq_mul_div,← Finset.sum_div]
  rw [div_right_comm,mul_div_cancel_left₀ _ hβ]

theorem gaussian_softmax_moment_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι]
    {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ} (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x)
    (a : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    HasDerivAt (fun t => gaussianSoftmaxMoment a β (z t))
      (a*gaussianSoftmaxMoment a β (z x)*(∑ i, gaussianSoftmaxWeight β (z x) i*d i)) x := by
  have hh := ((gaussian_softmax_hasDerivAt hz hβ).const_mul a).exp
  convert hh using 1
  unfold gaussianSoftmaxMoment
  ring

theorem gaussian_softmax_weight_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι]
    {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ} (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x)
    (β : ℝ) (i : ι) :
    HasDerivAt (fun t => gaussianSoftmaxWeight β (z t) i)
      (β*gaussianSoftmaxWeight β (z x) i*(d i-∑ j, gaussianSoftmaxWeight β (z x) j*d j)) x := by
  have hh := (((hz i).const_mul β).exp).div (gaussian_exp_sum_hasDerivAt hz β)
    (gaussian_exp_sum_positive β (z x)).ne'
  have hAvg : (∑ j, gaussianSoftmaxWeight β (z x) j*d j) =
      (∑ j, Real.exp (β*z x j)*d j)/gaussianExpSum β (z x) := by
    simp only [gaussianSoftmaxWeight,div_mul_eq_mul_div,Finset.sum_div]
  convert hh using 1
  rw [hAvg]
  unfold gaussianSoftmaxWeight
  field_simp [(gaussian_exp_sum_positive β (z x)).ne']
  <;> ring

def gaussianSoftmaxGradient {ι : Type*} [Fintype ι] (a β : ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  a*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i

theorem gaussian_softmax_gradient_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι]
    {z : ℝ → ι → ℝ} {d : ι → ℝ} {x : ℝ} (hz : ∀ i, HasDerivAt (fun t => z t i) (d i) x)
    (a : ℝ) {β : ℝ} (hβ : β ≠ 0) (i : ι) :
    HasDerivAt (fun t => gaussianSoftmaxGradient a β (z t) i)
      (a*β*gaussianSoftmaxMoment a β (z x)*gaussianSoftmaxWeight β (z x) i*d i+
        a*(a-β)*gaussianSoftmaxMoment a β (z x)*gaussianSoftmaxWeight β (z x) i*
          (∑ j, gaussianSoftmaxWeight β (z x) j*d j)) x := by
  have hh := ((gaussian_softmax_moment_hasDerivAt hz a hβ).mul
    (gaussian_softmax_weight_hasDerivAt hz β i)).const_mul a
  convert hh using 1
  · funext t
    unfold gaussianSoftmaxGradient
    ring
  · ring

theorem gaussian_softmax_off_diagonal_derivative {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (a : ℝ) {β : ℝ} (hβ : β ≠ 0) (z : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    HasDerivAt (fun t : ℝ => gaussianSoftmaxGradient a β
      (fun k => z k+t*(if k = j then 1 else 0)) i)
      (a*(a-β)*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i*gaussianSoftmaxWeight β z j) 0 := by
  classical
  have hz (k : ι) : HasDerivAt (fun t : ℝ => z k+t*(if k = j then 1 else 0))
      (if k = j then 1 else 0) 0 := by
    simpa only [id_eq,one_mul] using
      ((hasDerivAt_id 0).mul_const (if k = j then (1 : ℝ) else 0)).const_add (z k)
  have hh := gaussian_softmax_gradient_hasDerivAt hz a hβ i
  simpa [hij] using hh

theorem gaussian_softmax_off_diagonal_nonpos {ι : Type*} [Fintype ι] [Nonempty ι]
    {a β : ℝ} (ha : 0 ≤ a) (haβ : a ≤ β) (z : ι → ℝ) (i j : ι) :
    a*(a-β)*gaussianSoftmaxMoment a β z*gaussianSoftmaxWeight β z i*gaussianSoftmaxWeight β z j ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ha (sub_nonpos.mpr haβ))
        (Real.exp_pos _).le) (gaussian_softmax_weight_positive β z i).le)
    (gaussian_softmax_weight_positive β z j).le

end ScalarMonotone.EndOfPaper
end
