import EndOfPaper.GaussianSoftmax
import Mathlib.Data.Finset.Lattice.Fold

/-!
Exact deterministic bounds for the smooth finite maximum.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianFiniteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty z

theorem gaussian_le_finite_maximum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (i : ι) :
    z i ≤ gaussianFiniteMaximum z := Finset.le_sup' z (Finset.mem_univ i)

theorem gaussian_finite_maximum_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℝ) {c : ℝ} (h : ∀ i, z i ≤ c) : gaussianFiniteMaximum z ≤ c :=
  Finset.sup'_le Finset.univ_nonempty z (fun i _ => h i)

theorem gaussian_finite_maximum_le_softmax {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℝ) {β : ℝ} (hβ : 0 < β) : gaussianFiniteMaximum z ≤ gaussianSoftmax β z := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty z
  have hOne : Real.exp (β*gaussianFiniteMaximum z) ≤ gaussianExpSum β z := by
    change Real.exp (β*(Finset.univ.sup' Finset.univ_nonempty z)) ≤ ∑ j, Real.exp (β*z j)
    rw [hmax]
    exact Finset.single_le_sum (f := fun j => Real.exp (β*z j)) (fun j _ => (Real.exp_pos _).le) hi
  have hLog := Real.log_le_log (Real.exp_pos _) hOne
  rw [Real.log_exp] at hLog
  unfold gaussianSoftmax
  exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hLog)

theorem gaussian_softmax_le_finite_maximum {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    gaussianSoftmax β z ≤ gaussianFiniteMaximum z+Real.log (Fintype.card ι : ℝ)/β := by
  have hCard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hSum : gaussianExpSum β z ≤ (Fintype.card ι : ℝ)*Real.exp (β*gaussianFiniteMaximum z) := by
    calc
      _ ≤ ∑ i : ι, Real.exp (β*gaussianFiniteMaximum z) :=
        Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (gaussian_le_finite_maximum z i) hβ.le))
      _ = _ := by simp
  have hLog := Real.log_le_log (gaussian_exp_sum_positive β z) hSum
  rw [Real.log_mul hCard.ne' (Real.exp_pos _).ne',Real.log_exp] at hLog
  unfold gaussianSoftmax
  apply (div_le_iff₀ hβ).mpr
  rw [add_mul,div_mul_cancel₀ _ hβ.ne']
  linarith only [hLog]

theorem gaussian_softmax_moment_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℝ) {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    gaussianSoftmaxMoment a β z ≤
      Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*Real.exp (a*gaussianFiniteMaximum z) := by
  unfold gaussianSoftmaxMoment
  calc
    _ ≤ Real.exp (a*(gaussianFiniteMaximum z+Real.log (Fintype.card ι : ℝ)/β)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (gaussian_softmax_le_finite_maximum z hβ) ha)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end ScalarMonotone.EndOfPaper
end
