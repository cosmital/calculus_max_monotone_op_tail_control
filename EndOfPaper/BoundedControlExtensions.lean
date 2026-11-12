import EndOfPaper.LipschitzBrackets
import MonotoneOperators.ProbabilityBounds

/-!
Countably many actual bounded-control Lipschitz extensions
transfer zero copy differences to the locally controlled function.
No separability or control moment assumption is imposed.
-/

open Set Filter MeasureTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem randomized_modulus_lipschitz_on_bounded_controls {ι E : Type*} [Fintype ι]
    [PseudoMetricSpace E] {h : E → ℝ} {Λ : ι → E → ℝ}
    (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {M : ℝ} (hM : 0 ≤ M) :
    LipschitzOnWith ⟨M^Fintype.card ι,pow_nonneg hM _⟩ h {x | ∀ i, Λ i x ≤ M} := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  have hprod : (∏ i, max (Λ i x) (Λ i y)) ≤ M^Fintype.card ι := by
    calc
      _ ≤ ∏ _i : ι, M := Finset.prod_le_prod
        (fun i _ => (hΛ0 i x).trans (le_max_left _ _)) (fun i _ => max_le (hx i) (hy i))
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ]
  exact (hmod x y).trans (by simpa only [mul_comm (dist x y)] using
    mul_le_mul_of_nonneg_left hprod (show 0 ≤ dist x y from dist_nonneg))

theorem ae_difference_zero_of_bounded_control_extensions {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [PseudoMetricSpace E] {μ : Measure Ω} {Z Z' : Ω → E}
    {h : E → ℝ} {Λ : ι → E → ℝ} (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (htests : ∀ (K : ℝ≥0), 0 < (K : ℝ) → ∀ f : E → ℝ, LipschitzWith K f →
      (fun ω => f (Z ω)) =ᵐ[μ] (fun ω => f (Z' ω))) :
    (fun ω => h (Z ω)) =ᵐ[μ] (fun ω => h (Z' ω)) := by
  classical
  let M := fun n : ℕ => (n : ℝ)+1
  have hM (n : ℕ) : 0 < M n := by dsimp [M]; positivity
  let K := fun n : ℕ => (⟨M n^Fintype.card ι,pow_nonneg (hM n).le _⟩ : ℝ≥0)
  let A := fun n : ℕ => {x : E | ∀ i, Λ i x ≤ M n}
  have hK (n : ℕ) : 0 < (K n : ℝ) := pow_pos (hM n) _
  have hex (n : ℕ) : ∃ f : E → ℝ, LipschitzWith (K n) f ∧ EqOn h f (A n) := by
    by_cases hA : (A n).Nonempty
    · have hLip : LipschitzOnWith (K n) h (A n) :=
        randomized_modulus_lipschitz_on_bounded_controls hΛ0 hmod (hM n).le
      have he := upperLipschitzExtension_properties hA hLip
      exact ⟨_,he.1,he.2.1⟩
    · refine ⟨fun _ => 0,?_,?_⟩
      · apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [dist_self]
        exact mul_nonneg (K n).property dist_nonneg
      · intro x hx
        exact (hA ⟨x,hx⟩).elim
  choose f hfl hfe using hex
  have ha : ∀ᵐ ω ∂μ, ∀ n : ℕ, f n (Z ω) = f n (Z' ω) :=
    ae_all_iff.mpr (fun n => htests (K n) (hK n) (f n) (hfl n))
  filter_upwards [ha] with ω hω
  let R : ℝ := ∑ i : ι, (Λ i (Z ω)+Λ i (Z' ω))
  obtain ⟨n,hn⟩ := exists_nat_gt R
  have hsingle (i : ι) : Λ i (Z ω)+Λ i (Z' ω) ≤ R :=
    Finset.single_le_sum (fun j _ => add_nonneg (hΛ0 j (Z ω)) (hΛ0 j (Z' ω))) (Finset.mem_univ i)
  have hxA : Z ω ∈ A n := by
    intro i
    have hb := hsingle i
    have hnn := hΛ0 i (Z' ω)
    change Λ i (Z ω) ≤ (n : ℝ)+1
    linarith
  have hyA : Z' ω ∈ A n := by
    intro i
    have hb := hsingle i
    have hnn := hΛ0 i (Z ω)
    change Λ i (Z' ω) ≤ (n : ℝ)+1
    linarith
  calc
    h (Z ω) = f n (Z ω) := hfe n hxA
    _ = f n (Z' ω) := hω n
    _ = h (Z' ω) := (hfe n hyA).symm

end ScalarMonotone.EndOfPaper
end
