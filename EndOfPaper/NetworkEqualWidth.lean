import EndOfPaper.NetworkTailProfileDefinition

/-!
Exact dimension factors for equal-width networks, with no asymptotic replacement of the manuscript constants.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_equal_width_prefactor (L N : ℕ) {d : ℕ} (hd : 0 < d) :
    networkPrefactor L N (fun _ => d) =
      Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : (∑ _i : Fin L, (((d+d : ℕ) : ℝ))⁻¹) = (L : ℝ)/(2*(d : ℝ)) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]
    rw [show (d : ℝ)+(d : ℝ) = 2*(d : ℝ) by ring,div_eq_mul_inv]
  have hin : 1+((N*d : ℕ) : ℝ)*((L : ℝ)/(2*(d : ℝ))) = 1+(N : ℝ)*(L : ℝ)/2 := by
    push_cast
    field_simp [hdR.ne']
    <;> ring
  unfold networkPrefactor
  dsimp only
  rw [hsum,hin,Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv]
  ring

theorem network_equal_width_inverse_dimension {L : ℕ} (N d : ℕ) (i : Fin L) :
    networkInverseDimension N (fun _ => d) i = (Real.sqrt (((d*min N 2 : ℕ) : ℝ)))⁻¹ := by
  have he : min (N*d) (d+d) = d*min N 2 := by
    rw [Nat.mul_comm N d,show d+d = d*2 by omega,min_mul_mul_left]
  unfold networkInverseDimension
  dsimp only
  rw [he]

def networkMedianMaximum {L : ℕ} (mx : ℝ) (mw : Fin L → ℝ) : ℝ :=
  (Finset.univ : Finset (Option (Fin L))).sup' ⟨none,Finset.mem_univ _⟩
    (fun j => match j with | none => mx | some i => mw i)

theorem network_medians_le_maximum {L : ℕ} (mx : ℝ) (mw : Fin L → ℝ) :
    mx ≤ networkMedianMaximum mx mw ∧ ∀ i, mw i ≤ networkMedianMaximum mx mw := by
  constructor
  · exact Finset.le_sup' (fun j : Option (Fin L) => match j with | none => mx | some i => mw i)
      (Finset.mem_univ none)
  · intro i
    exact Finset.le_sup' (fun j : Option (Fin L) => match j with | none => mx | some i => mw i)
      (Finset.mem_univ (some i))

end ScalarMonotone.EndOfPaper
end
