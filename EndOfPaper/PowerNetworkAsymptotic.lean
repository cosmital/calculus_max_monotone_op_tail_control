import EndOfPaper.PowerNetworkProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
The displayed upper profile has exactly the far-tail quantile power alpha*(L+1); this does not assert a lower tail for every network output.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem power_network_bound_rescaled {L : ℕ} (D A α : ℝ) (m κ : Fin L → ℝ)
    {u : ℝ} (hu : 0 < u) :
    powerNetworkBound D A α m κ u * u^(α*((L : ℝ)+1)) =
      D*A*Real.exp (α*(L : ℝ))*6^α * ∏ i, (m i*u^α+κ i*A*12^α) := by
  have hratio (c : ℝ) (hc : 0 ≤ c) : (c/u)^α = c^α*u^(-α) := by
    rw [Real.div_rpow hc hu.le,Real.rpow_neg hu.le,div_eq_mul_inv]
  have hcancel : u^(-α)*u^α = 1 := by
    rw [← Real.rpow_add hu,neg_add_cancel,Real.rpow_zero]
  have hpow : u^(α*((L : ℝ)+1)) = u^α*(u^α)^L := by
    rw [mul_add,mul_one,Real.rpow_add hu,Real.rpow_mul_natCast hu.le,mul_comm]
  have hprod : (∏ i, (m i+κ i*A*(12^α*u^(-α)))) * (u^α)^L =
      ∏ i, (m i*u^α+κ i*A*12^α) := by
    calc
      _ = ∏ i : Fin L, ((m i+κ i*A*(12^α*u^(-α)))*u^α) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        calc
          _ = m i*u^α+(κ i*A*12^α)*(u^(-α)*u^α) := by ring
          _ = _ := by rw [hcancel,mul_one]
  unfold powerNetworkBound
  rw [hratio 6 (by norm_num),hratio 12 (by norm_num),hpow]
  calc
    _ = (D*A*Real.exp (α*(L : ℝ))*6^α)*(u^(-α)*u^α)*
        ((∏ i, (m i+κ i*A*(12^α*u^(-α))))*(u^α)^L) := by ring
    _ = _ := by rw [hcancel,mul_one,hprod]

theorem power_network_far_tail_limit {L : ℕ} (D A α : ℝ) (m κ : Fin L → ℝ)
    (hα : 0 < α) :
    Tendsto (fun u => powerNetworkBound D A α m κ u*u^(α*((L : ℝ)+1)))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (𝓝 (D*A*Real.exp (α*(L : ℝ))*6^α * ∏ i, (κ i*A*12^α))) := by
  have hcont : Continuous (fun u : ℝ =>
      D*A*Real.exp (α*(L : ℝ))*6^α * ∏ i, (m i*u^α+κ i*A*12^α)) := by
    apply continuous_const.mul
    apply continuous_finset_prod
    intro i _
    exact (continuous_const.mul (Real.continuous_rpow_const hα.le)).add continuous_const
  have hlim : Tendsto (fun u : ℝ => D*A*Real.exp (α*(L : ℝ))*6^α *
      ∏ i, (m i*u^α+κ i*A*12^α)) (nhdsWithin 0 (Ioi (0 : ℝ)))
      (𝓝 (D*A*Real.exp (α*(L : ℝ))*6^α * ∏ i, (m i*0^α+κ i*A*12^α))) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun u => powerNetworkBound D A α m κ u*u^(α*((L : ℝ)+1))) =ᶠ[nhdsWithin 0 (Ioi (0 : ℝ))]
      (fun u => D*A*Real.exp (α*(L : ℝ))*6^α * ∏ i, (m i*u^α+κ i*A*12^α)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact power_network_bound_rescaled D A α m κ hu
  simpa only [Real.zero_rpow hα.ne',mul_zero,zero_add] using hlim.congr' heq.symm

theorem power_network_far_tail_constant_positive {L : ℕ} {D A α : ℝ} {κ : Fin L → ℝ}
    (hD : 0 < D) (hA : 0 < A) (hκ : ∀ i, 0 < κ i) :
    0 < D*A*Real.exp (α*(L : ℝ))*6^α * ∏ i, (κ i*A*12^α) := by
  apply mul_pos
  · exact mul_pos (mul_pos (mul_pos hD hA) (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by norm_num) _)
  · exact Finset.prod_pos (fun i _ => mul_pos (mul_pos (hκ i) hA)
      (Real.rpow_pos_of_pos (by norm_num) _))

end ScalarMonotone.EndOfPaper
end
