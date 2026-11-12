import EndOfPaper.NetworkTailProfiles
import EndOfPaper.NetworkEqualWidth
import EndOfPaper.SqrtLogNetworkMajorant

/-!
The exact equal-width strict-tail inequality in the subgaussian depth example. The baseline is a property of the original joint law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_subgaussian_depth {L N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NetworkParameters L N (fun _ => d))]
    [OpensMeasurableSpace (NetworkParameters L N (fun _ => d))]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → NetworkParameters L N (fun _ => d)}
    (hL : 0 < L) (hN : 0 < N) (hd : 0 < d)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ i, LipschitzWith 1 (σ i)) (hσ0 : ∀ i, σ i 0 = 0)
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {qδ : DecGraph} (hδdom : interior (dom qδ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qδ.val x, 0 ≤ v)
    (hδ : ∀ f : NetworkParameters L N (fun _ => d) → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qδ.val)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ mx)
    (hmw : ∀ i : Fin L, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) i)‖/
      Real.sqrt ((d+d : ℕ) : ℝ)) μ (mw i))
    {g : HSMatrix (Fin d) (Fin N) → ℝ} (hg : LipschitzWith 1 g) {mV : ℝ}
    (hmV : IsRealMedian (fun ω => g (finiteNetworkMap σ (Z ω))) μ mV)
    {A : ℝ} (hA : 0 ≤ A) (hSG : DecLE qδ.val (affineSqrtLogProfile 0 A hA).val) :
    ∀ u ∈ Ioo (0 : ℝ) 1,
      μ.real {ω | A*Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ))*networkDepthRadius u*
        (networkMedianMaximum mx mw+A*networkDepthRadius u/
          Real.sqrt (((d*min N 2 : ℕ) : ℝ)))^L < |g (finiteNetworkMap σ (Z ω))-mV|} ≤ u := by
  classical
  have hp : ∀ j ≤ L, 0 < (fun _ : ℕ => d) j := fun _ _ => hd
  have hmx0 : 0 ≤ mx := nonnegative_realMedian hmx
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hmw0 (i : Fin L) : 0 ≤ mw i := nonnegative_realMedian (hmw i)
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hm (i : Fin L) : 0 ≤ max mx (mw i) := hmx0.trans (le_max_left _ _)
  have hκ (i : Fin L) : 0 ≤ networkInverseDimension N (fun _ => d) i :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hD := network_prefactor_pos (N := N) (L := L) (p := fun _ => d) hd
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection (Or.inr qδ.property.1) measurableSet_Ioo
    (fun x hx => interior_subset (by rwa [hδdom]))
  have hP := positive_log_area_of_sqrt_log_control hδ0 hs hA hSG
  have hNet := network_tail_profiles hL hN hp σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV hs hP
  have hT := network_tail_profile_geometry (N := N) (L := L) (p := fun _ => d) hd
    hδdom hδ0 hsm hs hP hmx0 hmw0
  have hVm : Measurable (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) :=
    ((((hg.continuous.comp (finite_network_continuous hN hp σ hσ hσ0)).measurable).comp hZ).sub
      measurable_const).abs
  let M := networkMedianMaximum mx mw
  let k := (Real.sqrt (((d*min N 2 : ℕ) : ℝ)))⁻¹
  have hmed := network_medians_le_maximum mx mw
  have hM : 0 ≤ M := hmx0.trans hmed.1
  have hk : 0 ≤ k := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hmM (i : Fin L) : max mx (mw i) ≤ M := max_le hmed.1 (hmed.2 i)
  have hκk (i : Fin L) : networkInverseDimension N (fun _ => d) i ≤ k :=
    (network_equal_width_inverse_dimension N d i).le
  intro u hu
  have hBase := quantile_comparison_strict_tail hVm hNet.2.2 (hT.2.2 u hu)
  have hBound := sqrt_log_network_selection_bound hδdom hδ0 hsm hs hD.le hA hM hk hSG hm hκ hmM hκk hu
  have hkAR : k*A*networkDepthRadius u = A*networkDepthRadius u/
      Real.sqrt (((d*min N 2 : ℕ) : ℝ)) := by
    dsimp only [k]
    rw [div_eq_mul_inv]
    ring
  have hEq : networkPrefactor L N (fun _ => d)*A*networkDepthRadius u*
      (M+k*A*networkDepthRadius u)^L =
      A*Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ))*networkDepthRadius u*
        (M+A*networkDepthRadius u/Real.sqrt (((d*min N 2 : ℕ) : ℝ)))^L := by
    rw [network_equal_width_prefactor L N hd,hkAR]
    ring
  rw [hEq] at hBound
  exact (measureReal_mono (fun ω hω => lt_of_le_of_lt hBound hω)).trans hBase

end ScalarMonotone.EndOfPaper
end
