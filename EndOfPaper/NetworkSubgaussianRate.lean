import EndOfPaper.NetworkSubgaussianDepth
import EndOfPaper.NetworkUniformRate

/-!
The original joint-law subgaussian network example gives the stated two-regime rate. The uniform constant depends only on the depth, baseline constant, median bound and batch-to-width upper bound.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_subgaussian_two_regime_tail {L N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
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
    {A : ℝ} (hA : 0 ≤ A) (hSG : DecLE qδ.val (affineSqrtLogProfile 0 A hA).val)
    {c M : ℝ} (hRatio : (N : ℝ)/(d : ℝ) ≤ c) (hmxM : mx ≤ M) (hmwM : ∀ i, mw i ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | A*Real.sqrt (1+c*(L : ℝ)/2)*(M+A)^L*t < |g (finiteNetworkMap σ (Z ω))-mV|} ≤
      24*Real.exp 1*Real.exp (-(min (t^2)
        ((d : ℝ)^((L : ℝ)/((L : ℝ)+1))*t^(2/((L : ℝ)+1))))) := by
  classical
  have hmx0 : 0 ≤ mx := nonnegative_realMedian hmx
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hm : 0 ≤ networkMedianMaximum mx mw := hmx0.trans (network_medians_le_maximum mx mw).1
  have hmM : networkMedianMaximum mx mw ≤ M := by
    apply Finset.sup'_le
    intro j _
    cases j with
    | none => exact hmxM
    | some i => exact hmwM i
  have hTail := network_subgaussian_depth hL hN hd σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ
    hmx hmw hg hmV hA hSG
  exact network_depth_tail_implies_uniform_rate L hN hd hRatio hm hmM hA hTail ht

end ScalarMonotone.EndOfPaper
end
