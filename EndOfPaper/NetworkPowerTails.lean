import EndOfPaper.NetworkTailProfiles
import EndOfPaper.PowerNetworkProfile
import EndOfPaper.PowerNetworkAsymptotic

/-!
The original joint-law power-tail network example, with the displayed whole completed bound and strict tails, without a separate log-area assumption.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_inverse_dimension_pos {L N : ℕ} {p : ℕ → ℕ}
    (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j) (i : Fin L) :
    0 < networkInverseDimension N p i := by
  have hdim : 0 < min (N*p 0) (p (i.val+1)+p i.val) :=
    lt_min (Nat.mul_pos hN (hp 0 (Nat.zero_le L))) (Nat.add_pos_left (hp (i.val+1) (by omega)) _)
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hdim))

theorem power_network_bound_network_formula {L : ℕ} (N : ℕ) (p : ℕ → ℕ)
    (A α mx : ℝ) (mw : Fin L → ℝ) (u : ℝ) :
    powerNetworkBound (networkPrefactor L N p) A α (fun i => max mx (mw i))
      (networkInverseDimension N p) u =
    networkPrefactor L N p*A*Real.exp (α*(L : ℝ))*(6/u)^α *
      ∏ i, (max mx (mw i)+A*(12/u)^α/
        Real.sqrt (((min (N*p 0) (p (i.val+1)+p i.val) : ℕ) : ℝ))) := by
  unfold powerNetworkBound
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  unfold networkInverseDimension
  rw [div_eq_mul_inv]
  ring

theorem network_power_far_tail {L N : ℕ} {p : ℕ → ℕ}
    (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j) {A α mx : ℝ} (mw : Fin L → ℝ)
    (hA : 0 < A) (hα : 0 < α) :
    let C := networkPrefactor L N p*A*Real.exp (α*(L : ℝ))*6^α *
      ∏ i : Fin L, (networkInverseDimension N p i*A*12^α)
    0 < C ∧ Tendsto (fun u => powerNetworkBound (networkPrefactor L N p) A α
      (fun i => max mx (mw i)) (networkInverseDimension N p) u*u^(α*((L : ℝ)+1)))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 C) := by
  exact ⟨power_network_far_tail_constant_positive
      (network_prefactor_pos (N := N) (hp L le_rfl)) hA (network_inverse_dimension_pos hN hp),
    power_network_far_tail_limit _ A α (fun i => max mx (mw i)) _ hα⟩

theorem network_power_tails {L N : ℕ} {p : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NetworkParameters L N p)] [OpensMeasurableSpace (NetworkParameters L N p)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → NetworkParameters L N p}
    (hL : 0 < L) (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ i, LipschitzWith 1 (σ i)) (hσ0 : ∀ i, σ i 0 = 0)
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {qδ : DecGraph} (hδdom : interior (dom qδ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qδ.val x, 0 ≤ v)
    (hδ : ∀ f : NetworkParameters L N p → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qδ.val)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) μ mx)
    (hmw : ∀ i : Fin L, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) i)‖/
      Real.sqrt ((p (i.val+1)+p i.val : ℕ) : ℝ)) μ (mw i))
    {g : HSMatrix (Fin (p L)) (Fin N) → ℝ} (hg : LipschitzWith 1 g) {mV : ℝ}
    (hmV : IsRealMedian (fun ω => g (finiteNetworkMap σ (Z ω))) μ mV)
    {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hPower : DecLE qδ.val (affinePowerProfile 0 A α hA.le hα).val) :
    let B := powerNetworkBound (networkPrefactor L N p) A α (fun i => max mx (mw i))
      (networkInverseDimension N p)
    let R := completedDecreasingRestriction (Ioo (0 : ℝ) 1) (ofFun B)
    MaximalDecreasing R ∧ interior (dom R) = Ioo (0 : ℝ) 1 ∧
    DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ)) R ∧
    ∀ u ∈ Ioo (0 : ℝ) 1,
      (∀ v ∈ tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ) u,
        v ≤ B u) ∧ μ.real {ω | B u < |g (finiteNetworkMap σ (Z ω))-mV|} ≤ u := by
  classical
  dsimp only
  have hmx0 : 0 ≤ mx := nonnegative_realMedian hmx
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hmw0 (i : Fin L) : 0 ≤ mw i := nonnegative_realMedian (hmw i)
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hm (i : Fin L) : 0 ≤ max mx (mw i) := hmx0.trans (le_max_left _ _)
  have hκ (i : Fin L) : 0 ≤ networkInverseDimension N p i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hD := network_prefactor_pos (N := N) (hp L le_rfl)
  obtain ⟨s,hsm,hs⟩ := exists_global_measurable_selection (Or.inr qδ.property.1) measurableSet_Ioo
    (fun x hx => interior_subset (by rwa [hδdom]))
  have hP := positive_log_area_of_power_control hδ0 hs hA hα hPower
  have hNet := network_tail_profiles hL hN hp σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV hs hP
  have hT := network_tail_profile_geometry (N := N) (hp L le_rfl) hδdom hδ0 hsm hs hP hmx0 hmw0
  have hVm : Measurable (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) :=
    ((((hg.continuous.comp (finite_network_continuous hN hp σ hσ hσ0)).measurable).comp hZ).sub
      measurable_const).abs
  letI : IsProbabilityMeasure (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ) :=
    isProbabilityMeasure_map hVm.aemeasurable
  let B := powerNetworkBound (networkPrefactor L N p) A α (fun i => max mx (mw i))
    (networkInverseDimension N p)
  let P := powerNetworkProfile (networkPrefactor L N p) A α (fun i => max mx (mw i))
    (networkInverseDimension N p) hD.le hA.le hα hm hκ
  have hPP := power_network_profile_properties hD.le hA.le hα hm hκ
  have hTail (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      μ.real {ω | B u < |g (finiteNetworkMap σ (Z ω))-mV|} ≤ u := by
    have hBase := quantile_comparison_strict_tail hVm hNet.2.2 (hT.2.2 u hu)
    have hBound := power_network_selection_bound hδdom hδ0 hsm hs hD.le hA hα hPower hm hκ hu
    exact (measureReal_mono (fun ω hω => lt_of_le_of_lt hBound hω)).trans hBase
  have hQ : DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ)) P.val :=
    tailQuantile_decLE_of_profile_selection_tail_bounds hVm P.property hPP.1 hPP.2.1 hTail
  refine ⟨P.property,hPP.1,hQ,?_⟩
  intro u hu
  refine ⟨?_,hTail u hu⟩
  intro v hv
  exact decLE_value_le_singleton (tailQuantile_maximal _) P.property hQ hv (hPP.2.2 u hu)

end ScalarMonotone.EndOfPaper
end
