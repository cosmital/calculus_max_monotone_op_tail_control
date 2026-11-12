import EndOfPaper.NetworkTailGeometry
import EndOfPaper.NetworkControlProfiles
import EndOfPaper.PositiveMedianScaling
import EndOfPaper.RandomizedMedianAllProfiles

/-!
The full original network tail theorem, allowing arbitrary original profile selections and retaining zero inputs, atoms, original dependence and every completed fiber.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper
section
variable {L N : ℕ} {p : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
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
include hL hN hp σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV

theorem network_tail_profiles_of_measurable_selection {sδ : ℝ → ℝ}
    (hsm : Measurable sδ) (hsδ : SelectionOn qδ.val (Ioo (0 : ℝ) 1) sδ)
    (hPδ : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ x)) 0)) < ∞) :
    MaximalDecreasing (networkTailProfile N p qδ hδdom mx mw) ∧
      interior (dom (networkTailProfile N p qδ hδdom mx mw)) = Ioo (0 : ℝ) 1 ∧
      DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ))
        (networkTailProfile N p qδ hδdom mx mw) := by
  classical
  have hmx0 : 0 ≤ mx := nonnegative_realMedian hmx
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hmw0 (i : Fin L) : 0 ≤ mw i := nonnegative_realMedian (hmw i)
    (fun ω => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  let κ : Fin L → ℝ := networkInverseDimension N p
  let a := fun i : Fin L => max mx (mw i)
  have ha (i : Fin L) : 0 ≤ a i := hmx0.trans (le_max_left _ _)
  have hκ (i : Fin L) : 0 ≤ κ i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let q : Fin L → DecGraph := fun i => halfAffineProfile qδ hδdom (a i) (κ i) (hκ i)
  let s := fun i : Fin L => fun x : ℝ => a i+κ i*sδ (x/2)
  let sr := fun i : Fin L => fun x : ℝ => a i+κ i*sδ x
  have hqdata (i : Fin L) : interior (dom (q i).val) = Ioo (0 : ℝ) 1 ∧
      SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i) :=
    halfAffineProfile_selection hδdom (hκ i) hsδ
  have hqdom (i : Fin L) : interior (dom (q i).val) = Ioo (0 : ℝ) 1 := (hqdata i).1
  have hsq (i : Fin L) : SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i) := (hqdata i).2
  have hq0 (i : Fin L) : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val x, 0 ≤ v :=
    halfAffineProfile_nonnegative hδdom (ha i) (hκ i) hδ0
  have hPi (i : Fin L) : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞ :=
    half_affine_positive_log_area_finite hsm (fun x hx => hδ0 x hx _ (hsδ x hx)) hPδ (ha i) (hκ i)
  have hQ (i : Fin L) : DecLE (tailQuantile (Measure.map (fun ω => networkControl i (Z ω)) μ)) (q i).val :=
    network_control_quantile_bound hN hp i hZ hZ' hi he hδdom hδ0 hδ hmx (hmw i) hsδ
  have hms (i : Fin L) : Measurable (s i) := by dsimp only [s]; fun_prop
  let S : Option (Fin L) → ℝ → ℝ := fun j => match j with | none => sδ | some i => s i
  have hSM (j : Option (Fin L)) : Measurable (S j) := by
    cases j with | none => exact hsm | some i => exact hms i
  have hS0 (j : Option (Fin L)) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ S j x := by
    cases j with
    | none => exact hδ0 x hx _ (hsδ x hx)
    | some i => exact hq0 i x hx _ (hsq i x hx)
  have hPS (j : Option (Fin L)) :
      (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (S j x)) 0)) < ∞ := by
    cases j with | none => exact hPδ | some i => exact hPi i
  have hPtotal : (∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sδ x*(∏ i, s i x))) 0)) < ∞ := by
    have hh := positive_log_area_finset_prod_finite hSM hS0 hPS Finset.univ
    have heq (x : ℝ) : (∏ j : Option (Fin L), S j x) = sδ x*(∏ i, s i x) := by
      rw [Fintype.prod_option]
    simpa only [heq] using hh
  let C := networkPrefactor L N p
  have hC : 0 < C := network_prefactor_pos (N := N) (hp L le_rfl)
  let φ := fun z : NetworkParameters L N p => g (finiteNetworkMap σ z)/C
  have hφm : Measurable φ :=
    (normalized_network_observation_continuous hN hp σ hσ hσ0 hg).measurable
  have hφmod (z w : NetworkParameters L N p) :
      dist (φ z) (φ w) ≤ dist z w*(∏ i, max (networkControl i z) (networkControl i w)) :=
    normalized_network_observation_modulus hN hp σ hσ hσ0 hg z w
  have hφmedian : IsRealMedian (fun ω => φ (Z ω)) μ (mV/C) := isRealMedian_div_positive hmV hC
  have hΛm (i : Fin L) : Measurable (networkControl i : NetworkParameters L N p → ℝ) :=
    (network_control_continuous i).measurable
  let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
  let P := completedProfileProduct 1 qδ G (by norm_num) hδdom hG.1 hδ0 hG.2.1
  have hPD := (completedProfileProduct_domain (by norm_num) hδdom hG.1 hδ0 hG.2.1).1
  let D := completedProfileDilation 1 1 (1/6) P hPD (by norm_num) (by norm_num) (by norm_num)
  have hDI : interior (dom D.val) = Ioo (0 : ℝ) 1 :=
    (completedProfileDilation_properties hPD (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/6) (by norm_num : (1/6 : ℝ)*1 ≤ 1)).1
  have hBound : DecLE (tailQuantile (Measure.map (fun ω => |φ (Z ω)-mV/C|) μ)) D.val :=
    randomized_lipschitz_median_with_individual_areas hL hZ hZ' hi he hδdom hδ0 hδ hΛm
      network_control_nonnegative hqdom hq0 hQ hsδ hsq hPtotal hPi hφm hφmod LipschitzWith.id hφmedian
  have hDS : SelectionOn D.val (Ioo (0 : ℝ) 1)
      (fun u => sδ ((1/6)*u)*(∏ i, geometricPrefixValue (s i) ((1/6)*u))) :=
    geometric_product_dilation_selection hδdom hδ0 hqdom hq0 hsδ hsq hPi
      (by norm_num : (0 : ℝ) < 1/6) (by norm_num : (1/6 : ℝ) ≤ 1)
  let τ := fun u : ℝ => sδ (u/6)*(∏ i, geometricPrefixValue (sr i) (u/12))
  have hDτ : SelectionOn D.val (Ioo (0 : ℝ) 1) τ := by
    intro u hu
    have hh := hDS u hu
    change sδ ((1/6)*u)*(∏ i, geometricPrefixValue (s i) ((1/6)*u)) ∈ D.val u at hh
    have hu6 : (1/6 : ℝ)*u = u/6 := by ring
    rw [hu6] at hh
    have heq : (∏ i, geometricPrefixValue (s i) (u/6)) =
        ∏ i, geometricPrefixValue (sr i) (u/12) := by
      apply Finset.prod_congr rfl
      intro i _
      exact half_affine_geometric_network_level hδdom hδ0 hsm hsδ hPδ (ha i) (hκ i) hu
    rw [heq] at hh
    exact hh
  have hTarget := network_tail_profile_geometry (N := N) (hp L le_rfl) hδdom hδ0 hsm hsδ hPδ hmx0 hmw0
  have hTargetS : SelectionOn (networkTailProfile N p qδ hδdom mx mw) (Ioo (0 : ℝ) 1)
      (fun u => C*τ u) := by
    intro u hu
    have hh := hTarget.2.2 u hu
    simpa only [C,τ,sr,a,κ,mul_assoc] using hh
  have hScaledI : interior (dom (outputScale C D.val)) = Ioo (0 : ℝ) 1 := by
    rw [dom_outputScale]
    exact hDI
  have hScaledS : SelectionOn (outputScale C D.val) (Ioo (0 : ℝ) 1) (fun u => C*τ u) :=
    fun u hu => ⟨τ u,hDτ u hu,rfl⟩
  have hEq : outputScale C D.val = networkTailProfile N p qδ hδdom mx mw :=
    (initial_profile_eq_completed_scalar (by norm_num) (outputScale_maximal_decreasing hC D.property)
      hScaledI hScaledS).trans
    (initial_profile_eq_completed_scalar (by norm_num) hTarget.1 hTarget.2.1 hTargetS).symm
  have hVm : Measurable (fun ω => g (finiteNetworkMap σ (Z ω))) :=
    ((hg.continuous.comp (finite_network_continuous hN hp σ hσ hσ0)).measurable).comp hZ
  have hMain : DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ))
      (outputScale C D.val) := by
    rw [centered_quantile_positive_normalization hVm mV hC]
    exact (decLE_outputScale_iff hC).mpr hBound
  rw [hEq] at hMain
  exact ⟨hTarget.1,hTarget.2.1,hMain⟩

theorem network_tail_profiles {sδ : ℝ → ℝ}
    (hsδ : SelectionOn qδ.val (Ioo (0 : ℝ) 1) sδ)
    (hPδ : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ x)) 0)) < ∞) :
    MaximalDecreasing (networkTailProfile N p qδ hδdom mx mw) ∧
      interior (dom (networkTailProfile N p qδ hδdom mx mw)) = Ioo (0 : ℝ) 1 ∧
      DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ))
        (networkTailProfile N p qδ hδdom mx mw) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hδdom hsδ
  have htP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rw [harea]
    exact hPδ
  exact network_tail_profiles_of_measurable_selection hL hN hp σ hσ hσ0 hZ hZ' hi he
    hδdom hδ0 hδ hmx hmw hg hmV ht hts htP

end
end ScalarMonotone.EndOfPaper
end
