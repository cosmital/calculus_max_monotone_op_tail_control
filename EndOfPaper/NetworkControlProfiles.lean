import EndOfPaper.NetworkControls
import EndOfPaper.NormalizedNormLipschitz
import EndOfPaper.MaxMedianControlProfile

/-!
Actual network norm medians are nonnegative, and the original joint baseline gives the displayed whole normalized max-control profiles.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem nonnegative_realMedian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {m : ℝ} (hm : IsRealMedian X μ m) (hX0 : ∀ ω, 0 ≤ X ω) : 0 ≤ m := by
  by_contra h
  have hn : m < 0 := lt_of_not_ge h
  have he : {ω | X ω ≤ m} = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro ω hω
    exact (not_le_of_gt (hn.trans_le (hX0 ω))) hω
  have hh := hm.1
  rw [he,measureReal_empty] at hh
  norm_num at hh

theorem network_normalized_norm_lipschitz {L N : ℕ} {p : ℕ → ℕ}
    (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j) (l : Fin L) :
    let d : ℝ := ((min (N*p 0) (p (l.val+1)+p l.val) : ℕ) : ℝ)
    let K : ℝ≥0 := ⟨(Real.sqrt d)⁻¹,inv_nonneg.mpr (Real.sqrt_nonneg _)⟩
    LipschitzWith K (fun z : NetworkParameters L N p => ‖networkData z‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) ∧
    LipschitzWith K (fun z : NetworkParameters L N p =>
      ‖hsMatrixOp (networkWeight z l)‖/Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ)) := by
  dsimp only
  have hdim : 0 < min (N*p 0) (p (l.val+1)+p l.val) := by
    apply lt_min
    · exact Nat.mul_pos hN (hp 0 (Nat.zero_le L))
    · exact Nat.add_pos_left (hp (l.val+1) (by omega)) _
  have hd : 0 < ((min (N*p 0) (p (l.val+1)+p l.val) : ℕ) : ℝ) := by exact_mod_cast hdim
  constructor
  · have hf : LipschitzWith 1 (fun z : NetworkParameters L N p => ‖networkData z‖) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      have hh : ‖networkData z-networkData w‖ ≤ ‖z-w‖ := by
        simpa only [network_data_sub] using network_data_norm_le (z-w)
      simpa only [Real.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using
        (abs_norm_sub_norm_le (networkData z) (networkData w)).trans hh
    exact inv_sqrt_dimension_lipschitz hf hd (by exact_mod_cast min_le_left (N*p 0) (p (l.val+1)+p l.val))
  · have hf : LipschitzWith 1 (fun z : NetworkParameters L N p => ‖hsMatrixOp (networkWeight z l)‖) := by
      simpa only [one_mul] using hs_matrix_operator_norm_lipschitz.comp (network_weight_lipschitz l)
    exact inv_sqrt_dimension_lipschitz hf hd (by exact_mod_cast min_le_right (N*p 0) (p (l.val+1)+p l.val))

theorem network_control_quantile_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L N : ℕ} {p : ℕ → ℕ}
    [MeasurableSpace (NetworkParameters L N p)] [OpensMeasurableSpace (NetworkParameters L N p)]
    (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j) (l : Fin L)
    {Z Z' : Ω → NetworkParameters L N p} (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ q.val x, 0 ≤ t)
    (hq : ∀ f : NetworkParameters L N p → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q.val)
    {mx mw : ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) μ mx)
    (hmw : IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) l)‖/
      Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ)) μ mw)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s) :
    DecLE (tailQuantile (Measure.map (fun ω => networkControl l (Z ω)) μ))
      (halfAffineProfile q hqi (max mx mw)
        (Real.sqrt (((min (N*p 0) (p (l.val+1)+p l.val) : ℕ) : ℝ)))⁻¹
        (inv_nonneg.mpr (Real.sqrt_nonneg _))).val := by
  have hdim : 0 < min (N*p 0) (p (l.val+1)+p l.val) :=
    lt_min (Nat.mul_pos hN (hp 0 (Nat.zero_le L))) (Nat.add_pos_left (hp (l.val+1) (by omega)) _)
  have hK : 0 < (Real.sqrt (((min (N*p 0) (p (l.val+1)+p l.val) : ℕ) : ℝ)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hdim))
  have hLip := network_normalized_norm_lipschitz hN hp l
  exact max_median_control_quantile_bound hZ hZ' hi he hqi hq0 hq
    (K := ⟨(Real.sqrt (((min (N*p 0) (p (l.val+1)+p l.val) : ℕ) : ℝ)))⁻¹,
      inv_nonneg.mpr (Real.sqrt_nonneg _)⟩) hK hLip.1 hLip.2 hmx hmw hs

end ScalarMonotone.EndOfPaper
end
