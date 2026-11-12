import EndOfPaper.GaussianMatrixMedian
import EndOfPaper.GaussianHSNormMedian
import EndOfPaper.NetworkParameters

/-!
The two literal network median constants, derived from the joint standard Gaussian entry laws on the original parameter probability space.
-/

open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_network_data_median {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {Z : Ω → NetworkParameters L N (fun _ => d)}
    (hi : iIndepFun (fun i => fun ω => Z ω i) μ)
    (hm : ∀ i, Measurable (fun ω => Z ω i))
    (hLaw : ∀ i, Measure.map (fun ω => Z ω i) μ = gaussianReal 0 1)
    {mx : ℝ} (hmed : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ mx) :
    mx ≤ 1+Real.sqrt (2*Real.log 2/((N*d : ℕ) : ℝ)) := by
  have hInd : iIndepFun (fun i : Fin d × Fin N => fun ω => networkData (Z ω) i) μ :=
    iIndepFun.precomp (fun _ _ h => Sum.inl.inj h) hi
  exact gaussian_hs_normalized_median hN hd hInd
    (fun i => hm (Sum.inl i)) (fun i => hLaw (Sum.inl i)) hmed

theorem gaussian_network_weight_median {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L N d : ℕ} (hd : 0 < d)
    {Z : Ω → NetworkParameters L N (fun _ => d)}
    (hi : iIndepFun (fun i => fun ω => Z ω i) μ)
    (hm : ∀ i, Measurable (fun ω => Z ω i))
    (hLaw : ∀ i, Measure.map (fun ω => Z ω i) μ = gaussianReal 0 1)
    (l : Fin L) {mw : ℝ}
    (hmed : IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) l)‖/
      Real.sqrt ((d+d : ℕ) : ℝ)) μ mw) :
    mw ≤ Real.sqrt 2+Real.sqrt (Real.log 2/(d : ℝ)) := by
  have hInd : iIndepFun (fun i : Fin d × Fin d => fun ω => networkWeight (Z ω) l i) μ :=
    iIndepFun.precomp (fun _ _ h => sigma_mk_injective (Sum.inr.inj h)) hi
  have hmed' : IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) l)‖/
      Real.sqrt (2*(d : ℝ))) μ mw := by
    simpa only [Nat.cast_add,two_mul] using hmed
  exact gaussian_square_matrix_normalized_operator_median hd hInd
    (fun i => hm (Sum.inr ⟨l,i⟩)) (fun i => hLaw (Sum.inr ⟨l,i⟩)) hmed'

theorem gaussian_network_norm_medians {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {Z : Ω → NetworkParameters L N (fun _ => d)}
    (hi : iIndepFun (fun i => fun ω => Z ω i) μ)
    (hm : ∀ i, Measurable (fun ω => Z ω i))
    (hLaw : ∀ i, Measure.map (fun ω => Z ω i) μ = gaussianReal 0 1)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ mx)
    (hmw : ∀ l, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) l)‖/
      Real.sqrt ((d+d : ℕ) : ℝ)) μ (mw l)) :
    mx ≤ 1+Real.sqrt (2*Real.log 2/((N*d : ℕ) : ℝ)) ∧
      ∀ l, mw l ≤ Real.sqrt 2+Real.sqrt (Real.log 2/(d : ℝ)) :=
  ⟨gaussian_network_data_median hN hd hi hm hLaw hmx,
    fun l => gaussian_network_weight_median hd hi hm hLaw l (hmw l)⟩

end ScalarMonotone.EndOfPaper
end
