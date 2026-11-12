import EndOfPaper.GaussianSequenceMaximum
import EndOfPaper.HSMatrixOperator
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
The actual Euclidean operator norm as increasing maxima over one fixed dense sequence of unit pairs. No random maximizer is selected.
-/

open Set Filter
open scoped InnerProductSpace Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

abbrev GaussianUnitVector (m : Type*) [Fintype m] :=
  {u : EuclideanSpace ℝ m // ‖u‖ = 1}

instance gaussian_unit_vector_nonempty (m : Type*) [Fintype m] [Nonempty m] :
    Nonempty (GaussianUnitVector m) := by
  classical
  exact ⟨⟨EuclideanSpace.single (Classical.arbitrary m) (1 : ℝ), by simp⟩⟩

instance gaussian_unit_vector_secondCountable (m : Type*) [Fintype m] :
    SecondCountableTopology (GaussianUnitVector m) := by
  exact ((EuclideanSpace.equiv m ℝ).toHomeomorph.isEmbedding.comp
    (show Topology.IsEmbedding (Subtype.val : GaussianUnitVector m → EuclideanSpace ℝ m) from
      Topology.IsEmbedding.subtypeVal)).secondCountableTopology

def gaussianUnitPairValue {m n : Type*} [Fintype m] [Fintype n]
    (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (p : GaussianUnitVector m × GaussianUnitVector n) : ℝ :=
  ⟪p.1.val,T p.2.val⟫_ℝ

theorem gaussian_unit_pair_value_continuous {m n : Type*} [Fintype m] [Fintype n]
    (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :
    Continuous (gaussianUnitPairValue T) :=
  (continuous_subtype_val.comp continuous_fst).inner
    (T.continuous.comp (continuous_subtype_val.comp continuous_snd))

theorem gaussian_unit_pair_value_le {m n : Type*} [Fintype m] [Fintype n]
    (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (p : GaussianUnitVector m × GaussianUnitVector n) :
    gaussianUnitPairValue T p ≤ ‖T‖ := by
  calc
    _ ≤ ‖p.1.val‖*‖T p.2.val‖ := real_inner_le_norm _ _
    _ ≤ ‖p.1.val‖*(‖T‖*‖p.2.val‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm p.2.val) (norm_nonneg _)
    _ = _ := by rw [p.1.property,p.2.property,one_mul,mul_one]

theorem gaussian_unit_pair_value_isLUB {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :
    IsLUB (range (gaussianUnitPairValue T)) ‖T‖ := by
  constructor
  · rintro _ ⟨p,rfl⟩
    exact gaussian_unit_pair_value_le T p
  · intro b hb
    let u : GaussianUnitVector m := Classical.arbitrary _
    let v : GaussianUnitVector n := Classical.arbitrary _
    have hPlus := hb (mem_range_self (u,v))
    have hMinus := hb (mem_range_self ((⟨-u.val,by simp only [norm_neg,u.property]⟩ : GaussianUnitVector m),v))
    change ⟪u.val,T v.val⟫_ℝ ≤ b at hPlus
    change ⟪-u.val,T v.val⟫_ℝ ≤ b at hMinus
    rw [inner_neg_left] at hMinus
    have hb0 : 0 ≤ b := by linarith only [hPlus,hMinus]
    apply T.opNorm_le_bound hb0
    intro x
    by_cases hx : x = 0
    · simp only [hx,map_zero,norm_zero,mul_zero,le_refl]
    by_cases hy : T x = 0
    · rw [hy,norm_zero]
      exact mul_nonneg hb0 (norm_nonneg x)
    have hxPos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hyPos : 0 < ‖T x‖ := norm_pos_iff.mpr hy
    let vx : GaussianUnitVector n := ⟨‖x‖⁻¹ • x,by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hxPos),inv_mul_cancel₀ hxPos.ne']⟩
    let uy : GaussianUnitVector m := ⟨‖T x‖⁻¹ • T x,by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hyPos),inv_mul_cancel₀ hyPos.ne']⟩
    have hValue : gaussianUnitPairValue T (uy,vx) = ‖T x‖/‖x‖ := by
      change ⟪‖T x‖⁻¹ • T x,T (‖x‖⁻¹ • x)⟫_ℝ = _
      rw [map_smul,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq]
      field_simp
      <;> ring
    have hRatio := hb (mem_range_self (uy,vx))
    rw [hValue] at hRatio
    exact (div_le_iff₀ hxPos).mp hRatio

def gaussianUnitPairSequence (m n : Type*) [Fintype m] [Fintype n] [Nonempty m] [Nonempty n] :
    ℕ → GaussianUnitVector m × GaussianUnitVector n :=
  TopologicalSpace.denseSeq _

theorem gaussian_unit_pair_sequence_dense (m n : Type*) [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] : DenseRange (gaussianUnitPairSequence m n) :=
  TopologicalSpace.denseRange_denseSeq _

theorem gaussian_operator_dense_maximum_tendsto {m n : Type*} [Fintype m] [Fintype n]
    [Nonempty m] [Nonempty n] (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :
    Tendsto (gaussianSequenceMaximum (gaussianUnitPairValue T ∘ gaussianUnitPairSequence m n))
      atTop (𝓝 ‖T‖) := by
  apply gaussian_sequence_maximum_tendsto
  exact gaussian_dense_continuous_isLUB _ (gaussian_unit_pair_sequence_dense m n)
    (gaussian_unit_pair_value_continuous T) (gaussian_unit_pair_value_isLUB T)

end ScalarMonotone.EndOfPaper
end
