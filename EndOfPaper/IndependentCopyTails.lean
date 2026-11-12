import EndOfPaper.EndpointSymmetry

/-!
The original-space median-to-copy and copy-to-pivot
strict-tail comparisons, without integrability and with atoms allowed.
-/

open Set Filter MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

def IsRealMedian {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (μ : Measure Ω) (m : ℝ) : Prop :=
  (1/2 : ℝ) ≤ μ.real {ω | X ω ≤ m} ∧ (1/2 : ℝ) ≤ μ.real {ω | m ≤ X ω}

theorem indepFun_measureReal_inter {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ} (hi : IndepFun X Y μ)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    μ.real (X ⁻¹' S ∩ Y ⁻¹' T) = μ.real (X ⁻¹' S)*μ.real (Y ⁻¹' T) := by
  exact (congrArg ENNReal.toReal (hi.measure_inter_preimage_eq_mul S T hS hT)).trans
    ENNReal.toReal_mul

theorem median_independent_copy_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    {m t : ℝ} (hm : IsRealMedian X μ m) (ht : 0 ≤ t) :
    μ.real {ω | t < |X ω-m|} ≤ 2*μ.real {ω | t < |X ω-X' ω|} := by
  let A := {ω | X ω < m-t}
  let B := {ω | m+t < X ω}
  let C := {ω | m ≤ X' ω}
  let D := {ω | X' ω ≤ m}
  have hAm : MeasurableSet A := hX measurableSet_Iio
  have hBm : MeasurableSet B := hX measurableSet_Ioi
  have hCm : MeasurableSet C := hX' measurableSet_Ici
  have hDm : MeasurableSet D := hX' measurableSet_Iic
  have hC : (1/2 : ℝ) ≤ μ.real C := by
    have heC : μ.real {ω | m ≤ X ω} = μ.real C :=
      congrArg ENNReal.toReal (he.measure_mem_eq measurableSet_Ici)
    rw [← heC]
    exact hm.2
  have hD : (1/2 : ℝ) ≤ μ.real D := by
    have heD : μ.real {ω | X ω ≤ m} = μ.real D :=
      congrArg ENNReal.toReal (he.measure_mem_eq measurableSet_Iic)
    rw [← heD]
    exact hm.1
  have hAC : μ.real (A ∩ C) = μ.real A*μ.real C :=
    indepFun_measureReal_inter hi measurableSet_Iio measurableSet_Ici
  have hBD : μ.real (B ∩ D) = μ.real B*μ.real D :=
    indepFun_measureReal_inter hi measurableSet_Ioi measurableSet_Iic
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro ω hA hB
    change X ω < m-t at hA
    change m+t < X ω at hB
    linarith
  have hpairdis : Disjoint (A ∩ C) (B ∩ D) := hdis.mono inter_subset_left inter_subset_left
  have hsub : (A ∩ C) ∪ (B ∩ D) ⊆ {ω | t < |X ω-X' ω|} := by
    intro ω hω
    rcases hω with ⟨hA,hCω⟩ | ⟨hB,hDω⟩
    · change X ω < m-t at hA
      change m ≤ X' ω at hCω
      have hh := neg_le_abs (X ω-X' ω)
      change t < |X ω-X' ω|
      linarith
    · change m+t < X ω at hB
      change X' ω ≤ m at hDω
      have hh := le_abs_self (X ω-X' ω)
      change t < |X ω-X' ω|
      linarith
  have hlowA := mul_le_mul_of_nonneg_left hC (measureReal_nonneg (μ := μ) (s := A))
  have hlowB := mul_le_mul_of_nonneg_left hD (measureReal_nonneg (μ := μ) (s := B))
  have hsum : (μ.real A+μ.real B)/2 ≤ μ.real (A ∩ C)+μ.real (B ∩ D) := by
    rw [hAC,hBD]
    linarith
  have hupper : μ.real (A ∩ C)+μ.real (B ∩ D) ≤ μ.real {ω | t < |X ω-X' ω|} := by
    rw [← measureReal_union hpairdis (hBm.inter hDm)]
    exact measureReal_mono hsub
  have hset : {ω | t < |X ω-m|} = A ∪ B := by
    ext ω
    constructor
    · intro hω
      change t < |X ω-m| at hω
      by_cases hA : X ω < m-t
      · exact Or.inl hA
      · right
        by_contra hB
        have hb : X ω ≤ m+t := le_of_not_gt hB
        have ha : m-t ≤ X ω := le_of_not_gt hA
        have habs : |X ω-m| ≤ t := abs_le.mpr ⟨by linarith,by linarith⟩
        exact (not_le_of_gt hω) habs
    · intro hω
      change t < |X ω-m|
      rcases hω with hA | hB
      · change X ω < m-t at hA
        linarith [neg_le_abs (X ω-m)]
      · change m+t < X ω at hB
        linarith [le_abs_self (X ω-m)]
  rw [hset,measureReal_union hdis hBm]
  linarith

theorem independent_copy_pivot_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (he : IdentDistrib X X' μ μ) (c t : ℝ) :
    μ.real {ω | t < |X ω-X' ω|} ≤ 2*μ.real {ω | t/2 < |X ω-c|} := by
  have hsub : {ω | t < |X ω-X' ω|} ⊆
      {ω | t/2 < |X ω-c|} ∪ {ω | t/2 < |X' ω-c|} := by
    intro ω hω
    by_cases hA : t/2 < |X ω-c|
    · exact Or.inl hA
    · right
      by_contra hB
      have htri : |X ω-X' ω| ≤ |X ω-c|+|X' ω-c| := by
        simpa only [abs_sub_comm c (X' ω)] using abs_sub_le (X ω) c (X' ω)
      change t < |X ω-X' ω| at hω
      have hA' : |X ω-c| ≤ t/2 := le_of_not_gt hA
      have hB' : |X' ω-c| ≤ t/2 := le_of_not_gt hB
      linarith
  have hMeas : Measurable (fun x : ℝ => |x-c|) := (measurable_id.sub_const c).abs
  have heTail : μ.real {ω | t/2 < |X ω-c|} = μ.real {ω | t/2 < |X' ω-c|} :=
    congrArg ENNReal.toReal (he.measure_mem_eq
      (show MeasurableSet {x : ℝ | t/2 < |x-c|} from
        hMeas measurableSet_Ioi))
  have hb : μ.real {ω | t < |X ω-X' ω|} ≤
      μ.real {ω | t/2 < |X ω-c|}+μ.real {ω | t/2 < |X' ω-c|} :=
    (measureReal_mono hsub).trans (measureReal_union_le
    {ω | t/2 < |X ω-c|} {ω | t/2 < |X' ω-c|})
  rw [← heTail] at hb
  linarith

end ScalarMonotone.EndOfPaper
end
