import EndOfPaper.IndependentCopyTails

/-!
The original one-sided median-to-copy tail inequality
with coefficient one, needed to derive the network control
profiles. No integrability or atomlessness is assumed.
-/

open Set Filter MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem upper_median_independent_copy_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    {m t : ℝ} (hm : IsRealMedian X μ m) (ht : 0 ≤ t) :
    μ.real {ω | m+t < X ω} ≤ μ.real {ω | t < |X ω-X' ω|} := by
  let A := {ω | m+t < X ω}
  let B := {ω | X ω ≤ m}
  let A' := {ω | m+t < X' ω}
  let B' := {ω | X' ω ≤ m}
  have hB : (1/2 : ℝ) ≤ μ.real B := hm.1
  have heA : μ.real A' = μ.real A :=
    (congrArg ENNReal.toReal (he.measure_mem_eq (measurableSet_Ioi (a := m+t)))).symm
  have heB : μ.real B' = μ.real B :=
    (congrArg ENNReal.toReal (he.measure_mem_eq (measurableSet_Iic (a := m)))).symm
  have hfirst : μ.real (A ∩ B') = μ.real A*μ.real B' :=
    indepFun_measureReal_inter hi measurableSet_Ioi measurableSet_Iic
  have hsecond : μ.real (B ∩ A') = μ.real B*μ.real A' :=
    indepFun_measureReal_inter hi measurableSet_Iic measurableSet_Ioi
  have hhalf := mul_le_mul_of_nonneg_left hB (measureReal_nonneg (μ := μ) (s := A))
  have hlower : μ.real A ≤ μ.real (A ∩ B')+μ.real (B ∩ A') := by
    rw [hfirst,hsecond,heA,heB]
    nlinarith
  have hdisAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro ω hA hBω
    change m+t < X ω at hA
    change X ω ≤ m at hBω
    linarith
  have hdis : Disjoint (A ∩ B') (B ∩ A') := hdisAB.mono inter_subset_left inter_subset_left
  have hmeas : MeasurableSet (B ∩ A') := (hX measurableSet_Iic).inter (hX' measurableSet_Ioi)
  have hsub : (A ∩ B') ∪ (B ∩ A') ⊆ {ω | t < |X ω-X' ω|} := by
    intro ω hω
    rcases hω with ⟨hA,hBω⟩ | ⟨hBω,hA⟩
    · change m+t < X ω at hA
      change X' ω ≤ m at hBω
      change t < |X ω-X' ω|
      linarith [le_abs_self (X ω-X' ω)]
    · change X ω ≤ m at hBω
      change m+t < X' ω at hA
      change t < |X ω-X' ω|
      linarith [neg_le_abs (X ω-X' ω)]
  calc
    μ.real A ≤ μ.real (A ∩ B')+μ.real (B ∩ A') := hlower
    _ = μ.real ((A ∩ B') ∪ (B ∩ A')) := (measureReal_union hdis hmeas).symm
    _ ≤ μ.real {ω | t < |X ω-X' ω|} := measureReal_mono hsub

end ScalarMonotone.EndOfPaper
end
