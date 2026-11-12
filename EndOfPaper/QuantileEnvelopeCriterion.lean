import MonotoneOperators.Survival
import MonotoneOperators.OrderGeometry

/-!
Strict tail probabilities bound every quantile fiber.
An explicit separated-order criterion proves a whole completed-graph
least-upper-bound when its strict graph witnesses are constructed.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem tail_probability_lt_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t r z : ℝ} (hr : r < μ.real (Ioi t)) (hz : z ∈ tailQuantile μ r) :
    t < z := by
  change μ.real (Ioi z) ≤ r ∧ r ≤ μ.real (Ici z) at hz
  by_contra h
  have hzt : z ≤ t := le_of_not_gt h
  have hmono : μ.real (Ioi t) ≤ μ.real (Ioi z) :=
    measureReal_mono (fun x hx => hzt.trans_lt hx)
  exact (not_lt_of_ge (hmono.trans hz.1)) hr

theorem decGraph_upper_domain_nonnegative {A : Set DecGraph} (hne : A.Nonempty)
    (hdom : ∀ C ∈ A, dom C.val ⊆ Icc (0 : ℝ) 1)
    {B : DecGraph} (hB : ∀ C ∈ A, C ≤ B) :
    dom B.val ⊆ Ici (0 : ℝ) := by
  obtain ⟨C, hC⟩ := hne
  have hd := decLE_domains C.property B.property (hB C hC)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hd.1 (mem_upperHull hy)
  exact (hdom C hC hx).1.trans hxy

theorem quantile_family_isLUB {A : Set DecGraph} (hne : A.Nonempty)
    (hdom : ∀ C ∈ A, dom C.val ⊆ Icc (0 : ℝ) 1)
    (f : DecGraph) (hfdom : dom f.val ⊆ Icc (0 : ℝ) 1)
    (hfcover : Ioo (0 : ℝ) 1 ⊆ dom f.val)
    (hupper : ∀ C ∈ A, C ≤ f)
    (hnear : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ a ∈ f p, ∀ t < a,
      ∀ r ∈ Ioo (0 : ℝ) p, ∃ C ∈ A, ∃ z ∈ C r, t < z) :
    IsLUB A f := by
  refine ⟨hupper, ?_⟩
  intro B hB
  have hBdom := decGraph_upper_domain_nonnegative hne hdom hB
  change DecLE f.val B.val
  intro x u y v hu hv hyx
  have hy0 : 0 ≤ y := hBdom ⟨v, hv⟩
  have hx1 : x ≤ 1 := (hfdom ⟨u, hu⟩).2
  obtain ⟨p, hyp, hpx⟩ := exists_between hyx
  have hp : p ∈ Ioo (0 : ℝ) 1 := ⟨hy0.trans_lt hyp, hpx.trans_le hx1⟩
  obtain ⟨a, ha⟩ := hfcover hp
  have hua : u ≤ a := Decreasing.le_of_lt f.property.1 ha hu hpx
  by_contra h
  have hva : v < a := (lt_of_not_ge h).trans_le hua
  obtain ⟨r, hyr, hrp⟩ := exists_between hyp
  obtain ⟨C, hC, z, hz, hvz⟩ := hnear p hp a ha v hva r ⟨hy0.trans_lt hyr, hrp⟩
  have hzv : z ≤ v := hB hC hz hv hyr
  exact (not_lt_of_ge hzv) hvz

end ScalarMonotone.EndOfPaper
end
