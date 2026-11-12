import MonotoneOperators.Minty

/-!
# Completed survival graphs and tail quantiles

Probability statements are made for the law `μ : Measure ℝ`. This separates
the graph calculus from a particular realization of a random variable.
The quantile selection theorem uses the uniform measure on `(0,1)`.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace ScalarMonotone

/-- Filling the jumps of a right-continuous monotone function. -/
def completedStieltjes (F : StieltjesFunction) : Operator :=
  fun x => Icc (Function.leftLim F x) (F x)

theorem completedStieltjes_top_mem (F : StieltjesFunction) (x : ℝ) :
    F x ∈ completedStieltjes F x :=
  ⟨F.mono.leftLim_le le_rfl, le_rfl⟩

/-- A completed Stieltjes graph is maximally increasing on the whole real line. -/
theorem completedStieltjes_maximal (F : StieltjesFunction) :
    MaximalIncreasing (completedStieltjes F) := by
  refine ⟨?_, ?_⟩
  · apply increasing_iff_order.mpr
    intro x u y v hu hv hxy
    exact hu.2.trans ((F.mono.le_leftLim hxy).trans hv.1)
  · intro x u hc
    have hb := compatible_iff_bounds.mp hc
    constructor
    · apply le_of_tendsto (F.mono.tendsto_leftLim x)
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hb.1 (completedStieltjes_top_mem F y) hy
    · have hlim : Tendsto F (𝓝[>] x) (𝓝 (F x)) :=
        (F.right_continuous x).mono Ioi_subset_Ici_self
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hb.2 (completedStieltjes_top_mem F y) hy

/-- An output translation preserves maximal increasing graphs. -/
private theorem output_translation_maximal {f : Operator} (hf : MaximalIncreasing f) (a : ℝ) :
    MaximalIncreasing (fun x => {u | u + a ∈ f x}) := by
  refine ⟨?_, ?_⟩
  · intro x u y v hu hv
    have h := hf.1 hu hv
    nlinarith
  · intro x u hc
    apply hf.2
    intro y v hv
    have hv' : v - a ∈ {w | w + a ∈ f y} := by simpa using hv
    have h := hc hv'
    nlinarith

/-- The survival graph includes both strict and weak upper-tail probabilities. -/
def survival (μ : Measure ℝ) : Operator :=
  fun t => Icc (μ.real (Ioi t)) (μ.real (Ici t))

def tailQuantile (μ : Measure ℝ) : Operator := inverse (survival μ)

theorem survival_lower_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ.real (Ioi x) = 1 - cdf μ x := by
  have h := (cdf μ).measure_Ioi (tendsto_cdf_atTop μ) x
  rw [measure_cdf μ] at h
  rw [measureReal_def, h, ENNReal.toReal_ofReal (sub_nonneg.mpr (cdf_le_one μ x))]

theorem survival_upper_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ.real (Ici x) = 1 - Function.leftLim (cdf μ) x := by
  have h := (cdf μ).measure_Ici (tendsto_cdf_atTop μ) x
  rw [measure_cdf μ] at h
  have hle : Function.leftLim (cdf μ) x ≤ 1 :=
    ((cdf μ).mono.leftLim_le le_rfl).trans (cdf_le_one μ x)
  rw [measureReal_def, h, ENNReal.toReal_ofReal (sub_nonneg.mpr hle)]

theorem survival_mem_iff_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (x p : ℝ) :
    p ∈ survival μ x ↔ 1 - p ∈ completedStieltjes (cdf μ) x := by
  change (μ.real (Ioi x) ≤ p ∧ p ≤ μ.real (Ici x)) ↔
    (Function.leftLim (cdf μ) x ≤ 1 - p ∧ 1 - p ≤ cdf μ x)
  rw [survival_lower_cdf μ x, survival_upper_cdf μ x]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem survival_maximal (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MaximalDecreasing (survival μ) := by
  change MaximalIncreasing (negOut (survival μ))
  have heq : negOut (survival μ) =
      fun x => {u | u + 1 ∈ completedStieltjes (cdf μ) x} := by
    funext x
    ext u
    change -u ∈ survival μ x ↔ u + 1 ∈ completedStieltjes (cdf μ) x
    rw [survival_mem_iff_cdf μ x (-u)]
    simp [add_comm]
  rw [heq]
  exact output_translation_maximal (completedStieltjes_maximal (cdf μ)) 1

theorem tailQuantile_maximal (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MaximalDecreasing (tailQuantile μ) :=
  inverse_maximal_decreasing (survival_maximal μ)

theorem tailQuantile_fiber_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) :
    tailQuantile μ p = inverse (completedStieltjes (cdf μ)) (1 - p) := by
  ext x
  exact survival_mem_iff_cdf μ x p

theorem tailQuantile_fiber_closed (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) :
    IsClosed (tailQuantile μ p) := by
  rw [tailQuantile_fiber_eq μ p]
  exact maximal_fiber_closed (inverse_maximal (completedStieltjes_maximal (cdf μ))) (1 - p)

theorem tailQuantile_fiber_ordConnected (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) :
    (tailQuantile μ p).OrdConnected := by
  rw [tailQuantile_fiber_eq μ p]
  exact maximal_fiber_ordConnected (inverse_maximal (completedStieltjes_maximal (cdf μ))) (1 - p)

private theorem cdf_brackets_tail_level (μ : Measure ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a b, cdf μ a < 1 - p ∧ 1 - p < cdf μ b := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const
    (show 0 < 1 - p by linarith [hp.2])).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt
    (show 1 - p < 1 by linarith [hp.1])).exists
  exact ⟨a, b, ha, hb⟩

theorem tailQuantile_fiber_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p ∈ Ioo 0 1) : (tailQuantile μ p).Nonempty := by
  obtain ⟨a, b, ha, hb⟩ := cdf_brackets_tail_level μ hp
  have hlevel : 1 - p ∈ ran (completedStieltjes (cdf μ)) :=
    (ran_ordConnected (completedStieltjes_maximal (cdf μ))).out
      ⟨a, completedStieltjes_top_mem (cdf μ) a⟩
      ⟨b, completedStieltjes_top_mem (cdf μ) b⟩ ⟨ha.le, hb.le⟩
  obtain ⟨x, hx⟩ := hlevel
  exact ⟨x, (survival_mem_iff_cdf μ x p).mpr hx⟩

theorem tailQuantile_fiber_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p ∈ Ioo 0 1) : ∃ a b, tailQuantile μ p ⊆ Icc a b := by
  obtain ⟨a, b, ha, hb⟩ := cdf_brackets_tail_level μ hp
  refine ⟨a, b, ?_⟩
  intro x hx
  have hx' : 1 - p ∈ completedStieltjes (cdf μ) x :=
    (survival_mem_iff_cdf μ x p).mp hx
  constructor
  · by_contra h
    have hxa : x < a := lt_of_not_ge h
    have hle := (completedStieltjes_maximal (cdf μ)).1.le_of_lt hx'
      (completedStieltjes_top_mem (cdf μ) a) hxa
    linarith
  · by_contra h
    have hbx : b < x := lt_of_not_ge h
    have hle := (completedStieltjes_maximal (cdf μ)).1.le_of_lt
      (completedStieltjes_top_mem (cdf μ) b) hx' hbx
    linarith

theorem tailQuantile_fiber_compact (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p ∈ Ioo 0 1) : IsCompact (tailQuantile μ p) := by
  obtain ⟨a, b, hab⟩ := tailQuantile_fiber_bounded μ hp
  exact isCompact_Icc.of_isClosed_subset (tailQuantile_fiber_closed μ p) hab

/-- At probability zero the tail quantile is empty or a closed upper ray. -/
theorem tailQuantile_zero_empty_or_ray (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    tailQuantile μ 0 = ∅ ∨ ∃ a : ℝ, tailQuantile μ 0 = Ici a := by
  rcases (tailQuantile μ 0).eq_empty_or_nonempty with h | hne
  · exact Or.inl h
  · right
    obtain ⟨c, hc⟩ := tailQuantile_fiber_nonempty μ (p := 1 / 2) (by norm_num)
    have hB : BddBelow (tailQuantile μ 0) := by
      refine ⟨c, ?_⟩
      intro x hx
      have h := negOut_increasing_iff.mp (tailQuantile_maximal μ).1 hx hc
      norm_num at h
      linarith
    have hleast := (tailQuantile_fiber_closed μ 0).isLeast_csInf hne hB
    refine ⟨sInf (tailQuantile μ 0), ?_⟩
    ext x
    constructor
    · exact fun hx => hleast.2 hx
    · intro hx
      have ha : μ.real (Ioi (sInf (tailQuantile μ 0))) ≤ 0 ∧
          0 ≤ μ.real (Ici (sInf (tailQuantile μ 0))) := hleast.1
      change μ.real (Ioi x) ≤ 0 ∧ 0 ≤ μ.real (Ici x)
      refine ⟨?_, measureReal_nonneg⟩
      have hsub : Ioi x ⊆ Ioi (sInf (tailQuantile μ 0)) := by
        intro y hy
        change sInf (tailQuantile μ 0) < y
        exact lt_of_le_of_lt hx hy
      exact (measureReal_mono (μ := μ) hsub).trans ha.1

/-- At probability one the tail quantile is empty or a closed lower ray. -/
theorem tailQuantile_one_empty_or_ray (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    tailQuantile μ 1 = ∅ ∨ ∃ a : ℝ, tailQuantile μ 1 = Iic a := by
  rcases (tailQuantile μ 1).eq_empty_or_nonempty with h | hne
  · exact Or.inl h
  · right
    obtain ⟨c, hc⟩ := tailQuantile_fiber_nonempty μ (p := 1 / 2) (by norm_num)
    have hB : BddAbove (tailQuantile μ 1) := by
      refine ⟨c, ?_⟩
      intro x hx
      have h := negOut_increasing_iff.mp (tailQuantile_maximal μ).1 hc hx
      norm_num at h
      linarith
    have hgreatest := (tailQuantile_fiber_closed μ 1).isGreatest_csSup hne hB
    refine ⟨sSup (tailQuantile μ 1), ?_⟩
    ext x
    constructor
    · exact fun hx => hgreatest.2 hx
    · intro hx
      have ha : μ.real (Ioi (sSup (tailQuantile μ 1))) ≤ 1 ∧
          1 ≤ μ.real (Ici (sSup (tailQuantile μ 1))) := hgreatest.1
      change μ.real (Ioi x) ≤ 1 ∧ 1 ≤ μ.real (Ici x)
      refine ⟨measureReal_le_one, ?_⟩
      have hsub : Ici (sSup (tailQuantile μ 1)) ⊆ Ici x := by
        intro y hy
        change x ≤ y
        exact le_trans hx hy
      exact ha.2.trans (measureReal_mono (μ := μ) hsub)

/-- The equally weighted Bernoulli law on `{0,1}`. -/
def symmetricBernoulli : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 1

instance symmetricBernoulli_probability : IsProbabilityMeasure symmetricBernoulli where
  measure_univ := by
    norm_num [symmetricBernoulli, Measure.add_apply, Measure.smul_apply,
      ENNReal.inv_two_add_inv_two]

/-- A quantile fiber can be a genuine interval, even for a two-atom law. -/
theorem tailQuantile_symmetricBernoulli_half :
    tailQuantile symmetricBernoulli (1 / 2) = Icc 0 1 := by
  ext x
  change (symmetricBernoulli.real (Ioi x) ≤ 1 / 2 ∧
    1 / 2 ≤ symmetricBernoulli.real (Ici x)) ↔ 0 ≤ x ∧ x ≤ 1
  by_cases h0 : x < 0 <;> by_cases h1 : x < 1 <;>
    by_cases h2 : x ≤ 0 <;> by_cases h3 : x ≤ 1
  all_goals try { exfalso; linarith }
  all_goals norm_num [symmetricBernoulli, measureReal_def, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator,
    h0, h1, h2, h3, ENNReal.inv_two_add_inv_two]
  all_goals linarith

/-- Lebesgue measure restricted to the open unit interval has total mass one. -/
def unitUniform : Measure ℝ := volume.restrict (Ioo 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform where
  measure_univ := by simp [unitUniform, Real.volume_Ioo]

/-- The level set of any quantile selection has exactly the prescribed upper-tail mass.
Measurability is needed only in the subsequent pushforward statement. -/
theorem tailQuantile_selection_tail_volume (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ → ℝ} (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p) (t : ℝ) :
    volume ((q ⁻¹' Ioi t) ∩ Ioo 0 1) = μ (Ioi t) := by
  let a : ℝ := μ.real (Ioi t)
  have ha1 : a ≤ 1 := measureReal_le_one
  have hlower : Ioo 0 a ⊆ (q ⁻¹' Ioi t) ∩ Ioo 0 1 := by
    intro p hp
    have hp01 : p ∈ Ioo 0 1 := ⟨hp.1, hp.2.trans_le ha1⟩
    have hq : μ.real (Ioi (q p)) ≤ p ∧ p ≤ μ.real (Ici (q p)) := hsel p hp01
    refine ⟨?_, hp01⟩
    change t < q p
    by_contra h
    have hqt : q p ≤ t := le_of_not_gt h
    have hs : Ioi t ⊆ Ioi (q p) := fun x hx => hqt.trans_lt hx
    have hmass := measureReal_mono (μ := μ) hs
    have : a ≤ p := hmass.trans hq.1
    linarith [hp.2]
  have hupper : (q ⁻¹' Ioi t) ∩ Ioo 0 1 ⊆ Ioc 0 a := by
    intro p hp
    have hq : μ.real (Ioi (q p)) ≤ p ∧ p ≤ μ.real (Ici (q p)) := hsel p hp.2
    have htq : t < q p := hp.1
    have hs : Ici (q p) ⊆ Ioi t := fun x hx => htq.trans_le hx
    exact ⟨hp.2.1, hq.2.trans (measureReal_mono (μ := μ) hs)⟩
  have hlo := measure_mono (μ := volume) hlower
  have hup := measure_mono (μ := volume) hupper
  rw [Real.volume_Ioo, sub_zero] at hlo
  rw [Real.volume_Ioc, sub_zero] at hup
  have hvol : volume ((q ⁻¹' Ioi t) ∩ Ioo 0 1) = ENNReal.ofReal a :=
    le_antisymm hup hlo
  rw [hvol]
  exact ofReal_measureReal

/-- Every measurable selection of the completed tail quantile sends a uniform input
to the original law, including laws with atoms. -/
theorem tailQuantile_selection_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ → ℝ} (hq : Measurable q)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p) :
    Measure.map q unitUniform = μ := by
  letI : IsProbabilityMeasure (Measure.map q unitUniform) :=
    isProbabilityMeasure_map hq.aemeasurable
  have htail : ∀ t : ℝ, Measure.map q unitUniform (Ioi t) = μ (Ioi t) := by
    intro t
    rw [Measure.map_apply hq measurableSet_Ioi, unitUniform,
      Measure.restrict_apply (measurableSet_Ioi.preimage hq)]
    exact tailQuantile_selection_tail_volume μ hsel t
  apply Measure.ext_of_Iic
  intro t
  calc
    Measure.map q unitUniform (Iic t) = 1 - Measure.map q unitUniform (Ioi t) := by
      simpa only [compl_Ioi, measure_univ] using
        (measure_compl (μ := Measure.map q unitUniform) measurableSet_Ioi (measure_ne_top _ _))
    _ = 1 - μ (Ioi t) := by rw [htail t]
    _ = μ (Iic t) := by
      symm
      simpa only [compl_Ioi, measure_univ] using
        (measure_compl (μ := μ) measurableSet_Ioi (measure_ne_top _ _))

theorem tailQuantile_selection_uniform_argument
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {U : Ω → ℝ} {q : ℝ → ℝ}
    (hU : Measurable U) (hq : Measurable q)
    (hUlaw : Measure.map U ν = unitUniform)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p) :
    Measure.map (q ∘ U) ν = μ := by
  rw [← Measure.map_map hq hU, hUlaw]
  exact tailQuantile_selection_law μ hq hsel

end ScalarMonotone
