import MonotoneOperators.Cubic
import MonotoneOperators.Examples

/-!
# The nested cubic parallel expression

The constant profile is the survival graph of a positive constant, restricted
to nonnegative inputs and maximally completed at zero.  Its exceptional inverse
fibers at levels zero and one are retained throughout the calculation.
-/

namespace ScalarMonotone

open Set MeasureTheory

noncomputable section

theorem survival_dirac_left {σ t : ℝ} (ht : t < σ) :
    survival (Measure.dirac σ) t = {1} := by
  ext u
  simp [survival, measureReal_def, Measure.dirac_apply, Set.indicator, ht, ht.le]

theorem survival_dirac_at (σ : ℝ) : survival (Measure.dirac σ) σ = Icc (0 : ℝ) 1 := by
  ext u
  simp [survival, measureReal_def, Measure.dirac_apply, Set.indicator]

theorem survival_dirac_right {σ t : ℝ} (ht : σ < t) :
    survival (Measure.dirac σ) t = {0} := by
  ext u
  simp [survival, measureReal_def, Measure.dirac_apply, Set.indicator,
    not_lt.mpr ht.le, not_le.mpr ht]

/-- The positively completed survival operator of the constant `σ`. -/
def positiveConstantProfile (σ : ℝ) : Operator :=
  add (survival (Measure.dirac σ)) (negOut normalHalfline)

theorem positiveConstantProfile_maximal {σ : ℝ} (hσ : 0 < σ) :
    MaximalDecreasing (positiveConstantProfile σ) := by
  apply add_maximal_decreasing (survival_maximal (Measure.dirac σ))
    (show MaximalDecreasing (negOut normalHalfline) by
      simpa only [MaximalDecreasing, negOut_negOut] using normalHalfline_maximal)
  refine ⟨0, ⟨1, ?_⟩, ⟨0, ?_⟩⟩
  · rw [survival_dirac_left hσ]
    rfl
  · simp [negOut, normalHalfline]

theorem positiveConstantProfile_negative {σ t : ℝ} (ht : t < 0) :
    positiveConstantProfile σ t = ∅ := by
  ext u
  simp [positiveConstantProfile, add, negOut, normalHalfline, not_le.mpr ht]

theorem positiveConstantProfile_zero {σ : ℝ} (hσ : 0 < σ) :
    positiveConstantProfile σ 0 = Ici 1 := by
  ext u
  unfold positiveConstantProfile add
  rw [survival_dirac_left hσ]
  simp only [mem_setOf_eq, mem_singleton_iff, exists_eq_left, negOut, normalHalfline,
    neg_nonpos, zero_mul, le_refl, and_true, true_and, mem_Ici]
  constructor
  · rintro ⟨b, hb, rfl⟩
    linarith
  · intro hu
    exact ⟨u - 1, by linarith, by ring⟩

theorem positiveConstantProfile_positive {σ t : ℝ} (ht : 0 < t) :
    positiveConstantProfile σ t = survival (Measure.dirac σ) t := by
  ext u
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have htb : t * (-b) = 0 := hb.2.2
    have hb0 : b = 0 := by
      have hh := (mul_eq_zero.mp htb).resolve_left (ne_of_gt ht)
      linarith
    simpa only [hb0, add_zero] using ha
  · intro hu
    exact ⟨u, hu, 0, by simp [negOut, normalHalfline, ht.le], by ring⟩

theorem positiveConstantProfile_mem_iff {σ t u : ℝ} (hσ : 0 < σ) :
    u ∈ positiveConstantProfile σ t ↔
      (t = 0 ∧ 1 ≤ u) ∨ (0 < t ∧ t < σ ∧ u = 1) ∨
      (t = σ ∧ 0 ≤ u ∧ u ≤ 1) ∨ (σ < t ∧ u = 0) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [positiveConstantProfile_negative ht]
    simp only [mem_empty_iff_false, false_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> linarith
  · rw [positiveConstantProfile_zero hσ]
    simp [hσ.ne, hσ.ne', not_lt.mpr hσ.le]
  · rw [positiveConstantProfile_positive ht]
    rcases lt_trichotomy t σ with hts | rfl | hst
    · rw [survival_dirac_left hts]
      simp [ht.ne', ht, hts, hts.ne, not_lt.mpr hts.le]
    · rw [survival_dirac_at]
      simp [ht.ne', hσ]
    · rw [survival_dirac_right hst]
      simp [ht.ne', ht, hst, hst.ne', not_lt.mpr hst.le]

theorem inverse_positiveConstantProfile_negative {σ u : ℝ} (hσ : 0 < σ) (hu : u < 0) :
    inverse (positiveConstantProfile σ) u = ∅ := by
  ext t
  change u ∈ positiveConstantProfile σ t ↔ False
  rw [positiveConstantProfile_mem_iff hσ]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h, _⟩ | ⟨_, h⟩) <;> linarith
  · exact False.elim

theorem inverse_positiveConstantProfile_zero {σ : ℝ} (hσ : 0 < σ) :
    inverse (positiveConstantProfile σ) 0 = Ici σ := by
  ext t
  change 0 ∈ positiveConstantProfile σ t ↔ σ ≤ t
  rw [positiveConstantProfile_mem_iff hσ]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨h, _⟩) <;> linarith
  · intro ht
    rcases ht.eq_or_lt with rfl | ht
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, by norm_num⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ht, rfl⟩))

theorem inverse_positiveConstantProfile_interior {σ u : ℝ}
    (hσ : 0 < σ) (hu : 0 < u) (hu1 : u < 1) :
    inverse (positiveConstantProfile σ) u = {σ} := by
  ext t
  change u ∈ positiveConstantProfile σ t ↔ t = σ
  rw [positiveConstantProfile_mem_iff hσ]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨_, h⟩) <;> linarith
  · rintro rfl
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hu.le, hu1.le⟩))

theorem inverse_positiveConstantProfile_one {σ : ℝ} (hσ : 0 < σ) :
    inverse (positiveConstantProfile σ) 1 = Icc 0 σ := by
  ext t
  change 1 ∈ positiveConstantProfile σ t ↔ 0 ≤ t ∧ t ≤ σ
  rw [positiveConstantProfile_mem_iff hσ]
  constructor
  · rintro (⟨h, _⟩ | ⟨ht, hts, _⟩ | ⟨h, _, _⟩ | ⟨_, h⟩)
    · subst t
      exact ⟨le_rfl, hσ.le⟩
    · exact ⟨ht.le, hts.le⟩
    · subst t
      exact ⟨hσ.le, le_rfl⟩
    · norm_num at h
  · rintro ⟨ht, hts⟩
    rcases ht.eq_or_lt with rfl | ht
    · exact Or.inl ⟨rfl, le_rfl⟩
    · rcases hts.eq_or_lt with rfl | hts
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, by norm_num, le_rfl⟩))
      · exact Or.inr (Or.inl ⟨ht, hts, rfl⟩)

theorem inverse_positiveConstantProfile_above_one {σ u : ℝ}
    (hσ : 0 < σ) (hu : 1 < u) : inverse (positiveConstantProfile σ) u = {0} := by
  ext t
  change u ∈ positiveConstantProfile σ t ↔ t = 0
  rw [positiveConstantProfile_mem_iff hσ]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩) <;> linarith
  · rintro rfl
    exact Or.inl ⟨rfl, hu.le⟩

theorem positiveProfile_nonnegative {α : Operator} (hα : MaximalDecreasing α)
    (hdom : dom α = Ici 0) (hbound : ∀ t > 0, α t ⊆ Icc 0 1) : Nonnegative α := by
  intro x u hu
  have hx : 0 ≤ x := by
    have hh : x ∈ dom α := ⟨u, hu⟩
    simpa only [hdom, mem_Ici] using hh
  have hxp : 0 < x + 1 := by linarith
  obtain ⟨v, hv⟩ : (α (x + 1)).Nonempty := by
    change x + 1 ∈ dom α
    rw [hdom]
    exact hxp.le
  exact ((hbound (x + 1) hxp) hv).1.trans
    (Decreasing.le_of_lt hα.1 hu hv (by linarith))

theorem positiveProfile_one_mem_zero {α : Operator} (hα : MaximalDecreasing α)
    (hdom : dom α = Ici 0) (hbound : ∀ t > 0, α t ⊆ Icc 0 1) : 1 ∈ α 0 := by
  have hh : (-1 : ℝ) ∈ negOut α 0 := by
    apply hα.2
    intro y v hv
    have hy : 0 ≤ y := by
      have hm : y ∈ dom α := ⟨-v, hv⟩
      simpa only [hdom, mem_Ici] using hm
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have hv1 := ((hbound y hyp) hv).2
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  simpa only [negOut, neg_neg, mem_setOf_eq] using hh

theorem positiveProfile_zero_mem_of_le {α : Operator} (hα : MaximalDecreasing α)
    (hdom : dom α = Ici 0) (hbound : ∀ t > 0, α t ⊆ Icc 0 1)
    {a b : ℝ} (ha : 0 ∈ α a) (hab : a ≤ b) : 0 ∈ α b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact ha
  have ha0 : 0 ≤ a := by
    have hh : a ∈ dom α := ⟨0, ha⟩
    simpa only [hdom, mem_Ici] using hh
  have hb0 : 0 < b := ha0.trans_lt hab
  obtain ⟨v, hv⟩ : (α b).Nonempty := by
    change b ∈ dom α
    rw [hdom]
    exact hb0.le
  have hlow := ((hbound b hb0) hv).1
  have hupp := Decreasing.le_of_lt hα.1 ha hv hab
  have hv0 : v = 0 := le_antisymm hupp hlow
  simpa only [hv0] using hv

theorem positiveProfile_input_zero_of_above_one {α : Operator}
    (hdom : dom α = Ici 0) (hbound : ∀ t > 0, α t ⊆ Icc 0 1)
    {x u : ℝ} (hu : u ∈ α x) (hu1 : 1 < u) : x = 0 := by
  have hx : 0 ≤ x := by
    have hh : x ∈ dom α := ⟨u, hu⟩
    simpa only [hdom, mem_Ici] using hh
  by_contra h
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
  exact (not_le_of_gt hu1) (((hbound x hxp) hu).2)

def nestedCubicProfile (α : Operator) (σ₀ σ₁ σ₂ : ℝ) : Operator :=
  parallelMul α (parallelAdd (positiveConstantProfile σ₀)
    (parallelMul α (parallelAdd (positiveConstantProfile σ₁) (inputDivide σ₂ α))))

theorem nestedCubicProfile_mem_iff {α : Operator} {σ₀ σ₁ σ₂ t u : ℝ} (h₂ : σ₂ ≠ 0) :
    u ∈ nestedCubicProfile α σ₀ σ₁ σ₂ t ↔
      ∃ a, u ∈ α a ∧ ∃ b₀, u ∈ positiveConstantProfile σ₀ b₀ ∧
      ∃ b, u ∈ α b ∧ ∃ b₁, u ∈ positiveConstantProfile σ₁ b₁ ∧
      ∃ c, u ∈ α c ∧ t = a * (b₀ + b * (b₁ + σ₂ * c)) := by
  constructor
  · rintro ⟨a, ha, _, ⟨b₀, hb₀, _, ⟨b, hb, _, ⟨b₁, hb₁, z, hz, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, b₀, hb₀, b, hb, b₁, hb₁, z / σ₂, hz, ?_⟩
    have hs : σ₂ * (z / σ₂) = z := by field_simp
    rw [hs]
  · rintro ⟨a, ha, b₀, hb₀, b, hb, b₁, hb₁, c, hc, rfl⟩
    refine ⟨a, ha, b₀ + b * (b₁ + σ₂ * c),
      ⟨b₀, hb₀, b * (b₁ + σ₂ * c),
        ⟨b, hb, b₁ + σ₂ * c, ⟨b₁, hb₁, σ₂ * c, ?_, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    change u ∈ α ((σ₂ * c) / σ₂)
    have hs : (σ₂ * c) / σ₂ = c := by field_simp
    simpa only [hs] using hc

private theorem nested_min_mem {A : Set ℝ} {a b c : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) : min a (min b c) ∈ A := by
  rcases le_total a (min b c) with h | h
  · simpa only [min_eq_left h] using ha
  · rw [min_eq_right h]
    rcases le_total b c with hbc | hbc
    · simpa only [min_eq_left hbc] using hb
    · simpa only [min_eq_right hbc] using hc

private theorem nested_max_mem {A : Set ℝ} {a b c : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) : max a (max b c) ∈ A := by
  rcases le_total a (max b c) with h | h
  · rw [max_eq_right h]
    rcases le_total b c with hbc | hbc
    · simpa only [max_eq_right hbc] using hc
    · simpa only [max_eq_left hbc] using hb
  · simpa only [max_eq_left h] using ha

theorem cubic_interval_nested_diagonal {A : Set ℝ} (hA : A.OrdConnected)
    (hA₀ : A ⊆ Ici 0) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂)
    {a b c : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    ∃ r ∈ A, cubicPolynomial σ₀ σ₁ σ₂ r = a * (σ₀ + b * (σ₁ + σ₂ * c)) := by
  let l := min a (min b c)
  let h := max a (max b c)
  have hlA : l ∈ A := nested_min_mem ha hb hc
  have hhA : h ∈ A := nested_max_mem ha hb hc
  have hl0 : 0 ≤ l := hA₀ hlA
  have hh0 : 0 ≤ h := hA₀ hhA
  have ha0 : 0 ≤ a := hA₀ ha
  have hb0 : 0 ≤ b := hA₀ hb
  have hc0 : 0 ≤ c := hA₀ hc
  have hla : l ≤ a := min_le_left _ _
  have hlb : l ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hlc : l ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have hah : a ≤ h := le_max_left _ _
  have hbh : b ≤ h := (le_max_left _ _).trans (le_max_right _ _)
  have hch : c ≤ h := (le_max_right _ _).trans (le_max_right _ _)
  have hlow : cubicPolynomial σ₀ σ₁ σ₂ l ≤ a * (σ₀ + b * (σ₁ + σ₂ * c)) := by
    rw [cubicPolynomial_nested]
    gcongr
  have hupp : a * (σ₀ + b * (σ₁ + σ₂ * c)) ≤ cubicPolynomial σ₀ σ₁ σ₂ h := by
    rw [cubicPolynomial_nested]
    gcongr
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc (hla.trans hah)
    (cubicPolynomial_continuous σ₀ σ₁ σ₂).continuousOn ⟨hlow, hupp⟩
  exact ⟨r, hA.out hlA hhA hr, heq⟩

/-- Exact identity of the nested parallel expression with the cubic input
change, including the exceptional inverse levels `0` and `1`. -/
theorem nestedCubicProfile_eq_cubicProfile {α : Operator}
    (hα : MaximalDecreasing α) (hdom : dom α = Ici 0)
    (hbound : ∀ t > 0, α t ⊆ Icc 0 1) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    nestedCubicProfile α σ₀ σ₁ σ₂ = cubicProfile α σ₀ σ₁ σ₂ := by
  have hα₀ : dom α ⊆ Ici 0 := by rw [hdom]
  have hnonneg := positiveProfile_nonnegative hα hdom hbound
  ext t u
  constructor
  · rw [nestedCubicProfile_mem_iff h₂.ne']
    rintro ⟨a, ha, b₀, hb₀, b, hb, b₁, hb₁, c, hc, ht⟩
    have hu0 : 0 ≤ u := hnonneg ha
    have ha0 : 0 ≤ a := hα₀ ⟨u, ha⟩
    have hb0 : 0 ≤ b := hα₀ ⟨u, hb⟩
    have hc0 : 0 ≤ c := hα₀ ⟨u, hc⟩
    have hA : (inverse α u).OrdConnected :=
      decreasing_fiber_ordConnected (inverse_maximal_decreasing hα) u
    have hA0 : inverse α u ⊆ Ici 0 := fun x hx => hα₀ ⟨u, hx⟩
    rcases hu0.eq_or_lt with rfl | hu0
    · have hb₀' : σ₀ ≤ b₀ := by
        simpa only [inverse_positiveConstantProfile_zero h₀, mem_Ici] using
          (show b₀ ∈ inverse (positiveConstantProfile σ₀) 0 from hb₀)
      have hb₁' : σ₁ ≤ b₁ := by
        simpa only [inverse_positiveConstantProfile_zero h₁, mem_Ici] using
          (show b₁ ∈ inverse (positiveConstantProfile σ₁) 0 from hb₁)
      have hb₀0 : 0 ≤ b₀ := h₀.le.trans hb₀'
      have hb₁0 : 0 ≤ b₁ := h₁.le.trans hb₁'
      let l := min a (min b c)
      have hlA : l ∈ inverse α 0 := nested_min_mem ha hb hc
      have hl0 : 0 ≤ l := hA0 hlA
      have hla : l ≤ a := min_le_left _ _
      have hlb : l ≤ b := (min_le_right _ _).trans (min_le_left _ _)
      have hlc : l ≤ c := (min_le_right _ _).trans (min_le_right _ _)
      have hlow : cubicPolynomial σ₀ σ₁ σ₂ l ≤ t := by
        rw [ht, cubicPolynomial_nested]
        gcongr
      obtain ⟨r, hr⟩ := cubicExtension_surjective h₀ h₁.le h₂.le t
      have hlr : l ≤ r := by
        by_contra hn
        have hlt := cubicExtension_strictMono h₀ h₁.le h₂.le (lt_of_not_ge hn)
        rw [hr, cubicExtension_eq hl0] at hlt
        exact (not_lt_of_ge hlow) hlt
      have hr0 : 0 ≤ r := hl0.trans hlr
      rw [cubicExtension_eq hr0] at hr
      exact ⟨r, positiveProfile_zero_mem_of_le hα hdom hbound hlA hlr, hr.symm⟩
    · rcases lt_trichotomy u 1 with hu1 | rfl | hu1
      · have hb₀' : b₀ = σ₀ := by
          simpa only [inverse_positiveConstantProfile_interior h₀ hu0 hu1,
            mem_singleton_iff] using
            (show b₀ ∈ inverse (positiveConstantProfile σ₀) u from hb₀)
        have hb₁' : b₁ = σ₁ := by
          simpa only [inverse_positiveConstantProfile_interior h₁ hu0 hu1,
            mem_singleton_iff] using
            (show b₁ ∈ inverse (positiveConstantProfile σ₁) u from hb₁)
        obtain ⟨r, hr, heq⟩ := cubic_interval_nested_diagonal hA hA0 h₀.le h₁.le h₂.le ha hb hc
        have ht' : t = a * (σ₀ + b * (σ₁ + σ₂ * c)) := by
          simpa only [hb₀', hb₁'] using ht
        exact ⟨r, hr, ht'.trans heq.symm⟩
      · have hb₀' : 0 ≤ b₀ ∧ b₀ ≤ σ₀ := by
          simpa only [inverse_positiveConstantProfile_one h₀, mem_Icc] using
            (show b₀ ∈ inverse (positiveConstantProfile σ₀) 1 from hb₀)
        have hb₁' : 0 ≤ b₁ ∧ b₁ ≤ σ₁ := by
          simpa only [inverse_positiveConstantProfile_one h₁, mem_Icc] using
            (show b₁ ∈ inverse (positiveConstantProfile σ₁) 1 from hb₁)
        have hb₀0 := hb₀'.1
        have hb₀σ := hb₀'.2
        have hb₁0 := hb₁'.1
        have hb₁σ := hb₁'.2
        let h := max a (max b c)
        have hhA : h ∈ inverse α 1 := nested_max_mem ha hb hc
        have hh0 : 0 ≤ h := hA0 hhA
        have hah : a ≤ h := le_max_left _ _
        have hbh : b ≤ h := (le_max_left _ _).trans (le_max_right _ _)
        have hch : c ≤ h := (le_max_right _ _).trans (le_max_right _ _)
        have hlow : cubicPolynomial σ₀ σ₁ σ₂ 0 ≤ t := by
          rw [ht]
          simp only [cubicPolynomial, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
            zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero, add_zero]
          exact mul_nonneg ha0 (add_nonneg hb₀'.1
            (mul_nonneg hb0 (add_nonneg hb₁'.1 (mul_nonneg h₂.le hc0))))
        have hupp : t ≤ cubicPolynomial σ₀ σ₁ σ₂ h := by
          rw [ht, cubicPolynomial_nested]
          gcongr
        obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hh0
          (cubicPolynomial_continuous σ₀ σ₁ σ₂).continuousOn ⟨hlow, hupp⟩
        exact ⟨r, hA.out (positiveProfile_one_mem_zero hα hdom hbound) hhA hr, heq.symm⟩
      · have haeq := positiveProfile_input_zero_of_above_one hdom hbound ha hu1
        refine ⟨a, ha, ?_⟩
        simpa [haeq, cubicPolynomial] using ht
  · rintro ⟨r, hr, ht⟩
    rw [nestedCubicProfile_mem_iff h₂.ne']
    have hu0 : 0 ≤ u := hnonneg hr
    by_cases hu1 : u ≤ 1
    · have hβ₀ : u ∈ positiveConstantProfile σ₀ σ₀ := by
        rw [positiveConstantProfile_positive h₀, survival_dirac_at]
        exact ⟨hu0, hu1⟩
      have hβ₁ : u ∈ positiveConstantProfile σ₁ σ₁ := by
        rw [positiveConstantProfile_positive h₁, survival_dirac_at]
        exact ⟨hu0, hu1⟩
      exact ⟨r, hr, σ₀, hβ₀, r, hr, σ₁, hβ₁, r, hr,
        ht.trans (cubicPolynomial_nested σ₀ σ₁ σ₂ r)⟩
    · have hr0 := positiveProfile_input_zero_of_above_one hdom hbound hr (lt_of_not_ge hu1)
      have hβ₀ : u ∈ positiveConstantProfile σ₀ 0 := by
        rw [positiveConstantProfile_zero h₀]
        exact (lt_of_not_ge hu1).le
      have hβ₁ : u ∈ positiveConstantProfile σ₁ 0 := by
        rw [positiveConstantProfile_zero h₁]
        exact (lt_of_not_ge hu1).le
      refine ⟨r, hr, 0, hβ₀, r, hr, 0, hβ₁, r, hr, ?_⟩
      simpa [hr0, cubicPolynomial] using ht

theorem nestedCubicProfile_maximal {α : Operator}
    (hα : MaximalDecreasing α) (hdom : dom α = Ici 0)
    (hbound : ∀ t > 0, α t ⊆ Icc 0 1) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    MaximalDecreasing (nestedCubicProfile α σ₀ σ₁ σ₂) := by
  rw [nestedCubicProfile_eq_cubicProfile hα hdom hbound h₀ h₁ h₂]
  exact cubicProfile_maximal hα (by rw [hdom]) h₀ h₁.le h₂.le

theorem nestedCubicProfile_eq_parallel_monomials {α : Operator}
    (hα : MaximalDecreasing α) (hdom : dom α = Ici 0)
    (hbound : ∀ t > 0, α t ⊆ Icc 0 1) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    nestedCubicProfile α σ₀ σ₁ σ₂ =
      parallelAdd (parallelAdd (monomialProfile α σ₀ 1) (monomialProfile α σ₁ 2))
        (monomialProfile α σ₂ 3) := by
  rw [nestedCubicProfile_eq_cubicProfile hα hdom hbound h₀ h₁ h₂]
  exact cubicProfile_eq_parallel_monomials hα (by rw [hdom]) h₀.le h₁.le h₂.le

theorem survival_nested_cubic_comparison {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hmX : Measurable X)
    {α : Operator} (hα : MaximalDecreasing α) (hdom : dom α = Ici 0)
    (hbound : ∀ t > 0, α t ⊆ Icc 0 1)
    (hX : DecLE (survival (Measure.map X ν)) α)
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    DecLE (survival (Measure.map (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω)) ν))
      (nestedCubicProfile α σ₀ σ₁ σ₂) := by
  rw [nestedCubicProfile_eq_cubicProfile hα hdom hbound h₀ h₁ h₂]
  exact survival_cubic_comparison ν hmX hX hX₀ (by rw [hdom]) h₀.le h₁.le h₂.le

end

end ScalarMonotone
