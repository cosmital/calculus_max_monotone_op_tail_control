import MonotoneOperators.ProbabilityBounds

/-!
# A cubic transformation and its three concentration scales

The probability estimate is a deterministic monotone transformation of the
same random variable. Consequently it has no union-bound coefficient.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

namespace ScalarMonotone

def cubicPolynomial (σ₀ σ₁ σ₂ x : ℝ) : ℝ := σ₀ * x + σ₁ * x ^ 2 + σ₂ * x ^ 3

theorem cubicPolynomial_nested (σ₀ σ₁ σ₂ x : ℝ) :
    cubicPolynomial σ₀ σ₁ σ₂ x = x * (σ₀ + x * (σ₁ + σ₂ * x)) := by
  unfold cubicPolynomial
  ring

theorem cubicPolynomial_continuous (σ₀ σ₁ σ₂ : ℝ) :
    Continuous (cubicPolynomial σ₀ σ₁ σ₂) := by
  unfold cubicPolynomial
  fun_prop

theorem cubicPolynomial_monotoneOn {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    MonotoneOn (cubicPolynomial σ₀ σ₁ σ₂) (Ici 0) := by
  intro x hx y hy hxy
  unfold cubicPolynomial
  gcongr <;> exact hx

theorem cubicPolynomial_strictMonoOn {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    StrictMonoOn (cubicPolynomial σ₀ σ₁ σ₂) (Ici 0) := by
  intro x hx y hy hxy
  have hlin := mul_lt_mul_of_pos_left hxy h₀
  have hsquare := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy.le 2) h₁
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy.le 3) h₂
  unfold cubicPolynomial
  linarith

/-- Applying the polynomial to every point of an inverse fiber. -/
def cubicProfile (α : Operator) (σ₀ σ₁ σ₂ : ℝ) : Operator :=
  fun t => {u | ∃ r, u ∈ α r ∧ t = cubicPolynomial σ₀ σ₁ σ₂ r}

theorem inverse_cubicProfile (α : Operator) (σ₀ σ₁ σ₂ : ℝ) (u : ℝ) :
    inverse (cubicProfile α σ₀ σ₁ σ₂) u =
      cubicPolynomial σ₀ σ₁ σ₂ '' inverse α u := by
  ext t
  constructor
  · rintro ⟨r, hr, ht⟩
    exact ⟨r, hr, ht.symm⟩
  · rintro ⟨r, hr, ht⟩
    exact ⟨r, hr, ht.symm⟩

/-- Reparametrization of the input coordinate by a strictly increasing bijection. -/
def inputChange (e : ℝ → ℝ) (f : Operator) : Operator :=
  fun t => {u | ∃ x, u ∈ f x ∧ t = e x}

theorem inputChange_increasing {e : ℝ → ℝ} {f : Operator}
    (he : StrictMono e) (hf : Increasing f) : Increasing (inputChange e f) := by
  rintro _ u _ v ⟨x, hu, rfl⟩ ⟨y, hv, rfl⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (he hxy).le)
      (sub_nonpos.mpr (hf.le_of_lt hu hv hxy))
  · simp
  · exact mul_nonneg (sub_nonneg.mpr (he hyx).le)
      (sub_nonneg.mpr (hf.le_of_lt hv hu hyx))

theorem inputChange_maximal {e : ℝ → ℝ} {f : Operator}
    (he : StrictMono e) (hs : Function.Surjective e) (hf : MaximalIncreasing f) :
    MaximalIncreasing (inputChange e f) := by
  refine ⟨inputChange_increasing he hf.1, ?_⟩
  intro t u htu
  obtain ⟨x, rfl⟩ := hs t
  refine ⟨x, hf.2 ?_, rfl⟩
  intro y v hv
  have h := htu (show v ∈ inputChange e f (e y) from ⟨y, hv, rfl⟩)
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hexy := he hxy
    have huv : u - v ≤ 0 := by nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy.le) huv
  · simp
  · have heyx := he hyx
    have huv : 0 ≤ u - v := by nlinarith
    exact mul_nonneg (sub_nonneg.mpr hyx.le) huv

theorem inputChange_maximal_decreasing {e : ℝ → ℝ} {f : Operator}
    (he : StrictMono e) (hs : Function.Surjective e) (hf : MaximalDecreasing f) :
    MaximalDecreasing (inputChange e f) :=
  inputChange_maximal he hs hf

/-- A globally increasing extension agrees with the cubic on the nonnegative half-line. -/
def cubicExtension (σ₀ σ₁ σ₂ x : ℝ) : ℝ :=
  σ₀ * x + σ₁ * (max x 0) ^ 2 + σ₂ * (max x 0) ^ 3

theorem cubicExtension_eq {x σ₀ σ₁ σ₂ : ℝ} (hx : 0 ≤ x) :
    cubicExtension σ₀ σ₁ σ₂ x = cubicPolynomial σ₀ σ₁ σ₂ x := by
  simp [cubicExtension, cubicPolynomial, max_eq_left hx]

theorem cubicExtension_strictMono {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    StrictMono (cubicExtension σ₀ σ₁ σ₂) := by
  intro x y hxy
  have hlin := mul_lt_mul_of_pos_left hxy h₀
  have hmax : max x 0 ≤ max y 0 := max_le_max hxy.le le_rfl
  have hsquare := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_max_right x 0) hmax 2) h₁
  have hcube := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_max_right x 0) hmax 3) h₂
  unfold cubicExtension
  linarith

theorem cubicExtension_surjective {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    Function.Surjective (cubicExtension σ₀ σ₁ σ₂) := by
  intro t
  have hlin : σ₀ * (t / σ₀) = t := by field_simp
  by_cases ht : t < 0
  · refine ⟨t / σ₀, ?_⟩
    have hx : t / σ₀ ≤ 0 := (div_neg_of_neg_of_pos ht h₀).le
    simpa [cubicExtension, max_eq_right hx] using hlin
  · have ht₀ : 0 ≤ t := le_of_not_gt ht
    have hx : 0 ≤ t / σ₀ := div_nonneg ht₀ h₀.le
    have hc : Continuous (cubicExtension σ₀ σ₁ σ₂) := by
      unfold cubicExtension
      fun_prop
    have hleft : cubicExtension σ₀ σ₁ σ₂ 0 ≤ t := by
      simpa [cubicExtension] using ht₀
    have hright : t ≤ cubicExtension σ₀ σ₁ σ₂ (t / σ₀) := by
      rw [cubicExtension_eq hx]
      unfold cubicPolynomial
      rw [hlin]
      have ha : 0 ≤ σ₁ * (t / σ₀) ^ 2 := by positivity
      have hb : 0 ≤ σ₂ * (t / σ₀) ^ 3 := by positivity
      linarith
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hx hc.continuousOn ⟨hleft, hright⟩
    exact ⟨x, hx⟩

/-- The cubic graph includes its endpoint fibers and is already maximal. -/
theorem cubicProfile_maximal {α : Operator} (hα : MaximalDecreasing α)
    (hα₀ : dom α ⊆ Ici 0) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 < σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    MaximalDecreasing (cubicProfile α σ₀ σ₁ σ₂) := by
  have heq : cubicProfile α σ₀ σ₁ σ₂ = inputChange (cubicExtension σ₀ σ₁ σ₂) α := by
    ext t u
    constructor
    · rintro ⟨r, hr, ht⟩
      exact ⟨r, hr, ht.trans (cubicExtension_eq (hα₀ ⟨u, hr⟩)).symm⟩
    · rintro ⟨r, hr, ht⟩
      exact ⟨r, hr, ht.trans (cubicExtension_eq (hα₀ ⟨u, hr⟩))⟩
  rw [heq]
  exact inputChange_maximal_decreasing (cubicExtension_strictMono h₀ h₁ h₂)
    (cubicExtension_surjective h₀ h₁ h₂) hα

/-- A positive monomial acts on inverse fibers, retaining the completed zero fiber. -/
def monomialProfile (α : Operator) (σ : ℝ) (n : ℕ) : Operator :=
  fun t => {u | ∃ r, u ∈ α r ∧ t = σ * r ^ n}

/-- This is precisely composition with the positive root on `[0,∞)`,
including the inherited maximal fiber at zero. -/
theorem monomialProfile_mem_iff {α : Operator} (hα₀ : dom α ⊆ Ici 0)
    {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) {t u : ℝ} :
    u ∈ monomialProfile α σ n t ↔
      0 ≤ t ∧ u ∈ α ((t / σ) ^ ((n : ℝ)⁻¹)) := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr₀ : 0 ≤ r := hα₀ ⟨u, hr⟩
    constructor
    · positivity
    · have hdiv : σ * r ^ n / σ = r ^ n := by field_simp
      rw [hdiv, Real.pow_rpow_inv_natCast hr₀ hn]
      exact hr
  · rintro ⟨ht, hu⟩
    have hbase : 0 ≤ t / σ := div_nonneg ht hσ.le
    refine ⟨(t / σ) ^ ((n : ℝ)⁻¹), hu, ?_⟩
    rw [Real.rpow_inv_natCast_pow hbase hn]
    field_simp

theorem monomialProfile_one {α : Operator} {σ : ℝ} (hσ : σ ≠ 0) :
    monomialProfile α σ 1 = inputDivide σ α := by
  rw [← inverse_outputScale_inverse hσ α]
  ext t u
  simp only [monomialProfile, inverse, outputScale, pow_one, mem_setOf_eq]

private theorem min_three_mem {A : Set ℝ} {a b c : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) : min a (min b c) ∈ A := by
  rcases le_total a (min b c) with h | h
  · simpa [min_eq_left h] using ha
  · rw [min_eq_right h]
    rcases le_total b c with hbc | hcb
    · simpa [min_eq_left hbc] using hb
    · simpa [min_eq_right hcb] using hc

private theorem max_three_mem {A : Set ℝ} {a b c : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) : max a (max b c) ∈ A := by
  rcases le_total a (max b c) with h | h
  · rw [max_eq_right h]
    rcases le_total b c with hbc | hcb
    · simpa [max_eq_right hbc] using hc
    · simpa [max_eq_left hcb] using hb
  · simpa [max_eq_left h] using ha

/-- On a nonnegative interval, three independent monomial witnesses have the
same range as the diagonal polynomial. This includes unbounded fibers. -/
theorem cubic_interval_diagonal {A : Set ℝ} (hA : A.OrdConnected)
    (hA₀ : A ⊆ Ici 0) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂)
    {a b c : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    ∃ r ∈ A, cubicPolynomial σ₀ σ₁ σ₂ r = σ₀ * a + σ₁ * b ^ 2 + σ₂ * c ^ 3 := by
  let l := min a (min b c)
  let h := max a (max b c)
  have hlA : l ∈ A := min_three_mem ha hb hc
  have hhA : h ∈ A := max_three_mem ha hb hc
  have hl₀ : 0 ≤ l := hA₀ hlA
  have hh₀ : 0 ≤ h := hA₀ hhA
  have ha₀ : 0 ≤ a := hA₀ ha
  have hb₀ : 0 ≤ b := hA₀ hb
  have hc₀ : 0 ≤ c := hA₀ hc
  have hla : l ≤ a := min_le_left _ _
  have hlb : l ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hlc : l ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have hah : a ≤ h := le_max_left _ _
  have hbh : b ≤ h := (le_max_left _ _).trans (le_max_right _ _)
  have hch : c ≤ h := (le_max_right _ _).trans (le_max_right _ _)
  have hlower : cubicPolynomial σ₀ σ₁ σ₂ l ≤ σ₀ * a + σ₁ * b ^ 2 + σ₂ * c ^ 3 := by
    unfold cubicPolynomial
    gcongr
  have hupper : σ₀ * a + σ₁ * b ^ 2 + σ₂ * c ^ 3 ≤ cubicPolynomial σ₀ σ₁ σ₂ h := by
    unfold cubicPolynomial
    gcongr
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc (hla.trans hah)
    (cubicPolynomial_continuous σ₀ σ₁ σ₂).continuousOn ⟨hlower, hupper⟩
  exact ⟨r, hA.out hlA hhA hr, heq⟩

/-- The three-term parallel identity, with no loss at zero or at a jump. -/
theorem cubicProfile_eq_parallel_monomials {α : Operator}
    (hα : MaximalDecreasing α) (hα₀ : dom α ⊆ Ici 0)
    {σ₀ σ₁ σ₂ : ℝ} (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    cubicProfile α σ₀ σ₁ σ₂ =
      parallelAdd (parallelAdd (monomialProfile α σ₀ 1) (monomialProfile α σ₁ 2))
        (monomialProfile α σ₂ 3) := by
  ext t u
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨σ₀ * r + σ₁ * r ^ 2,
      ⟨σ₀ * r, ⟨r, hr, by simp⟩, σ₁ * r ^ 2, ⟨r, hr, rfl⟩, rfl⟩,
      σ₂ * r ^ 3, ⟨r, hr, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨p, ⟨a, ha, rfl⟩, q, ⟨b, hb, rfl⟩, rfl⟩,
      w, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨r, hr, heq⟩ := cubic_interval_diagonal
      (decreasing_fiber_ordConnected (inverse_maximal_decreasing hα) u)
      (fun x hx => hα₀ ⟨u, hx⟩) h₀ h₁ h₂ ha hb hc
    exact ⟨r, hr, by simpa only [pow_one] using heq.symm⟩

/-- Deterministic cubic transformation of a common-level tail bound. -/
theorem cubic_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} {α : Operator}
    (hX : TailBound ν X α) (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω)
    (hα₀ : dom α ⊆ Ici 0) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    TailBound ν (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω))
      (cubicProfile α σ₀ σ₁ σ₂) := by
  rintro t u ⟨r, hr, rfl⟩
  have hr₀ : 0 ≤ r := hα₀ ⟨u, hr⟩
  have hsub : ({ω | cubicPolynomial σ₀ σ₁ σ₂ r <
      cubicPolynomial σ₀ σ₁ σ₂ (X ω)} : Set Ω) ≤ᵐ[ν] {ω | r < X ω} := by
    filter_upwards [hX₀] with ω hω
    intro hpoly
    by_contra h
    exact (not_lt_of_ge (cubicPolynomial_monotoneOn h₀ h₁ h₂ hω hr₀
      (le_of_not_gt h))) hpoly
  exact (ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono_ae hsub)).trans (hX hr)

theorem survival_cubic_comparison {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hmX : Measurable X)
    {α : Operator} (hX : DecLE (survival (Measure.map X ν)) α)
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω) (hα₀ : dom α ⊆ Ici 0) {σ₀ σ₁ σ₂ : ℝ}
    (h₀ : 0 ≤ σ₀) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    DecLE (survival (Measure.map (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω)) ν))
      (cubicProfile α σ₀ σ₁ σ₂) := by
  apply (survival_map_comparison_iff ν
    ((cubicPolynomial_continuous σ₀ σ₁ σ₂).measurable.comp hmX) _).2
  exact cubic_tail_bound ν ((survival_map_comparison_iff ν hmX _).1 hX)
    hX₀ hα₀ h₀ h₁ h₂

/-- A continuous strict-tail bound also controls the weak tail at every positive threshold. -/
theorem weak_tail_le_of_continuous_strict_tail {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} {b : ℝ → ℝ}
    (hb : Continuous b) (htail : ∀ r > 0, ν.real {ω | r < X ω} ≤ b r)
    {r : ℝ} (hr : 0 < r) : ν.real {ω | r ≤ X ω} ≤ b r := by
  apply ge_of_tendsto (hb.continuousAt.continuousWithinAt : Tendsto b (𝓝[<] r) (𝓝 (b r)))
  filter_upwards [Ioo_mem_nhdsLT hr] with s hs
  exact (measureReal_mono (fun ω hω => hs.2.trans_le hω)).trans (htail s hs.1)

/-- The squared radius corresponding to the three cubic scales. -/
def cubicRate (t σ₀ σ₁ σ₂ : ℝ) : ℝ :=
  min (t ^ 2 / (9 * σ₀ ^ 2))
    (min (t / (3 * σ₁)) ((t / (3 * σ₂)) ^ (2 / 3 : ℝ)))

theorem cubicRate_pos {t σ₀ σ₁ σ₂ : ℝ}
    (ht : 0 < t) (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    0 < cubicRate t σ₀ σ₁ σ₂ := by
  unfold cubicRate
  apply lt_min
  · positivity
  · apply lt_min <;> positivity

/-- At the square root of the rate, each polynomial term uses at most one third of `t`. -/
theorem cubicPolynomial_sqrt_rate_le {t σ₀ σ₁ σ₂ : ℝ}
    (ht : 0 < t) (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    cubicPolynomial σ₀ σ₁ σ₂ (Real.sqrt (cubicRate t σ₀ σ₁ σ₂)) ≤ t := by
  let m := cubicRate t σ₀ σ₁ σ₂
  let r := Real.sqrt m
  have hm : 0 < m := cubicRate_pos ht h₀ h₁ h₂
  have hr : 0 ≤ r := Real.sqrt_nonneg m
  have hr2 : r ^ 2 = m := Real.sq_sqrt hm.le
  have hma : m ≤ t ^ 2 / (9 * σ₀ ^ 2) := min_le_left _ _
  have hmb : m ≤ t / (3 * σ₁) := (min_le_right _ _).trans (min_le_left _ _)
  have hmc : m ≤ (t / (3 * σ₂)) ^ (2 / 3 : ℝ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ha : σ₀ * r ≤ t / 3 := by
    have hmul := (le_div_iff₀ (show 0 < 9 * σ₀ ^ 2 by positivity)).1 hma
    rw [← hr2] at hmul
    nlinarith [mul_nonneg h₀.le hr]
  have hb : σ₁ * r ^ 2 ≤ t / 3 := by
    have hmul := (le_div_iff₀ (show 0 < 3 * σ₁ by positivity)).1 hmb
    rw [← hr2] at hmul
    nlinarith
  let a := (t / (3 * σ₂)) ^ (1 / 3 : ℝ)
  have hbase : 0 ≤ t / (3 * σ₂) := by positivity
  have ha₀ : 0 ≤ a := Real.rpow_nonneg hbase _
  have ha2 : a ^ 2 = (t / (3 * σ₂)) ^ (2 / 3 : ℝ) := by
    change ((t / (3 * σ₂)) ^ (1 / 3 : ℝ)) ^ 2 = _
    rw [← Real.rpow_mul_natCast hbase]
    congr 1
    norm_num
  have ha3 : a ^ 3 = t / (3 * σ₂) := by
    have h := Real.rpow_inv_natCast_pow hbase (show (3 : ℕ) ≠ 0 by norm_num)
    simpa [a, one_div] using h
  have hra : r ≤ a := by
    rw [← hr2, ← ha2] at hmc
    nlinarith
  have hc : σ₂ * r ^ 3 ≤ t / 3 := by
    have hpow := pow_le_pow_left₀ hr hra 3
    rw [ha3] at hpow
    have hmul := (le_div_iff₀ (show 0 < 3 * σ₂ by positivity)).1 hpow
    nlinarith
  change σ₀ * r + σ₁ * r ^ 2 + σ₂ * r ^ 3 ≤ t
  linarith

/-- The displayed multilevel bound, with exponents `2`, `1`, and `2/3`.
This controls the weak tail and hence every value of the completed survival fiber. -/
theorem cubic_gaussian_weak_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ}
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω)
    (htail : ∀ r > 0, ν.real {ω | r < X ω} ≤ Real.exp (-(r ^ 2)))
    {t σ₀ σ₁ σ₂ : ℝ} (ht : 0 < t)
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    ν.real {ω | t ≤ cubicPolynomial σ₀ σ₁ σ₂ (X ω)} ≤
      Real.exp (-cubicRate t σ₀ σ₁ σ₂) := by
  let m := cubicRate t σ₀ σ₁ σ₂
  let r := Real.sqrt m
  have hm : 0 < m := cubicRate_pos ht h₀ h₁ h₂
  have hr : 0 < r := Real.sqrt_pos.2 hm
  have hpoly : cubicPolynomial σ₀ σ₁ σ₂ r ≤ t := cubicPolynomial_sqrt_rate_le ht h₀ h₁ h₂
  have hsub : ({ω | t ≤ cubicPolynomial σ₀ σ₁ σ₂ (X ω)} : Set Ω) ≤ᵐ[ν]
      {ω | r ≤ X ω} := by
    filter_upwards [hX₀] with ω hω
    intro htω
    by_contra h
    have hlt := cubicPolynomial_strictMonoOn h₀ h₁.le h₂.le hω hr.le (lt_of_not_ge h)
    exact (not_lt_of_ge (htω.trans' hpoly)) hlt
  have hb : ν.real {ω | r ≤ X ω} ≤ Real.exp (-(r ^ 2)) :=
    weak_tail_le_of_continuous_strict_tail ν (by fun_prop) htail hr
  have hr2 : r ^ 2 = m := Real.sq_sqrt hm.le
  exact (ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono_ae hsub)).trans (by
    simpa only [hr2] using hb)

/-- The multilevel numerical bound applies to every member of the completed
survival fiber, including its upper endpoint at an atom. -/
theorem cubic_gaussian_survival_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → ℝ} (hmX : Measurable X)
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω)
    (htail : ∀ r > 0, ν.real {ω | r < X ω} ≤ Real.exp (-(r ^ 2)))
    {t σ₀ σ₁ σ₂ u : ℝ} (ht : 0 < t)
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂)
    (hu : u ∈ survival
      (Measure.map (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω)) ν) t) :
    u ≤ Real.exp (-cubicRate t σ₀ σ₁ σ₂) := by
  have hm : Measurable (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω)) :=
    (cubicPolynomial_continuous σ₀ σ₁ σ₂).measurable.comp hmX
  have hu' := hu.2
  rw [map_measureReal_apply hm measurableSet_Ici] at hu'
  exact hu'.trans (cubic_gaussian_weak_tail_bound ν hX₀ htail ht h₀ h₁ h₂)

theorem cubic_gaussian_survival_bound_of_comparison
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hmX : Measurable X) {α : Operator}
    (hX : DecLE (survival (Measure.map X ν)) α)
    (hX₀ : ∀ᵐ ω ∂ν, 0 ≤ X ω)
    (hgauss : ∀ r > 0, Real.exp (-(r ^ 2)) ∈ α r)
    {t σ₀ σ₁ σ₂ u : ℝ} (ht : 0 < t)
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂)
    (hu : u ∈ survival
      (Measure.map (fun ω => cubicPolynomial σ₀ σ₁ σ₂ (X ω)) ν) t) :
    u ≤ Real.exp (-cubicRate t σ₀ σ₁ σ₂) :=
  cubic_gaussian_survival_bound ν hmX hX₀
    (fun r hr => (survival_map_comparison_iff ν hmX α).1 hX (hgauss r hr))
    ht h₀ h₁ h₂ hu

end ScalarMonotone
