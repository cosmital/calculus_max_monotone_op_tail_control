import EndOfPaper.Area
import MonotoneOperators.Completion

/-!
# Scalar Hardy averages

Source: `hardycalculus`, `hardyconvexity`, `hardyscalar`.
The scalar identities are separated from the not-yet-proved identification
with the manuscript's measurable-family operator integral.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- The finite scalar average. Integrability is an explicit hypothesis in
all theorems that interpret this as an actual area average. -/
def hardyScalar (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..p, f u) / p

/-- The dilation representation, derived by the affine substitution theorem. -/
theorem hardyScalar_dilation (f : ℝ → ℝ) {p : ℝ} (hp : 0 < p) :
    hardyScalar f p = ∫ r in (0 : ℝ)..1, f (r*p) := by
  simpa [hardyScalar, div_eq_mul_inv, smul_eq_mul, mul_comm] using
    (intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) f hp.ne').symm

theorem hardyScalar_dilation_integrable {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : IntervalIntegrable f volume 0 p) :
    IntervalIntegrable (fun r => f (r*p)) volume 0 1 := by
  simpa [hp.ne'] using hf.comp_mul_right p

/-- The integration interval has the required invariance under positive dilation. -/
theorem dilation_mem_Ioo {L p r : ℝ} (hp : p ∈ Ioo 0 L) (hr : r ∈ Ioo 0 1) :
    r*p ∈ Ioo 0 L := by
  constructor
  · exact mul_pos hr.1 hp.1
  · exact (mul_lt_of_lt_one_left hp.1 hr.2).trans hp.2

theorem hardyScalar_add {f g : ℝ → ℝ} {p : ℝ}
    (hf : IntervalIntegrable f volume 0 p) (hg : IntervalIntegrable g volume 0 p) :
    hardyScalar (fun x => f x+g x) p = hardyScalar f p+hardyScalar g p := by
  simp only [hardyScalar, intervalIntegral.integral_add hf hg, add_div]

theorem hardyScalar_smul (f : ℝ → ℝ) (c p : ℝ) :
    hardyScalar (fun x => c*f x) p = c*hardyScalar f p := by
  simp only [hardyScalar, intervalIntegral.integral_const_mul]
  ring

theorem hardyScalar_neg (f : ℝ → ℝ) (p : ℝ) :
    hardyScalar (fun x => -f x) p = -hardyScalar f p := by
  simpa using hardyScalar_smul f (-1) p

theorem hardyScalar_const (c : ℝ) {p : ℝ} (hp : p ≠ 0) :
    hardyScalar (fun _ => c) p = c := by
  simp [hardyScalar, intervalIntegral.integral_const, smul_eq_mul, hp]

/-- Pointwise comparison requires no chosen values at the endpoints. -/
theorem hardyScalar_mono {f g : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : IntervalIntegrable f volume 0 p) (hg : IntervalIntegrable g volume 0 p)
    (hfg : ∀ u ∈ Ioo 0 p, f u ≤ g u) :
    hardyScalar f p ≤ hardyScalar g p := by
  exact (div_le_div_iff_of_pos_right hp).mpr
    (intervalIntegral.integral_mono_on_of_le_Ioo hp.le hf hg hfg)

/-- Every decreasing selection lies below its upper-tail average. -/
theorem le_hardyScalar {f : ℝ → ℝ} {L p : ℝ}
    (hf : AntitoneOn f (Ioo 0 L)) (hp : p ∈ Ioo 0 L)
    (hi : IntervalIntegrable f volume 0 p) : f p ≤ hardyScalar f p := by
  have h : (∫ u in (0 : ℝ)..p, f p) ≤ ∫ u in (0 : ℝ)..p, f u := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hp.1.le
      intervalIntegrable_const hi
    intro u hu
    exact hf ⟨hu.1, hu.2.trans hp.2⟩ hp hu.2.le
  apply (le_div_iff₀ hp.1).mpr
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- Monotonicity in the tail mass follows by integrating dilations. -/
theorem hardyScalar_antitoneOn {f : ℝ → ℝ} {L : ℝ}
    (hf : AntitoneOn f (Ioo 0 L))
    (hi : ∀ p ∈ Ioo 0 L, IntervalIntegrable f volume 0 p) :
    AntitoneOn (hardyScalar f) (Ioo 0 L) := by
  intro p hp q hq hpq
  rw [hardyScalar_dilation f hq.1, hardyScalar_dilation f hp.1]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    (hardyScalar_dilation_integrable hq.1 (hi q hq))
    (hardyScalar_dilation_integrable hp.1 (hi p hp))
  intro r hr
  exact hf (dilation_mem_Ioo hp hr) (dilation_mem_Ioo hq hr)
    (mul_le_mul_of_nonneg_left hpq hr.1.le)

/-- Separated comparison, allowing different right endpoints. -/
theorem hardyScalar_separated {f g : ℝ → ℝ} {Lf Lg p q : ℝ}
    (hp : p ∈ Ioo 0 Lf) (hq : q ∈ Ioo 0 Lg) (hpq : q < p)
    (hf : IntervalIntegrable f volume 0 p) (hg : IntervalIntegrable g volume 0 q)
    (hfg : ∀ x ∈ Ioo 0 Lf, ∀ y ∈ Ioo 0 Lg, y < x → f x ≤ g y) :
    hardyScalar f p ≤ hardyScalar g q := by
  rw [hardyScalar_dilation f hp.1, hardyScalar_dilation g hq.1]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    (hardyScalar_dilation_integrable hp.1 hf)
    (hardyScalar_dilation_integrable hq.1 hg)
  intro r hr
  exact hfg (r*p) (dilation_mem_Ioo hp hr) (r*q) (dilation_mem_Ioo hq hr)
    (mul_lt_mul_of_pos_left hpq hr.1)

/-- The scalar Hardy transformation preserves convexity. -/
theorem hardyScalar_convexOn {f : ℝ → ℝ} {L : ℝ}
    (hf : ConvexOn ℝ (Ioo 0 L) f)
    (hi : ∀ p ∈ Ioo 0 L, IntervalIntegrable f volume 0 p) :
    ConvexOn ℝ (Ioo 0 L) (hardyScalar f) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x+b • y ∈ Ioo 0 L := hf.1 hx hy ha hb hab
  have hxint := hardyScalar_dilation_integrable hx.1 (hi x hx)
  have hyint := hardyScalar_dilation_integrable hy.1 (hi y hy)
  rw [hardyScalar_dilation f hz.1, hardyScalar_dilation f hx.1,
    hardyScalar_dilation f hy.1]
  calc
    (∫ r in (0 : ℝ)..1, f (r*(a • x+b • y))) ≤
        ∫ r in (0 : ℝ)..1, a*f (r*x)+b*f (r*y) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
        (hardyScalar_dilation_integrable hz.1 (hi _ hz))
        ((hxint.const_mul a).add (hyint.const_mul b))
      intro r hr
      have hc := hf.2 (dilation_mem_Ioo hx hr) (dilation_mem_Ioo hy hr) ha hb hab
      have he : r*(a*x+b*y) = a*(r*x)+b*(r*y) := by ring
      simpa only [smul_eq_mul, he] using hc
    _ = a • (∫ r in (0 : ℝ)..1, f (r*x)) +
        b • (∫ r in (0 : ℝ)..1, f (r*y)) := by
      rw [intervalIntegral.integral_add (hxint.const_mul _) (hyint.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]

/-- Concavity follows by negating the convexity statement. -/
theorem hardyScalar_concaveOn {f : ℝ → ℝ} {L : ℝ}
    (hf : ConcaveOn ℝ (Ioo 0 L) f)
    (hi : ∀ p ∈ Ioo 0 L, IntervalIntegrable f volume 0 p) :
    ConcaveOn ℝ (Ioo 0 L) (hardyScalar f) := by
  have hn := (hardyScalar_convexOn hf.neg (fun p hp => (hi p hp).neg)).neg
  have hneg : hardyScalar (-f) = -hardyScalar f := by
    funext p
    exact hardyScalar_neg f p
  rwa [hneg, neg_neg] at hn

/-- A scalar antitone function has the manuscript's unique maximal completion. -/
theorem antitoneOn_unique_completion {f : ℝ → ℝ} {I : Set ℝ}
    (hf : AntitoneOn f I) (hI : I.OrdConnected) (hne : I.Nonempty) :
    ∃! g : Operator, MaximalDecreasing g ∧ restrictOperator (ofFun f) I ≤ g ∧
      dom g ⊆ closure I := by
  apply unique_maximal_decreasing_completion hI hne
  · apply increasing_iff_order.mpr
    intro x u y v hu hv hxy
    have hu' : x ∈ I ∧ -u = f x := hu
    have hv' : y ∈ I ∧ -v = f y := hv
    have hle := hf hu'.1 hv'.1 hxy.le
    linarith [hu'.2, hv'.2]
  · apply dom_restrictOperator
    intro x hx
    exact ⟨f x, rfl⟩

/-- Existence and uniqueness of completion for the scalar Hardy average.
This is not yet the identification with the measurable-family integral. -/
theorem hardyScalar_unique_completion {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : AntitoneOn f (Ioo 0 L))
    (hi : ∀ p ∈ Ioo 0 L, IntervalIntegrable f volume 0 p) :
    ∃! g : Operator, MaximalDecreasing g ∧
      restrictOperator (ofFun (hardyScalar f)) (Ioo 0 L) ≤ g ∧
      dom g ⊆ closure (Ioo 0 L) :=
  antitoneOn_unique_completion (hardyScalar_antitoneOn hf hi)
    ordConnected_Ioo (nonempty_Ioo.mpr hL)


/-- Positive-half-line version; no finite right endpoint is imposed. -/
theorem hardyScalar_antitoneOn_Ioi {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ioi 0))
    (hi : ∀ p > 0, IntervalIntegrable f volume 0 p) :
    AntitoneOn (hardyScalar f) (Ioi 0) := by
  intro p hp q hq hpq
  let L : ℝ := max p q+1
  have hpL : p ∈ Ioo 0 L := ⟨hp, by dsimp [L]; linarith [le_max_left p q]⟩
  have hqL : q ∈ Ioo 0 L := ⟨hq, by dsimp [L]; linarith [le_max_right p q]⟩
  have hfL : AntitoneOn f (Ioo 0 L) := fun _ hx _ hy hxy => hf hx.1 hy.1 hxy
  exact hardyScalar_antitoneOn hfL (fun t ht => hi t ht.1) hpL hqL hpq

theorem le_hardyScalar_Ioi {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ioi 0)) {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p) : f p ≤ hardyScalar f p := by
  apply le_hardyScalar (L := p+1)
  · exact fun _ hx _ hy hxy => hf hx.1 hy.1 hxy
  · exact ⟨hp, by linarith⟩
  · exact hi

theorem hardyScalar_unique_completion_Ioi {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ioi 0))
    (hi : ∀ p > 0, IntervalIntegrable f volume 0 p) :
    ∃! g : Operator, MaximalDecreasing g ∧
      restrictOperator (ofFun (hardyScalar f)) (Ioi 0) ≤ g ∧
      dom g ⊆ closure (Ioi 0) :=
  antitoneOn_unique_completion (hardyScalar_antitoneOn_Ioi hf hi)
    ordConnected_Ioi ⟨1, by norm_num⟩

theorem hardyScalar_convexOn_Ioi {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f)
    (hi : ∀ p > 0, IntervalIntegrable f volume 0 p) :
    ConvexOn ℝ (Ioi 0) (hardyScalar f) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  let L : ℝ := max x y+1
  have hxL : x ∈ Ioo 0 L := ⟨hx, by dsimp [L]; linarith [le_max_left x y]⟩
  have hyL : y ∈ Ioo 0 L := ⟨hy, by dsimp [L]; linarith [le_max_right x y]⟩
  have hfL : ConvexOn ℝ (Ioo 0 L) f := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro u hu v hv c d hc hd hcd
    exact hf.2 hu.1 hv.1 hc hd hcd
  exact (hardyScalar_convexOn hfL (fun p hp => hi p hp.1)).2 hxL hyL ha hb hab

theorem hardyScalar_concaveOn_Ioi {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Ioi 0) f)
    (hi : ∀ p > 0, IntervalIntegrable f volume 0 p) :
    ConcaveOn ℝ (Ioi 0) (hardyScalar f) := by
  have hn := (hardyScalar_convexOn_Ioi hf.neg (fun p hp => (hi p hp).neg)).neg
  have hneg : hardyScalar (-f) = -hardyScalar f := by
    funext p
    exact hardyScalar_neg f p
  rwa [hneg, neg_neg] at hn

end ScalarMonotone.EndOfPaper

end -- noncomputable section
