import MonotoneOperators.Interface
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Scalar area: selections, exceptional fibers, and finite partitions

Source: the last manuscript excerpt, Definitions `stepoperator`, `area`,
`piecewisearea`, and the expectation identity following Proposition `area`.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
This module does not claim the Darboux supremum theorem or inverse-area formula.
The nonnegative integral below takes values in ENNReal, so divergence is retained.
-/

open Set Filter MeasureTheory
open scoped ENNReal Interval

noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- Membership of a scalar selection, on a specified set. -/
def SelectionOn (f : Operator) (I : Set ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ x ∈ I, s x ∈ f x

/-- Fibers with two strictly ordered real values. No maximality is needed. -/
def jumpInputs (f : Operator) : Set ℝ :=
  {x | ∃ u ∈ f x, ∃ v ∈ f x, u < v}

/-- The rational-interval argument for countability of nonsingleton fibers. -/
theorem countable_jumpInputs {f : Operator} (hf : Increasing f) :
    (jumpInputs f).Countable := by
  classical
  have hex : ∀ x : jumpInputs f, ∃ q : ℚ,
      ∃ u ∈ f x.val, ∃ v ∈ f x.val, u < (q : ℝ) ∧ (q : ℝ) < v := by
    intro x
    obtain ⟨u, hu, v, hv, huv⟩ := x.property
    obtain ⟨q, huq, hqv⟩ := exists_rat_btwn huv
    exact ⟨q, u, hu, v, hv, huq, hqv⟩
  choose q hq using hex
  have hinj : Function.Injective q := by
    intro x y hxy
    obtain ⟨u, hu, v, hv, huq, hqv⟩ := hq x
    obtain ⟨w, hw, z, hz, hwq, hqz⟩ := hq y
    have he : (q x : ℝ) = (q y : ℝ) := congrArg (fun a : ℚ => (a : ℝ)) hxy
    apply Subtype.ext
    rcases lt_trichotomy x.val y.val with h | h | h
    · have hb := (increasing_iff_order.mp hf) hv hw h
      linarith
    · exact h
    · have hb := (increasing_iff_order.mp hf) hz hu h
      linarith
  letI : Countable (jumpInputs f) := hinj.countable
  exact Set.to_countable _

/-- An increasing graph has at most one value off the exceptional set. -/
theorem fiber_subsingleton_off_jumps (f : Operator) {x : ℝ}
    (hx : x ∉ jumpInputs f) : (f x).Subsingleton := by
  intro u hu v hv
  rcases lt_trichotomy u v with h | h | h
  · exact (hx ⟨u, hu, v, hv, h⟩).elim
  · exact h
  · exact (hx ⟨v, hv, u, hu, h⟩).elim

/-- Selections agree almost everywhere, for every atomless base measure. -/
theorem selections_ae_eq {f : Operator} (hf : Increasing f)
    {I : Set ℝ} {s t : ℝ → ℝ} (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (hI : MeasurableSet I) :
    s =ᵐ[μ.restrict I] t := by
  filter_upwards [(countable_jumpInputs hf).ae_not_mem (μ.restrict I),
    ae_restrict_mem hI] with x hx hxi
  exact fiber_subsingleton_off_jumps f hx (hs x hxi) (ht x hxi)

/-- The decreasing version uses reflection of the output. -/
theorem decreasing_selections_ae_eq {f : Operator} (hf : Decreasing f)
    {I : Set ℝ} {s t : ℝ → ℝ} (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (hI : MeasurableSet I) :
    s =ᵐ[μ.restrict I] t := by
  have hs' : SelectionOn (negOut f) I (fun x => -s x) := by
    intro x hx
    change -(-s x) ∈ f x
    simpa only [neg_neg] using hs x hx
  have ht' : SelectionOn (negOut f) I (fun x => -t x) := by
    intro x hx
    change -(-t x) ∈ f x
    simpa only [neg_neg] using ht x hx
  have he := selections_ae_eq hf hs' ht' μ hI
  filter_upwards [he] with x hx
  exact neg_injective hx

/-- Independence of the scalar integral from the choice of selection. -/
theorem selection_integral_eq {f : Operator} (hf : Increasing f)
    {I : Set ℝ} {s t : ℝ → ℝ} (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (hI : MeasurableSet I) :
    (∫ x in I, s x ∂μ) = ∫ x in I, t x ∂μ :=
  integral_congr_ae (selections_ae_eq hf hs ht μ hI)

theorem decreasing_selection_integral_eq {f : Operator} (hf : Decreasing f)
    {I : Set ℝ} {s t : ℝ → ℝ} (hs : SelectionOn f I s) (ht : SelectionOn f I t)
    (μ : Measure ℝ) [NoAtoms μ] (hI : MeasurableSet I) :
    (∫ x in I, s x ∂μ) = ∫ x in I, t x ∂μ :=
  integral_congr_ae (decreasing_selections_ae_eq hf hs ht μ hI)

/-- A selection inherits monotonicity, including at filled jumps. -/
theorem selection_monotoneOn {f : Operator} (hf : Increasing f)
    {I : Set ℝ} {s : ℝ → ℝ} (hs : SelectionOn f I s) : MonotoneOn s I := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with h | h
  · simp [h]
  · exact (increasing_iff_order.mp hf) (hs x hx) (hs y hy) h

theorem selection_intervalIntegrable {f : Operator} (hf : Increasing f)
    {a b : ℝ} {s : ℝ → ℝ} (hs : SelectionOn f (uIcc a b) s) :
    IntervalIntegrable s volume a b :=
  (selection_monotoneOn hf hs).intervalIntegrable

/-- Endpoints and finitely many breakpoints do not affect a scalar area. -/
theorem integral_eq_off_finite {s t : ℝ → ℝ} {I E : Set ℝ}
    (hE : E.Finite) (heq : ∀ x, x ∉ E → s x = t x) :
    (∫ x in I, s x) = ∫ x in I, t x := by
  apply integral_congr_ae
  filter_upwards [hE.countable.ae_not_mem (volume.restrict I)] with x hx
  exact heq x hx

/-- The signed scalar step area, before completion of the graph. -/
def stepArea (n : ℕ) (x c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, c j * (x (j+1) - x j)

/-- Splitting a step leaves its area unchanged. -/
theorem split_step_area (a b c h : ℝ) :
    h * (c-a) = h * (b-a) + h * (c-b) := by ring

/-- A convenient telescoping identity for partition errors. -/
theorem sum_differences (n : ℕ) (u : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, (u (j+1)-u j)) = u n-u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The quantitative estimate in the proof of the Darboux area formula. -/
theorem darboux_gap_bound (n : ℕ) (x u : ℕ → ℝ) (mesh : ℝ)
    (hx : ∀ j < n, 0 ≤ x (j+1)-x j)
    (hmesh : ∀ j < n, x (j+1)-x j ≤ mesh)
    (hu : ∀ j < n, 0 ≤ u (j+1)-u j) :
    0 ≤ (∑ j ∈ Finset.range n, (x (j+1)-x j) * (u (j+1)-u j)) ∧
    (∑ j ∈ Finset.range n, (x (j+1)-x j) * (u (j+1)-u j)) ≤
      mesh * (u n-u 0) := by
  constructor
  · exact Finset.sum_nonneg fun j hj =>
      mul_nonneg (hx j (Finset.mem_range.mp hj)) (hu j (Finset.mem_range.mp hj))
  · calc
      _ ≤ ∑ j ∈ Finset.range n, mesh * (u (j+1)-u j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hmesh j (Finset.mem_range.mp hj))
          (hu j (Finset.mem_range.mp hj))
      _ = mesh * (u n-u 0) := by rw [← Finset.mul_sum, sum_differences]

/-- The upper-minus-lower sum has exactly the error estimated above. -/
theorem stepArea_upper_sub_lower (n : ℕ) (x u : ℕ → ℝ) :
    stepArea n x (fun j => u (j+1)) - stepArea n x u =
      ∑ j ∈ Finset.range n, (x (j+1)-x j) * (u (j+1)-u j) := by
  unfold stepArea
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Integral additivity for an arbitrary finite admissible partition. -/
theorem integral_partition (n : ℕ) (x : ℕ → ℝ) (s : ℝ → ℝ)
    (hs : ∀ j < n, IntervalIntegrable s volume (x j) (x (j+1))) :
    (∫ t in (x 0)..(x n), s t) =
      ∑ j ∈ Finset.range n, ∫ t in x j..x (j+1), s t :=
  (intervalIntegral.sum_integral_adjacent_intervals hs).symm

/-- The ordinary integral of a step selection equals its finite area sum. -/
theorem integral_step_eq_area (n : ℕ) (x c : ℕ → ℝ) (s : ℝ → ℝ)
    (hx : ∀ j < n, x j ≤ x (j+1))
    (hs : ∀ j < n, IntervalIntegrable s volume (x j) (x (j+1)))
    (heq : ∀ j < n, ∀ t ∈ Ioo (x j) (x (j+1)), s t = c j) :
    (∫ t in (x 0)..(x n), s t) = stepArea n x c := by
  rw [integral_partition n x s hs]
  unfold stepArea
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  have h : (∫ t in x j..x (j+1), s t) =
      ∫ t in x j..x (j+1), c j := by
    simp only [intervalIntegral.integral_of_le (hx j hjn),
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo (heq j hjn)
  rw [h, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_comm]

/-- Tail area identity with possible infinite expectation. -/
theorem expectation_tail_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (hY0 : 0 ≤ᵐ[μ] Y) :
    (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} :=
  lintegral_eq_lintegral_meas_lt μ hY0 hY

/-- Tail domination implies area domination; no finite-expectation shortcut. -/
theorem expectation_le_tail_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Y : Ω → ℝ} {b : ℝ → ℝ≥0∞}
    (hY : AEMeasurable Y μ) (hY0 : 0 ≤ᵐ[μ] Y)
    (hb : ∀ t > 0, μ {ω | t < Y ω} ≤ b t) :
    (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) ≤ ∫⁻ t in Ioi (0 : ℝ), b t := by
  rw [expectation_tail_area μ hY hY0]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hb t ht

end ScalarMonotone.EndOfPaper

end -- noncomputable section
