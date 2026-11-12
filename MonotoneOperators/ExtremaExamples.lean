import MonotoneOperators.ExtremaFinite
import MonotoneOperators.OrderGeometry

/-! # Unbounded families and the necessity of completing infinite envelopes -/

namespace ScalarMonotone

open Set Filter
open scoped Topology

noncomputable section

def IncGraph.constant (c : ℝ) : IncGraph :=
  ⟨ofFun (fun _ => c), constant_maximal c⟩
def DecGraph.constant (c : ℝ) : DecGraph :=
  ⟨ofFun (fun _ => c), constant_maximal_decreasing c⟩
def IncGraph.vertical (c : ℝ) : IncGraph :=
  ⟨ScalarMonotone.vertical c, vertical_maximal c⟩
def DecGraph.vertical (c : ℝ) : DecGraph :=
  ⟨ScalarMonotone.vertical c, vertical_maximal_decreasing c⟩

theorem IncGraph.constants_not_bddAbove :
    ¬ BddAbove (range (fun n : ℕ => IncGraph.constant n)) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, u, hu⟩ := maximal_nonempty g.property
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have h : IncLE (ofFun (fun _ => (n : ℝ))) g.val := hg (mem_range_self n)
  have hh := h (x := x - 1) (u := n) rfl hu (by linarith)
  exact (not_le_of_gt hn) hh

theorem DecGraph.constants_not_bddAbove :
    ¬ BddAbove (range (fun n : ℕ => DecGraph.constant n)) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, u, hu⟩ := maximal_nonempty g.property
  obtain ⟨n, hn⟩ := exists_nat_gt (-u)
  have h : DecLE (ofFun (fun _ => (n : ℝ))) g.val := hg (mem_range_self n)
  have hh := h (x := x + 1) (u := n) (v := -u) rfl hu (by linarith)
  exact (not_le_of_gt hn) hh

theorem IncGraph.inf_vertical_zero_one :
    IncGraph.vertical 0 ⊓ IncGraph.vertical 1 = IncGraph.vertical 1 := by
  apply inf_eq_right.mpr
  exact (incLE_vertical_iff 1 0).mpr (by norm_num)

theorem IncGraph.vertical_zero_empty_at_one : (IncGraph.vertical 0).val 1 = ∅ := by
  exact vertical_fiber_empty (by norm_num)

/-- Resolvent of the completed increasing step from `0` to `1` at `a`. -/
def stepResolvent (a s : ℝ) : ℝ := max (s - 1) (min a s)

theorem stepResolvent_monotone (a : ℝ) : Monotone (stepResolvent a) :=
  (show Monotone (fun s : ℝ => s - 1) from fun _ _ h => sub_le_sub_right h 1).max
    (monotone_const.min monotone_id)

theorem stepResolvent_lipschitz (a : ℝ) : LipschitzWith 1 (stepResolvent a) := by
  have hl : LipschitzWith 1 (fun s : ℝ => s - 1) := by
    apply LipschitzWith.mk_one
    intro x y
    simp only [Real.dist_eq]
    ring_nf
    exact le_rfl
  simpa [stepResolvent] using hl.max (LipschitzWith.id.const_min a)

def IncGraph.step (a : ℝ) : IncGraph :=
  IncGraph.ofJ (stepResolvent a) (stepResolvent_monotone a) (stepResolvent_lipschitz a)

@[simp] theorem IncGraph.J_step (a s : ℝ) : (IncGraph.step a).J s = stepResolvent a s := by
  simp [IncGraph.step]

theorem IncGraph.step_fiber_left {a x : ℝ} (hx : x < a) :
    (IncGraph.step a).val x = {0} := by
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_step]
  change max (x + u - 1) (min a (x + u)) = x ↔ u = 0
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> intro h <;> linarith

theorem IncGraph.step_fiber_right {a x : ℝ} (hx : a < x) :
    (IncGraph.step a).val x = {1} := by
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_step]
  change max (x + u - 1) (min a (x + u)) = x ↔ u = 1
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> intro h <;> linarith

theorem IncGraph.step_zero_fiber_of_pos {a : ℝ} (ha : 0 < a) :
    (IncGraph.step a).val 0 = {0} := by
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_step]
  simp only [zero_add, stepResolvent, mem_singleton_iff]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> intro h <;> linarith

theorem IncGraph.step_fiber_at_jump (a : ℝ) :
    (IncGraph.step a).val a = Icc (0 : ℝ) 1 := by
  ext u
  rw [IncGraph.mem_iff_J, IncGraph.J_step]
  change max (a + u - 1) (min a (a + u)) = a ↔ 0 ≤ u ∧ u ≤ 1
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> intro h
  all_goals first | constructor <;> linarith | linarith [h.1, h.2]

theorem IncGraph.step_antitone : Antitone IncGraph.step := by
  intro a b hab
  apply IncGraph.le_iff_J.mpr
  intro s
  simp only [IncGraph.J_step, stepResolvent]
  exact max_le_max_left _ (min_le_min_right _ hab)

theorem IncGraph.step_sequence_isLUB :
    IsLUB (range (fun n : ℕ => IncGraph.step (1 / ((n : ℝ) + 1)))) (IncGraph.step 0) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact IncGraph.step_antitone (by positivity)
  · intro g hg
    apply IncGraph.le_iff_J.mpr
    intro s
    have ht : Tendsto (fun n : ℕ => stepResolvent (1 / ((n : ℝ) + 1)) s)
        atTop (𝓝 (stepResolvent 0 s)) :=
      tendsto_const_nhds.max (tendsto_one_div_add_atTop_nhds_zero_nat.min tendsto_const_nhds)
    have hh : ∀ n : ℕ, g.J s ≤ stepResolvent (1 / ((n : ℝ) + 1)) s := by
      intro n
      simpa only [IncGraph.J_step] using IncGraph.le_iff_J.mp (hg (mem_range_self n)) s
    simpa only [IncGraph.J_step] using ge_of_tendsto ht (Eventually.of_forall hh)

theorem IncGraph.iSup_step_sequence :
    (⨆ n : ℕ, IncGraph.step (1 / ((n : ℝ) + 1))) = IncGraph.step 0 :=
  (isLUB_ciSup ⟨IncGraph.step 0, IncGraph.step_sequence_isLUB.1⟩).unique
    IncGraph.step_sequence_isLUB

/-- The infinite supremum fills a jump at zero although every individual
fiber at zero is the singleton `{0}`. -/
theorem IncGraph.infinite_fiber_completion_example :
    (∀ n : ℕ, (IncGraph.step (1 / ((n : ℝ) + 1))).val 0 = {0}) ∧
    (⨆ n : ℕ, IncGraph.step (1 / ((n : ℝ) + 1))).val 0 = Icc (0 : ℝ) 1 := by
  constructor
  · intro n
    exact IncGraph.step_zero_fiber_of_pos (by positivity)
  · rw [IncGraph.iSup_step_sequence]
    exact IncGraph.step_fiber_at_jump 0

end

end ScalarMonotone
