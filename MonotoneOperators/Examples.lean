import MonotoneOperators.CompositionMaximal

/-!
# The two obstructions in the manuscript

The first example is the normal cone of the nonnegative halfline.  The
second uses ReLU and the graph `u = -1 / x`, `x < 0`; both factors are
maximal and nonnegative, but their product is not maximal.
-/

open Set

namespace ScalarMonotone

def normalHalfline : Operator := fun x => {u | 0 ≤ x ∧ u ≤ 0 ∧ x * u = 0}

theorem normalHalfline_increasing : Increasing normalHalfline := by
  rintro x u y v ⟨hx, hu, hxu⟩ ⟨hy, hv, hyv⟩
  have h₁ := mul_nonpos_of_nonneg_of_nonpos hx hv
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hy hu
  nlinarith

theorem normalHalfline_maximal : MaximalIncreasing normalHalfline := by
  refine ⟨normalHalfline_increasing, ?_⟩
  intro x u hc
  have hbounds := compatible_iff_bounds.mp hc
  have hy : 0 ≤ max x 0 + 1 := by have := le_max_right x 0; linarith
  have hxy : x < max x 0 + 1 := by have := le_max_left x 0; linarith
  have hu : u ≤ 0 := hbounds.2
    (show 0 ∈ normalHalfline (max x 0 + 1) from ⟨hy, le_rfl, by ring⟩) hxy
  have hx : 0 ≤ x := by
    by_contra h
    have hlt : x < 0 := lt_of_not_ge h
    have hbad := hbounds.2
      (show u - 1 ∈ normalHalfline 0 from ⟨le_rfl, by linarith, by ring⟩) hlt
    linarith
  have hxu := hc (show 0 ∈ normalHalfline 0 from ⟨le_rfl, le_rfl, by ring⟩)
  exact ⟨hx, hu, by nlinarith [mul_nonpos_of_nonneg_of_nonpos hx hu]⟩

theorem normalHalfline_self_comp :
    comp normalHalfline normalHalfline = fun x => {u | 0 ≤ x ∧ u ≤ 0} := by
  funext x
  ext u
  constructor
  · rintro ⟨z, ⟨hx, _, _⟩, ⟨_, hu, _⟩⟩
    exact ⟨hx, hu⟩
  · rintro ⟨hx, hu⟩
    exact ⟨0, ⟨hx, le_rfl, by ring⟩, ⟨le_rfl, hu, by ring⟩⟩

theorem normalHalfline_self_comp_not_increasing :
    ¬ Increasing (comp normalHalfline normalHalfline) := by
  rw [normalHalfline_self_comp]
  intro h
  have hh := h (show (0 : ℝ) ∈ {u | 0 ≤ (0 : ℝ) ∧ u ≤ 0} from ⟨le_rfl, le_rfl⟩)
    (show (-1 : ℝ) ∈ {u | 0 ≤ (1 : ℝ) ∧ u ≤ 0} by norm_num)
  norm_num at hh

theorem normalHalfline_self_comp_not_decreasing :
    ¬ Decreasing (comp normalHalfline normalHalfline) := by
  rw [normalHalfline_self_comp]
  intro h
  have hh := (negOut_increasing_iff.mp h)
    (show (-1 : ℝ) ∈ {u | 0 ≤ (0 : ℝ) ∧ u ≤ 0} by norm_num)
    (show (0 : ℝ) ∈ {u | 0 ≤ (1 : ℝ) ∧ u ≤ 0} by norm_num)
  norm_num at hh

def relu : Operator := ofFun fun x => max x 0

theorem relu_nonnegative : Nonnegative relu := by
  intro x u hu
  have heq : u = max x 0 := hu
  rw [heq]
  exact le_max_right x 0

theorem relu_increasing : Increasing relu := by
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  have hu' : u = max x 0 := hu
  have hv' : v = max y 0 := hv
  rw [hu', hv']
  exact max_le_max hxy.le le_rfl

theorem relu_maximal : MaximalIncreasing relu := by
  apply maximal_of_minty relu_increasing
  intro s
  by_cases hs : 0 ≤ s
  · refine ⟨s / 2, ?_⟩
    change s - s / 2 = max (s / 2) 0
    rw [max_eq_left (by linarith : 0 ≤ s / 2)]
    ring
  · refine ⟨s, ?_⟩
    change s - s = max s 0
    rw [max_eq_right (le_of_not_ge hs)]
    ring

def reciprocalBarrier : Operator := fun x => {u | x * u = -1 ∧ 0 < u}

theorem reciprocalBarrier_nonnegative : Nonnegative reciprocalBarrier :=
  fun {_ _} hu => hu.2.le

theorem reciprocalBarrier_input_neg {x u : ℝ} (hu : u ∈ reciprocalBarrier x) : x < 0 := by
  by_contra h
  have hh := mul_nonneg (le_of_not_gt h) hu.2.le
  linarith [hu.1]

theorem reciprocalBarrier_increasing : Increasing reciprocalBarrier := by
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  by_contra h
  have hvu : v < u := lt_of_not_ge h
  have hh : x * u < y * v :=
    (mul_lt_mul_of_pos_right hxy hu.2).trans
      (mul_lt_mul_of_neg_left hvu (reciprocalBarrier_input_neg hv))
  linarith [hu.1, hv.1]

theorem reciprocalBarrier_maximal : MaximalIncreasing reciprocalBarrier := by
  apply maximal_of_minty reciprocalBarrier_increasing
  intro s
  have hD : 0 ≤ s ^ 2 + 4 := by nlinarith [sq_nonneg s]
  have hsqrt : Real.sqrt (s ^ 2 + 4) ^ 2 = s ^ 2 + 4 := Real.sq_sqrt hD
  have hbounds : -Real.sqrt (s ^ 2 + 4) < s ∧ s < Real.sqrt (s ^ 2 + 4) :=
    Real.sq_lt.mp (by linarith : s ^ 2 < s ^ 2 + 4)
  refine ⟨(s - Real.sqrt (s ^ 2 + 4)) / 2, ?_⟩
  change ((s - Real.sqrt (s ^ 2 + 4)) / 2) *
    (s - (s - Real.sqrt (s ^ 2 + 4)) / 2) = -1 ∧
    0 < s - (s - Real.sqrt (s ^ 2 + 4)) / 2
  constructor
  · nlinarith
  · linarith [hbounds.1]

theorem reciprocalBarrier_eq (x : ℝ) :
    reciprocalBarrier x = {u | x < 0 ∧ u = -1 / x} := by
  ext u
  constructor
  · intro hu
    have hx := reciprocalBarrier_input_neg hu
    refine ⟨hx, ?_⟩
    apply (eq_div_iff hx.ne).mpr
    nlinarith [hu.1]
  · rintro ⟨hx, rfl⟩
    exact ⟨mul_div_cancel₀ (-1) hx.ne,
      div_pos_of_neg_of_neg (by norm_num) hx⟩

theorem relu_mul_reciprocalBarrier :
    mul relu reciprocalBarrier = fun x => {u | x < 0 ∧ u = 0} := by
  funext x
  ext u
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hx := reciprocalBarrier_input_neg hb
    have ha' : a = max x 0 := ha
    rw [max_eq_right hx.le] at ha'
    exact ⟨hx, by simp [ha']⟩
  · rintro ⟨hx, rfl⟩
    refine ⟨0, ?_, -1 / x, ?_, by ring⟩
    · change 0 = max x 0
      simp [max_eq_right hx.le]
    · rw [reciprocalBarrier_eq]
      exact ⟨hx, rfl⟩

theorem relu_mul_reciprocalBarrier_not_maximal :
    ¬ MaximalIncreasing (mul relu reciprocalBarrier) := by
  rw [relu_mul_reciprocalBarrier]
  intro h
  have hh : (0 : ℝ) ∈ {u | (0 : ℝ) < 0 ∧ u = 0} := h.2 (by
    rintro y v ⟨_, rfl⟩
    simp)
  exact (lt_irrefl (0 : ℝ)) hh.1

theorem relu_mul_reciprocalBarrier_range_identity_fails :
    ran (mul relu reciprocalBarrier) ≠ setMul (ran relu) (ran reciprocalBarrier) := by
  intro h
  have hright : (1 : ℝ) ∈ setMul (ran relu) (ran reciprocalBarrier) := by
    refine ⟨1, ⟨1, ?_⟩, 1, ⟨-1, ?_⟩, by ring⟩
    · change (1 : ℝ) = max 1 0
      norm_num
    · change (-1 : ℝ) * 1 = -1 ∧ 0 < (1 : ℝ)
      norm_num
  have hleft : (1 : ℝ) ∈ ran (mul relu reciprocalBarrier) := h.symm ▸ hright
  rw [relu_mul_reciprocalBarrier] at hleft
  rcases hleft with ⟨x, _, hbad⟩
  norm_num at hbad

end ScalarMonotone
