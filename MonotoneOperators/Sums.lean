import MonotoneOperators.Minty

/-!
# Ordinary and parallel sums

The scalar sum theorem below is proved using the intermediate value theorem
for the two resolvents. In particular, it does not require a higher-dimensional
sum theorem or an interior-domain qualification.
-/

open Set

namespace ScalarMonotone

theorem add_increasing {f g : Operator} (hf : Increasing f) (hg : Increasing g) :
    Increasing (add f g) := by
  intro x w y z hw hz
  rcases hw with ⟨u, hu, v, hv, rfl⟩
  rcases hz with ⟨p, hp, q, hq, rfl⟩
  have h₁ := hf hu hp
  have h₂ := hg hv hq
  nlinarith

/-- A continuous function taking opposite weak signs at interval endpoints has a zero. -/
private theorem zero_between {F : ℝ → ℝ} (hF : Continuous F)
    {a b : ℝ} (hab : a ≤ b) (ha : F a ≤ 0) (hb : 0 ≤ F b) :
    ∃ s, F s = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (F a) (F b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab hF.continuousOn hzero with ⟨s, _, hs⟩
  exact ⟨s, hs⟩

/-- The doubled diagonal of a sum is onto as soon as the domains meet. -/
theorem add_two_diagonal_surjective {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : (dom f ∩ dom g).Nonempty) (t : ℝ) :
    ∃ x w, w ∈ add f g x ∧ t = 2 * x + w := by
  rcases hfg with ⟨c, hc⟩
  rcases hc.1 with ⟨u, hu⟩
  rcases hc.2 with ⟨v, hv⟩
  let Jf := resolvent f hf
  let Jg := resolvent g hg
  let A := c + u
  let B := t - c - v
  let F := fun s => Jf s - Jg (t - s)
  have hJf : Monotone Jf := resolvent_monotone hf
  have hJg : Monotone Jg := resolvent_monotone hg
  have hJfu : Jf A = c := (resolvent_eq_iff hf).2 hu
  have hJgv : Jg (c + v) = c := (resolvent_eq_iff hg).2 hv
  have hFc : Continuous F :=
    (resolvent_continuous hf).sub
      ((resolvent_continuous hg).comp (continuous_const.sub continuous_id))
  have hz : ∃ s, F s = 0 := by
    rcases le_total A B with hAB | hBA
    · have hA : F A ≤ 0 := by
        have harg : c + v ≤ t - A := by dsimp [A, B] at *; linarith
        have hval := hJg harg
        dsimp [F]
        rw [hJfu]
        rw [hJgv] at hval
        linarith
      have hB : 0 ≤ F B := by
        have hval := hJf hAB
        have htB : t - B = c + v := by dsimp [B]; ring
        dsimp [F]
        rw [htB, hJgv]
        rw [hJfu] at hval
        linarith
      exact zero_between hFc hAB hA hB
    · have hB : F B ≤ 0 := by
        have hval := hJf hBA
        have htB : t - B = c + v := by dsimp [B]; ring
        dsimp [F]
        rw [htB, hJgv]
        rw [hJfu] at hval
        linarith
      have hA : 0 ≤ F A := by
        have harg : t - A ≤ c + v := by dsimp [A, B] at *; linarith
        have hval := hJg harg
        dsimp [F]
        rw [hJfu]
        rw [hJgv] at hval
        linarith
      exact zero_between hFc hBA hB hA
  rcases hz with ⟨s, hs⟩
  have hsame : Jg (t - s) = Jf s := by dsimp [F] at hs; linarith
  have hp : s - Jf s ∈ f (Jf s) := resolvent_mem hf s
  have hq : t - s - Jf s ∈ g (Jf s) := by
    have hq' : t - s - Jg (t - s) ∈ g (Jg (t - s)) := resolvent_mem hg (t - s)
    simpa only [hsame] using hq'
  refine ⟨Jf s, (s - Jf s) + (t - s - Jf s),
    ⟨s - Jf s, hp, t - s - Jf s, hq, rfl⟩, ?_⟩
  ring

/-- In one dimension, nonempty domain intersection suffices for sum maximality. -/
theorem add_maximal {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : (dom f ∩ dom g).Nonempty) : MaximalIncreasing (add f g) := by
  refine ⟨add_increasing hf.1 hg.1, ?_⟩
  intro a w haw
  rcases add_two_diagonal_surjective hf hg hfg (2 * a + w) with
    ⟨x, z, hz, heq⟩
  have hcompat := haw hz
  have hdiff : w - z = 2 * (x - a) := by linarith
  rw [hdiff] at hcompat
  have hsquare : (a - x) ^ 2 = 0 := by nlinarith [sq_nonneg (a - x)]
  have hax : a = x := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  have hwz : w = z := by linarith
  simpa only [hax, hwz] using hz

/-- The range of a nonempty scalar sum is the Minkowski sum of the ranges. -/
theorem ran_add_eq {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : (dom f ∩ dom g).Nonempty) :
    ran (add f g) = setAdd (ran f) (ran g) := by
  apply Set.Subset.antisymm
  · rintro w ⟨x, u, hu, v, hv, rfl⟩
    exact ⟨u, ⟨x, hu⟩, v, ⟨x, hv⟩, rfl⟩
  · rintro w ⟨u, ⟨a, hu⟩, v, ⟨b, hv⟩, hw⟩
    rcases add_two_diagonal_surjective hf hg hfg (2 * min a b + w) with
      ⟨x, s, hs, heq⟩
    have hsw : s ≤ w := by
      by_contra h
      have hws : w < s := lt_of_not_ge h
      have hx : x < min a b := by linarith
      rcases hs with ⟨p, hp, q, hq, hsum⟩
      have hp_le := hf.1.le_of_lt hp hu (lt_of_lt_of_le hx (min_le_left a b))
      have hq_le := hg.1.le_of_lt hq hv (lt_of_lt_of_le hx (min_le_right a b))
      linarith
    rcases add_two_diagonal_surjective hf hg hfg (2 * max a b + w) with
      ⟨y, r, hr, heq'⟩
    have hwr : w ≤ r := by
      by_contra h
      have hrw : r < w := lt_of_not_ge h
      have hy : max a b < y := by linarith
      rcases hr with ⟨p, hp, q, hq, hsum⟩
      have hu_le := hf.1.le_of_lt hu hp (lt_of_le_of_lt (le_max_left a b) hy)
      have hv_le := hg.1.le_of_lt hv hq (lt_of_le_of_lt (le_max_right a b) hy)
      linarith
    exact (ran_ordConnected (add_maximal hf hg hfg)).out
      (show s ∈ ran (add f g) from ⟨x, hs⟩)
      (show r ∈ ran (add f g) from ⟨y, hr⟩) ⟨hsw, hwr⟩

private theorem diagonal_mem {f : Operator} {x u : ℝ} (hu : u ∈ f x) :
    x + u ∈ ran (add f identity) := by
  exact ⟨x, u, hu, x, by simp [identity, ofFun], by ring⟩

theorem mem_ran_add_identity {f : Operator} {t : ℝ} :
    t ∈ ran (add f identity) ↔ ∃ x, t - x ∈ f x := by
  constructor
  · rintro ⟨x, u, hu, v, hv, ht⟩
    have hvx : v = x := by simpa [identity, ofFun] using hv
    subst v
    refine ⟨x, ?_⟩
    have heq : t - x = u := by linarith
    simpa only [heq] using hu
  · rintro ⟨x, hx⟩
    exact ⟨x, t - x, hx, x, by simp [identity, ofFun], by ring⟩

theorem ran_add_identity_eq_univ {f : Operator} (hf : MaximalIncreasing f) :
    ran (add f identity) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact mem_ran_add_identity.2 (minty_surjective hf t)

/-- The manuscript's interval and domain--range criterion for maximality. -/
theorem maximal_iff_domain_range {f : Operator} (hf : Increasing f) :
    MaximalIncreasing f ↔
      (ran (add f identity)).OrdConnected ∧ setAdd (ran f) (dom f) = Set.univ := by
  constructor
  · intro hmax
    constructor
    · rw [ran_add_identity_eq_univ hmax]
      exact Set.ordConnected_univ
    · apply Set.eq_univ_of_forall
      intro t
      rcases minty_surjective hmax t with ⟨x, hx⟩
      exact ⟨t - x, ⟨x, hx⟩, x, ⟨t - x, hx⟩, by ring⟩
  · rintro ⟨hinterval, hfull⟩
    apply (maximal_iff_minty hf).2
    intro t
    have ht : t ∈ setAdd (ran f) (dom f) := by rw [hfull]; trivial
    rcases ht with ⟨v, ⟨y, hy⟩, x, ⟨u, hx⟩, ht⟩
    apply mem_ran_add_identity.1
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have huv := hf.le_of_lt hx hy hxy
      exact hinterval.out (diagonal_mem hx) (diagonal_mem hy)
        ⟨by linarith, by linarith⟩
    · have hty : t = y + v := by linarith
      simpa only [hty] using diagonal_mem hy
    · have hvu := hf.le_of_lt hy hx hyx
      exact hinterval.out (diagonal_mem hy) (diagonal_mem hx)
        ⟨by linarith, by linarith⟩

/-- Parallel sum maximality is the sum theorem applied to inverse relations. -/
theorem parallelAdd_maximal {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : (ran f ∩ ran g).Nonempty) : MaximalIncreasing (parallelAdd f g) := by
  apply inverse_maximal
  exact add_maximal (inverse_maximal hf) (inverse_maximal hg) (by simpa using hfg)

theorem dom_parallelAdd_eq {f g : Operator}
    (hf : MaximalIncreasing f) (hg : MaximalIncreasing g)
    (hfg : (ran f ∩ ran g).Nonempty) :
    dom (parallelAdd f g) = setAdd (dom f) (dom g) := by
  change ran (add (inverse f) (inverse g)) = setAdd (dom f) (dom g)
  simpa using ran_add_eq (inverse_maximal hf) (inverse_maximal hg) (by simpa using hfg)

/-! ## Change of orientation -/

/-- Reflection of a set through the origin. -/
def setNeg (A : Set ℝ) : Set ℝ := {u | -u ∈ A}

@[simp] theorem setNeg_setNeg (A : Set ℝ) : setNeg (setNeg A) = A := by
  ext u
  simp [setNeg]

@[simp] theorem setNeg_univ : setNeg (Set.univ : Set ℝ) = Set.univ := by
  ext u
  simp [setNeg]

@[simp] theorem setNeg_eq_univ_iff {A : Set ℝ} : setNeg A = Set.univ ↔ A = Set.univ := by
  constructor
  · intro h
    have h' := congrArg setNeg h
    simpa using h'
  · rintro rfl
    exact setNeg_univ

theorem setNeg_setAdd (A B : Set ℝ) :
    setNeg (setAdd A B) = setAdd (setNeg A) (setNeg B) := by
  ext w
  change (∃ u ∈ A, ∃ v ∈ B, -w = u + v) ↔
    ∃ u, -u ∈ A ∧ ∃ v, -v ∈ B ∧ w = u + v
  constructor
  · rintro ⟨u, hu, v, hv, hw⟩
    exact ⟨-u, by simpa using hu, -v, by simpa using hv, by linarith⟩
  · rintro ⟨u, hu, v, hv, hw⟩
    exact ⟨-u, hu, -v, hv, by linarith⟩

theorem ordConnected_setNeg {A : Set ℝ} (hA : A.OrdConnected) :
    (setNeg A).OrdConnected := by
  constructor
  intro a ha b hb x hx
  exact hA.out hb ha ⟨by linarith [hx.2], by linarith [hx.1]⟩

@[simp] theorem ordConnected_setNeg_iff {A : Set ℝ} :
    (setNeg A).OrdConnected ↔ A.OrdConnected := by
  constructor
  · intro h
    simpa using ordConnected_setNeg h
  · exact ordConnected_setNeg

@[simp] theorem dom_negOut (f : Operator) : dom (negOut f) = dom f := by
  ext x
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨-u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨-u, by simpa [negOut] using hu⟩

@[simp] theorem ran_negOut (f : Operator) : ran (negOut f) = setNeg (ran f) := rfl

theorem negOut_add (f g : Operator) :
    negOut (add f g) = add (negOut f) (negOut g) := by
  ext x w
  change (∃ u ∈ f x, ∃ v ∈ g x, -w = u + v) ↔
    ∃ u, -u ∈ f x ∧ ∃ v, -v ∈ g x ∧ w = u + v
  constructor
  · rintro ⟨u, hu, v, hv, hw⟩
    exact ⟨-u, by simpa using hu, -v, by simpa using hv, by linarith⟩
  · rintro ⟨u, hu, v, hv, hw⟩
    exact ⟨-u, hu, -v, hv, by linarith⟩

theorem add_decreasing {f g : Operator} (hf : Decreasing f) (hg : Decreasing g) :
    Decreasing (add f g) := by
  change Increasing (negOut (add f g))
  rw [negOut_add]
  exact add_increasing hf hg

theorem add_maximal_decreasing {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : (dom f ∩ dom g).Nonempty) : MaximalDecreasing (add f g) := by
  change MaximalIncreasing (negOut (add f g))
  rw [negOut_add]
  exact add_maximal hf hg (by simpa using hfg)

theorem ran_add_eq_decreasing {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : (dom f ∩ dom g).Nonempty) :
    ran (add f g) = setAdd (ran f) (ran g) := by
  have h := ran_add_eq hf hg (by simpa using hfg)
  rw [← negOut_add, ran_negOut, ran_negOut, ran_negOut, ← setNeg_setAdd] at h
  have h' := congrArg setNeg h
  simpa using h'

theorem inverse_decreasing {f : Operator} (hf : Decreasing f) : Decreasing (inverse f) := by
  apply negOut_increasing_iff.2
  intro x u y v hu hv
  simpa only [mul_comm] using (negOut_increasing_iff.1 hf) hu hv

theorem parallelAdd_maximal_decreasing {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : (ran f ∩ ran g).Nonempty) : MaximalDecreasing (parallelAdd f g) := by
  apply inverse_maximal_decreasing
  exact add_maximal_decreasing (inverse_maximal_decreasing hf)
    (inverse_maximal_decreasing hg) (by simpa using hfg)

theorem dom_parallelAdd_eq_decreasing {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfg : (ran f ∩ ran g).Nonempty) :
    dom (parallelAdd f g) = setAdd (dom f) (dom g) := by
  change ran (add (inverse f) (inverse g)) = setAdd (dom f) (dom g)
  simpa using ran_add_eq_decreasing (inverse_maximal_decreasing hf)
    (inverse_maximal_decreasing hg) (by simpa using hfg)

/-- The decreasing criterion uses the range of `f - id` and `ran f - dom f`. -/
theorem maximalDecreasing_iff_domain_range {f : Operator} (hf : Decreasing f) :
    MaximalDecreasing f ↔
      (ran (add f (negOut identity))).OrdConnected ∧
        setAdd (ran f) (setNeg (dom f)) = Set.univ := by
  change MaximalIncreasing (negOut f) ↔ _
  rw [maximal_iff_domain_range hf]
  have hdiag : add (negOut f) identity = negOut (add f (negOut identity)) := by
    rw [negOut_add, negOut_negOut]
  rw [hdiag, ran_negOut, ordConnected_setNeg_iff, ran_negOut, dom_negOut]
  have hsum : setAdd (setNeg (ran f)) (dom f) =
      setNeg (setAdd (ran f) (setNeg (dom f))) := by
    rw [setNeg_setAdd, setNeg_setNeg]
  rw [hsum, setNeg_eq_univ_iff]

end ScalarMonotone
