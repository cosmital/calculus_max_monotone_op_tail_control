import MonotoneOperators.Basic

/-!
# Ordinary and parallel operations

This file proves the algebraic identities in the manuscript directly from
membership witnesses.  No maximality or nonempty-domain hypotheses are needed
unless they occur in the statement.
-/

open Set

namespace ScalarMonotone

theorem inverse_comp (f g : Operator) :
    inverse (comp g f) = comp (inverse f) (inverse g) := by
  funext v
  ext x
  constructor
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, hv, hu⟩
  · rintro ⟨u, hv, hu⟩
    exact ⟨u, hu, hv⟩

theorem comp_assoc (f g h : Operator) :
    comp h (comp g f) = comp (comp h g) f := by
  funext x
  ext w
  constructor
  · rintro ⟨v, ⟨u, hu, hv⟩, hw⟩
    exact ⟨u, hu, v, hv, hw⟩
  · rintro ⟨u, hu, v, hv, hw⟩
    exact ⟨v, ⟨u, hu, hv⟩, hw⟩

theorem comp_ofFun (f : Operator) (φ : ℝ → ℝ) :
    comp f (ofFun φ) = fun x => f (φ x) := by
  funext x
  ext u
  simp [comp, ofFun]

theorem dom_add (f g : Operator) : dom (add f g) = dom f ∩ dom g := by
  ext x
  constructor
  · rintro ⟨w, u, hu, v, hv, _⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨u + v, u, hu, v, hv, rfl⟩

theorem dom_mul (f g : Operator) : dom (mul f g) = dom f ∩ dom g := by
  ext x
  constructor
  · rintro ⟨w, u, hu, v, hv, _⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨u * v, u, hu, v, hv, rfl⟩

theorem op_add_comm (f g : Operator) : add f g = add g f := by
  funext x
  ext w
  constructor <;> rintro ⟨u, hu, v, hv, h⟩
  · exact ⟨v, hv, u, hu, h.trans (_root_.add_comm u v)⟩
  · exact ⟨v, hv, u, hu, h.trans (_root_.add_comm u v)⟩

theorem op_add_assoc (f g h : Operator) :
    add (add f g) h = add f (add g h) := by
  funext x
  ext w
  constructor
  · rintro ⟨s, ⟨u, hu, v, hv, rfl⟩, t, ht, rfl⟩
    exact ⟨u, hu, v + t, ⟨v, hv, t, ht, rfl⟩, _root_.add_assoc u v t⟩
  · rintro ⟨u, hu, s, ⟨v, hv, t, ht, rfl⟩, rfl⟩
    exact ⟨u + v, ⟨u, hu, v, hv, rfl⟩, t, ht, (_root_.add_assoc u v t).symm⟩

theorem op_mul_comm (f g : Operator) : mul f g = mul g f := by
  funext x
  ext w
  constructor <;> rintro ⟨u, hu, v, hv, h⟩
  · exact ⟨v, hv, u, hu, h.trans (_root_.mul_comm u v)⟩
  · exact ⟨v, hv, u, hu, h.trans (_root_.mul_comm u v)⟩

theorem op_mul_assoc (f g h : Operator) :
    mul (mul f g) h = mul f (mul g h) := by
  funext x
  ext w
  constructor
  · rintro ⟨s, ⟨u, hu, v, hv, rfl⟩, t, ht, rfl⟩
    exact ⟨u, hu, v * t, ⟨v, hv, t, ht, rfl⟩, _root_.mul_assoc u v t⟩
  · rintro ⟨u, hu, s, ⟨v, hv, t, ht, rfl⟩, rfl⟩
    exact ⟨u * v, ⟨u, hu, v, hv, rfl⟩, t, ht, (_root_.mul_assoc u v t).symm⟩

theorem parallelAdd_comm (f g : Operator) : parallelAdd f g = parallelAdd g f := by
  unfold parallelAdd
  rw [op_add_comm]

theorem parallelAdd_assoc (f g h : Operator) :
    parallelAdd (parallelAdd f g) h = parallelAdd f (parallelAdd g h) := by
  simp only [parallelAdd, inverse_inverse, op_add_assoc]

theorem parallelMul_comm (f g : Operator) : parallelMul f g = parallelMul g f := by
  unfold parallelMul
  rw [op_mul_comm]

theorem parallelMul_assoc (f g h : Operator) :
    parallelMul (parallelMul f g) h = parallelMul f (parallelMul g h) := by
  simp only [parallelMul, inverse_inverse, op_mul_assoc]

theorem ran_parallelAdd (f g : Operator) : ran (parallelAdd f g) = ran f ∩ ran g := by
  simp only [parallelAdd, ran_inverse, dom_add, dom_inverse]

theorem ran_parallelMul (f g : Operator) : ran (parallelMul f g) = ran f ∩ ran g := by
  simp only [parallelMul, ran_inverse, dom_mul, dom_inverse]

theorem Increasing.add {f g : Operator} (hf : Increasing f) (hg : Increasing g) :
    Increasing (add f g) := by
  apply increasing_iff_order.mpr
  rintro x w y z ⟨u, hu, v, hv, rfl⟩ ⟨s, hs, t, ht, rfl⟩ hxy
  exact add_le_add (hf.le_of_lt hu hs hxy) (hg.le_of_lt hv ht hxy)

theorem Increasing.mul {f g : Operator} (hf : Increasing f) (hg : Increasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) : Increasing (mul f g) := by
  apply increasing_iff_order.mpr
  rintro x w y z ⟨u, hu, v, hv, rfl⟩ ⟨s, hs, t, ht, rfl⟩ hxy
  exact mul_le_mul (hf.le_of_lt hu hs hxy) (hg.le_of_lt hv ht hxy) (hg₀ hv) (hf₀ hs)

theorem Nonnegative.mul {f g : Operator} (hf : Nonnegative f) (hg : Nonnegative g) :
    Nonnegative (mul f g) := by
  rintro x w ⟨u, hu, v, hv, rfl⟩
  exact mul_nonneg (hf hu) (hg hv)

theorem Decreasing.mul {f g : Operator} (hf : Decreasing f) (hg : Decreasing g)
    (hf₀ : Nonnegative f) (hg₀ : Nonnegative g) : Decreasing (mul f g) := by
  apply reflect_increasing_iff.mp
  exact (reflect_increasing_iff.mpr hf).mul (reflect_increasing_iff.mpr hg)
    (fun {_ _} hu => hf₀ hu) (fun {_ _} hu => hg₀ hu)

/-- The synchronized intermediate output gives the inclusion in Proposition
`distribution`; the opposite inclusion generally fails. -/
theorem comp_parallelAdd_le (f g h : Operator) :
    comp f (parallelAdd g h) ≤ parallelAdd (comp f g) (comp f h) := by
  rintro x u ⟨t, ⟨a, ha, b, hb, hxab⟩, htu⟩
  exact ⟨a, ⟨t, ha, htu⟩, b, ⟨t, hb, htu⟩, hxab⟩

theorem comp_parallelMul_le (f g h : Operator) :
    comp f (parallelMul g h) ≤ parallelMul (comp f g) (comp f h) := by
  rintro x u ⟨t, ⟨a, ha, b, hb, hxab⟩, htu⟩
  exact ⟨a, ⟨t, ha, htu⟩, b, ⟨t, hb, htu⟩, hxab⟩

theorem comp_parallelAdd_eq_of_singleValued (f g h : Operator)
    (hf : SingleValued (inverse f)) :
    comp f (parallelAdd g h) = parallelAdd (comp f g) (comp f h) := by
  apply le_antisymm (comp_parallelAdd_le f g h)
  rintro x u ⟨a, ⟨t, ht, htu⟩, b, ⟨s, hs, hsu⟩, hxab⟩
  have hts : t = s := hf u htu hsu
  subst s
  exact ⟨t, ⟨a, ht, b, hs, hxab⟩, htu⟩

theorem comp_parallelMul_eq_of_singleValued (f g h : Operator)
    (hf : SingleValued (inverse f)) :
    comp f (parallelMul g h) = parallelMul (comp f g) (comp f h) := by
  apply le_antisymm (comp_parallelMul_le f g h)
  rintro x u ⟨a, ⟨t, ht, htu⟩, b, ⟨s, hs, hsu⟩, hxab⟩
  have hts : t = s := hf u htu hsu
  subst s
  exact ⟨t, ⟨a, ht, b, hs, hxab⟩, htu⟩

theorem comp_parallelAdd_eq_of_maximal (f g h : Operator)
    (hl : MaximalIncreasing (comp f (parallelAdd g h)))
    (hr : Increasing (parallelAdd (comp f g) (comp f h))) :
    comp f (parallelAdd g h) = parallelAdd (comp f g) (comp f h) :=
  hl.eq_of_le hr (comp_parallelAdd_le f g h)

theorem comp_parallelMul_eq_of_maximal (f g h : Operator)
    (hl : MaximalIncreasing (comp f (parallelMul g h)))
    (hr : Increasing (parallelMul (comp f g) (comp f h))) :
    comp f (parallelMul g h) = parallelMul (comp f g) (comp f h) :=
  hl.eq_of_le hr (comp_parallelMul_le f g h)

theorem comp_parallelAdd_eq_of_maximalDecreasing (f g h : Operator)
    (hl : MaximalDecreasing (comp f (parallelAdd g h)))
    (hr : Decreasing (parallelAdd (comp f g) (comp f h))) :
    comp f (parallelAdd g h) = parallelAdd (comp f g) (comp f h) := by
  have heq := hl.eq_of_le hr
    (show negOut (comp f (parallelAdd g h)) ≤
      negOut (parallelAdd (comp f g) (comp f h)) from
      fun x u hu => comp_parallelAdd_le f g h x hu)
  simpa only [negOut_negOut] using congrArg negOut heq

theorem comp_parallelMul_eq_of_maximalDecreasing (f g h : Operator)
    (hl : MaximalDecreasing (comp f (parallelMul g h)))
    (hr : Decreasing (parallelMul (comp f g) (comp f h))) :
    comp f (parallelMul g h) = parallelMul (comp f g) (comp f h) := by
  have heq := hl.eq_of_le hr
    (show negOut (comp f (parallelMul g h)) ≤
      negOut (parallelMul (comp f g) (comp f h)) from
      fun x u hu => comp_parallelMul_le f g h x hu)
  simpa only [negOut_negOut] using congrArg negOut heq

/-- For a real interval, multiplication distributes over addition of
nonnegative sets.  Convexity supplies the weighted intermediate value. -/
theorem setMul_setAdd_of_interval {I J K : Set ℝ} (hI : I.OrdConnected)
    (hJ : J ⊆ Ici 0) (hK : K ⊆ Ici 0) :
    setMul I (setAdd J K) = setAdd (setMul I J) (setMul I K) := by
  ext w
  constructor
  · rintro ⟨i, hi, s, ⟨j, hj, k, hk, rfl⟩, rfl⟩
    exact ⟨i * j, ⟨i, hi, j, hj, rfl⟩,
      i * k, ⟨i, hi, k, hk, rfl⟩, mul_add i j k⟩
  · rintro ⟨p, ⟨i₁, hi₁, j, hj, rfl⟩,
      q, ⟨i₂, hi₂, k, hk, rfl⟩, rfl⟩
    have hj₀ : 0 ≤ j := hJ hj
    have hk₀ : 0 ≤ k := hK hk
    by_cases hzero : j + k = 0
    · have hjzero : j = 0 := by linarith
      have hkzero : k = 0 := by linarith
      refine ⟨i₁, hi₁, j + k, ⟨j, hj, k, hk, rfl⟩, ?_⟩
      simp [hjzero, hkzero]
    · have hpos : 0 < j + k := lt_of_le_of_ne (add_nonneg hj₀ hk₀) (Ne.symm hzero)
      have hcv : Convex ℝ I := hI.convex
      have hcoeff : j / (j + k) + k / (j + k) = 1 := by
        rw [← add_div, div_self hzero]
      have hw : (j / (j + k)) * i₁ + (k / (j + k)) * i₂ ∈ I := by
        simpa only [smul_eq_mul] using
          hcv hi₁ hi₂ (div_nonneg hj₀ hpos.le) (div_nonneg hk₀ hpos.le) hcoeff
      refine ⟨_, hw, j + k, ⟨j, hj, k, hk, rfl⟩, ?_⟩
      field_simp [hzero]
      ring

theorem parallelMul_parallelAdd (f g h : Operator)
    (hf : ∀ u, (inverse f u).OrdConnected)
    (hg : dom g ⊆ Ici 0) (hh : dom h ⊆ Ici 0) :
    parallelMul f (parallelAdd g h) =
      parallelAdd (parallelMul f g) (parallelMul f h) := by
  funext x
  ext u
  change x ∈ setMul (inverse f u) (setAdd (inverse g u) (inverse h u)) ↔
    x ∈ setAdd (setMul (inverse f u) (inverse g u))
      (setMul (inverse f u) (inverse h u))
  rw [setMul_setAdd_of_interval (I := inverse f u) (J := inverse g u) (K := inverse h u) (hf u)
    (fun y hy => hg ⟨u, hy⟩) (fun y hy => hh ⟨u, hy⟩)]

theorem parallelAdd_translate (f g : Operator) (a b : ℝ) :
    parallelAdd (comp f (ofFun fun x => x + a)) (comp g (ofFun fun x => x + b)) =
      comp (parallelAdd f g) (ofFun fun x => x + a + b) := by
  simp only [comp_ofFun]
  funext x
  ext u
  change (∃ r, u ∈ f (r + a) ∧ ∃ s, u ∈ g (s + b) ∧ x = r + s) ↔
    (∃ p, u ∈ f p ∧ ∃ q, u ∈ g q ∧ x + a + b = p + q)
  constructor
  · rintro ⟨r, hr, s, hs, hx⟩
    exact ⟨r + a, hr, s + b, hs, by linarith⟩
  · rintro ⟨p, hp, q, hq, hx⟩
    exact ⟨p - a, by simpa using hp, q - b, by simpa using hq, by linarith⟩

theorem parallelMul_scale (f g : Operator) {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    parallelMul (comp f (ofFun fun x => c * x)) (comp g (ofFun fun x => d * x)) =
      comp (parallelMul f g) (ofFun fun x => (c * d) * x) := by
  simp only [comp_ofFun]
  funext x
  ext u
  change (∃ r, u ∈ f (c * r) ∧ ∃ s, u ∈ g (d * s) ∧ x = r * s) ↔
    (∃ p, u ∈ f p ∧ ∃ q, u ∈ g q ∧ (c * d) * x = p * q)
  constructor
  · rintro ⟨r, hr, s, hs, rfl⟩
    exact ⟨c * r, hr, d * s, hs, by ring⟩
  · rintro ⟨p, hp, q, hq, hx⟩
    refine ⟨p / c, ?_, q / d, ?_, ?_⟩
    · simpa [mul_div_cancel₀ _ hc] using hp
    · simpa [mul_div_cancel₀ _ hd] using hq
    · apply mul_left_cancel₀ (mul_ne_zero hc hd)
      calc
        (c * d) * x = p * q := hx
        _ = (c * d) * (p / c * (q / d)) := by field_simp

end ScalarMonotone
