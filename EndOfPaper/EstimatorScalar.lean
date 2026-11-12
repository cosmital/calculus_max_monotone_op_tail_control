import EndOfPaper.MedianSharpness
import EndOfPaper.NormExamples

/-!
Deterministic heterogeneous-estimator formulas: the exact ternary
median sharp transform, normalized-sum aggregation and error bound,
median/mean permutation invariance, translations and concrete scaled
errors and scalar bounds. Probability-level assembly is separate.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def meanThree (x : Fin 3 → ℝ) : ℝ := (∑ i, x i) / 3

theorem meanThree_continuous : Continuous meanThree :=
  (coordinateMass_continuous 3).div_const 3

theorem meanThree_aggregation_axioms : AggregationAxioms meanThree := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact div_nonneg (Finset.sum_nonneg (fun i _ => hx i)) (by norm_num)
  · intro x y hx hxy
    change (∑ i, x i)/3 ≤ (∑ i, y i)/3
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun i _ => hxy i))
        (show (0 : ℝ) ≤ (3 : ℝ)⁻¹ by positivity)
  · intro c hc x hx
    simp only [meanThree, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

theorem meanThree_sharp_transform {a : Fin 3 → ℝ} (ha : 0 ≤ a) :
    superadditiveTransform meanThree a = meanThree a := by
  apply superadditiveTransform_eq_self meanThree_aggregation_axioms _ ha
  intro x y hx hy
  simp only [meanThree, Pi.add_apply, Finset.sum_add_distrib]
  linarith

theorem meanThree_error_domination (x : Fin 3 → ℝ) (θ : ℝ) :
    |meanThree x-θ| ≤ meanThree (fun i => |x i-θ|) := by
  have he : meanThree x-θ = (∑ i, (x i-θ))/3 := by
    simp only [meanThree, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [he, abs_div, show |(3 : ℝ)| = 3 from by norm_num]
  simpa only [meanThree, div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs (fun i => x i-θ) Finset.univ)
      (show (0 : ℝ) ≤ (3 : ℝ)⁻¹ by positivity)

theorem majority_reindex {r : ℕ} (σ : Equiv.Perm (Fin (2*r+1))) {P : Fin (2*r+1) → Prop}
    (h : ∃ I : Majority r, ∀ i ∈ I.val, P i) :
    ∃ J : Majority r, ∀ j ∈ J.val, P (σ j) := by
  classical
  obtain ⟨I, hI⟩ := h
  refine ⟨⟨I.val.map σ.symm.toEmbedding, by simpa using I.property⟩, ?_⟩
  intro j hj
  obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hj
  subst j
  simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using hI i hi

theorem scalarMedian_perm (r : ℕ) (x : Fin (2*r+1) → ℝ)
    (σ : Equiv.Perm (Fin (2*r+1))) : scalarMedian r (x ∘ σ) = scalarMedian r x := by
  apply le_antisymm
  · exact median_le_of_majority r _ (majority_reindex σ (median_upper_majority r x))
  · exact le_median_of_majority r _ (majority_reindex σ (median_lower_majority r x))

theorem scalarMedian_add_const (r : ℕ) (x : Fin (2*r+1) → ℝ) (c : ℝ) :
    scalarMedian r (fun i => x i+c) = scalarMedian r x+c := by
  apply le_antisymm
  · obtain ⟨I, hI⟩ := median_upper_majority r x
    exact median_le_of_majority r _ ⟨I, fun i hi => add_le_add_right (hI i hi) c⟩
  · obtain ⟨I, hI⟩ := median_lower_majority r x
    exact le_median_of_majority r _ ⟨I, fun i hi => add_le_add_right (hI i hi) c⟩

theorem meanThree_perm (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    meanThree (x ∘ σ) = meanThree x := by
  unfold meanThree
  congr 1
  exact Equiv.sum_comp σ x

theorem median_three_sharp_formula (a : Fin 3 → ℝ) (ha : 0 ≤ a) :
    superadditiveTransform (scalarMedian 1) a =
      min (a (Tuple.sort a 0)+a (Tuple.sort a 1)) ((∑ i, a i)/2) := by
  classical
  rw [median_transform_formula 1 a ha]
  let f : Fin 2 → ℝ := fun ℓ =>
    (∑ i ∈ Finset.univ.filter (fun i : Fin 3 => i.val < 1+(ℓ.val+1)),
      a (Tuple.sort a i)) / ((ℓ.val+1 : ℕ) : ℝ)
  have htwo : (⨅ i, f i) = min (f 0) (f 1) := by
    apply le_antisymm
    · exact le_min (ciInf_le (finite_range f).bddBelow 0) (ciInf_le (finite_range f).bddBelow 1)
    · apply le_ciInf
      intro i
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
  change (⨅ i, f i) = _
  rw [htwo]
  have hsum : (∑ i, a (Tuple.sort a i)) = ∑ i, a i := Equiv.sum_comp (Tuple.sort a) a
  have h0 : f 0 = a (Tuple.sort a 0)+a (Tuple.sort a 1) := by
    simp [f, Finset.sum_filter, Fin.sum_univ_succ]
  have h1 : f 1 = (∑ i, a i)/2 := by
    have hfilter : Finset.univ.filter (fun i : Fin 3 => i.val < 3) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro i.isLt
    change (∑ i ∈ Finset.univ.filter (fun i : Fin 3 => i.val < 3), a (Tuple.sort a i))/2 = _
    rw [hfilter, hsum]
  rw [h0, h1]

theorem median_three_scaled_exact {z b θ : ℝ} (hz : 0 ≤ z) (hb : 2 ≤ b) :
    scalarMedian 1 ![θ+z, θ+2*z, θ+b*z] = θ+2*z := by
  have hbz : 2*z ≤ b*z := mul_le_mul_of_nonneg_right hb hz
  apply le_antisymm
  · apply median_le_of_majority 1 _
    refine ⟨⟨{0,1}, by norm_num⟩, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp <;> linarith
  · apply le_median_of_majority 1 _
    refine ⟨⟨{1,2}, by decide⟩, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp <;> linarith

theorem meanThree_scaled_exact (z b θ : ℝ) :
    meanThree ![θ+z, θ+2*z, θ+b*z] = θ+(b+3)/3*z := by
  simp [meanThree, Fin.sum_univ_succ]
  ring

theorem median_three_scale_bound {h b : ℝ} (hh : 0 ≤ h) (hb : 3 ≤ b) :
    superadditiveTransform (scalarMedian 1) ![h, 2*h, b*h] = 3*h := by
  classical
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 3).trans hb
  have ha : 0 ≤ (![h, 2*h, b*h] : Fin 3 → ℝ) := by
    intro i
    fin_cases i <;> simp <;> positivity
  apply le_antisymm
  · have hu := median_transform_subset_upper 1 1 (by norm_num) ({0,1} : Finset (Fin 3))
      (by norm_num) ha
    convert hu using 1 <;> norm_num <;> ring
  · apply median_transform_lower_of_capacity 1 ha (by positivity)
    have h1 : min h (3*h) = h := min_eq_left (by linarith)
    have h2 : min (2*h) (3*h) = 2*h := min_eq_left (by linarith)
    have h3 : min (b*h) (3*h) = 3*h := min_eq_right (mul_le_mul_of_nonneg_right hb hh)
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, h1, h2, h3]
    norm_num <;> linarith

end ScalarMonotone.EndOfPaper
end
