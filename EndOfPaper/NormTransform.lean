import EndOfPaper.Superadditive
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
The actual ell-p norm sharp transform (ex:normtransform), for every
1 <= p <= infinity. Monotonicity, homogeneity and axis values are proved
for Mathlib PiLp norms; the sharp transform equals the coordinate sum.
-/

open Set
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem aggregation_finset_subadditive_bound {n : ℕ} {ι : Type*} [DecidableEq ι]
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hsub : ∀ x y, 0 ≤ x → 0 ≤ y → F (x+y) ≤ F x+F y)
    (s : Finset ι) (v : ι → CoordinateVector n) (hv : ∀ i ∈ s, 0 ≤ v i) :
    F (∑ i ∈ s, v i) ≤ ∑ i ∈ s, F (v i) := by
  revert hv
  induction s using Finset.induction_on with
  | empty => intro hv; simp [aggregation_zero hF]
  | @insert i s hi ih =>
    intro hv
    have hvi : 0 ≤ v i := hv i (Finset.mem_insert_self i s)
    have hvs : ∀ j ∈ s, 0 ≤ v j := fun j hj => hv j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (hsub _ _ hvi (Finset.sum_nonneg hvs)).trans (add_le_add_left (ih hvs) _)

def coordinateLpNorm (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x : CoordinateVector n) : ℝ := ‖(WithLp.equiv p (Fin n → ℝ)).symm x‖

theorem coordinateLpNorm_mono (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {x y : CoordinateVector n} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coordinateLpNorm n p x ≤ coordinateLpNorm n p y := by
  have hnorm : ∀ i, ‖x i‖ ≤ ‖y i‖ := by
    intro i
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hx i),
      abs_of_nonneg ((hx i).trans (hxy i))] using hxy i
  by_cases hp : p = ∞
  · subst p
    by_cases hn : n = 0
    · subst n
      have he : x = y := funext (fun i => Fin.elim0 i)
      rw [he]
    letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simp only [coordinateLpNorm, PiLp.norm_eq_ciSup, WithLp.equiv_symm_pi_apply]
    apply ciSup_le
    intro i
    exact (hnorm i).trans (le_ciSup (finite_range (fun j => ‖y j‖)).bddAbove i)
  · have hp0 : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    simp only [coordinateLpNorm, PiLp.norm_eq_sum hp0, WithLp.equiv_symm_pi_apply]
    apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
      (Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (norm_nonneg _) (hnorm i) hp0.le))
      (one_div_nonneg.mpr hp0.le)

theorem coordinateLpNorm_aggregation_axioms (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    AggregationAxioms (coordinateLpNorm n p) where
  nonneg := fun _ _ => norm_nonneg _
  mono := fun hx hxy => coordinateLpNorm_mono n p hx hxy
  homogeneous := fun c hc x _ => by
    simp only [coordinateLpNorm, WithLp.equiv_symm_smul, norm_smul, Real.norm_of_nonneg hc]

theorem coordinateLpNorm_axis (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    coordinateLpNorm n p (coordinateAxis i t) = t := by
  have he : coordinateAxis i t = Pi.single i t := by
    ext j
    simp [coordinateAxis, Pi.single_apply, eq_comm]
  rw [coordinateLpNorm, he, PiLp.norm_equiv_symm_single]
  exact Real.norm_of_nonneg ht

theorem coordinateLpNorm_le_mass (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {x : CoordinateVector n} (hx : 0 ≤ x) :
    coordinateLpNorm n p x ≤ coordinateMass x := by
  classical
  have hsub (a b : CoordinateVector n) (_ : 0 ≤ a) (_ : 0 ≤ b) :
      coordinateLpNorm n p (a+b) ≤ coordinateLpNorm n p a+coordinateLpNorm n p b := by
    simpa only [coordinateLpNorm, WithLp.equiv_symm_add] using
      norm_add_le ((WithLp.equiv p (Fin n → ℝ)).symm a)
        ((WithLp.equiv p (Fin n → ℝ)).symm b)
  have h := aggregation_finset_subadditive_bound (coordinateLpNorm_aggregation_axioms n p)
    hsub Finset.univ (fun i => coordinateAxis i (x i))
    (fun i _ => coordinateAxis_nonneg i (hx i))
  rw [sum_coordinateAxis] at h
  have he : ∀ i, coordinateLpNorm n p (coordinateAxis i (x i)) = x i :=
    fun i => coordinateLpNorm_axis n p i (x i) (hx i)
  simpa only [he] using h

/-- Example ex:normtransform for all 1≤p≤infinity, with the actual norm
structure rather than a functional postulated to have the desired axes. -/
theorem ellp_superadditive_transform (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform (coordinateLpNorm n p) a = ∑ i, a i := by
  exact superadditiveTransform_eq_mass_of_axes (coordinateLpNorm_aggregation_axioms n p)
    (fun x hx => coordinateLpNorm_le_mass n p hx)
    (fun i t ht => coordinateLpNorm_axis n p i t ht) ha

end ScalarMonotone.EndOfPaper
end
