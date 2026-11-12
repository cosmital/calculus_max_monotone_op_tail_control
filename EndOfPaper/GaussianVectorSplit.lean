import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Actual finite Euclidean coordinate insertion and extraction, with exact square-distance decomposition and the two required isometries.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def gaussianCons {n : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) :=
  (WithLp.equiv 2 _).symm (Fin.cons s (fun i => u i))

def gaussianTail {n : ℕ} (z : EuclideanSpace ℝ (Fin (n+1))) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 _).symm (fun i => z i.succ)

@[simp] theorem gaussianCons_zero {n : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    gaussianCons s u 0 = s := rfl

@[simp] theorem gaussianCons_succ {n : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gaussianCons s u i.succ = u i := rfl

@[simp] theorem gaussianTail_apply {n : ℕ} (z : EuclideanSpace ℝ (Fin (n+1))) (i : Fin n) :
    gaussianTail z i = z i.succ := rfl

theorem gaussianCons_sub_norm_sq {n : ℕ} (s t : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    ‖gaussianCons s u-gaussianCons t v‖^2 = (s-t)^2+‖u-v‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ,PiLp.sub_apply,Real.norm_eq_abs,sq_abs,
    gaussianCons_zero,gaussianCons_succ]

theorem gaussianCons_dist_sq {n : ℕ} (s t : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    (dist (gaussianCons s u) (gaussianCons t v))^2 = (s-t)^2+(dist u v)^2 := by
  simpa only [dist_eq_norm] using gaussianCons_sub_norm_sq s t u v

theorem gaussianCons_isometry {n : ℕ} (s : ℝ) :
    Isometry (gaussianCons s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1))) := by
  apply Isometry.of_dist_eq
  intro u v
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  simpa only [sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add] using gaussianCons_dist_sq s s u v

theorem gaussianCons_coordinate_isometry {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    Isometry (fun s : ℝ => gaussianCons s u) := by
  apply Isometry.of_dist_eq
  intro s t
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  simpa only [dist_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero,Real.dist_eq,sq_abs] using
    gaussianCons_dist_sq s t u u

theorem gaussianCons_head_tail {n : ℕ} (z : EuclideanSpace ℝ (Fin (n+1))) :
    gaussianCons (z 0) (gaussianTail z) = z := by
  ext i
  exact Fin.cases (by rfl) (fun j => by rfl) i

end ScalarMonotone.EndOfPaper
end
