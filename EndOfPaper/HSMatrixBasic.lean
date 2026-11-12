import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix

/-!
Actual matrices as finite Euclidean spaces with the Hilbert--Schmidt norm and exact entrywise squared-norm identity.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

abbrev HSMatrix (m n : Type*) := EuclideanSpace ℝ (m × n)

def hsMatrixToMatrix {m n : Type*} (A : HSMatrix m n) : Matrix m n ℝ :=
  fun i j => A (i,j)

def hsMatrixOfMatrix {m n : Type*} (A : Matrix m n ℝ) : HSMatrix m n :=
  (WithLp.equiv 2 _).symm (fun p => A p.1 p.2)

theorem hs_matrix_to_of {m n : Type*} (A : Matrix m n ℝ) :
    hsMatrixToMatrix (hsMatrixOfMatrix A) = A := rfl

theorem hs_matrix_of_to {m n : Type*} (A : HSMatrix m n) :
    hsMatrixOfMatrix (hsMatrixToMatrix A) = A := by
  ext p
  rfl

theorem hs_matrix_norm_sq {m n : Type*} [Fintype m] [Fintype n] (A : HSMatrix m n) :
    ‖A‖^2 = ∑ i, ∑ j, (hsMatrixToMatrix A i j)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type,Real.norm_eq_abs,sq_abs,hsMatrixToMatrix]

end ScalarMonotone.EndOfPaper
end
