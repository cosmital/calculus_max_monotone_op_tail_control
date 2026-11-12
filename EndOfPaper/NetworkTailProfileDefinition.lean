import EndOfPaper.NetworkTwoPoint
import EndOfPaper.InitialProfileAffine
import EndOfPaper.FiniteProfileProduct

/-!
The literal manuscript RHS: baseline at u/6, actual geometric affine-input factors at u/12, finite interior graph product and endpoint completion.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkInverseDimension {L : ℕ} (N : ℕ) (p : ℕ → ℕ) (i : Fin L) : ℝ :=
  (Real.sqrt (((min (N*p 0) (p (i.val+1)+p i.val) : ℕ) : ℝ)))⁻¹

def networkAffineInputProfile {L : ℕ} (N : ℕ) (p : ℕ → ℕ) (q : DecGraph)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1) (mx : ℝ) (mw : Fin L → ℝ) (i : Fin L) : DecGraph :=
  completedProfileAffine 1 (max mx (mw i)) (networkInverseDimension N p i) q
    (by norm_num) hqi (inv_nonneg.mpr (Real.sqrt_nonneg _))

def networkTailComponent {L : ℕ} (N : ℕ) (p : ℕ → ℕ) (q : DecGraph)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1) (mx : ℝ) (mw : Fin L → ℝ) :
    Option (Fin L) → Operator
  | none => fun u => q.val (u/6)
  | some i => fun u => geometricHardyTransform 1 (networkAffineInputProfile N p q hqi mx mw i) (u/12)

def networkTailProfile {L : ℕ} (N : ℕ) (p : ℕ → ℕ) (q : DecGraph)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1) (mx : ℝ) (mw : Fin L → ℝ) : Operator :=
  outputScale (networkPrefactor L N p)
    (negOut (completion (Ioo (0 : ℝ) 1) (negOut
      (interiorFiniteProfileProduct 1 (networkTailComponent N p q hqi mx mw)))))

end ScalarMonotone.EndOfPaper
end
