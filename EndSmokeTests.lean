import EndOfPaper

/-! Scalar smoke tests. Current execution evidence: docs/CODEX_PROGRESS.md. -/
open ScalarMonotone ScalarMonotone.EndOfPaper MeasureTheory Set

example (p : ℝ) (hp : 0 < p) :
    hardyScalar (fun u => -Real.log u) p = 1-Real.log p :=
  hardyScalar_exponential_profile hp

example (κ p : ℝ) (hκ : 1 < κ) (hp : 0 < p) :
    hardyScalar (fun u => u^((-1 : ℝ)/κ)) p = (κ/(κ-1))*p^((-1 : ℝ)/κ) :=
  hardyScalar_power_profile hκ hp

example (r : ℕ) (x : Fin (2*r+1) → ℝ) (θ : ℝ) :
    |scalarMedian r x-θ| ≤ scalarMedian r (fun i => |x i-θ|) :=
  median_error_domination r x θ

example {n : ℕ} {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    {a b : CoordinateVector n} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    superadditiveTransform F a+superadditiveTransform F b ≤
      superadditiveTransform F (a+b) :=
  superadditiveTransform_superadditive hF ha hb
