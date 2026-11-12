import Paper

open ScalarMonotone ScalarMonotone.EndOfPaper MeasureTheory Set
open scoped ENNReal Topology BigOperators Interval

-- Independently stated expected types for current manuscript correspondences.

/- Independent finite-maximum approximation and covariance/Hessian readers.
These check analytic ingredients; complete Gaussian matrix bounds are checked below. -/
open Set
open scoped BigOperators InnerProductSpace
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    Finset.univ.sup' Finset.univ_nonempty z ≤ Real.log (∑ i, Real.exp (β*z i))/β ∧
      Real.log (∑ i, Real.exp (β*z i))/β ≤
        Finset.univ.sup' Finset.univ_nonempty z+Real.log (Fintype.card ι : ℝ)/β := by
  exact ⟨gaussian_finite_maximum_le_softmax z hβ,gaussian_softmax_le_finite_maximum z hβ⟩

example {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {a β : ℝ} (ha : 0 ≤ a) (haβ : a ≤ β) (z : ι → ℝ) (D : ι → ι → ℝ)
    (hDiag : ∀ i, D i i = 0) (hOff : ∀ i j, i ≠ j → 0 ≤ D i j) :
    (∑ i, ∑ j, D i j*gaussianSoftmaxHessian a β z i j) ≤ 0 := by
  exact gaussian_softmax_covariance_contraction_nonpos ha haβ z D hDiag hOff

example {m n : Type*} [Fintype m] [Fintype n]
    (u u' : EuclideanSpace ℝ m) (v v' : EuclideanSpace ℝ n)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    0 ≤ (∑ k, gaussianMatrixCoefficient u v k*gaussianMatrixCoefficient u' v' k)-
      (∑ k, gaussianVectorComparisonCoefficient u v k*gaussianVectorComparisonCoefficient u' v' k) ∧
      (∑ k, (gaussianMatrixCoefficient u v k)^2) = 2 ∧
      (∑ k, (gaussianVectorComparisonCoefficient u v k)^2) = 2 := by
  exact ⟨gaussian_matrix_comparison_covariance_nonneg u u' v v' hu hu' hv hv',
    gaussian_matrix_comparison_variances u v hu hv⟩

end ScalarMonotone.EndOfPaper
end


/- Independent actual Gaussian integration-by-parts statements. -/
open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {f d : ℝ → ℝ} (hfd : ∀ x, HasDerivAt f (d x) x)
    (hf : Integrable f (gaussianReal 0 1)) (hd : Integrable d (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, d x ∂gaussianReal 0 1 := by
  exact gaussian_real_integration_by_parts hfd hf hd hxf

example {n : ℕ} {f d : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (i : Fin (n+1))
    (hf : Measurable f) (hd : Measurable d)
    (hfd : ∀ z : EuclideanSpace ℝ (Fin (n+1)), ∀ s : ℝ,
      HasDerivAt (fun t => f (gaussianReplace z i t)) (d (gaussianReplace z i s)) s)
    (hfI : Integrable (fun z => f (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)))
    (hdI : Integrable (fun z => d (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)))
    (hxfI : Integrable (fun z => z i*f (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1))) :
    (∫ z, z i*f (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1)) =
      ∫ z, d (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1) := by
  exact gaussian_product_coordinate_integration_by_parts i hf hd hfd hfI hdI hxfI

end ScalarMonotone.EndOfPaper
end


/- Independent actual interpolation derivative, domination and endpoint-continuity readers. -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {ι : Type*} {n : ℕ} (A B : ι → Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n))
    (i : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => gaussianInterpolatedProcess A B s z i)
      (gaussianLinearProcess A z i/(2*Real.sqrt t)-gaussianLinearProcess B z i/(2*Real.sqrt (1-t))) t := by
  exact gaussian_interpolated_process_hasDerivAt A B z i ht

example {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ} (A B : ι → Fin n → ℝ)
    {t a β : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) (hβ : 0 < β)
    (z : EuclideanSpace ℝ (Fin n)) :
    gaussianSoftmaxMoment a β (gaussianInterpolatedProcess A B t z) ≤
      Real.exp (a*Real.log (Fintype.card ι : ℝ)/β)*
        Real.exp ((a*(gaussianCoefficientMass A+gaussianCoefficientMass B))*‖z‖) := by
  exact gaussian_interpolated_softmax_bound A B ht ha hβ z

example {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ} (A B : ι → Fin n → ℝ)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    ContinuousOn (fun t : ℝ => ∫ z, gaussianSoftmaxMoment a β
      (gaussianInterpolatedProcess A B t (gaussianProductVector n z)) ∂gaussianProductMeasure n)
      (Icc (0 : ℝ) 1) := by
  exact gaussian_interpolation_moment_continuousOn A B ha hβ

end ScalarMonotone.EndOfPaper
end


/- Independent actual differentiation-under-Gaussian-expectation statements;
every domination and integrability premise is derived. -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ} (A B : ι → Fin n → ℝ)
    {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun z => gaussianInterpolationDerivative A B a β t (gaussianProductVector n z))
        (gaussianProductMeasure n) ∧
      HasDerivAt (fun s => ∫ z, gaussianSoftmaxMoment a β
        (gaussianInterpolatedProcess A B s (gaussianProductVector n z)) ∂gaussianProductMeasure n)
        (∫ z, gaussianInterpolationDerivative A B a β t (gaussianProductVector n z) ∂gaussianProductMeasure n) t := by
  exact gaussian_interpolation_moment_hasDerivAt A B ha hβ ht

example {ι : Type*} [Fintype ι] {n : ℕ} (A B : ι → Fin n → ℝ) (a β t : ℝ) :
    Integrable (fun z => gaussianInterpolationDominant A B a β t (gaussianProductVector n z))
      (gaussianProductMeasure n) := by
  exact gaussian_interpolation_dominant_integrable A B a β t

end ScalarMonotone.EndOfPaper
end


/- Independent actual Gaussian gradient-IBP and covariance cancellation statements. -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ}
    (A B : ι → Fin (n+1) → ℝ) {a β t : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β)
    (ht : t ∈ Icc (0 : ℝ) 1) (i : ι) (k : Fin (n+1)) :
    (∫ z, z k*gaussianSoftmaxGradient a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i
      ∂gaussianProductMeasure (n+1)) =
      ∫ z, (∑ j, gaussianSoftmaxHessian a β (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) i j*
        (Real.sqrt t*A j k+Real.sqrt (1-t)*B j k)) ∂gaussianProductMeasure (n+1) := by
  exact gaussian_interpolation_gradient_coordinate_ibp A B ha hβ haβ ht i k

example {ι : Type*} {n : ℕ} (A B : ι → Fin n → ℝ)
    (hCross : ∀ i j, (∑ k, A i k*B j k) = 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i j : ι) :
    gaussianInterpolationCovarianceWeight A B t i j =
      (gaussianLinearCovariance A i j-gaussianLinearCovariance B i j)/2 := by
  exact gaussian_interpolation_covariance_weight A B hCross ht i j

end ScalarMonotone.EndOfPaper
end


/- Independent actual Gaussian interpolation monotonicity and smooth moment comparison. -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ}
    (A B : ι → Fin (n+1) → ℝ) (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) :
    AntitoneOn (fun t : ℝ => ∫ z, gaussianSoftmaxMoment a β
      (gaussianInterpolatedProcess A B t (gaussianProductVector (n+1) z)) ∂gaussianProductMeasure (n+1))
      (Icc (0 : ℝ) 1) := by
  exact gaussian_interpolation_moment_antitoneOn A B hCross hDiag hOff ha hβ haβ

example {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ}
    (A B : ι → Fin (n+1) → ℝ) (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (haβ : a ≤ β) :
    (∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess A (gaussianProductVector (n+1) z))
      ∂gaussianProductMeasure (n+1)) ≤
      ∫ z, gaussianSoftmaxMoment a β (gaussianLinearProcess B (gaussianProductVector (n+1) z))
        ∂gaussianProductMeasure (n+1) := by
  exact gaussian_linear_softmax_moment_comparison A B hCross hDiag hOff ha hβ haβ

end ScalarMonotone.EndOfPaper
end


/- Independent actual finite Gaussian maximum, matrix arrays, and original-law L1 readers. -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {n : ℕ}
    (A B : ι → Fin (n+1) → ℝ) (hCross : ∀ i j, (∑ k, A i k*B j k) = 0)
    (hDiag : ∀ i, gaussianLinearCovariance A i i = gaussianLinearCovariance B i i)
    (hOff : ∀ i j, i ≠ j → gaussianLinearCovariance B i j ≤ gaussianLinearCovariance A i j)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, Real.exp (a*gaussianFiniteMaximum (gaussianLinearProcess A (gaussianProductVector (n+1) z)))
      ∂gaussianProductMeasure (n+1)) ≤
      ∫ z, Real.exp (a*gaussianFiniteMaximum (gaussianLinearProcess B (gaussianProductVector (n+1) z)))
        ∂gaussianProductMeasure (n+1) := by
  exact gaussian_linear_finite_maximum_moment_comparison A B hCross hDiag hOff ha

example {ι m n : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) {a : ℝ} (ha : 0 ≤ a) :
    gaussianFiniteMaxMoment (gaussianMatrixComparisonArray u v) a ≤
      gaussianFiniteMaxMoment (gaussianVectorComparisonArray u v) a := by
  exact gaussian_matrix_unit_family_maximum_comparison u v hu hv ha

example {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hX : Measurable X) (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (a : ℝ) :
    Integrable (fun ω => Real.exp (a*‖hsMatrixOp (X ω)‖)) μ := by
  exact gaussian_matrix_operator_exponential_integrable hX hi hm hLaw a

end ScalarMonotone.EndOfPaper
end


/-! Reader checks the actual norm and deterministic finite-max limit. -/
open Set Filter
open scoped InnerProductSpace Topology
namespace ScalarMonotone.EndOfPaper

example (b : ℕ → ℝ) (c : ℝ) (hc : IsLUB (range b) c) :
    Tendsto (fun N => gaussianFiniteMaximum (fun k : Fin (N+1) => b k.val)) atTop (𝓝 c) :=
  gaussian_sequence_maximum_tendsto b hc

example {m n : Type*} [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    (T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :
    IsLUB (range (fun p : {u : EuclideanSpace ℝ m // ‖u‖ = 1} ×
      {v : EuclideanSpace ℝ n // ‖v‖ = 1} => ⟪p.1.val,T p.2.val⟫_ℝ)) ‖T‖ :=
  gaussian_unit_pair_value_isLUB T

example {m n : Type*} [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    (A : HSMatrix m n) :
    Tendsto (gaussianSequenceMaximum (gaussianUnitPairValue (hsMatrixOp A) ∘ gaussianUnitPairSequence m n))
      atTop (𝓝 ‖hsMatrixOp A‖) := gaussian_operator_dense_maximum_tendsto (hsMatrixOp A)

end ScalarMonotone.EndOfPaper


/-! Reader expands actual sample laws, independence and moments. -/
open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace ScalarMonotone.EndOfPaper

example {m n : Type*} [Fintype m] [Fintype n] :
    IndepFun (gaussianJointMatrix (m := m) (n := n)) gaussianJointScalar
      (gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) :=
  gaussian_joint_matrix_scalar_independence

example {m n : Type*} [Fintype m] [Fintype n] (a : ℝ) :
    (∫ z, Real.exp (a*gaussianJointScalar (m := m) (n := n) z)
      ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) = Real.exp (a^2/2) :=
  (gaussian_joint_scalar_exp_integral a).2

example {m n : Type*} [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, Real.exp (a*(‖gaussianJointLeftVector (m := m) (n := n) z‖+‖gaussianJointRightVector z‖))
      ∂gaussianProductMeasure (gaussianMatrixJointDimension m n+1)) ≤
    Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2) :=
  (gaussian_joint_vector_norm_sum_mgf ha).2

example {ι m n : Type*} [Fintype m] [Fintype n]
    (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n)
    (z : Fin (gaussianMatrixJointDimension m n+1) → ℝ) (i : ι) :
    gaussianLinearProcess (gaussianMatrixComparisonArray u v)
      (gaussianProductVector (gaussianMatrixJointDimension m n+1) z) i =
    ⟪u i,hsMatrixOp (gaussianJointMatrix z) (v i)⟫_ℝ+gaussianJointScalar z :=
  gaussian_joint_matrix_process u v z i

end ScalarMonotone.EndOfPaper


/-! Reader checks the literal sharp Gaussian operator-norm conclusions on
arbitrary original probability spaces, with actual coordinate laws. -/
open Set MeasureTheory ProbabilityTheory
namespace ScalarMonotone.EndOfPaper

example {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun ω => Real.exp (a*‖hsMatrixOp (X ω)‖)) μ ∧
      (∫ ω, Real.exp (a*‖hsMatrixOp (X ω)‖) ∂μ) ≤
      Real.exp (a*(Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ))+a^2/2) :=
  gaussian_matrix_operator_norm_mgf hi hm hLaw ha

example {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+s ≤ ‖hsMatrixOp (X ω)‖} ≤
      Real.exp (-(s^2)/2) := gaussian_matrix_operator_norm_tail hi hm hLaw hs

example {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {t : ℝ} (hmed : IsRealMedian (fun ω => ‖hsMatrixOp (X ω)‖) μ t) :
    t ≤ Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+Real.sqrt (2*Real.log 2) :=
  gaussian_matrix_operator_norm_median hi hm hLaw hmed

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} (hd : 0 < d) {X : Ω → HSMatrix (Fin d) (Fin d)}
    (hi : iIndepFun (fun i : Fin d × Fin d => fun ω => X ω i) μ)
    (hm : ∀ i : Fin d × Fin d, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : Fin d × Fin d, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {t : ℝ} (hmed : IsRealMedian (fun ω => ‖hsMatrixOp (X ω)‖/Real.sqrt (2*(d : ℝ))) μ t) :
    t ≤ Real.sqrt 2+Real.sqrt (Real.log 2/(d : ℝ)) :=
  gaussian_square_matrix_normalized_operator_median hd hi hm hLaw hmed

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {Z : Ω → NetworkParameters L N (fun _ => d)}
    (hi : iIndepFun (fun i => fun ω => Z ω i) μ)
    (hm : ∀ i, Measurable (fun ω => Z ω i))
    (hLaw : ∀ i, Measure.map (fun ω => Z ω i) μ = gaussianReal 0 1)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ mx)
    (hmw : ∀ l, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) l)‖/
      Real.sqrt ((d+d : ℕ) : ℝ)) μ (mw l)) :
    mx ≤ 1+Real.sqrt (2*Real.log 2/((N*d : ℕ) : ℝ)) ∧
      ∀ l, mw l ≤ Real.sqrt 2+Real.sqrt (Real.log 2/(d : ℝ)) :=
  gaussian_network_norm_medians hN hd hi hm hLaw hmx hmw

#print axioms gaussian_matrix_operator_norm_mgf
#print axioms gaussian_matrix_operator_norm_tail
#print axioms gaussian_square_matrix_normalized_operator_median
#print axioms gaussian_network_norm_medians

end ScalarMonotone.EndOfPaper



/- Independent statements for the actual Gaussian HS median, weak norm tail,
exponential integrability and midpoint premise. No input concentration or
Gaussian operator-norm median estimate is assumed here. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {Ω : Type*} [MeasurableSpace Ω] {N d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → HSMatrix (Fin d) (Fin N)} (hN : 0 < N) (hd : 0 < d)
    (hi : iIndepFun (fun i : Fin d × Fin N => fun ω => X ω i) μ)
    (hm : ∀ i : Fin d × Fin N, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : Fin d × Fin N, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {m : ℝ} (hmed : IsRealMedian (fun ω => ‖X ω‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ m) :
    m ≤ 1+Real.sqrt (2*Real.log 2/((N*d : ℕ) : ℝ)) := by
  exact gaussian_hs_normalized_median hN hd hi hm hLaw hmed

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | Real.sqrt (Fintype.card ι : ℝ)+s ≤ ‖X ω‖} ≤ Real.exp (-(s^2)/2) := by
  exact gaussian_euclidean_norm_tail hi hm hLaw hn hs

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) :
    Integrable (fun ω => Real.exp (a*f (X ω))) μ := by
  exact gaussian_lipschitz_exponential_integrable hX hi hm hLaw hf a

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} (hf : LipschitzWith 1 f) (a : ℝ) (x y : E) :
    (Real.exp (a*f x)*Real.exp (-(‖x‖^2)/2))*(Real.exp (-a*f y)*Real.exp (-(‖y‖^2)/2)) ≤
      (Real.exp ((a^2)/2)*Real.exp (-(‖(1/2 : ℝ) • (x+y)‖^2)/2))^2 := by
  simpa only [gaussianKernel] using gaussian_lipschitz_midpoint_domination hf a x y

end ScalarMonotone.EndOfPaper
end

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun ω => Real.exp (a*‖X ω‖)) μ ∧
      (∫ ω, Real.exp (a*‖X ω‖) ∂μ) ≤ Real.exp (a*Real.sqrt (Fintype.card ι : ℝ)+a^2/2) := by
  exact gaussian_euclidean_norm_mgf hX hi hm hLaw hn ha

end ScalarMonotone.EndOfPaper
end


/- Independent scalar integral and marginal statements. These do not replace
the remaining finite-dimensional Gaussian induction or matrix comparison. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {f g H : ℝ → ℝ} (hf : Continuous f) (hfp : ∀ x, 0 < f x) (hfi : Integrable f volume)
    (hg : Continuous g) (hgp : ∀ x, 0 < g x) (hgi : Integrable g volume) (hH : Integrable H volume)
    (hCompare : ∀ x y : ℝ, Real.sqrt (f x*g y) ≤ H ((x+y)/2)) :
    Real.sqrt ((∫ x : ℝ, f x)*(∫ x : ℝ, g x)) ≤ ∫ x : ℝ, H x := by
  exact midpoint_prekopa_leindler_real hf hfp hfi hg hgp hgi hH hCompare

example {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFI : Integrable (fun x => Real.exp (F x)) (gaussianReal 0 1))
    (hGI : Integrable (fun x => Real.exp (G x)) (gaussianReal 0 1)) {b : ℝ}
    (hCompare : ∀ x y : ℝ, F x+G y ≤ b+(x-y)^2/4) :
    Real.log (∫ x, Real.exp (F x) ∂gaussianReal 0 1)+
      Real.log (∫ x, Real.exp (G x) ∂gaussianReal 0 1) ≤ b := by
  exact gaussian_real_midpoint_log_integral hF hG hFI hGI hCompare

example {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] {μ : Measure Ω} [NeZero μ]
    {F : E → Ω → ℝ} {K : ℝ≥0} (hInt : ∀ x, Integrable (fun ω => Real.exp (F x ω)) μ)
    (hLip : ∀ x y ω, |F x ω-F y ω| ≤ (K : ℝ)*dist x y) :
    LipschitzWith K (fun x => Real.log (∫ ω, Real.exp (F x ω) ∂μ)) := by
  simpa only [logExpIntegral] using log_exp_integral_lipschitz hInt hLip

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {K : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith K f) :
    Integrable (fun ω => Real.exp (f (X ω))) μ := by
  exact gaussian_exp_integrable_lipschitz hX hi hm hLaw hf

end ScalarMonotone.EndOfPaper
end


/- Independent original Gaussian weak-tail and whole-profile reader statements. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | |f (X ω)-f (X' ω)| ≥ t} ≤ 2*Real.exp (-t^2/4) := by
  exact gaussian_lipschitz_copy_weak_tail hX hi hm hLaw hInd hCopy hf ht

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : iIndepFun (fun i ω => X ω i) μ)
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ) :
    let q := affineSqrtLogProfile 0 2 (by norm_num)
    interior (dom q.val) = Ioo (0 : ℝ) 1 ∧
      (∀ u ∈ Ioo (0 : ℝ) 1, q.val u = {2*Real.sqrt (Real.log (2/u))}) ∧
      ∀ f : EuclideanSpace ℝ ι → ℝ, LipschitzWith 1 f →
        DecLE (tailQuantile (Measure.map (fun ω => |f (X ω)-f (X' ω)|) μ)) q.val := by
  dsimp only
  have hP := affine_sqrt_log_profile_properties (m := 0) (c := 2) (by norm_num) (by norm_num)
  refine ⟨hP.1,?_,gaussian_input_profile hX hX' hi hLaw hInd hCopy⟩
  intro u hu
  rw [hP.2.1 u hu]
  simp only [zero_add,sqrtLogScalar,Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hu.1.ne']

end ScalarMonotone.EndOfPaper
end



/- Independent expected types for the original power-tail example. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

example {L N : ℕ} {p : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NetworkParameters L N p)] [OpensMeasurableSpace (NetworkParameters L N p)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → NetworkParameters L N p}
    (hL : 0 < L) (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ i, LipschitzWith 1 (σ i)) (hσ0 : ∀ i, σ i 0 = 0)
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {qδ : DecGraph} (hδdom : interior (dom qδ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qδ.val x, 0 ≤ v)
    (hδ : ∀ f : NetworkParameters L N p → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qδ.val)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) μ mx)
    (hmw : ∀ i : Fin L, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) i)‖/
      Real.sqrt ((p (i.val+1)+p i.val : ℕ) : ℝ)) μ (mw i))
    {g : HSMatrix (Fin (p L)) (Fin N) → ℝ} (hg : LipschitzWith 1 g) {mV : ℝ}
    (hmV : IsRealMedian (fun ω => g (finiteNetworkMap σ (Z ω))) μ mV)
    {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hPower : DecLE qδ.val (affinePowerProfile 0 A α hA.le hα).val) :
    let D := (Real.sqrt (p L : ℝ))⁻¹*Real.sqrt (1+((N*p 0 : ℕ) : ℝ)*
      (∑ i : Fin L, (((p (i.val+1)+p i.val : ℕ) : ℝ))⁻¹))
    let B := fun u : ℝ => D*A*Real.exp (α*(L : ℝ))*(6/u)^α *
      ∏ i : Fin L, (max mx (mw i)+A*(12/u)^α/
        Real.sqrt (((min (N*p 0) (p (i.val+1)+p i.val) : ℕ) : ℝ)))
    let R := completedDecreasingRestriction (Ioo (0 : ℝ) 1) (ofFun B)
    MaximalDecreasing R ∧ interior (dom R) = Ioo (0 : ℝ) 1 ∧
    DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ)) R ∧
    ∀ u ∈ Ioo (0 : ℝ) 1,
      (∀ v ∈ tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ) u,
        v ≤ B u) ∧ μ.real {ω | B u < |g (finiteNetworkMap σ (Z ω))-mV|} ≤ u := by
  have hB : (fun u : ℝ => (Real.sqrt (p L : ℝ))⁻¹*Real.sqrt (1+((N*p 0 : ℕ) : ℝ)*
      (∑ i : Fin L, (((p (i.val+1)+p i.val : ℕ) : ℝ))⁻¹))*A*Real.exp (α*(L : ℝ))*(6/u)^α *
      ∏ i : Fin L, (max mx (mw i)+A*(12/u)^α/
        Real.sqrt (((min (N*p 0) (p (i.val+1)+p i.val) : ℕ) : ℝ)))) =
      powerNetworkBound (networkPrefactor L N p) A α (fun i => max mx (mw i))
        (networkInverseDimension N p) := by
    funext u
    rw [power_network_bound_network_formula]
    rfl
  have h := network_power_tails hL hN hp σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV hA hα hPower
  dsimp only at h ⊢
  rw [← hB] at h
  exact h

example {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j)
    {A α mx : ℝ} (mw : Fin L → ℝ) (hA : 0 < A) (hα : 0 < α) :
    let C := networkPrefactor L N p*A*Real.exp (α*(L : ℝ))*6^α *
      ∏ i : Fin L, (((Real.sqrt (((min (N*p 0) (p (i.val+1)+p i.val) : ℕ) : ℝ)))⁻¹)*A*12^α)
    0 < C ∧ Tendsto (fun u : ℝ =>
      (networkPrefactor L N p*A*Real.exp (α*(L : ℝ))*(6/u)^α *
        ∏ i : Fin L, (max mx (mw i)+A*(12/u)^α/
          Real.sqrt (((min (N*p 0) (p (i.val+1)+p i.val) : ℕ) : ℝ))))*u^(α*((L : ℝ)+1)))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 C) := by
  have h := network_power_far_tail (mx := mx) hN hp mw hA hα
  dsimp only at h ⊢
  simpa only [power_network_bound_network_formula,networkInverseDimension] using h

end ScalarMonotone.EndOfPaper
end


/- Independent exact statements of the depth inequality and its uniform rate.
Actual Gaussian concentration and Gaussian norm medians are separate claims. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper
section
variable {L N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NetworkParameters L N (fun _ => d))]
    [OpensMeasurableSpace (NetworkParameters L N (fun _ => d))]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → NetworkParameters L N (fun _ => d)}
    (hL : 0 < L) (hN : 0 < N) (hd : 0 < d)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ i, LipschitzWith 1 (σ i)) (hσ0 : ∀ i, σ i 0 = 0)
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {qδ : DecGraph} (hδdom : interior (dom qδ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qδ.val x, 0 ≤ v)
    (hδ : ∀ f : NetworkParameters L N (fun _ => d) → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qδ.val)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*d : ℕ) : ℝ)) μ mx)
    (hmw : ∀ i : Fin L, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) i)‖/
      Real.sqrt ((d+d : ℕ) : ℝ)) μ (mw i))
    {g : HSMatrix (Fin d) (Fin N) → ℝ} (hg : LipschitzWith 1 g) {mV : ℝ}
    (hmV : IsRealMedian (fun ω => g (finiteNetworkMap σ (Z ω))) μ mV)
    {A : ℝ} (hA : 0 ≤ A) (hSG : DecLE qδ.val (affineSqrtLogProfile 0 A hA).val)
include hL hN hd σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV hA hSG

example :
    let M := (Finset.univ : Finset (Option (Fin L))).sup' ⟨none,Finset.mem_univ _⟩
      (fun j => match j with | none => mx | some i => mw i)
    ∀ u ∈ Ioo (0 : ℝ) 1,
      μ.real {ω | A*Real.sqrt ((1+(N : ℝ)*(L : ℝ)/2)/(d : ℝ))*
        Real.sqrt (Real.log (24*Real.exp 1/u))*
        (M+A*Real.sqrt (Real.log (24*Real.exp 1/u))/
          Real.sqrt (((d*min N 2 : ℕ) : ℝ)))^L < |g (finiteNetworkMap σ (Z ω))-mV|} ≤ u := by
  simpa only [networkMedianMaximum,networkDepthRadius] using
    network_subgaussian_depth hL hN hd σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV hA hSG

example {c M t : ℝ} (hRatio : (N : ℝ)/(d : ℝ) ≤ c) (hmxM : mx ≤ M)
    (hmwM : ∀ i, mw i ≤ M) (ht : 0 ≤ t) :
    μ.real {ω | A*Real.sqrt (1+c*(L : ℝ)/2)*(M+A)^L*t < |g (finiteNetworkMap σ (Z ω))-mV|} ≤
      24*Real.exp 1*Real.exp (-(min (t^2)
        ((d : ℝ)^((L : ℝ)/((L : ℝ)+1))*t^(2/((L : ℝ)+1))))) := by
  exact network_subgaussian_two_regime_tail hL hN hd σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ
    hmx hmw hg hmV hA hSG hRatio hmxM hmwM ht

end
end ScalarMonotone.EndOfPaper
end



namespace NetworkControlReader
open ScalarMonotone ScalarMonotone.EndOfPaper Set MeasureTheory ProbabilityTheory
open scoped BigOperators

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L N : ℕ} {p : ℕ → ℕ}
    [MeasurableSpace (NetworkParameters L N p)] [OpensMeasurableSpace (NetworkParameters L N p)]
    (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j) (l : Fin L)
    {Z Z' : Ω → NetworkParameters L N p} (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ q.val x, 0 ≤ t)
    (hq : ∀ f : NetworkParameters L N p → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q.val)
    {mx mw : ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) μ mx)
    (hmw : IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) l)‖/
      Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ)) μ mw)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s) :
    let κ := (Real.sqrt (((min (N*p 0) (p (l.val+1)+p l.val) : ℕ) : ℝ)))⁻¹
    let A : Operator := negOut (completion (Ioo (0 : ℝ) 1) (negOut
      (fun x => {v | x ∈ Ioo (0 : ℝ) 1 ∧ ∃ a ∈ q.val x, v = max mx mw+κ*a})))
    DecLE (tailQuantile (Measure.map
      (fun ω => max (‖networkData (Z ω)‖/Real.sqrt ((N*p 0 : ℕ) : ℝ))
        (‖hsMatrixOp (networkWeight (Z ω) l)‖/Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ))) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1) (positiveInputDilation (1/2) A)) := by
  exact network_control_quantile_bound hN hp l hZ hZ' hi he hqi hq0 hq hmx hmw hs

example {L N : ℕ} {p : ℕ → ℕ} (hN : 0 < N) (hp : ∀ l ≤ L, 0 < p l)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    {g : HSMatrix (Fin (p L)) (Fin N) → ℝ} (hg : LipschitzWith 1 g)
    (z w : NetworkParameters L N p) :
    |g (finiteNetworkMap σ z)/networkPrefactor L N p-
      g (finiteNetworkMap σ w)/networkPrefactor L N p| ≤
      ‖z-w‖*(∏ l : Fin L, max (networkControl l z) (networkControl l w)) := by
  simpa only [Real.dist_eq,dist_eq_norm] using normalized_network_observation_modulus hN hp σ hσ hσ0 hg z w

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (m : ℝ) {c : ℝ} (hc : 0 < c) :
    tailQuantile (Measure.map (fun ω => |X ω-m|) μ) =
      (fun p => {v | ∃ a ∈ tailQuantile (Measure.map (fun ω => |X ω/c-m/c|) μ) p, v = c*a}) := by
  exact centered_quantile_positive_normalization hX m hc

end NetworkControlReader


namespace OriginalNetworkProfileReader
open ScalarMonotone ScalarMonotone.EndOfPaper Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

example {L N : ℕ} {p : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NetworkParameters L N p)] [OpensMeasurableSpace (NetworkParameters L N p)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → NetworkParameters L N p}
    (hL : 0 < L) (hN : 0 < N) (hp : ∀ j ≤ L, 0 < p j)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ i, LipschitzWith 1 (σ i)) (hσ0 : ∀ i, σ i 0 = 0)
    (hZ : Measurable Z) (hZ' : Measurable Z') (hi : IndepFun Z Z' μ) (he : IdentDistrib Z Z' μ μ)
    {qδ : DecGraph} (hδdom : interior (dom qδ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qδ.val x, 0 ≤ v)
    (hδ : ∀ f : NetworkParameters L N p → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qδ.val)
    {mx : ℝ} {mw : Fin L → ℝ}
    (hmx : IsRealMedian (fun ω => ‖networkData (Z ω)‖/Real.sqrt ((N*p 0 : ℕ) : ℝ)) μ mx)
    (hmw : ∀ i : Fin L, IsRealMedian (fun ω => ‖hsMatrixOp (networkWeight (Z ω) i)‖/
      Real.sqrt ((p (i.val+1)+p i.val : ℕ) : ℝ)) μ (mw i))
    {g : HSMatrix (Fin (p L)) (Fin N) → ℝ} (hg : LipschitzWith 1 g) {mV : ℝ}
    (hmV : IsRealMedian (fun ω => g (finiteNetworkMap σ (Z ω))) μ mV)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qδ.val (Ioo (0 : ℝ) 1) sδ)
    (hPδ : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ x)) 0)) < ∞) :
    let D := (1/Real.sqrt (p L : ℝ))*Real.sqrt (1+((N*p 0 : ℕ) : ℝ)*
      (∑ i : Fin L, 1/(((p (i.val+1)+p i.val : ℕ) : ℝ))))
    let factors : Option (Fin L) → Operator := fun j => match j with
      | none => fun u => qδ.val (u/6)
      | some i => fun u => geometricHardyTransform 1
          (networkAffineInputProfile N p qδ hδdom mx mw i) (u/12)
    let T := outputScale D (negOut (completion (Ioo (0 : ℝ) 1)
      (negOut (interiorFiniteProfileProduct 1 factors))))
    MaximalDecreasing T ∧ interior (dom T) = Ioo (0 : ℝ) 1 ∧
      DecLE (tailQuantile (Measure.map (fun ω => |g (finiteNetworkMap σ (Z ω))-mV|) μ)) T := by
  simpa only [networkTailProfile,networkTailComponent,networkPrefactor,one_div] using
    network_tail_profiles hL hN hp σ hσ hσ0 hZ hZ' hi he hδdom hδ0 hδ hmx hmw hg hmV hsδ hPδ

end OriginalNetworkProfileReader



example (m c α v : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) (hv : 0 < v) :
    ScalarMonotone.EndOfPaper.geometricPrefixValue (fun x => m+c*x^(-α)) v ≤
      Real.exp α*(m+c*v^(-α)) := by
  exact ScalarMonotone.EndOfPaper.geometricPrefixValue_affine_power_bound hm hc hα hv

example (m c α : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) (hα : 0 < α) :
    ∃ q : ScalarMonotone.DecGraph,
      q.val = ScalarMonotone.EndOfPaper.completedDecreasingRestriction (Set.Ioo (0 : ℝ) 1)
        (ScalarMonotone.ofFun (fun x => m+c*x^(-α))) ∧
      ScalarMonotone.MaximalDecreasing (ScalarMonotone.EndOfPaper.geometricHardyTransform 1 q) ∧
      ScalarMonotone.DecLE (ScalarMonotone.EndOfPaper.geometricHardyTransform 1 q)
        (ScalarMonotone.outputScale (Real.exp α) q.val) ∧
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ v ∈ ScalarMonotone.EndOfPaper.geometricHardyTransform 1 q p,
        v ≤ Real.exp α*(m+c*p^(-α)) := by
  exact ⟨ScalarMonotone.EndOfPaper.affinePowerProfile m c α hc hα,rfl,
    ScalarMonotone.EndOfPaper.affine_power_geometric_bound hm hc hα⟩

example (L N : ℕ) (p : ℕ → ℕ) (z : ScalarMonotone.EndOfPaper.NetworkParameters L N p) :
    ‖z‖^2 = ‖ScalarMonotone.EndOfPaper.networkData z‖^2+
      ∑ l : Fin L, ‖ScalarMonotone.EndOfPaper.networkWeight z l‖^2 := by
  exact ScalarMonotone.EndOfPaper.network_parameter_norm_sq z

example (L N : ℕ) (p : ℕ → ℕ) (σ : Fin L → ℝ → ℝ)
    (z : ScalarMonotone.EndOfPaper.NetworkParameters L N p) (l : Fin L) :
    ScalarMonotone.EndOfPaper.networkLayer p (ScalarMonotone.EndOfPaper.networkActivationsAt σ)
      (ScalarMonotone.EndOfPaper.networkData z) (ScalarMonotone.EndOfPaper.networkWeightsAt z) (l.val+1) =
    ScalarMonotone.EndOfPaper.hsMatrixActivation (σ l)
      ((Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ))⁻¹ •
        ScalarMonotone.EndOfPaper.hsMatrixMul (ScalarMonotone.EndOfPaper.networkWeight z l)
          (ScalarMonotone.EndOfPaper.networkLayer p (ScalarMonotone.EndOfPaper.networkActivationsAt σ)
            (ScalarMonotone.EndOfPaper.networkData z) (ScalarMonotone.EndOfPaper.networkWeightsAt z) l.val)) := by
  simp only [ScalarMonotone.EndOfPaper.networkLayer,ScalarMonotone.EndOfPaper.networkActivationsAt,
    ScalarMonotone.EndOfPaper.networkWeightsAt,dif_pos l.isLt]

example (L N : ℕ) (p : ℕ → ℕ) (hN : 0 < N) (hp : ∀ l ≤ L, 0 < p l)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0)
    (z w : ScalarMonotone.EndOfPaper.NetworkParameters L N p) :
    ‖ScalarMonotone.EndOfPaper.finiteNetworkMap σ z-ScalarMonotone.EndOfPaper.finiteNetworkMap σ w‖ ≤
      (1/Real.sqrt (p L : ℝ))*
      Real.sqrt (1+((N*p 0 : ℕ) : ℝ)*(∑ l : Fin L, 1/(((p (l.val+1)+p l.val : ℕ) : ℝ))))*
      dist z w*(∏ l : Fin L,
        max (max (‖ScalarMonotone.EndOfPaper.networkData z‖/Real.sqrt ((N*p 0 : ℕ) : ℝ))
          (‖ScalarMonotone.EndOfPaper.hsMatrixOp (ScalarMonotone.EndOfPaper.networkWeight z l)‖/
            Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ)))
        (max (‖ScalarMonotone.EndOfPaper.networkData w‖/Real.sqrt ((N*p 0 : ℕ) : ℝ))
          (‖ScalarMonotone.EndOfPaper.hsMatrixOp (ScalarMonotone.EndOfPaper.networkWeight w l)‖/
            Real.sqrt ((p (l.val+1)+p l.val : ℕ) : ℝ)))) := by
  simpa only [ScalarMonotone.EndOfPaper.networkPrefactor,ScalarMonotone.EndOfPaper.networkControl,one_div] using
    ScalarMonotone.EndOfPaper.network_two_point_bound hN hp σ hσ hσ0 z w

example (L N : ℕ) (p : ℕ → ℕ) (hN : 0 < N) (hp : ∀ l ≤ L, 0 < p l)
    (σ : Fin L → ℝ → ℝ) (hσ : ∀ l, LipschitzWith 1 (σ l)) (hσ0 : ∀ l, σ l 0 = 0) :
    @Measurable (ScalarMonotone.EndOfPaper.NetworkParameters L N p)
      (ScalarMonotone.EndOfPaper.HSMatrix (Fin (p L)) (Fin N)) (borel _) (borel _)
      (ScalarMonotone.EndOfPaper.finiteNetworkMap σ) := by
  exact ScalarMonotone.EndOfPaper.finite_network_borel_measurable hN hp σ hσ hσ0


example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (F : ScalarMonotone.EndOfPaper.CoordinateVector n → ℝ)
    (hF : ScalarMonotone.EndOfPaper.AggregationAxioms F)
    (hc : ContinuousOn F {a | 0 ≤ a})
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ScalarMonotone.EndOfPaper.CoordinateVector n) (hm : Measurable X)
    (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω) (β : Fin n → ScalarMonotone.DecGraph)
    (h1 : ∀ i, ScalarMonotone.DecLE (β i).val (ScalarMonotone.ofFun (fun _ => (1 : ℝ))))
    (hz : ∀ i, IsGLB (ScalarMonotone.ran (β i).val) 0)
    (hS : ∀ i, ScalarMonotone.DecLE
      (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => X ω i) μ)) (β i).val)
    (b : Fin n → ℝ → ℝ)
    (hb : ∀ i p, p ∈ Set.Ioo (0 : ℝ) 1 → b i p ∈ ScalarMonotone.inverse (β i).val p)
    (hf : ∀ i, (∫⁻ p in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |b i p|) < ∞) :
    let A := ScalarMonotone.EndOfPaper.aggregationOperator
      (ScalarMonotone.EndOfPaper.superadditiveTransform F) (Set.Ioo (0 : ℝ) 1)
      (fun i => ScalarMonotone.EndOfPaper.hardyFamilyIntegral
        (interior (ScalarMonotone.dom (ScalarMonotone.inverse (β i).val)))
        (ScalarMonotone.inverse (β i).val))
    ScalarMonotone.MaximalDecreasing (ScalarMonotone.inverse A) ∧
      ScalarMonotone.DecLE (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => F (X ω)) μ))
        (ScalarMonotone.inverse A) := by
  exact ScalarMonotone.EndOfPaper.tail_envelope_aggregation hF hc μ hm hx
    (fun i => (β i).property) h1 hz hS hb hf

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (F : ScalarMonotone.EndOfPaper.CoordinateVector n → ℝ)
    (hF : ScalarMonotone.EndOfPaper.AggregationAxioms F) (hc : ContinuousOn F {a | 0 ≤ a})
    (hnz : ¬ ∀ a, 0 ≤ a → F a = 0)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ScalarMonotone.EndOfPaper.CoordinateVector n) (hm : Measurable X)
    (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω) (β : ScalarMonotone.DecGraph)
    (h1 : ScalarMonotone.DecLE β.val (ScalarMonotone.ofFun (fun _ => (1 : ℝ))))
    (hz : IsGLB (ScalarMonotone.ran β.val) 0)
    (hS : ∀ i, ScalarMonotone.DecLE
      (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => X ω i) μ)) β.val)
    (b : ℝ → ℝ) (hb : ∀ p ∈ Set.Ioo (0 : ℝ) 1, b p ∈ ScalarMonotone.inverse β.val p)
    (hf : (∫⁻ p in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |b p|) < ∞) :
    let C := ScalarMonotone.EndOfPaper.superadditiveTransform F (fun _ => 1)
    0 < C ∧
    ScalarMonotone.DecLE (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => F (X ω)) μ))
      (ScalarMonotone.comp (ScalarMonotone.EndOfPaper.hardyTailTransform β.val)
        (ScalarMonotone.ofFun (fun t => t/C))) ∧
    ∀ t ∈ (fun x : ℝ => C*x) '' ScalarMonotone.dom (ScalarMonotone.EndOfPaper.hardyTailTransform β.val),
      μ.real {ω | t < F (X ω)} ≤ sInf (ScalarMonotone.EndOfPaper.hardyTailTransform β.val (t/C)) := by
  simpa only [ScalarMonotone.inputDivide_eq_comp] using
    ScalarMonotone.EndOfPaper.common_envelope_survival_bound hn hF hc hnz μ hm hx β.property h1 hz hS hb hf

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (hx : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω)
    (β : Fin n → ScalarMonotone.DecGraph)
    (h1 : ∀ i, ScalarMonotone.DecLE (β i).val (ScalarMonotone.ofFun (fun _ => (1 : ℝ))))
    (hz : ∀ i, IsGLB (ScalarMonotone.ran (β i).val) 0)
    (hS : ∀ i, ScalarMonotone.DecLE (ScalarMonotone.survival (MeasureTheory.Measure.map (X i) μ)) (β i).val)
    (b : Fin n → ℝ → ℝ)
    (hb : ∀ i p, p ∈ Set.Ioo (0 : ℝ) 1 → b i p ∈ ScalarMonotone.inverse (β i).val p)
    (hf : ∀ i, (∫⁻ p in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |b i p|) < ∞) :
    (∀ i, MeasureTheory.Integrable (X i) μ) ∧
    ScalarMonotone.DecLE (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => ∑ i, X i ω) μ))
      (ScalarMonotone.inverse (fun p => {v : ℝ | ∃ a : Fin n → ℝ,
        (∀ i, a i ∈ ScalarMonotone.EndOfPaper.quantileHardy (MeasureTheory.Measure.map (X i) μ) p) ∧ v = ∑ i, a i})) := by
  have h := ScalarMonotone.EndOfPaper.hardy_sum_survival_of_envelopes hn μ X hm hx
    (fun i => (β i).property) h1 hz hS hb hf
  exact ⟨h.1,h.2.2⟩

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ScalarMonotone.EndOfPaper.CoordinateVector n) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (F : ScalarMonotone.EndOfPaper.CoordinateVector n → ℝ) (h0 : ∀ a, 0 ≤ a → F a = 0) :
    MeasureTheory.Measure.map (fun ω => F (X ω)) μ = MeasureTheory.Measure.dirac (0 : ℝ) := by
  exact ScalarMonotone.EndOfPaper.zero_aggregation_law μ hx h0


example {f g : ScalarMonotone.Operator} (h : ScalarMonotone.Increasing (ScalarMonotone.mul f g))
    (x w : ℝ) :
    ScalarMonotone.Increasing (fun y => {v | v ∈ ScalarMonotone.mul f g y ∨ (y=x ∧ v=w)}) ↔
      ∀ p ∈ ScalarMonotone.graph (ScalarMonotone.mul f g), 0 ≤ (x-p.1)*(w-p.2) := by
  exact ScalarMonotone.EndOfPaper.product_compatibility_criterion h

example (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) (p : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    ScalarMonotone.inverse
      (ScalarMonotone.EndOfPaper.completedDecreasingRestriction (Set.Ioi 0) (ScalarMonotone.survival ν)) p =
        ScalarMonotone.tailQuantile ν p ∧
    (∀ u > (1 : ℝ), ScalarMonotone.inverse
      (ScalarMonotone.EndOfPaper.completedDecreasingRestriction (Set.Ioi 0) (ScalarMonotone.survival ν)) u = {0}) ∧
    ScalarMonotone.EndOfPaper.completedDecreasingRestriction (Set.Ioi 0) (ScalarMonotone.survival ν) 0 =
      Set.Ici (ν.real (Set.Ioi 0)) := by
  exact ⟨ScalarMonotone.EndOfPaper.positive_survival_inverse_interior ν hν hp,
    (fun u hu => ScalarMonotone.EndOfPaper.positive_survival_inverse_above_one ν hu),
    ScalarMonotone.EndOfPaper.positive_survival_zero ν⟩

example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (s q : ℝ → ℝ)
    (hs : ∀ t > 0, s t ∈ ScalarMonotone.EndOfPaper.completedDecreasingRestriction
      (Set.Ioi 0) (ScalarMonotone.survival (MeasureTheory.Measure.map Y μ)) t)
    (hq : ∀ p > 0, q p ∈ ScalarMonotone.inverse
      (ScalarMonotone.EndOfPaper.completedDecreasingRestriction
        (Set.Ioi 0) (ScalarMonotone.survival (MeasureTheory.Measure.map Y μ))) p) :
    ((∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (s t)) ∧
    ((∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (s t)) =
      ∫⁻ p in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (q p)) := by
  have h := ScalarMonotone.EndOfPaper.positive_survival_expectation_area μ hY hY0 hs hq
  exact ⟨h.1,h.2.1.trans h.2.2⟩

example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hi : MeasureTheory.Integrable X μ) (q : ℝ → ℝ)
    (hq : ∀ p ∈ Set.Ioo (0 : ℝ) 1, q p ∈ ScalarMonotone.tailQuantile (MeasureTheory.Measure.map X μ) p) :
    MeasureTheory.Integrable q ScalarMonotone.unitUniform ∧
      (∫ ω, X ω ∂μ) = ∫ p in Set.Ioo (0 : ℝ) 1, q p := by
  exact ScalarMonotone.EndOfPaper.signed_expectation_quantile_area μ hX hi hq

example {n : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → E) (hZ : Measurable Z)
    (Λ : Fin n → E → ℝ) (hm : ∀ i, Measurable (Λ i)) (h0 : ∀ i z, 0 ≤ Λ i z)
    (q : Option (Fin n) → ScalarMonotone.Operator)
    (hq : ∀ j, ScalarMonotone.MaximalDecreasing (q j))
    (hpos : ∀ j p, p ∈ Set.Ioo (0 : ℝ) 1 → ∀ v ∈ q j p, 0 < v)
    (hQ : ∀ i, ScalarMonotone.DecLE
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map (fun ω => Λ i (Z ω)) μ)) (q (some i)))
    (sq : Option (Fin n) → ℝ → ℝ)
    (hs : ∀ j p, p ∈ Set.Ioo (0 : ℝ) 1 → sq j p ∈ q j p)
    (hP : (∫⁻ p in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (∏ j : Option (Fin n), sq j p)) 0)) < ∞)
    (b : ℝ) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (c : Fin n → ℝ) (hc : ∀ i, c i ∈ q (some i) b) :
    MeasureTheory.Integrable (fun ω => ∑ i, max (Real.log (Λ i (Z ω)/c i)) 0) μ ∧
    ((∫ ω, ∑ i, max (Real.log (Λ i (Z ω)/c i)) 0 ∂μ) ≤
      ∫ p in Set.Ioo (0 : ℝ) b, Real.log ((∏ i, sq (some i) p)/(∏ i, c i))) := by
  have h := ScalarMonotone.EndOfPaper.local_logarithmic_mean μ (fun i => (hm i).comp hZ)
    (fun i => Filter.Eventually.of_forall (fun ω => h0 i (Z ω))) hq hpos hQ hs hP hb hc
  exact ⟨h.2.1,h.2.2.1.trans_le (h.2.2.2.1.trans_eq h.2.2.2.2)⟩

example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℝ) (hm : Measurable X)
    (c : ℝ) (α : ScalarMonotone.DecGraph)
    (hd : Set.Ioi 0 ⊆ ScalarMonotone.dom α.val)
    (h0 : ∀ t > 0, ∀ v ∈ α.val t, 0 ≤ v)
    (hS : ScalarMonotone.DecLE
      (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => |X ω-c|) μ)) α.val)
    (b : ℝ → ℝ)
    (hb : ∀ t > 0, b t ∈ (sInf {α, ScalarMonotone.DecGraph.constant 1}).val t)
    (r : ℝ) (hr : 0 < r) :
    (Set.Ioi 0 ⊆ ScalarMonotone.dom (sInf {α, ScalarMonotone.DecGraph.constant 1}).val) ∧
    ScalarMonotone.DecLE (ScalarMonotone.survival (MeasureTheory.Measure.map (fun ω => |X ω-c|) μ))
      (sInf {α, ScalarMonotone.DecGraph.constant 1}).val ∧
    ((∫⁻ ω, ENNReal.ofReal (|X ω-c|^r) ∂μ) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (b (t^(1/r)))) ∧
    ((∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (b (t^(1/r)))) = ENNReal.ofReal r *
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1)*b t)) := by
  have hb' : ∀ t > 0, b t ∈ (α ⊓ ScalarMonotone.DecGraph.constant 1).val t := by
    simpa only [csInf_pair] using hb
  refine ⟨?_,?_⟩
  · simpa only [csInf_pair] using ScalarMonotone.EndOfPaper.operator_cap_positive_domain α hd
  · simpa only [csInf_pair] using
      ScalarMonotone.EndOfPaper.centered_moment_operator_cap μ hm c α hd h0 hS hb' hr


-- The literal completed unit profile is the quantile graph of delta_1.
-- This reader asks for the obstruction on arbitrary original spaces,
-- without a boundedness or integrability assumption on the observation.
example {n : ℕ} (hn : 0 < n) {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hQ : ∀ i, ScalarMonotone.DecLE
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map (fun ω => Λ i (Z ω)) μ))
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.dirac (1 : ℝ))))
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f → ScalarMonotone.DecLE
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ))
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.dirac (1 : ℝ))))
    {φ : E → ℝ} (hφ : Measurable φ)
    (hmod : ∀ z w, dist (φ z) (φ w) ≤ dist z w*(∏ i, max (Λ i z) (Λ i w)))
    {r C : ℝ} (hr : 1 ≤ r) (hC : (2 : ℝ)^(-1/r) < C) :
    ¬ ENNReal.ofReal C ≤ MeasureTheory.eLpNorm (fun ω => φ (Z ω)-φ (Z' ω)) (ENNReal.ofReal r) μ := by
  exact ScalarMonotone.EndOfPaper.unit_profile_no_larger_coefficient
    hn hZ hZ' hi he hΛm hΛ0 hQ hδ hφ hmod hr hC

example (n : ℕ) :
    (∀ f : ℝ → ℝ, LipschitzWith 1 f → ScalarMonotone.DecLE
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map (fun z : ℝ × ℝ => |f z.1-f z.2|)
        (ScalarMonotone.symmetricBernoulli.prod ScalarMonotone.symmetricBernoulli)))
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.dirac (1 : ℝ)))) ∧
    (∀ _i : Fin n, ScalarMonotone.DecLE
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map (fun _ : ℝ × ℝ => (1 : ℝ))
        (ScalarMonotone.symmetricBernoulli.prod ScalarMonotone.symmetricBernoulli)))
      (ScalarMonotone.tailQuantile (MeasureTheory.Measure.dirac (1 : ℝ)))) ∧
    (∀ z w : ℝ, dist z w ≤ dist z w*(∏ _i : Fin n, max (1 : ℝ) 1)) ∧
    (∀ r : ℝ, 0 < r →
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r)
        ∂(ScalarMonotone.symmetricBernoulli.prod ScalarMonotone.symmetricBernoulli)) = ENNReal.ofReal (1/2 : ℝ) ∧
      MeasureTheory.eLpNorm (fun z : ℝ × ℝ => z.1-z.2) (ENNReal.ofReal r)
        (ScalarMonotone.symmetricBernoulli.prod ScalarMonotone.symmetricBernoulli) =
        ENNReal.ofReal ((2 : ℝ)^(-1/r))*MeasureTheory.eLpNorm
          (fun _ : ℝ => (1 : ℝ)*(∏ _i : Fin n, (1 : ℝ))) (ENNReal.ofReal r) ScalarMonotone.unitUniform) := by
  refine ⟨ScalarMonotone.EndOfPaper.bernoulli_unit_profile_baseline,
    (fun _ => ScalarMonotone.EndOfPaper.unit_profile_constant_control _),
    ScalarMonotone.EndOfPaper.bernoulli_unit_profile_modulus n,?_⟩
  intro r hr
  rw [ScalarMonotone.EndOfPaper.unit_profile_product_norm_one n hr,mul_one]
  exact ⟨ScalarMonotone.EndOfPaper.symmetricBernoulli_copy_moment hr,
    ScalarMonotone.EndOfPaper.symmetricBernoulli_copy_norm hr⟩

example (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z : ℝ × ℝ, |z.1-z.2| ∂(ν.prod ν)) =
      2*(∫ t in Set.Ioo (0 : ℝ) 1, ProbabilityTheory.cdf ν t*(1-ProbabilityTheory.cdf ν t)) := by
  exact ScalarMonotone.EndOfPaper.copy_moment_cdf_unit_interval ν hsupport


-- Reader convention: `none` is the baseline and `some i` is control i.
-- The input is the literal product over all n+1 prescribed selections.
example {n : ℕ} (hn : 0 < n) (Q : Option (Fin n) → ScalarMonotone.DecGraph)
    (hdom : ∀ j, interior (ScalarMonotone.dom (Q j).val) = Set.Ioo (0 : ℝ) 1)
    (h0 : ∀ j p, p ∈ Set.Ioo (0 : ℝ) 1 → ∀ t ∈ (Q j).val p, 0 ≤ t)
    (s : Option (Fin n) → ℝ → ℝ)
    (hsel : ∀ j, ScalarMonotone.EndOfPaper.SelectionOn (Q j).val (Set.Ioo (0 : ℝ) 1) (s j))
    (hlog : (∫⁻ u in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (∏ j, s j u)) 0)) < ∞) :
    ∃ E : Type, ∃ d : MetricSpace E,
      letI := d
      ∃ m : MeasurableSpace E,
      letI := m
      OpensMeasurableSpace E ∧
      ∃ ν : MeasureTheory.Measure E, MeasureTheory.IsProbabilityMeasure ν ∧
      ∃ Λ : Fin n → E → ℝ, ∃ φ : E → ℝ,
        (∀ i, Measurable (Λ i)) ∧ (∀ i z, 0 ≤ Λ i z) ∧ Measurable φ ∧
        (∀ z w, dist (φ z) (φ w) ≤ dist z w*(∏ i, max (Λ i z) (Λ i w))) ∧
        (ProbabilityTheory.IndepFun (Prod.fst : E × E → E) Prod.snd (ν.prod ν) ∧
          ProbabilityTheory.IdentDistrib (Prod.fst : E × E → E) Prod.snd (ν.prod ν) (ν.prod ν)) ∧
        (∀ f : E → ℝ, LipschitzWith 1 f →
          ScalarMonotone.DecLE
            (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map
              (fun z : E × E => |f z.1-f z.2|) (ν.prod ν))) (Q none).val) ∧
        (∀ i, ScalarMonotone.DecLE
          (ScalarMonotone.tailQuantile (MeasureTheory.Measure.map
            (fun z : E × E => Λ i z.1) (ν.prod ν))) (Q (some i)).val) ∧
        (∀ r : ℝ, 0 < r →
          ENNReal.ofReal ((2 : ℝ)^(-1/r))*
            MeasureTheory.eLpNorm (fun u => ∏ j, s j u) (ENNReal.ofReal r) ScalarMonotone.unitUniform ≤
          MeasureTheory.eLpNorm (fun z : E × E => φ z.1-φ z.2)
            (ENNReal.ofReal r) (ν.prod ν)) := by
  have hCombined : (∫⁻ u in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (s none u*(∏ i : Fin n, s (some i) u))) 0)) < ∞ := by
    simpa only [Fintype.prod_option] using hlog
  simpa only [Fintype.prod_option] using
    ScalarMonotone.EndOfPaper.randomized_lipschitz_moment_lower hn (hdom none) (h0 none)
      (fun i => hdom (some i)) (fun i => h0 (some i)) (hsel none)
      (fun i => hsel (some i)) hCombined


-- Independent original-hypothesis checks for the centering remark.
section RandomizedCenteringExpected
variable {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sδ)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ p*(∏ i, s i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
include hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hsδ hs hP hΦ hmod

-- The sharper actual product profile, with completion and probability u/6.
example {g : F → ℝ} (hg : LipschitzWith 1 g)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
    (m : ℝ) (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hs hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hs hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hs hPi
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-m|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/6)
          (completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1).val)) :=
  (randomized_lipschitz_centering hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg).1 hnδ hnq m hm

-- Both zero-input cases force zero distance to every actual median.
example {g : F → ℝ} (hg : LipschitzWith 1 g) (m : ℝ)
    (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m)
    (hz : (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) :
    (fun ω => |g (Φ (Z ω))-m|) =ᵐ[μ] (fun _ => 0) :=
  (randomized_lipschitz_centering hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg).2.1 m hm hz

-- Every r>0 median bound, with the finite ordinary real norm explicitly checked.
example {g : F → ℝ} (hg : LipschitzWith 1 g) {m : ℝ}
    (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m) {r : ℝ} (hr : 0 < r)
    (hM : MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ∧
      (eLpNorm (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ).toReal ≤
        (6*Real.exp 1)^(1/r)*
          (eLpNorm (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform).toReal :=
  randomized_lipschitz_median_real_moment_bound hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg hm hr hM

-- Integrability is part of the conclusion, followed by the exact norm chain.
example {g : F → ℝ} (hg : LipschitzWith 1 g) {r : ℝ} (hr : 1 ≤ r)
    (hM : MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :
    Integrable (fun ω => g (Φ (Z ω))) μ ∧
      MemLp (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ≤
        eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform :=
  (randomized_lipschitz_centering hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg).2.2.2 r hr hM

example {g : F → ℝ} (hg : LipschitzWith 1 g) {r : ℝ} (hr : 1 ≤ r)
    (hM : MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :
    Integrable (fun ω => g (Φ (Z ω))) μ ∧
      MemLp (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ∧
      (eLpNorm (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ).toReal ≤
        (3*Real.exp 1)^(1/r)*
          (eLpNorm (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform).toReal :=
  randomized_lipschitz_mean_real_moment_bound hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg hr hM
end RandomizedCenteringExpected


-- The fresh point space carries the literal distance from the lower-model
-- appendix. Its metric axioms and product injection are proved, not premises.
example {n : ℕ} {C : Set (Option (Fin n) → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) (x y : PositiveProductPoint C) :
    letI := positiveChainMetric h0 hp hc
    dist x y = |(∏ j, x.coords j)-(∏ j, y.coords j)| /
      (∏ i : Fin n, max (x.coords (some i)) (y.coords (some i))) :=
  positiveChainMetric_distance h0 hp hc x y


example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → ℝ} (hX : Measurable X) (hX' : Measurable X')
    (hi : ProbabilityTheory.IndepFun X X' μ) (he : ProbabilityTheory.IdentDistrib X X' μ μ)
    {m t : ℝ} (hm : IsRealMedian X μ m) (ht : 0 < t) :
    μ.real {ω | m+t < X ω} ≤ μ.real {ω | t < |X ω-X' ω|} :=
  upper_median_independent_copy_tail hX hX' hi he hm ht.le



-- Original inputs and single combined area for the stronger unequal-level
-- conclusions. Arbitrary selections at every jump level are allowed.
section RandomizedUnequalExpected
variable {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sδ)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ p*(∏ i, s i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
include hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hnδ hnq hsδ hs hP hΦ hmod

example {g : F → ℝ} (hg : LipschitzWith 1 g) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hs hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hs hPi
    ∀ γ : ℝ → ℝ, SelectionOn G.val (Ioo (0 : ℝ) 1) γ →
      sInf (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) p) ≤
        sInf {t : ℝ | ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 < b ∧ a+2*b ≤ p ∧ t = sδ a*γ b} :=
  randomized_lipschitz_optimized hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hnδ hnq hsδ hs hP hΦ hmod hg hp

example {g : F → ℝ} (hg : LipschitzWith 1 g) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hs hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hs hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hs hPi
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/3)
          (completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1).val)) :=
  randomized_lipschitz_sharper_bound hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hnδ hnq hsδ hs hP hΦ hmod hg

example {g : F → ℝ} (hg : LipschitzWith 1 g)
    {a b t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (ht : t ∈ qΔ.val a) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hs hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hs hPi
    ∀ v ∈ G.val b, μ.real {ω | t*v < |g (Φ (Z ω))-g (Φ (Z' ω))|} ≤ a+2*b :=
  randomized_lipschitz_two_parameter_geometric hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hnδ hnq hsδ hs hP hΦ hmod hg ha hb ht
end RandomizedUnequalExpected


-- Actual independent-copy Jensen comparison on the original space; its
-- finite-moment hypotheses are discharged by the randomized centering wrapper.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → ℝ} (hX : Measurable X) (hX' : Measurable X')
    (hi : ProbabilityTheory.IndepFun X X' μ) (he : ProbabilityTheory.IdentDistrib X X' μ μ)
    {r : ℝ} (hr : 1 ≤ r) (hMem : MemLp X (ENNReal.ofReal r) μ)
    (hGap : MemLp (fun ω => |X ω-X' ω|) (ENNReal.ofReal r) μ) :
    MemLp (fun ω => X ω-∫ ω', X ω' ∂μ) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => X ω-∫ ω', X ω' ∂μ) (ENNReal.ofReal r) μ ≤
        eLpNorm (fun ω => |X ω-X' ω|) (ENNReal.ofReal r) μ :=
  independent_copy_mean_norm hX hX' hi he hr hMem hGap

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) : ∃ m : ℝ, IsRealMedian X μ m :=
  exists_realMedian hX

section RandomizedMedianExpected
variable {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sδ)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ p*(∏ i, s i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
include hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hsδ hs hP hΦ hmod

example {g : F → ℝ} (hg : LipschitzWith 1 g)
    {m : ℝ} (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m) {r : ℝ} (hr : 0 < r)
    (hM : MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((6*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform :=
  randomized_lipschitz_median_moment_bound hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg hm hr hM

example {g : F → ℝ} (hg : LipschitzWith 1 g) {r : ℝ} (hr : 0 < r)
    (hM : MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => g (Φ (Z ω))) (ENNReal.ofReal r) μ :=
  randomized_lipschitz_value_memLp hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg hr hM
end RandomizedMedianExpected


-- The constructed metric has the literal weighted product distance.
-- The full prescribed-profile random model remains a separate obligation.
example {α : Type*} [LinearOrder α] (A P : α → ℝ)
    (hA : Monotone A) (hP : Monotone P) (hA0 : ∀ x, 0 ≤ A x) (hP0 : ∀ x, 0 ≤ P x)
    (hi : Function.Injective (fun x => A x*P x)) (x y : α) :
    letI := weightedChainMetric A P hA hP hA0 hP0 hi
    dist x y = |A x*P x-A y*P y|/max (P x) (P y) := rfl

example {ι : Type*} [Fintype ι] {C : Set (ι → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) :
    Set.InjOn (fun x : ι → ℝ => ∏ i, x i) C :=
  product_injective_on_positive_or_zero_chain h0 hp hc

example {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hc : x ≤ y ∨ y ≤ x) (i : ι) :
    |x i-y i| * (∏ j ∈ Finset.univ.erase i, x j) ≤ |(∏ j, x j)-(∏ j, y j)| :=
  coordinate_gap_mul_le_product_gap hx hy hc i

example {x y P Q : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hP : 0 ≤ P) (hPQ : P ≤ Q) (hQ : 0 < Q)
    (hd : orderedChainGap x P y Q < x/2) :
    |y*Q-x*P| ≤ 2*P*orderedChainGap x P y Q :=
  orderedChainGap_local_product_bound hx hxy hP hPQ hQ hd



-- Lower endpoints are attained, and resolvent comparison bounds the actual
-- minimum by every selected value, including multivalued jump fibers.
example (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IsLeast (tailQuantile ν p) (sInf (tailQuantile ν p)) :=
  quantile_lower_endpoint_isLeast ν hp

example (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : Operator}
    (hq : MaximalDecreasing q) (h : DecLE (tailQuantile ν) q)
    {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : t ∈ q p) :
    sInf (tailQuantile ν p) ≤ t :=
  quantile_lower_endpoint_le_of_decLE ν hq h hp ht

-- Equal levels recover the literal binary product followed by one completed
-- probability dilation, as a whole graph, rather than only almost everywhere.
example {q r : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ r.val x, 0 ≤ v)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    {s t : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (ht : SelectionOn r.val (Ioo (0 : ℝ) 1) t) :
    (completedUnequalProfileProduct q r hqi hri hq0 hr0 hc hc).val =
      completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation c (completedProfileProduct 1 q r (by norm_num) hqi hri hq0 hr0).val) :=
  completedUnequalProfileProduct_equal_dilation hqi hri hq0 hr0 hc hs ht

-- This bundle's value is the actual geometric transform of the literal finite
-- input graph product. No closure of the output class is assumed.
example {ι : Type*} [Fintype ι] (q : ι → DecGraph)
    (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val x, 0 ≤ v)
    {s : ι → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hPi : ∀ i, (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞) :
    (geometricFiniteProfileProduct q hqi hq0 hs hPi).val =
      geometricHardyTransform 1 (completedFiniteProfileProduct 1 q (by norm_num) hqi hq0) := rfl

-- The exact original median definition and both independent-copy comparisons.
example {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (μ : Measure Ω) (m : ℝ) :
    IsRealMedian X μ m ↔
      (1/2 : ℝ) ≤ μ.real {ω | X ω ≤ m} ∧ (1/2 : ℝ) ≤ μ.real {ω | m ≤ X ω} := Iff.rfl

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → ℝ} (hX : Measurable X) (hX' : Measurable X')
    (hi : ProbabilityTheory.IndepFun X X' μ) (he : ProbabilityTheory.IdentDistrib X X' μ μ)
    {m t : ℝ} (hm : IsRealMedian X μ m) (ht : 0 < t) :
    μ.real {ω | t < |X ω-m|} ≤ 2*μ.real {ω | t < |X ω-X' ω|} ∧
      ∀ c : ℝ, μ.real {ω | t < |X ω-X' ω|} ≤ 2*μ.real {ω | t/2 < |X ω-c|} :=
  ⟨median_independent_copy_tail hX hX' hi he hm ht.le,fun c => independent_copy_pivot_tail he c t⟩

-- A nonnegative strict-tail comparison by a factor K yields exactly the
-- completed probability dilation c/K, including endpoints and jumps.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val p, 0 ≤ v)
    {c K : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (hK : 1 ≤ K)
    (hcomp : DecLE (tailQuantile (Measure.map X μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1) (positiveInputDilation c q.val)))
    (ht : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < Y ω} ≤ K*μ.real {ω | t < X ω}) :
    DecLE (tailQuantile (Measure.map Y μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1) (positiveInputDilation (c/K) q.val)) :=
  quantile_tail_multiplier_dilation hX hY hqi hq0 hc hK hcomp ht

-- The actual ordered-triple inequalities used to construct the lower metric.
-- This does not claim that the metric or probabilistic model is constructed.
example {x y z P Q R : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hP : 0 ≤ P) (hPQ : P ≤ Q) (hQ : 0 < Q) (hQR : Q ≤ R) :
    max (z-y*Q/R) (y-x*P/Q) ≤ z-x*P/R ∧
      z-x*P/R ≤ (y-x*P/Q)+(z-y*Q/R) := by
  simpa only [orderedChainGap,max_comm] using orderedChainGap_metric_bounds hx hxy hyz hP hPQ hQ hQR


-- The original randomized Lipschitz hypotheses, with one combined log area.
-- Input selections are arbitrary; finite moments are required only for the
-- separate moment conclusions. All zero-input cases remain present.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun ω => |X ω|) p μ = eLpNorm X p μ := by
  simpa only [Real.norm_eq_abs] using (eLpNorm_norm (p := p) (μ := μ) X)

section RandomizedControlExpected
variable {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sδ)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ p*(∏ i, s i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
include hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hsδ hs hP hΦ hmod

example {g : F → ℝ} (hg : LipschitzWith 1 g) :
    let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
    let X := fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|
    ((¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∧
      (∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) →
      DecLE (tailQuantile (Measure.map X μ))
        (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
          (positiveInputDilation (1/3) (geometricHardyTransform 1 P)))) ∧
    (((∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) → X =ᵐ[μ] (fun _ => 0)) ∧
    (∀ r : ℝ, 0 < r → MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform →
      MemLp X (ENNReal.ofReal r) μ ∧ eLpNorm X (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :=
  randomized_lipschitz_control hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg

example {g : F → ℝ} (hg : LipschitzWith 1 g) {r : ℝ} (hr : 0 < r)
    (hM : MemLp (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ∧
      (eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ).toReal ≤
        (3*Real.exp 1)^(1/r)*
          (eLpNorm (fun p => sδ p*(∏ i, s i p)) (ENNReal.ofReal r) unitUniform).toReal :=
  randomized_lipschitz_real_moment_bound hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hsδ hs hP hΦ hmod hg hr hM
end RandomizedControlExpected


-- The actual combined input profile is the finite interior graph product
-- of the baseline and every control profile, followed by maximal completion.
example {n : ℕ} (qΔ : DecGraph) (q : Fin n → DecGraph)
    (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v) :
    randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0 =
      (let Q : Option (Fin n) → DecGraph := fun j => match j with | none => qΔ | some i => q i
       let hD : ∀ j, interior (dom (Q j).val) = Ioo (0 : ℝ) 1 := fun j => by
         cases j with
         | none => exact hδdom
         | some i => exact hqdom i
       let h0 : ∀ j p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (Q j).val p, 0 ≤ v := fun j => by
         cases j with
         | none => exact hδ0
         | some i => exact hq0 i
       completedFiniteProfileProduct 1 Q (by norm_num) hD h0) := rfl

-- The original completed geometric graph bound, with the original
-- single combined positive-log area and arbitrary input selections.
example {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sδ)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sδ p*(∏ i, s i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {g : F → ℝ} (hg : LipschitzWith 1 g) :
    let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/3) (geometricHardyTransform 1 P))) :=
  randomized_lipschitz_geometric_bound hn hZ hZ' hi he hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ
    hnδ hnq hsδ hs hP hΦ hmod hg


-- The whole finite geometric product law uses actual interior graph
-- products followed by their unique maximal completion on both sides.
example {n : ℕ} (_hn : 0 < n) {q : Fin n → DecGraph}
    (hdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (h0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i p)) 0)) < ∞) :
    let hB : (0 : ℝ) < 1 := by norm_num
    let P := completedFiniteProfileProduct 1 q hB hdom h0
    let hG := fun i => geometricHardyTransform_well_defined_any_selection hB (hdom i) (h0 i) (hs i) (hP i)
    let G : Fin n → DecGraph := fun i => ⟨geometricHardyTransform 1 (q i),(hG i).1⟩
    geometricHardyTransform 1 P =
      (completedFiniteProfileProduct 1 G hB (fun i => (hG i).2.1) (fun i => (hG i).2.2.1)).val :=
  geometric_hardy_finite_product (by norm_num) hdom h0 hs hP

example {ι : Type*} [Fintype ι] {q : ι → DecGraph} {s : ι → ℝ → ℝ}
    (hdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (h0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hP : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i p)) 0)) < ∞)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    geometricPrefixValue (fun u => ∏ i, s i u) p = ∏ i, geometricPrefixValue (s i) p :=
  geometricPrefixValue_finite_product (by norm_num) hdom h0 hs hP hp

-- The general extended moment consequence. No finite moment, global
-- log L1 or global measurability of the input selection is assumed.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    {q : DecGraph} (hdom : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (h0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val p, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s p)) 0)) < ∞)
    {c r : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (hr : 0 < r)
    (hQ : DecLE (tailQuantile (Measure.map X μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation c (geometricHardyTransform 1 q)))) :
    (∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ) ≤
      ENNReal.ofReal (Real.exp 1/c)*(∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((s p)^r)) :=
  geometric_quantile_moment_bound μ hX hX0 hdom h0 hs hP hc hr hQ

example {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hXm : Measurable X) (hX0 : 0 ≤ᵐ[μ] X) (hY0 : 0 ≤ᵐ[ν] Y)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hb : (∫⁻ ω, ENNReal.ofReal ((X ω)^r) ∂μ) ≤
      ENNReal.ofReal C*(∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂ν))
    (hY : MemLp Y (ENNReal.ofReal r) ν) :
    MemLp X (ENNReal.ofReal r) μ ∧ eLpNorm X (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (C^(r⁻¹))*eLpNorm Y (ENNReal.ofReal r) ν :=
  ⟨memLp_of_nonnegative_moment_bound hXm hX0 hY0 hr hC hb hY,
    eLpNorm_le_of_nonnegative_moment_bound hX0 hY0 hr hC hb⟩


-- The literal finite graph product is formed on the interior before
-- completion, retaining every admissible choice of coordinate values.
example {ι : Type*} [Fintype ι] (q : ι → Operator) (B x v : ℝ) :
    v ∈ interiorFiniteProfileProduct B q x ↔ x ∈ Ioo (0 : ℝ) B ∧
      ∃ a : ι → ℝ, (∀ i, a i ∈ q i x) ∧ v = ∏ i, a i := Iff.rfl

example {ι : Type*} [Fintype ι] {q : ι → DecGraph} {B : ℝ} (hB : 0 < B)
    (hdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (h0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v)
    {f : Operator} (hf : MaximalDecreasing f)
    (hraw : interiorFiniteProfileProduct B (fun i => (q i).val) ≤ f)
    (hfd : dom f ⊆ closure (Ioo (0 : ℝ) B)) :
    f = (completedFiniteProfileProduct B q hB hdom h0).val :=
  completedFiniteProfileProduct_unique hB hdom h0 hf hraw hfd

example {q : DecGraph} {s : ℝ → ℝ} {p u : ℝ}
    (hdom : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (h0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hu : u ∈ q.val p) : u ≤ geometricPrefixValue s p :=
  profile_value_le_geometricPrefixValue hdom h0 hs hP hp hu

-- Both actual zero-input cases, for a 1-Lipschitz observation of the
-- original metric-valued map. No control moment assumption is added.
example {n : ℕ} (_hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [MetricSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hδdom : interior (dom qΔ) = Ioo (0 : ℝ) 1)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → Operator} (hqdom : ∀ i, interior (dom (q i)) = Ioo (0 : ℝ) 1)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    {Φ : E → F} (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (hz : (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q i p, v = 0)
    {g : F → ℝ} (hg : LipschitzWith 1 g) :
    (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) =ᵐ[μ] (fun _ => 0) :=
  randomized_lipschitz_zero_input hZ hZ' he hδ
    (fun p hp => interior_subset (show p ∈ interior (dom qΔ) from by rwa [hδdom]))
    hΛm hΛ0 (fun i p hp => interior_subset (show p ∈ interior (dom (q i)) from by rwa [hqdom i]))
    hQ hmod hz hg

-- The exact two-parameter scalar estimate, with the original single
-- combined log-area assumption and arbitrary input selections.
example {n : ℕ} (_hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hqΔ : MaximalDecreasing qΔ) (hδdom : interior (dom qΔ) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → Operator} (hq : ∀ i, MaximalDecreasing (q i))
    (hqdom : ∀ i, interior (dom (q i)) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i))
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q i p, v = 0)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {g : F → ℝ} (hg : LipschitzWith 1 g)
    {a b t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (ht : t ∈ qΔ a) :
    μ.real {ω | (∏ i, geometricPrefixValue (sq i) b)*t < |g (Φ (Z ω))-g (Φ (Z' ω))|} ≤ a+2*b := by
  have hscalar : ∀ x y, |g (Φ x)-g (Φ y)| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)) := by
    intro x y
    exact (show |g (Φ x)-g (Φ y)| ≤ dist (Φ x) (Φ y) from by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hg.dist_le_mul (Φ x) (Φ y)).trans (hmod x y)
  exact randomized_lipschitz_two_parameter hZ hZ' hi he hqΔ hδdom hδ0 hδ hΛm hΛ0
    hq hqdom hq0 hQ hnδ hnq hsδ hsq hP (hg.continuous.measurable.comp hΦ) hscalar ha hb ht


-- The zero baseline case needs neither a separability assumption nor
-- a moment bound on the controls. Countably many extensions suffice.
example {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z') {qΔ : Operator}
    (hQ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    (hdom : Ioo (0 : ℝ) 1 ⊆ dom qΔ)
    (hz : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, v = 0)
    {h : E → ℝ} {Λ : ι → E → ℝ} (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y))) :
    (fun ω => h (Z ω)) =ᵐ[μ] (fun ω => h (Z' ω)) := by
  have hzero : ∀ p ∈ Ioo (0 : ℝ) 1, (0 : ℝ) ∈ qΔ p := by
    intro p hp
    obtain ⟨v,hv⟩ := hdom hp
    simpa only [hz p hp v hv] using hv
  exact ae_difference_zero_of_bounded_control_extensions hΛ0 hmod
    (fun K hK f hf => lipschitz_difference_zero_of_quantile_zero hZ hZ' hQ hzero hK hf)

example {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z Z' : Ω → E} (hZ : Measurable Z) (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {Λ : ι → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {h : E → ℝ} (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    (i : ι) {q : Operator} {b : ℝ}
    (hQ : DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) q)
    (hb : (0 : ℝ) ∈ q b) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ < |h (Z ω)-h (Z' ω)|} ≤ 2*b :=
  randomized_zero_cutoff_tail hZ he hΛm hΛ0 hmod i hQ hb hτ

-- The single combined area controls all factors for arbitrary selections;
-- their global measurability is derived, not a final hypothesis.
example {ι : Type*} [Fintype ι] {q : ι → Operator} {sq : ι → ℝ → ℝ}
    (hq : ∀ i, MaximalDecreasing (q i))
    (h0 : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i x, 0 ≤ v)
    (hn : ∀ i, ¬ ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q i x, v = 0)
    (hs : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (∏ i, sq i x)) 0)) < ∞) :
    ∀ i, (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i x)) 0)) < ∞ :=
  nonzero_profiles_individual_log_areas (by norm_num) hq h0 hn hs hP

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {q : Operator} (hq : MaximalDecreasing q)
    (hdom : interior (dom q) = Ioo (0 : ℝ) 1)
    {sq : ℝ → ℝ} (hs : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    (hb : ∀ p ∈ Ioo (0 : ℝ) 1, μ.real {ω | sq p < X ω} ≤ p) :
    DecLE (tailQuantile (Measure.map X μ)) q :=
  tailQuantile_decLE_of_profile_selection_tail_bounds hX hq hdom hs hb

example {q : Operator} {sq : ℝ → ℝ} {b c : ℝ} (hq : Decreasing q)
    (hm : Measurable sq) (hs : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    (h0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p)) 0)) < ∞)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hcb : c ∈ q b) :
    geometricPrefixValue sq b = c*Real.exp ((∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq p/c)) 0)/b) :=
  geometricPrefixValue_log_excess hq hm hs h0 hP hb hc hcb


-- The combined product-area implication is derived using an actual
-- common positive point of the nonzero input profiles.
example {ι : Type*} [Fintype ι] {q : ι → Operator} {sq : ι → ℝ → ℝ}
    (hq : ∀ i, MaximalDecreasing (q i)) (hm : ∀ i, Measurable (sq i))
    (hs : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) 1) (sq i))
    (h0 : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ q i x, 0 ≤ v)
    (hn : ∀ i, ¬ ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q i x, v = 0)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (∏ i, sq i x)) 0)) < ∞) :
    ∀ i, (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i x)) 0)) < ∞ := by
  obtain ⟨b,hb,hb0⟩ := nonzero_profiles_common_positive_point (by norm_num) hq h0 hn hs
  exact positive_log_areas_of_finite_product hm
    (fun i => selection_antitoneOn (hq i).1 (hs i))
    (fun i x hx => h0 i x hx (sq i x) (hs i x hx)) hb hb0 hP

example {q : Operator} {sq : ℝ → ℝ} {b c : ℝ} (hq : Decreasing q)
    (hm : Measurable sq) (hs : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    (h0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q x, 0 ≤ v)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hc : 0 < c) (hcb : c ∈ q b) :
    IntegrableOn (fun x => max (Real.log (sq x/c)) 0) (Ioo (0 : ℝ) 1) volume ∧
      (∫ x in Ioo (0 : ℝ) 1, max (Real.log (sq x/c)) 0) =
        (∫ x in Ioo (0 : ℝ) b, Real.log (sq x))-b*Real.log c :=
  profile_log_excess_integral hq hm hs h0 hP hb hc hcb

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    {q : Operator} (hq : MaximalDecreasing q) (hdom : Ioo (0 : ℝ) 1 ⊆ dom q)
    (h0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q p, 0 ≤ v)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {sq : ℝ → ℝ} (hm : Measurable sq) (hs : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    {c : ℝ} (hc : 0 < c)
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq p/c)) 0)) < ∞) :
    Integrable (fun ω => max (Real.log (X ω/c)) 0) μ ∧
      (∫ ω, max (Real.log (X ω/c)) 0 ∂μ) ≤
        ∫ p in Ioo (0 : ℝ) 1, max (Real.log (sq p/c)) 0 :=
  ⟨logarithmic_excess_integrable μ hX hX0 hq hdom h0 hQ hs hc hP,
    logarithmic_excess_mean_bound μ hX hX0 hq hdom h0 hQ hm hs hc hP⟩

-- Both the zero-area and zero-threshold cases are included.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {C t a b I : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hb : 0 < b) (hI : 0 ≤ I)
    (hB : ∀ s : ℝ, 0 < s → μ.real {ω | C*Real.exp s*t < X ω} ≤ a+2*I/s) :
    μ.real {ω | C*Real.exp (I/b)*t < X ω} ≤ a+2*b :=
  logarithmic_tail_budget hX hC ht hb hI hB


-- The original endpoint theorem: arbitrary original probability space,
-- independent copy, domain inclusion, and finite nonnegative expectation.
example {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hi : ProbabilityTheory.IndepFun Z Z' μ)
    (he : ProbabilityTheory.IdentDistrib Z Z' μ μ)
    {qΔ : Operator} (hq : MaximalDecreasing qΔ)
    (hdom : Ioo (0 : ℝ) 1 ⊆ interior (dom qΔ))
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ p, 0 ≤ v)
    (hQ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ)
    {h U : E → ℝ} (hh : Measurable h) (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hm : (∫⁻ ω, ENNReal.ofReal (U (Z ω)) ∂μ) < ∞)
    {C : ℝ} (hC : 0 < C)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y)
    {a s t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (ht : t ∈ qΔ a) :
    μ.real {ω | C*Real.exp s*t < |h (Z ω)-h (Z' ω)|} ≤
      a+2*(∫ ω, U (Z ω) ∂μ)/s :=
  logarithmic_endpoint_control hZ hZ' hi he hq hdom hq0 hQ hh hU hU0 hm hC hmod ha hs ht

example {ι E : Type*} [Fintype ι] [MetricSpace E]
    {h : E → ℝ} {Λ : ι → E → ℝ} {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hΛ : ∀ i x, 0 ≤ Λ i x)
    (hmod : ∀ x y, |h x-h y| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y))) :
    ∀ x y, |h x-h y| ≤ (∏ i, c i)*Real.exp
      ((∑ i, max (Real.log (Λ i x/c i)) 0)+(∑ i, max (Real.log (Λ i y/c i)) 0))*dist x y :=
  randomized_modulus_logarithmic_form hc hΛ hmod

-- Marginal quantile comparison implies every extended nonnegative
-- monotone integral bound, even when either side is infinite.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {q : Operator} (hq : MaximalDecreasing q)
    (hdom : Ioo (0 : ℝ) 1 ⊆ dom q)
    (hQ : DecLE (tailQuantile (Measure.map X μ)) q)
    {sq : ℝ → ℝ} (hsq : SelectionOn q (Ioo (0 : ℝ) 1) sq)
    {ψ : ℝ → ℝ≥0∞} (hm : Measurable ψ) (hmono : Monotone ψ) :
    (∫⁻ ω, ψ (X ω) ∂μ) ≤ ∫⁻ p in Ioo (0 : ℝ) 1, ψ (sq p) :=
  random_variable_profile_lintegral_bound μ hX hq hdom hQ hsq hm hmono


-- Exact cutoff averaging on the original probability space.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : Set Ω} (hD : MeasurableSet D) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hu0 : ∀ ω, 0 ≤ u ω) (hv0 : ∀ ω, 0 ≤ v ω)
    (hui : Integrable u μ) (hvi : Integrable v μ) {s a : ℝ} (hs : 0 < s)
    (hcut : ∀ r ∈ Ioo (0 : ℝ) s,
      μ.real {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r} ≤ a) :
    μ.real D ≤ a+((∫ ω, u ω ∂μ)+(∫ ω, v ω ∂μ))/s :=
  cutoff_averaging_tail_bound hD hu hv hu0 hv0 hui hvi hs hcut

-- Scaling a globally Lipschitz test uses the actual marginal quantile
-- comparison and an arbitrary graph point; no integrability is assumed.
example {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z Z' : Ω → E} (hZ : Measurable Z) (hZ' : Measurable Z') {q : Operator}
    (hQ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) q)
    {a t : ℝ} (ht : t ∈ q a) {K : NNReal} (hK : 0 < (K : ℝ))
    {f : E → ℝ} (hf : LipschitzWith K f) :
    μ.real {ω | (K : ℝ)*t < |f (Z ω)-f (Z' ω)|} ≤ a :=
  scaled_lipschitz_tail_of_quantile_control hZ hZ' hQ ht hK hf

example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hi : ProbabilityTheory.IndepFun Z Z' μ)
    (he : ProbabilityTheory.IdentDistrib Z Z' μ μ) :
    ProbabilityTheory.IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ :=
  independent_copy_exchangeable hi he

-- Both extremal tails yield a single copy of the comparison probability.
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hs : ProbabilityTheory.IdentDistrib (fun ω => (Z ω,Z' ω)) (fun ω => (Z' ω,Z ω)) μ μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {h l u : E → ℝ} (hh : Measurable h) (hl : Measurable l) (hu : Measurable u)
    (heL : EqOn h l A) (heU : EqOn h u A)
    (hb : ∀ x ∈ B, l x ≤ h x ∧ h x ≤ u x) {τ a : ℝ} (ha : 0 ≤ a)
    (hTL : μ.real {ω | τ < |l (Z ω)-l (Z' ω)|} ≤ a)
    (hTU : μ.real {ω | τ < |u (Z ω)-u (Z' ω)|} ≤ a) :
    μ.real {ω | τ < |h (Z ω)-h (Z' ω)| ∧ Z ω ∈ A ∧ Z' ω ∈ B} ≤ a :=
  exchangeable_two_set_tail_bound hZ hZ' hs hA hB hAB hh hl hu heL heU hb ha hTL hTU


-- The original unit-interval identity for actual completed interior graph
-- products. The two measurable representatives and all output properties
-- are derived; the original selections are arbitrary.
example {q r : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ r.val x, 0 ≤ v)
    {sq sr : ℝ → ℝ} (hqs : SelectionOn q.val (Ioo (0 : ℝ) 1) sq)
    (hrs : SelectionOn r.val (Ioo (0 : ℝ) 1) sr)
    (hPq : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hPr : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sr x)) 0)) < ∞) :
    let hB : (0 : ℝ) < 1 := by norm_num
    let P := completedProfileProduct 1 q r hB hqi hri hq0 hr0
    let hGq := geometricHardyTransform_well_defined_any_selection hB hqi hq0 hqs hPq
    let hGr := geometricHardyTransform_well_defined_any_selection hB hri hr0 hrs hPr
    let Gq : DecGraph := ⟨geometricHardyTransform 1 q,hGq.1⟩
    let Gr : DecGraph := ⟨geometricHardyTransform 1 r,hGr.1⟩
    geometricHardyTransform 1 P =
      (completedProfileProduct 1 Gq Gr hB hGq.2.1 hGr.2.1 hGq.2.2.1 hGr.2.2.1).val :=
  geometric_hardy_product (by norm_num) hqi hri hq0 hr0 hqs hrs hPq hPr

example {s t : ℝ → ℝ} {p : ℝ} (hms : Measurable s) (hmt : Measurable t)
    (hs0 : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ s x) (ht0 : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ t x)
    (hPt : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞)
    (hNs : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x*t x)) = ∞ :=
  negative_log_area_mul_top_left hms hmt hs0 ht0 hPt hNs

example {f g : Operator} {B : ℝ} (hB : 0 < B)
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    (hgi : interior (dom g) = Ioo (0 : ℝ) B)
    {s t : ℝ → ℝ} (hs : SelectionOn f (Ioo (0 : ℝ) B) s)
    (ht : SelectionOn g (Ioo (0 : ℝ) B) t)
    (he : s =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] t) : f = g :=
  initial_profile_eq_of_selection_ae_eq hB hf hg hfi hgi hs ht he

example {E : Type*} [PseudoMetricSpace E] (A : Set E) (h : E → ℝ) (K : NNReal) (x : E) :
    upperLipschitzExtension A h K x = ⨅ z : A, h z+(K : ℝ)*dist x z := rfl

-- The deterministic two-extension ingredient of logarithmic endpoint
-- control. The probability bound and cutoff averaging remain separate.
example {E : Type*} [MetricSpace E] {h U : E → ℝ} {C r s : ℝ}
    (hC : 0 < C) (hrs : 2*r ≤ s) (hA : {x | U x ≤ r}.Nonempty)
    (hmod : ∀ x y, |h x-h y| ≤ C*Real.exp (U x+U y)*dist x y) :
    ∃ l u : E → ℝ,
      LipschitzWith (⟨C*Real.exp s,mul_nonneg hC.le (Real.exp_pos s).le⟩ : NNReal) l ∧
      LipschitzWith (⟨C*Real.exp s,mul_nonneg hC.le (Real.exp_pos s).le⟩ : NNReal) u ∧
      EqOn h l {x | U x ≤ r} ∧ EqOn h u {x | U x ≤ r} ∧
      ∀ y, U y ≤ s-r → l y ≤ h y ∧ h y ≤ u y :=
  two_level_lipschitz_brackets hC.le hrs hA hmod

open scoped Classical in
example {E : Type*} {A B : Set E} {h l u : E → ℝ}
    (hAB : A ⊆ B) (hL : EqOn h l A) (hU : EqOn h u A)
    (hbr : ∀ y ∈ B, l y ≤ h y ∧ h y ≤ u y) (x y : E) (τ : ℝ) :
    ((if τ < |h x-h y| ∧ x ∈ A ∧ y ∈ B then 1 else 0)+
        (if τ < |h x-h y| ∧ y ∈ A ∧ x ∈ B then 1 else 0) : ℝ≥0∞) ≤
      (if τ < |l x-l y| then 1 else 0)+(if τ < |u x-u y| then 1 else 0) :=
  bracket_two_tail_indicator_bound hAB hL hU hbr x y τ


-- The literal interior graph product, completed on its closed interval.
example {q r : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v) :
    (completedProfileProduct B q r hB hqi hri hq0 hr0).val =
      negOut (completion (Ioo (0 : ℝ) B) (negOut (fun x =>
        {v | x ∈ Ioo (0 : ℝ) B ∧ ∃ a ∈ q.val x, ∃ b ∈ r.val x, v = a*b}))) := rfl

example {q r : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v) :
    let P := completedProfileProduct B q r hB hqi hri hq0 hr0
    interior (dom P.val) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ a ∈ q.val x, ∀ b ∈ r.val x, a*b ∈ P.val x) ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ P.val x, 0 ≤ v) := by
  refine ⟨(completedProfileProduct_domain hB hqi hri hq0 hr0).1,?_,
    completedProfileProduct_nonnegative hB hqi hri hq0 hr0⟩
  intro x hx a ha b hb
  exact completedProfileProduct_raw_inclusion hB hqi hri hq0 hr0 x ⟨hx,a,ha,b,hb,rfl⟩

example {q r : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {f : Operator} (hf : MaximalDecreasing f)
    (hpf : ∀ x ∈ Ioo (0 : ℝ) B, ∀ a ∈ q.val x, ∀ b ∈ r.val x, a*b ∈ f x)
    (hfd : dom f ⊆ closure (Ioo (0 : ℝ) B)) :
    f = (completedProfileProduct B q r hB hqi hri hq0 hr0).val := by
  apply completedProfileProduct_unique hB hqi hri hq0 hr0 hf ?_ hfd
  rintro x v ⟨hx,a,ha,b,hb,rfl⟩
  exact hpf x hx a ha b hb


-- The input is exactly the maximal completion of the restricted dilation.
example {q : DecGraph} {B C c : ℝ}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hC : 0 < C) (hc : 0 < c) (hcover : c*C ≤ B) :
    (completedProfileDilation B C c q hqi hC hc hcover).val =
      negOut (completion (Ioo (0 : ℝ) C)
        (restrictOperator (negOut (fun x => q.val (c*x))) (Ioo (0 : ℝ) C))) := rfl

-- Whole completed identity on the manuscript J_c, from its original class
-- and arbitrary input selection. Neither global log L1 nor admissibility
-- of G(q) as another input is assumed.
example {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {c : ℝ} (hc : 0 < c) :
    let C := min (1 : ℝ) (1/c)
    let hC : 0 < C := lt_min zero_lt_one (one_div_pos.mpr hc)
    let hcover : c*C ≤ 1 := by
      calc
        c*min (1 : ℝ) (1/c) ≤ c*(1/c) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
        _ = 1 := by field_simp [hc.ne']
    geometricHardyTransform C (completedProfileDilation 1 C c q hqi hC hc hcover) =
      negOut (completion (Ioo (0 : ℝ) C)
        (restrictOperator (negOut (fun x => geometricHardyTransform 1 q (c*x))) (Ioo (0 : ℝ) C))) :=
  geometric_hardy_dilation hqi hq0 hs hP hc

example {F : ℝ → ℝ≥0∞} (hF : Measurable F) {c p : ℝ} (hc : 0 < c) :
    (∫⁻ x in Ioo (0 : ℝ) p, F (c*x)) =
      ENNReal.ofReal c⁻¹*(∫⁻ x in Ioo (0 : ℝ) (c*p), F x) :=
  lintegral_positive_prefix_dilation hF hc


-- The original all-power, all-prefix extended inequality. There is no
-- finite moment or global log-integrability hypothesis, and both selections
-- are arbitrary under the manuscript convention.
example {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s g : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hg : SelectionOn (geometricHardyTransform 1 q) (Ioo (0 : ℝ) 1) g)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a ∧ a ≤ 1) :
    (∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((g x)^r)) ≤
      ENNReal.ofReal (Real.exp 1)*(∫⁻ x in Ioo (0 : ℝ) a, ENNReal.ofReal ((s x)^r)) :=
  polya_knopp (by norm_num) hqi hq0 hs hg hP hr ha

-- The Tonelli estimate itself allows infinite nonnegative functions/integrals.
example {f : ℝ → ℝ≥0∞} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    (∫⁻ p in Ioo (0 : ℝ) a, ∫⁻ x in Ioo (0 : ℝ) p,
      ENNReal.ofReal ((p^2)⁻¹)*ENNReal.ofReal x*f x) ≤ ∫⁻ x in Ioo (0 : ℝ) a, f x :=
  knopp_weighted_lintegral_bound hf ha


-- Equality of whole completed graphs, including jumps and both endpoints.
example {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    geometricHardyTransform 1 q =
      negOut (completion (Ioo (0 : ℝ) 1)
        (restrictOperator (negOut (ofFun (fun p =>
          match extendedLogIntegral s p with
          | none => 0
          | some A => ((EReal.exp A)^(p⁻¹ : ℝ)).toReal))) (Ioo (0 : ℝ) 1))) :=
  geometric_hardy_scalar_completion (by norm_num) hqi hq0 hs hP

-- Finite positive-log area excludes the undefined signed-integral case
-- for every prefix, even when the originally chosen selection is not measurable.
example {q : DecGraph} {B p : ℝ}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) :
    ∃ A : EReal, extendedLogIntegral s p = some A :=
  extendedLogIntegral_defined_on_admissible_prefix hqi hs hP hp

example {q : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    ∀ p ∈ Ioo (0 : ℝ) B, geometricPrefixValue s p ∈ geometricHardyTransform B q p :=
  geometric_hardy_scalar_selection hB hqi hq0 hs hP

example {s : ℝ → ℝ} {p : ℝ} {A : EReal} (hA : extendedLogIntegral s p = some A) :
    geometricPrefixValue s p = (EReal.exp (A/(p : EReal))).toReal :=
  geometricPrefixValue_of_extended_integral hA

example : zeroRampProfile.val =
    completedDecreasingRestriction (Ioo (0 : ℝ) 1) (ofFun (fun u => max (1-2*u) 0)) :=
  initial_profile_eq_completed_scalar (by norm_num) zeroRampProfile.property
    zeroRampOperator_properties.2.1 zeroRampProfile_selection

example : zeroRampProfile.val (1/2 : ℝ) = {0} := by
  have he := zeroRampOperator_properties.2.2.2 (1/2 : ℝ) (by norm_num)
  simpa only [zeroRamp,show (1 : ℝ)-2*(1/2) = 0 by norm_num,max_self] using he

example {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1/2 : ℝ)) :
    geometricHardyTransform 1 zeroRampProfile p =
      {Real.exp (-1)*(1-2*p)^(-(1-2*p)/(2*p))} := zeroRamp_geometric_before_half hp

example : geometricHardyTransform 1 zeroRampProfile (1/2 : ℝ) =
    Icc (0 : ℝ) (Real.exp (-1)) := zeroRamp_geometric_jump

example {p : ℝ} (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    geometricHardyTransform 1 zeroRampProfile p = {0} := zeroRamp_geometric_after_half hp

example : Filter.Tendsto (fun p => sSup (geometricHardyTransform 1 zeroRampProfile p))
    (𝓝[<] (1/2 : ℝ)) (𝓝 (Real.exp (-1))) := zeroRamp_geometric_graph_left_limit

example {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    hardyFamilyIntegral (Ioo (0 : ℝ) 1) zeroRampProfile.val p =
      {if p ≤ (1/2 : ℝ) then 1-p else 1/(4*p)} := zeroRamp_hardy_fibers hp

-- A local auxiliary Jensen step; the full extended Polya--Knopp integral
-- inequality remains partial until Tonelli and the power/zero cases are assembled.
example {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < f x) :
    Real.exp ((∫ x in (0 : ℝ)..p, Real.log (f x))/p) ≤
      Real.exp 1/p^2*(∫ x in (0 : ℝ)..p, x*f x) :=
  geometric_weighted_prefix_upper hp hi hlog hpos


-- Full original-selection comparison, with ordinary L1 only in the upper bound.
example {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    DecLE q.val (geometricHardyTransform 1 q) ∧
      ((∃ u : ℝ → ℝ, SelectionOn q.val (Ioo (0 : ℝ) 1) u ∧
          IntegrableOn u (Ioo (0 : ℝ) 1) volume) →
        DecLE (geometricHardyTransform 1 q) (hardyFamilyIntegral (Ioo (0 : ℝ) 1) q.val)) := by
  simpa only [hqi] using hardy_geometric_comparison (by norm_num) hqi hq0 hs hP

example {q r : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {sq sr : ℝ → ℝ} (hqs : SelectionOn q.val (Ioo (0 : ℝ) B) sq)
    (hrs : SelectionOn r.val (Ioo (0 : ℝ) B) sr)
    (hPq : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hPr : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sr x)) 0)) < ∞)
    (hqr : DecLE q.val r.val) :
    DecLE (geometricHardyTransform B q) (geometricHardyTransform B r) :=
  geometric_hardy_order_preserving hB hqi hri hq0 hr0 hqs hrs hPq hPr hqr

example {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x) :
    extendedLogIntegral s p = some (↑(∫ x in (0 : ℝ)..p, Real.log (s x)) : EReal) ∧
      geometricPrefixValue s p = Real.exp ((∫ x in (0 : ℝ)..p, Real.log (s x))/p) :=
  ⟨extendedLogIntegral_of_integrable hp hi hpos,geometricPrefixValue_of_integrable hp hi hpos⟩

example {s : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hP : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) ≠ ∞)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞) :
    extendedLogIntegral s p = some ⊥ ∧ geometricPrefixValue s p = 0 :=
  ⟨extendedLogIntegral_of_negative_area_top hP hN,geometricPrefixValue_of_negative_area_top hp hP hN⟩

example {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hi : IntervalIntegrable f volume 0 p) :
    Filter.Tendsto (fun u => (∫ x in (0 : ℝ)..u, f x)/u) (𝓝[<] p)
      (𝓝 ((∫ x in (0 : ℝ)..p, f x)/p)) :=
  hardyScalar_tendsto_left_of_intervalIntegrable hp hi

example {f : Operator} {b m : ℝ} (hb : 0 < b) (hf : MaximalDecreasing f)
    (hd : dom f ⊆ Icc (0 : ℝ) b) {s : ℝ → ℝ}
    (hs : SelectionOn f (Ioo (0 : ℝ) b) s)
    (ht : Filter.Tendsto s (𝓝[<] b) (𝓝 m)) : f b = Iic m :=
  decreasing_right_boundary_fiber_of_tendsto hb hf hd hs ht

example {q : DecGraph} {B p : ℝ} (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞) :
    Ioo (0 : ℝ) p ⊆ interior (dom (logOp q.val)) ∧
      IntervalIntegrable (fun x => Real.log (s x)) volume 0 p :=
  ⟨prefix_log_domain_of_finite_negative_area hqi hq0 hs hp hN,
    logarithm_prefix_integrable_of_finite_negative_area hq0 hm hs hP hp hN⟩


-- The manuscript selection convention: no global measurability of s is assumed.
example {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    ∃! g : Operator, MaximalDecreasing g ∧ interior (dom g) = Ioo (0 : ℝ) 1 ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ g x, 0 ≤ v) ∧
      comp (ofFun Real.exp)
        (hardyFamilyIntegral (interior (dom (logOp (q ⊔ DecGraph.constant 0).val)))
          (logOp (q ⊔ DecGraph.constant 0).val)) ≤ g :=
  geometric_hardy_extension_any_selection (by norm_num) hqi hq0 hn hs hi

example {q : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    DecLE q.val (geometricHardyTransform B q) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  exact le_geometricHardyTransform hB hqi hq0 ht hts (by rwa [harea])

example {q r : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {sq sr : ℝ → ℝ} (hqs : SelectionOn q.val (Ioo (0 : ℝ) B) sq)
    (hrs : SelectionOn r.val (Ioo (0 : ℝ) B) sr)
    (hqiL : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hriL : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sr x)) 0)) < ∞)
    (hqr : DecLE q.val r.val) :
    DecLE (geometricHardyTransform B q) (geometricHardyTransform B r) := by
  obtain ⟨tq,htq,hstq,hqarea⟩ := measurable_selection_same_positive_log_area hqi hqs
  obtain ⟨tr,htr,hstr,hrarea⟩ := measurable_selection_same_positive_log_area hri hrs
  exact geometricHardyTransform_mono hB hqi hri hq0 hr0 htq htr hstq hstr
    (by rwa [hqarea]) (by rwa [hrarea]) hqr

example : (∫ s in (0 : ℝ)..(1/2 : ℝ), Real.log (1-2*s)) = -(1/2 : ℝ) :=
  zeroRamp_log_half_integral

example {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1/2 : ℝ)) :
    Real.exp ((∫ s in (0 : ℝ)..p, Real.log (1-2*s))/p) =
      Real.exp (-1)*(1-2*p)^(-(1-2*p)/(2*p)) :=
  zeroRamp_geometric_prefix_formula hp

example {p : ℝ} (hp : (1/2 : ℝ) < p) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (max (1-2*x) 0)) = ∞ :=
  zero_ramp_negative_log_after_half hp

example {f : ℝ → ℝ} {a b p : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbp : b ≤ p)
    (hz : ∀ x ∈ Ioo a b, f x = 0) :
    (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (f x)) = ∞ :=
  negative_log_area_eq_top_of_zero_interval ha hab hbp hz


example {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    ∃! g : Operator, MaximalDecreasing g ∧ interior (dom g) = Ioo (0 : ℝ) 1 ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ g x, 0 ≤ v) ∧
      comp (ofFun Real.exp)
        (hardyFamilyIntegral (interior (dom (logOp (q ⊔ DecGraph.constant 0).val)))
          (logOp (q ⊔ DecGraph.constant 0).val)) ≤ g :=
  geometric_hardy_extension_of_nonzero (by norm_num) q.property hqi hq0 hn hm hs hi

example {q : DecGraph} (hz : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, v = 0) :
    geometricHardyTransform 1 q = q.val :=
  geometricHardyTransform_zero hz

example {q : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    MaximalDecreasing (geometricHardyTransform B q) ∧
      interior (dom (geometricHardyTransform B q)) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ geometricHardyTransform B q x, 0 ≤ v) ∧
      ((∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0) ∨
        (geometricHardyExtensionPredicate B q (geometricHardyTransform B q) ∧
          ∀ g, geometricHardyExtensionPredicate B q g → g = geometricHardyTransform B q)) :=
  geometricHardyTransform_well_defined hB hqi hq0 hm hs hi

example {g : Operator} {x a : ℝ} (hg : MaximalDecreasing g)
    (hne : (g x).Nonempty) (hz : g x ⊆ Ici 0) (hl : logOp g x = Iic a) :
    g x = Icc (0 : ℝ) (Real.exp a) :=
  nonnegative_log_upper_ray_fiber hg hne hz hl

example {g : Operator} {x : ℝ} (hne : (g x).Nonempty) (hz : g x ⊆ Ici 0)
    (hl : logOp g x = ∅) : g x = {0} :=
  nonnegative_log_empty_fiber hne hz hl

example {g : Operator} {x a : ℝ} (hg : MaximalDecreasing g)
    (hne : (g x).Nonempty) (hz : g x ⊆ Ici 0) (hl : logOp g x = {a}) :
    g x = {Real.exp a} :=
  nonnegative_log_singleton_fiber hg hne hz hl

example {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hi : IntervalIntegrable f volume 0 p)
    (hli : IntervalIntegrable (fun x => Real.log (f x)) volume 0 p)
    (hf : ∀ x ∈ Ioo (0 : ℝ) p, 0 < f x) :
    Real.exp ((∫ x in (0 : ℝ)..p, Real.log (f x))/p) ≤ (∫ x in (0 : ℝ)..p, f x)/p :=
  geometric_average_le_arithmetic hp hi hli hf



example {f : Operator} {B : ℝ} (hB : 0 < B)
    (hf : MaximalDecreasing f) (hdom : dom f ⊆ Icc (0 : ℝ) B)
    (hz : IsGLB (dom f) 0) :
    ∃! g : Operator, MaximalDecreasing g ∧ interior (dom g) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
      (∀ x w, w ∈ f x → Real.exp w ∈ g x) :=
  unique_initial_exponential_completion hB hf hdom hz

example (q : DecGraph) : logOp (q ⊔ DecGraph.constant 0).val = logOp q.val :=
  logarithm_nonnegative_floor q

example {q : Operator} {B : ℝ} (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    SelectionOn (logOp q) (interior (dom (logOp q))) (fun x => Real.log (s x)) ∧
      ∀ p ∈ interior (dom (logOp q)),
        IntervalIntegrable (fun x => Real.log (s x)) volume 0 p :=
  logarithmic_prefix_integrability hB hq hqi hm hs hi




-- These checks retain the actual nonclosed endpoint, literal laws and zero graph.
example : ∃ q : Operator, MaximalDecreasing q ∧
    interior (dom q) = Ioo (0 : ℝ) 1 ∧
    (∀ p ∈ Ioo (0 : ℝ) 1, q p = {0}) ∧
    comp (ofFun Real.exp) q 1 = Ioc (0 : ℝ) 1 ∧
    ¬ MaximalDecreasing (comp (ofFun Real.exp) q) :=
  geometric_exponential_boundary_counterexample

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXL : Measure.map X μ = symmetricBernoulli)
    (hYL : Measure.map Y μ = Measure.dirac (0 : ℝ)) {p : ℝ}
    (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    tailQuantile (Measure.map (fun ω => (X ω+Y ω)/2) μ) p = {0} ∧
      outputScale ((2 : ℝ)⁻¹)
        (finiteSum (fun i : Fin 2 => quantileHardy (![symmetricBernoulli,Measure.dirac 0] i))) p =
        {1/(4*p)} ∧ 0 < 1/(4*p) := by
  exact replication_is_essential μ hX hY hXL hYL hp

example : ∃ X Y : ℝ → ℝ, Measurable X ∧ Measurable Y ∧
    Integrable X symmetricBernoulli ∧ Integrable Y symmetricBernoulli ∧
    Measure.map X symmetricBernoulli = symmetricBernoulli ∧
    Measure.map Y symmetricBernoulli = Measure.dirac 0 :=
  replication_counterexample_model

example : ∃ f : Operator, MaximalDecreasing f ∧ (∀ x : ℝ, f x = {0}) ∧
    logOp f = (fun _ : ℝ => (∅ : Set ℝ)) ∧ ¬ MaximalDecreasing (logOp f) :=
  logarithmic_zero_exception

-- A foundation for the geometric construction, not its entire definition.
example {f g : Operator} {B : ℝ} (hB : 0 < B)
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    (hgi : interior (dom g) = Ioo (0 : ℝ) B)
    (hf0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ u ∈ f x, 0 ≤ u)
    (hg0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ u ∈ g x, 0 ≤ u)
    (hlog : ∀ x ∈ Ioo (0 : ℝ) B, logOp f x = logOp g x) : f = g :=
  nonnegative_initial_graph_eq_of_log_eq hB hf hg hfi hgi hf0 hg0 hlog



universe verificationUniversalEnvelopeUniverse

-- The competing class is expanded literally: every replication count,
-- arbitrary original measurable spaces and probability measures in this
-- universe, and exact coordinate-law equalities. No independence, sign,
-- atomlessness, or near-optimal-witness premise is present.
example {n : ℕ} (hn : 0 < n) (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    (sSup {C : DecGraph | ∃ m : ℕ, 0 < m ∧
      ∃ (Ω : Type verificationUniversalEnvelopeUniverse) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ) (X : Fin n → Fin m → Ω → ℝ),
        (∀ i j, Measurable (X i j)) ∧
        (∀ i j, Measure.map (X i j) μ = laws i) ∧
        C.val = tailQuantile (Measure.map
          (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ)}).val =
      outputScale ((n : ℝ)⁻¹) (finiteSum (fun i =>
        hardyFamilyIntegral (interior (dom (tailQuantile (laws i)))) (tailQuantile (laws i)))) :=
  universal_replicated_quantile_envelope.{verificationUniversalEnvelopeUniverse} hn laws hi

example {n : ℕ} (hn : 0 < n) (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    IsLUB (replicatedQuantileFamily.{verificationUniversalEnvelopeUniverse} laws)
      (⟨replicatedHardyEnvelope laws, (replicatedHardyEnvelope_properties hn laws hi).1⟩ : DecGraph) :=
  replicated_quantile_envelope_isLUB hn laws hi

example {n : ℕ} (hn : 0 < n) (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    interior (dom (sSup (replicatedQuantileFamily.{verificationUniversalEnvelopeUniverse} laws)).val) =
      Ioo (0 : ℝ) 1 ∧
      dom (sSup (replicatedQuantileFamily.{verificationUniversalEnvelopeUniverse} laws)).val ⊆ Icc (0 : ℝ) 1 := by
  rw [universal_replicated_quantile_envelope hn laws hi]
  change interior (dom (replicatedHardyEnvelope laws)) = Ioo (0 : ℝ) 1 ∧
    dom (replicatedHardyEnvelope laws) ⊆ Icc (0 : ℝ) 1
  have h := replicatedHardyEnvelope_properties hn laws hi
  refine ⟨Subset.antisymm ?_ (interior_maximal h.2.2 isOpen_Ioo), h.2.1⟩
  simpa only [interior_Icc] using interior_mono h.2.1


universe verificationReplicaFamilyUniverse

example {n : ℕ} (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)] :
    (replicatedQuantileFamily.{verificationReplicaFamilyUniverse} laws).Nonempty :=
  replicatedQuantileFamily_nonempty laws

example {n : ℕ} (laws : Fin n → Measure ℝ) :
    ∀ C ∈ replicatedQuantileFamily.{verificationReplicaFamilyUniverse} laws,
      dom C.val ⊆ Icc (0 : ℝ) 1 := replicatedQuantileFamily_domains laws

example {n : ℕ} (hn : 0 < n) (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    ∀ C ∈ replicatedQuantileFamily.{verificationReplicaFamilyUniverse} laws,
      DecLE C.val (outputScale ((n : ℝ)⁻¹) (finiteSum (fun i => quantileHardy (laws i)))) :=
  replicatedQuantileFamily_upper hn laws hi

example {Ω : Type} [MeasurableSpace Ω] {n m : ℕ} (hm : 0 < m)
    (laws : Fin n → Measure ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Fin m → Ω → ℝ) (hXm : ∀ i j, Measurable (X i j))
    (hLaw : ∀ i j, Measure.map (X i j) μ = laws i) {C : DecGraph}
    (hC : C.val = tailQuantile (Measure.map
      (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ)) :
    C ∈ replicatedQuantileFamily.{verificationReplicaFamilyUniverse} laws :=
  replicatedQuantileFamily_of_model hm laws μ X hXm hLaw hC


example {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) :
    inverse (fun r : ℝ => if 0 ≤ r then
      ({(∏ i, (|a i|+σ i*r))-(∏ i, |a i|)} : Set ℝ) else ∅) =
      finiteParallelAdd (fun k : Fin n => fun t : ℝ => if 0 ≤ t then
        {(t/productCoefficient a σ (k.val+1))^(((k.val+1 : ℕ) : ℝ)⁻¹)} else ∅) :=
  product_inverse_parallel_root_maps hn a σ ha hσ

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : Measurable X) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hDom : dom α = Ici 0)
    (hGauss : ∀ r > 0, α r = {Real.exp (-(r^2))})
    (hX : ∀ i, DecLE (survival (Measure.map (fun ω => |X ω i-a i|) μ))
      (inputDivide (σ i) α)) {t : ℝ} (ht : 0 < t) :
    let d := (Finset.univ.filter
      (fun k : Fin n => 0 < productCoefficient a σ (k.val+1))).card
    μ.real {ω | t < |(∏ i, X ω i)-(∏ i, a i)|} ≤
      min 1 ((n : ℝ)*Real.exp (-(⨅ k : Fin n,
        (t/((d : ℝ)*productCoefficient a σ (k.val+1)))^((2 : ℝ)/((k.val+1 : ℕ) : ℝ))))) :=
  multilevel_product_gaussian_bound hn μ hm a σ ha hσ hGauss hX ht

example {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (laws : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (laws i)]
    (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin n → Fin m → Ω → ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hLaw : ∀ i j, Measure.map (X i j) μ = laws i) :
    let Y := fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))
    MaximalDecreasing (replicatedHardyEnvelope laws) ∧
      DecLE (quantileHardy (Measure.map Y μ)) (replicatedHardyEnvelope laws) ∧
      DecLE (tailQuantile (Measure.map Y μ)) (replicatedHardyEnvelope laws) :=
  replicated_average_operator_bound hn hm laws hi μ X hXm hLaw


example {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα0 : dom α ⊆ Ici 0) :
    ∃ g : ℝ → ℝ,
      (∀ t ≥ 0, 0 ≤ g t ∧ ((∏ i, (|a i|+σ i*g t))-(∏ i, |a i|)) = t) ∧
      (∀ r ≥ 0, g ((∏ i, (|a i|+σ i*r))-(∏ i, |a i|)) = r) ∧
      productProfile α a σ = comp α (fun t => if 0 ≤ t then {g t} else ∅) :=
  productProfile_root_representation hn a σ ha hσ hα0

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : Measurable X) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hDom : dom α = Ici 0)
    (hProfile : ∀ t > 0, α t ⊆ Icc (0 : ℝ) 1)
    (hX : ∀ i, DecLE (survival (Measure.map (fun ω => |X ω i-a i|) μ))
      (inputDivide (σ i) α)) (θ : PositiveWeights (Fin n)) :
    let g := productMonomialGraphs a σ ha hσ hα (by rw [hDom])
    MaximalDecreasing (productProfile α a σ) ∧
      DecLE (survival (Measure.map (fun ω => |(∏ i, X ω i)-(∏ i, a i)|) μ))
        (outputScale (n : ℝ) (productProfile α a σ)) ∧
      DecLE (survival (Measure.map (fun ω => |(∏ i, X ω i)-(∏ i, a i)|) μ))
        (outputScale (n : ℝ) (⨆ k, DecGraph.weightedProfile g θ k).val) :=
  multilevel_product_operator_bound hn μ hm a σ ha hσ hα
    (by rw [hDom]) hX θ

example {n : ℕ} {q : Fin n → ℝ → ℝ} (hm : ∀ i, Measurable (q i))
    (hi : ∀ i, Integrable (q i) unitUniform) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    (∀ i j, Measure.map (quantileReplica q p i j) (twoBranchMeasure p iidUniformMeasure) =
      Measure.map (q i) unitUniform) ∧
      (∀ i j, Integrable (quantileReplica q p i j) (twoBranchMeasure p iidUniformMeasure)) :=
  ⟨quantileReplica_law hm hp, quantileReplica_integrable hm hi hp⟩

example {n : ℕ} {q : Fin n → ℝ → ℝ} (hm : ∀ i, Measurable (q i))
    (hi : ∀ i, Integrable (q i) unitUniform) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {t r : ℝ} (ht : t < (∑ i, hardyScalar (q i) p)/(n : ℝ)) (hr : r ∈ Ioo 0 p) :
    ∃ m : ℕ, 1 ≤ m ∧ r < (twoBranchMeasure p iidUniformMeasure).real
      {z | t < (∑ i, ∑ j ∈ Finset.range m, quantileReplica q p i j z)/((n : ℝ)*(m : ℝ))} :=
  replicaAverage_near_mean hm hi hp ht hr

example {n : ℕ} (hn : 0 < n) (laws : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (laws i)] (hi : ∀ i, Integrable (fun x : ℝ => x) (laws i)) :
    MaximalDecreasing (outputScale ((n : ℝ)⁻¹) (finiteSum (fun i => quantileHardy (laws i)))) ∧
      dom (replicatedHardyEnvelope laws) ⊆ Icc (0 : ℝ) 1 ∧
      Ioo (0 : ℝ) 1 ⊆ dom (replicatedHardyEnvelope laws) :=
  replicatedHardyEnvelope_properties hn laws hi

example {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (laws : Fin n → Measure ℝ)
    (X : Fin n → Fin m → Ω → ℝ) (hXm : ∀ i j, Measurable (X i j))
    (hXi : ∀ i j, Integrable (X i j) μ)
    (hLaw : ∀ i j, Measure.map (X i j) μ = laws i) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ, (∀ i, quantileHardy (laws i) p = {a i}) ∧
      quantileHardy (Measure.map
        (fun ω => (∑ i, ∑ j, X i j ω)/((n : ℝ)*(m : ℝ))) μ) p = {b} ∧
      b ≤ (∑ i, a i)/(n : ℝ) :=
  replicated_average_hardy_values hn hm μ laws X hXm hXi hLaw hp


example {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0) :
    (fun t => {u | ∃ r, u ∈ α r ∧ t =
      (∏ i, (|a i|+σ i*r))-(∏ i, |a i|)}) =
      finiteParallelAdd (fun k : Fin n =>
        monomialProfile α (productCoefficient a σ (k.val+1)) (k.val+1)) :=
  productProfile_parallel_monomials hn a σ (fun i => (hσ i).le) hα hα0

example {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {α : Operator}
    (hα : MaximalDecreasing α) (hα0 : dom α ⊆ Ici 0) (θ : PositiveWeights (Fin n)) :
    MaximalDecreasing (productProfile α a σ) ∧
      DecLE (productProfile α a σ)
        (⨆ k, DecGraph.weightedProfile (productMonomialGraphs a σ ha hσ hα hα0) θ k).val :=
  ⟨productProfile_maximal hn a σ ha hσ hα hα0,
    productProfile_weighted_envelope hn a σ ha hσ hα hα0 θ⟩

example {p : ℝ} (hp : p ∈ Ioo 0 1) {q : ℝ → ℝ} (hq : Measurable q) :
    ENNReal.ofReal p • Measure.map (fun u : ℝ => q (p*u)) unitUniform +
      ENNReal.ofReal (1-p) • Measure.map (fun u : ℝ => q (p+(1-p)*u)) unitUniform =
        Measure.map q unitUniform := quantile_law_split hp hq

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    IsProbabilityMeasure (ENNReal.ofReal p • Measure.map (fun ω => ((0 : ℝ), ω)) μ +
      ENNReal.ofReal (1-p) • Measure.map (fun ω => ((1 : ℝ), ω)) μ) :=
  twoBranchMeasure_probability μ hp

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ)
    {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measure.map (fun z : ℝ × Ω => if z.1 = 0 then F z.2 else G z.2)
      (twoBranchMeasure p μ) = ENNReal.ofReal p • Measure.map F μ +
        ENNReal.ofReal (1-p) • Measure.map G μ := twoBranchFunction_law μ p hF hG

example {q : ℝ → ℝ} (hi : Integrable q unitUniform) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    IntervalIntegrable q volume 0 p ∧
      Integrable (fun u : ℝ => q (p*u)) unitUniform ∧
      (∫ u, q (p*u) ∂unitUniform) = (∫ u in (0 : ℝ)..p, q u)/p :=
  ⟨uniform_prefix_integrable hi hp, uniform_top_segment_integrable hi hp,
    uniform_top_segment_mean q hp.1⟩

example {A : Set DecGraph} (hne : A.Nonempty)
    (hdom : ∀ C ∈ A, dom C.val ⊆ Icc (0 : ℝ) 1) (f : DecGraph)
    (hfdom : dom f.val ⊆ Icc (0 : ℝ) 1) (hfcover : Ioo (0 : ℝ) 1 ⊆ dom f.val)
    (hupper : ∀ C ∈ A, C ≤ f)
    (hnear : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ a ∈ f p, ∀ t < a,
      ∀ r ∈ Ioo (0 : ℝ) p, ∃ C ∈ A, ∃ z ∈ C r, t < z) :
    IsLUB A f := quantile_family_isLUB hne hdom f hfdom hfcover hupper hnear


example {n : ℕ} (a σ : Fin n → ℝ) (r : ℝ) :
    (∏ i, (|a i|+σ i*r))-(∏ i, |a i|) =
      ∑ k : Fin n, productCoefficient a σ (k.val+1)*r^(k.val+1) :=
  product_polynomial_expansion a σ r

example {n : ℕ} (hn : 0 < n) (a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) :
    BijOn (fun r => (∏ i, (|a i|+σ i*r))-(∏ i, |a i|)) (Ici 0) (Ici 0) ∧
      ∀ k : ℕ, k ≤ n → 0 < productCoefficient a σ k :=
  ⟨productDeviation_bijOn hn a σ ha hσ,
    fun k hk => productCoefficient_positive a σ ha hσ hk⟩

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : ι → ℝ, ∃ v : ℝ,
      (∀ i, quantileHardy (Measure.map (X i) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => ∑ i, X i ω) μ) p = {v} ∧
      v ≤ ∑ i, a i :=
  signed_hardy_sum_values μ X hm hi hp

example {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) μ) :
    MaximalDecreasing (finiteSum (fun i => quantileHardy (Measure.map (X i) μ))) ∧
      DecLE (quantileHardy (Measure.map (fun ω => ∑ i, X i ω) μ))
        (finiteSum (fun i => quantileHardy (Measure.map (X i) μ))) :=
  signed_hardy_sum_operator_bound μ X hm hi

example : IsProbabilityMeasure iidUniformMeasure := iidUniformMeasure_probability

example (j : ℕ) : Measure.map (fun ω : ℕ → ℝ => ω j) iidUniformMeasure =
    volume.restrict (Ioo 0 1) := iid_uniform_eval_law j

example : ProbabilityTheory.iIndepFun (fun j : ℕ => fun ω : ℕ → ℝ => ω j)
    iidUniformMeasure := iid_uniform_coordinates_independent

example {F : ℝ → ℝ} (hm : Measurable F) (hi : Integrable F unitUniform) :
    ∀ᵐ ω ∂iidUniformMeasure,
      Filter.Tendsto (fun m : ℕ => (∑ j ∈ Finset.range m, F (ω j))/(m : ℝ)) Filter.atTop
        (𝓝 (∫ u, F u ∂unitUniform)) := iid_uniform_average_ae hm hi

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} (hm : ∀ m, Measurable (Y m)) {a b q : ℝ}
    (hab : a < b) (hq : q < 1)
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun m : ℕ => Y m ω) Filter.atTop (𝓝 b)) :
    ∃ m : ℕ, 1 ≤ m ∧ q < μ.real {ω | a < Y m ω} :=
  exists_strict_tail_probability_of_ae_limit μ hm hab hq hlim


-- Literal current-manuscript assumptions, with separate single-valuedness,
-- selection, continuity and open-domain conditions. The theorem proves a
-- stronger version in which the last two regularity premises are unnecessary.
example {α : Operator} {a : ℝ → ℝ} {L : EReal} {κ : ℝ}
    (hα : MaximalDecreasing α) (hSingle : SingleValued α)
    (ha : SelectionOn α (dom α) a) (hOpen : IsOpen (dom α))
    (hCont : ContinuousOn a (dom α)) (hm : StrictAntiOn a (dom α))
    (hL : 0 < L) (hrange : ran α = {p : ℝ | 0 < p ∧ (p : EReal) < L}) (hk : 1 < κ)
    (hc : ConvexOn ℝ (dom α) (fun x => (a x)^((-1 : ℝ)/κ))) :
    MaximalDecreasing (inverse (hardyFamilyIntegral (interior (dom (inverse α))) (inverse α))) ∧
      DecLE (inverse (hardyFamilyIntegral (interior (dom (inverse α))) (inverse α)))
        (outputScale ((κ/(κ-1))^κ) α) := by
  apply hardy_profiles_power hα ?_ hm hL hrange hk hc
  intro x hx
  ext u
  constructor
  · intro hu
    exact mem_singleton_iff.mpr (hSingle x hu (ha x hx))
  · intro hu
    rw [mem_singleton_iff.mp hu]
    exact ha x hx

example {α : Operator} {a : ℝ → ℝ} {L : EReal}
    (hα : MaximalDecreasing α) (hSingle : SingleValued α)
    (ha : SelectionOn α (dom α) a) (hOpen : IsOpen (dom α))
    (hCont : ContinuousOn a (dom α)) (hm : StrictAntiOn a (dom α))
    (hL : 0 < L) (hrange : ran α = {p : ℝ | 0 < p ∧ (p : EReal) < L})
    (hc : ConvexOn ℝ (dom α) (fun x => -Real.log (a x))) :
    MaximalDecreasing (inverse (hardyFamilyIntegral (interior (dom (inverse α))) (inverse α))) ∧
      DecLE (inverse (hardyFamilyIntegral (interior (dom (inverse α))) (inverse α)))
        (outputScale (Real.exp 1) α) := by
  apply hardy_profiles_exponential hα ?_ hm hL hrange hc
  intro x hx
  ext u
  constructor
  · intro hu
    exact mem_singleton_iff.mpr (hSingle x hu (ha x hx))
  · intro hu
    rw [mem_singleton_iff.mp hu]
    exact ha x hx

example {κ C : ℝ} (hk : 1 < κ) (hC : 0 < C) :
    hardyTailTransform (outputScale C (powerProfile κ 1)) =
      outputScale (C*(κ/(κ-1))^κ) (powerProfile κ 1) ∧
    hardyTailTransform (outputScale C (exponentialProfile 1)) =
      outputScale (C*Real.exp 1) (exponentialProfile 1) := hardy_regularized_profiles hk hC


example {n : ℕ} (hn : 0 < n) (x a σ : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hσ : ∀ i, 0 < σ i) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ i, |x i-a i| ≤ σ i*r) :
    |(∏ i, x i)-(∏ i, a i)| ≤ (∏ i, (|a i|+σ i*r))-(∏ i, |a i|) :=
  product_deviation_bound x a σ r hx

example {n : ℕ} (a σ : Fin n → ℝ) (k : ℕ) :
    productCoefficient a σ k =
      ∑ A ∈ Finset.univ.powersetCard k,
        (∏ i ∈ A, σ i)*(∏ i ∈ Finset.univ \ A, |a i|) := rfl

example {n : ℕ} (a σ : Fin n → ℝ) (r : ℝ) :
    (∏ i, (|a i|+σ i*r))-(∏ i, |a i|) =
      ∑ A ∈ Finset.univ.powerset.erase ∅,
        ((∏ i ∈ A, σ i)*(∏ i ∈ Finset.univ \ A, |a i|))*r^A.card :=
  productDeviation_powerset_expansion a σ r

example {n : ℕ} (a σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) :
    productCoefficient a σ n = (∏ i, σ i) ∧
      0 < productCoefficient a σ n ∧ ∀ k, 0 ≤ productCoefficient a σ k :=
  ⟨productCoefficient_top a σ, productCoefficient_top_positive a σ hσ,
    fun k => productCoefficient_nonnegative a σ (fun i => (hσ i).le) k⟩


example {L : EReal} (hL : 0 < L) :
    IsGLB {p : ℝ | 0 < p ∧ (p : EReal) < L} 0 := positiveInitialInterval_isGLB hL

example {α : Operator} {a : ℝ → ℝ} {L : EReal} {κ : ℝ}
    (hα : MaximalDecreasing α) (ha : ∀ x ∈ dom α, α x = {a x})
    (hm : StrictAntiOn a (dom α)) (hL : 0 < L)
    (hrange : ran α = {p : ℝ | 0 < p ∧ (p : EReal) < L}) (hk : 1 < κ)
    (hc : ConvexOn ℝ (dom α) (fun x => (a x)^((-1 : ℝ)/κ))) :
    ∃ q : ℝ → ℝ, Measurable q ∧ SelectionOn (inverse α) (ran α) q ∧
      ∀ p ∈ ran α, IntervalIntegrable q volume 0 p ∧
        hardyScalar q p ≤ q ((κ/(κ-1))^(-κ)*p) :=
  hardy_profile_power_prefix hα ha hm hL hrange hk hc

example {α : Operator} {a : ℝ → ℝ} {L : EReal}
    (hα : MaximalDecreasing α) (ha : ∀ x ∈ dom α, α x = {a x})
    (hm : StrictAntiOn a (dom α)) (hL : 0 < L)
    (hrange : ran α = {p : ℝ | 0 < p ∧ (p : EReal) < L})
    (hc : ConvexOn ℝ (dom α) (fun x => -Real.log (a x))) :
    ∃ q : ℝ → ℝ, Measurable q ∧ SelectionOn (inverse α) (ran α) q ∧
      ∀ p ∈ ran α, IntervalIntegrable q volume 0 p ∧
        hardyScalar q p ≤ q (Real.exp (-1)*p) :=
  hardy_profile_exponential_prefix hα ha hm hL hrange hc

-- Local hypotheses imply the entire graph comparison; the larger dilation
-- domain and every endpoint fiber are included.
example {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ p ∈ dom f, 0 < p)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hb : ∀ p ∈ interior (dom f), hardyScalar s p ≤ s (c*p)) :
    DecLE (hardyFamilyIntegral (interior (dom f)) f) (fun x => f (c*x)) :=
  hardyFamilyIntegral_le_inputDilation hf hz hp hs hi hc hc1 hb

example {α : Operator} (hα : MaximalDecreasing α)
    (hz : IsGLB (ran α) 0) (hp : ∃ p ∈ ran α, 0 < p)
    {q : ℝ → ℝ} (hq : SelectionOn (inverse α) (interior (ran α)) q)
    (hi : ∀ p ∈ interior (ran α), IntervalIntegrable q volume 0 p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hb : ∀ p ∈ interior (ran α), hardyScalar q p ≤ q (c*p)) :
    MaximalDecreasing (inverse (hardyFamilyIntegral (interior (dom (inverse α))) (inverse α))) ∧
      DecLE (inverse (hardyFamilyIntegral (interior (dom (inverse α))) (inverse α)))
        (outputScale c⁻¹ α) := hardyTailTransform_bound_of_scalar hα hz hp hq hi hc hc1 hb


-- The two actual estimation-error laws on an arbitrary original probability space.
-- Normalized sums are expanded independently of the meanThree abbreviation.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → (Fin 3 → ℝ)} (hm : Measurable X)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) (θ : ℝ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : Fin 3 → ℝ, ∃ m v : ℝ, 0 ≤ a ∧
      (∀ i, quantileHardy (Measure.map (fun ω => |X ω i-θ|) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => |scalarMedian 1 (X ω)-θ|) μ) p = {m} ∧
      quantileHardy (Measure.map (fun ω => |(∑ i, X ω i)/3-θ|) μ) p = {v} ∧
      m ≤ min (a (Tuple.sort a 0)+a (Tuple.sort a 1)) ((∑ i, a i)/2) ∧
      v ≤ (∑ i, a i)/3 := heterogeneous_estimators_bound μ hm hi θ hp

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z : Ω → ℝ} (hm : Measurable Z) (hn : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hpos : 0 < ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)
    (hfin : (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) < ∞) :
    Integrable Z μ ∧ 0 < ∫ ω, Z ω ∂μ :=
  integrable_positive_mean_of_lintegral μ hm hn hpos hfin

-- One h is chosen before b; arbitrary input permutations preserve both errors.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hm : Measurable Z) (hn : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hpos : 0 < ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)
    (hfin : (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) < ∞)
    (θ : ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ h : ℝ, 0 < h ∧ quantileHardy (Measure.map Z μ) p = {h} ∧
      (∀ b : ℝ, 6 < b →
        let X : Ω → (Fin 3 → ℝ) := fun ω => ![θ+Z ω, θ+2*Z ω, θ+b*Z ω]
        let a : Fin 3 → ℝ := ![h, 2*h, b*h]
        (∀ i, Measurable (fun ω => X ω i) ∧ Integrable (fun ω => X ω i) μ ∧
          quantileHardy (Measure.map (fun ω => |X ω i-θ|) μ) p = {a i}) ∧
        (∀ σ : Equiv.Perm (Fin 3),
          quantileHardy (Measure.map (fun ω => |scalarMedian 1 (fun i => X ω (σ i))-θ|) μ) p = {2*h} ∧
          quantileHardy (Measure.map (fun ω => |(∑ i, X ω (σ i))/3-θ|) μ) p = {(b+3)/3*h}) ∧
        superadditiveTransform (scalarMedian 1) a = 3*h ∧
        (∑ i, a i)/3 = (b+3)/3*h ∧ 3*h < (b+3)/3*h) ∧
      (∀ M : ℝ, ∃ b : ℝ, 6 < b ∧ M < (b+3)/3*h) :=
  heterogeneous_estimators_concrete μ hm hn hpos hfin θ hp

example {h : ℝ} (hh : 0 < h) :
    ∀ M : ℝ, ∃ b : ℝ, 6 < b ∧ M < (b+3)/3*h := normalized_sum_scale_unbounded hh


-- Restricted domains and derived composition L1 are explicit.
example {D U : Set ℝ} {φ ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ D φ) (hm : StrictMonoOn φ D) (hU : Convex ℝ U)
    (hψ : MapsTo ψ U D) (hinv : ∀ y ∈ U, φ (ψ y) = y) :
    MonotoneOn ψ U ∧ ConcaveOn ℝ U ψ :=
  ⟨monotoneOn_of_strictMonoOn_right_inverse hm hψ hinv,
    concaveOn_of_convexOn_right_inverse hc hm hU hψ hinv⟩

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D U : Set ℝ} {φ ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ D φ) (hm : StrictMonoOn φ D) (hU : Convex ℝ U) (ho : IsOpen U)
    (hψ : MapsTo ψ U D) (hinv : ∀ y ∈ U, φ (ψ y) = y)
    {a x₀ : ℝ} (ha : a ∈ U) (hx : x₀ ∈ U) (hax : a < x₀)
    (htail : Ici x₀ ⊆ U) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, x₀ ≤ X ω) (hi : Integrable X μ) :
    Integrable (fun ω => ψ (X ω)) μ ∧
      (∫ ω, ψ (X ω) ∂μ) ≤ ψ (∫ ω, X ω ∂μ) :=
  convex_inverse_jensen_derived_integrability hc hm hU ho hψ hinv ha hx hax htail hX hi

-- Equality of entire inverse graphs, including every boundary fiber.
example {c : ℝ} (hc : c ≠ 0) (f : Operator) :
    inverse (fun x => f (c*x)) = outputScale c⁻¹ (inverse f) :=
  inverse_positiveInputDilation hc f

example {g f : ℝ → ℝ} {U : Set ℝ}
    (hg : ConcaveOn ℝ U g) (hm : MonotoneOn g U) (ho : IsOpen U)
    {x₀ p : ℝ} (hx : x₀ ∈ U) (htail : Ici x₀ ⊆ U) (hp : 0 < p)
    (hf : IntervalIntegrable f volume 0 p)
    (hlower : ∀ t ∈ Ioo 0 p, x₀ ≤ f t) :
    IntervalIntegrable (fun t => g (f t)) volume 0 p ∧
      hardyScalar (fun t => g (f t)) p ≤ g (hardyScalar f p) :=
  hardyScalar_concave_composition hg hm ho hx htail hp hf hlower

example {g : ℝ → ℝ} {U : Set ℝ} {κ p : ℝ}
    (hg : ConcaveOn ℝ U g) (hm : MonotoneOn g U) (ho : IsOpen U)
    (hκ : 1 < κ) (hp : 0 < p) (hx : p^((-1 : ℝ)/κ) ∈ U)
    (htail : Ici (p^((-1 : ℝ)/κ)) ⊆ U) :
    IntervalIntegrable (fun t => g (t^((-1 : ℝ)/κ))) volume 0 p ∧
      hardyScalar (fun t => g (t^((-1 : ℝ)/κ))) p ≤
        g ((κ/(κ-1))*p^((-1 : ℝ)/κ)) :=
  power_inverse_profile_jensen hg hm ho hκ hp hx htail

example {g : ℝ → ℝ} {U : Set ℝ} {p : ℝ}
    (hg : ConcaveOn ℝ U g) (hm : MonotoneOn g U) (ho : IsOpen U)
    (hp : 0 < p) (hx : -Real.log p ∈ U) (htail : Ici (-Real.log p) ⊆ U) :
    IntervalIntegrable (fun t => g (-Real.log t)) volume 0 p ∧
      hardyScalar (fun t => g (-Real.log t)) p ≤ g (1-Real.log p) :=
  exponential_inverse_profile_jensen hg hm ho hp hx htail


example {α : Operator} {a q : ℝ → ℝ}
    (ha : ∀ x ∈ dom α, α x = {a x}) (hm : StrictAntiOn a (dom α))
    {I : Set ℝ} (hq : SelectionOn (inverse α) I q) {p : ℝ} (hp : p ∈ I) :
    inverse α p = {q p} ∧ q p ∈ dom α ∧ a (q p) = p :=
  inverse_selection_singleton_of_strictAnti ha hm hq hp

example {α : Operator} (hα : MaximalDecreasing α)
    (ho : IsOpen (ran α)) (hz : IsGLB (ran α) 0) (hp : ∃ p ∈ ran α, 0 < p) :
    (ran α).OrdConnected ∧ (ran α).Nonempty ∧
      (∀ p ∈ ran α, 0 < p) ∧ (∀ p ∈ ran α, Ioo 0 p ⊆ ran α) ∧
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ ran α, c*p ∈ ran α) :=
  profile_range_initial_geometry hα ho hz hp

example {a : ℝ → ℝ} {D : Set ℝ} {κ : ℝ}
    (hm : StrictAntiOn a D) (ha : ∀ x ∈ D, 0 < a x) (hk : 0 < κ) :
    StrictMonoOn (fun x => (a x)^((-1 : ℝ)/κ)) D ∧
      StrictMonoOn (fun x => -Real.log (a x)) D :=
  ⟨power_transform_strictMono hm ha hk, logarithmic_transform_strictMono hm ha⟩

-- The power substitution is positive; the logarithmic substitution can be
-- negative and has no imposed positive lower endpoint.
example {I : Set ℝ} {κ : ℝ} (ho : IsOpen I)
    (hprefix : ∀ p ∈ I, Ioo 0 p ⊆ I) (hk : 0 < κ) :
    IsOpen {y : ℝ | 0 < y ∧ y^(-κ) ∈ I} ∧
      Convex ℝ {y : ℝ | 0 < y ∧ y^(-κ) ∈ I} ∧
      ∀ x ∈ {y : ℝ | 0 < y ∧ y^(-κ) ∈ I}, Ici x ⊆ {y : ℝ | 0 < y ∧ y^(-κ) ∈ I} :=
  powerSubstitutionDomain_geometry ho hprefix hk

example {I : Set ℝ} (ho : IsOpen I) (hprefix : ∀ p ∈ I, Ioo 0 p ⊆ I) :
    IsOpen {y : ℝ | Real.exp (-y) ∈ I} ∧ Convex ℝ {y : ℝ | Real.exp (-y) ∈ I} ∧
      ∀ x ∈ {y : ℝ | Real.exp (-y) ∈ I}, Ici x ⊆ {y : ℝ | Real.exp (-y) ∈ I} :=
  exponentialSubstitutionDomain_geometry ho hprefix

example {I : Set ℝ} {κ p : ℝ} (hk : 0 < κ) (hp : 0 < p) (hpI : p ∈ I) :
    0 < p^((-1 : ℝ)/κ) ∧ (p^((-1 : ℝ)/κ))^(-κ) ∈ I ∧
      Real.exp (-(-Real.log p)) ∈ I := by
  exact ⟨(powerSubstitutionDomain_point hk hp hpI).1,
    (powerSubstitutionDomain_point hk hp hpI).2, exponentialSubstitutionDomain_point hp hpI⟩


universe uMedianWholeReader

-- Literal ordinary subset sum and positive scale, before taking lattice infima.
example (r : ℕ) (ℓ : Fin (r+1)) (J : medianCutSets r ℓ)
    (f : Fin (2*r+1) → Operator) :
    medianCutSum r ℓ J f = outputScale (1 / ((ℓ.val+1 : ℕ) : ℝ))
      (finiteOperatorSum (fun i => if i ∈ J.val then f i else ofFun (fun _ => 0))) := rfl

-- Independently expand both the actual Hardy graphs and the full nested lattice
-- infimum of scaled ordinary sums. All domain and maximality premises are derived.
example {Ω : Type uMedianWholeReader} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin (2*r+1) → ℝ)}
    (hm : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    let f : Fin (2*r+1) → DecGraph := fun i =>
      ⟨hardyFamilyIntegral
        (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)),
        (quantileHardy_original_properties μ (measurable_pi_iff.mp hm i) (hi i)).1⟩
    let hd : ∀ i, Ioo (0 : ℝ) 1 ⊆ dom (f i).val := fun i p hp =>
      interior_subset (by change p ∈ interior (dom (quantileHardy (Measure.map (fun ω => X ω i) μ)))
                          rwa [(quantileHardy_original_properties μ
        (measurable_pi_iff.mp hm i) (hi i)).2.1])
    let G : (ℓ : Fin (r+1)) → medianCutSets r ℓ → DecGraph := fun ℓ J =>
      ⟨outputScale (1 / ((ℓ.val+1 : ℕ) : ℝ))
        (finiteOperatorSum (fun i => if i ∈ J.val then (f i).val else ofFun (fun _ => 0))),
        medianCutSum_maximal r ℓ J _ (fun i => (f i).property) hd⟩
    DecLE
      (hardyFamilyIntegral
        (interior (dom (tailQuantile (Measure.map (fun ω => scalarMedian r (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => scalarMedian r (X ω)) μ)))
      (⨅ ℓ : Fin (r+1), ⨅ J : medianCutSets r ℓ, G ℓ J).val :=
  hardy_tail_median_operator_bound r μ hm hn hi

example {Ω : Type uMedianWholeReader} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin (2*r+1) → ℝ)}
    (hm : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : Fin (2*r+1) → ℝ, ∃ v : ℝ, 0 ≤ a ∧
      (∀ i, quantileHardy (Measure.map (fun ω => X ω i) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => scalarMedian r (X ω)) μ) p = {v} ∧
      v ≤ ⨅ ℓ : Fin (r+1),
        ⨅ J : {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)},
          (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ) :=
  hardy_tail_median_bound r μ hm hn hi hp

-- Original-space stochastic domination transfers to the full completed Hardy graphs.
example {Ω : Type uMedianWholeReader} [MeasurableSpace Ω] (r : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin (2*r+1) → ℝ)}
    (hm : Measurable X) (hi : ∀ i, Integrable (fun ω => X ω i) μ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) (a : Fin (2*r+1) → ℝ)
    (ha : ∀ i, quantileHardy (Measure.map (fun ω => X ω i) μ) p = {a i}) :
    (medianHardyBound r μ X hm hi).val p =
      {⨅ ℓ : Fin (r+1),
        ⨅ J : {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)},
          (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ)} :=
  medianHardyBound_value r μ hm hi hp a ha

-- Original-space stochastic domination transfers to the full completed Hardy graphs.
example {Ω : Type uMedianWholeReader} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y Z : Ω → ℝ}
    (hYm : Measurable Y) (hZm : Measurable Z) (hYi : Integrable Y μ) (hZi : Integrable Z μ)
    (hle : Y ≤ᵐ[μ] Z) :
    DecLE
      (hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map Y μ)))) (tailQuantile (Measure.map Y μ)))
      (hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map Z μ)))) (tailQuantile (Measure.map Z μ))) :=
  quantileHardy_original_mono μ hYm hZm hYi hZi hle

example {Ω : Type uMedianWholeReader} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hm : Measurable Y) (hi : Integrable Y μ) {c : ℝ} (hc : 0 ≤ c)
    {p a : ℝ} (hp : p ∈ Ioo 0 1)
    (ha : hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map Y μ))))
      (tailQuantile (Measure.map Y μ)) p = {a}) :
    hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => c*Y ω) μ))))
      (tailQuantile (Measure.map (fun ω => c*Y ω) μ)) p = {c*a} :=
  quantileHardy_smul_value μ hm hi hc hp ha

example {Ω : Type uMedianWholeReader} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hm : Measurable Y) (hi : Integrable Y μ) {p a : ℝ} (hp : p ∈ Ioo 0 1)
    (ha : quantileHardy (Measure.map Y μ) p = {a}) : (∫ ω, Y ω ∂μ) ≤ a :=
  quantileHardy_mean_le μ hm hi hp ha


example (a : Fin 3 → ℝ) (ha : 0 ≤ a) :
    superadditiveTransform (scalarMedian 1) a =
      min (a (Tuple.sort a 0)+a (Tuple.sort a 1)) ((∑ i, a i)/2) :=
  median_three_sharp_formula a ha

example (a : Fin 3 → ℝ) (ha : 0 ≤ a) :
    superadditiveTransform meanThree a = (∑ i, a i)/3 := meanThree_sharp_transform ha

example (x : Fin 3 → ℝ) (θ : ℝ) :
    |(∑ i, x i)/3-θ| ≤ (∑ i, |x i-θ|)/3 := meanThree_error_domination x θ

example (r : ℕ) (x : Fin (2*r+1) → ℝ) (σ : Equiv.Perm (Fin (2*r+1))) :
    scalarMedian r (fun i => x (σ i)) = scalarMedian r x := scalarMedian_perm r x σ

example (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    scalarMedian 1 (x ∘ σ) = scalarMedian 1 x ∧ (∑ i, x (σ i))/3 = (∑ i, x i)/3 :=
  ⟨scalarMedian_perm 1 x σ, meanThree_perm x σ⟩

-- Literal estimation errors, with theta subtracted, at the manuscript's b>6.
example (z b θ : ℝ) (hz : 0 ≤ z) (hb : 6 < b) :
    scalarMedian 1 ![θ+z, θ+2*z, θ+b*z]-θ = 2*z ∧
      meanThree ![θ+z, θ+2*z, θ+b*z]-θ = (b+3)/3*z := by
  rw [median_three_scaled_exact hz (by linarith), meanThree_scaled_exact]
  constructor <;> ring

example (h b : ℝ) (hh : 0 < h) (hb : 6 < b) :
    superadditiveTransform (scalarMedian 1) ![h, 2*h, b*h] = 3*h ∧
      meanThree ![h, 2*h, b*h] = (b+3)/3*h ∧ 3*h < meanThree ![h, 2*h, b*h] := by
  refine ⟨median_three_scale_bound hh.le (by linarith), ?_, ?_⟩
  · simp [meanThree, Fin.sum_univ_succ]
    ring
  · have ht : 0 < (b-6)*h := mul_pos (by linarith) hh
    simp only [meanThree, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    nlinarith



universe uMedianReader

-- The actual scalar median is continuous, including the arity-one case.
example (r : ℕ) : Continuous (scalarMedian r) := scalarMedian_continuous r

-- The full reverse inequality is supplied by the existing ordered-coordinate
-- formula and is retained by the bridge to every subset of a prescribed size.
example (r : ℕ) (a : Fin (2*r+1) → ℝ) (ha : 0 ≤ a) :
    superadditiveTransform (scalarMedian r) a =
      ⨅ ℓ : Fin (r+1),
        ⨅ J : {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)},
          (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ) :=
  median_transform_cut_formula r a ha

example (r : ℕ) {p : ℝ} (hp : p ∈ Ioo 0 1) {a : Fin (2*r+1) → ℝ} (ha : 0 ≤ a) :
    sSup (hardyTailValues.{uMedianReader} (scalarMedian r) p a) =
        (⨅ ℓ : Fin (r+1),
          ⨅ J : {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)},
            (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ)) ∧
      sSup (comonotoneHardyTailValues.{uMedianReader} (scalarMedian r) p a) =
        (⨅ ℓ : Fin (r+1),
          ⨅ J : {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)},
            (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ)) :=
  median_hardy_tail_sharp r hp ha

example (r : ℕ) {p : ℝ} (hp : p ∈ Ioo 0 1) {a : Fin (2*r+1) → ℝ} (ha : 0 ≤ a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ comonotoneHardyTailValues.{uMedianReader} (scalarMedian r) p a,
      (⨅ ℓ : Fin (r+1),
        ⨅ J : {J : Finset (Fin (2*r+1)) // J.card = r+(ℓ.val+1)},
          (∑ i ∈ J.val, a i) / ((ℓ.val+1 : ℕ) : ℝ)) - ε < z :=
  median_comonotone_near_sharp r hp ha hε


universe uNormReader

-- Full exponent range, including infinity, with the actual PiLp norm.
example (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] {a : Fin n → ℝ} (ha : 0 ≤ a) :
    superadditiveTransform (coordinateLpNorm n q) a = ∑ i, a i :=
  ellp_superadditive_transform n q ha

example (n : ℕ) :
    @coordinateLpNorm n (2 : ℝ≥0∞) ⟨by norm_num⟩ (fun _ => 1) = Real.sqrt n ∧
      superadditiveTransform (@coordinateLpNorm n (2 : ℝ≥0∞) ⟨by norm_num⟩) (fun _ => 1) = n :=
  euclidean_norm_sharp_ones n

-- Literal completed Hardy graphs and ordinary finite graph sum. The scalar
-- variables need only be nonnegative almost everywhere on the original space.
example {Ω : Type uNormReader} [MeasurableSpace Ω] (n : ℕ)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → (Fin (n+1) → ℝ)} (hm : ∀ i, Measurable (fun ω => X ω i))
    (hn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X ω i)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    DecLE
      (hardyFamilyIntegral
        (interior (dom (tailQuantile (Measure.map (fun ω => coordinateLpNorm (n+1) q (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => coordinateLpNorm (n+1) q (X ω)) μ)))
      (finiteOperatorSum (fun i => hardyFamilyIntegral
        (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)))) :=
  (hardy_tail_norm_sum_bound q μ (measurable_pi_iff.mpr hm) hn hi).2 (Nat.succ_pos n)

-- Both exact suprema quantify over the general classes checked independently
-- above for the sharpness theorem; no fixed atomless-space restriction occurs.
example (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : Fin n → ℝ} (ha : 0 ≤ a) :
    sSup (hardyTailValues.{uNormReader} (coordinateLpNorm n q) p a) = ∑ i, a i ∧
      sSup (comonotoneHardyTailValues.{uNormReader} (coordinateLpNorm n q) p a) = ∑ i, a i :=
  ellp_hardy_tail_sharp n q hp ha

-- Whole-graph sum/aggregation identity, retaining the explicit completed
-- restriction for the empty family rather than identifying two different zeros.
example {Ω : Type uNormReader} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    completedDecreasingRestriction (Ioo 0 1)
        (finiteOperatorSum (fun i => quantileHardy (Measure.map (fun ω => X ω i) μ))) =
      aggregationOperator (@coordinateMass n) (Ioo 0 1)
        (fun i => quantileHardy (Measure.map (fun ω => X ω i) μ)) :=
  (quantileHardy_sum_graphs μ hm hn hi).1


universe uHardySharpness

-- Both exact suprema, over all probability spaces in an arbitrary universe.
-- The strictly-positive homogeneity convention is discharged by the checked bridge.
example {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hm : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hh : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : Fin n → ℝ} (ha : 0 ≤ a) :
    superadditiveTransform F a = sSup (hardyTailValues.{uHardySharpness} F p a) ∧
      superadditiveTransform F a = sSup (comonotoneHardyTailValues.{uHardySharpness} F p a) :=
  hardy_tail_aggregation_sharp (aggregationAxioms_of_positive_homogeneity hn hm hh) hFc hp ha

-- Independently expand the actual original-space upper constraint and completed Hardy graphs.
example {Ω : Type uHardySharpness} [MeasurableSpace Ω]
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → (Fin n → ℝ)} (hm : Measurable X) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hfin : ∀ i, (Set.range (fun ω => X ω i)).Finite)
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : Fin n → ℝ} {z : ℝ}
    (hMarg : ∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
      (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a i})
    (hAgg : hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => F (X ω)) μ))))
      (tailQuantile (Measure.map (fun ω => F (X ω)) μ)) p = {z}) :
    z ≤ superadditiveTransform F a :=
  hardyTailValues_le hF hFc hp a z
    ⟨Ω, inferInstance, μ, inferInstance, X, hm, hx, hfin, hMarg, hAgg⟩

-- The finite lower model derives all shape, measurability and completed-value conditions.
example {n m : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {p ε : ℝ}
    (hp : p ∈ Ioo 0 1) (hε : ε ∈ Ioo 0 1)
    {v : Fin m → (Fin n → ℝ)} (hv : ∀ j, 0 ≤ v j)
    {a : Fin n → ℝ} (hva : (∑ j, v j) ≤ a) :
    ∃ q : Fin n → ℝ → ℝ, ∃ z : ℝ,
      (∀ i, Measurable (q i)) ∧ (∀ i, Antitone (q i)) ∧
      (∀ i, (Set.range (q i)).Finite) ∧ (∀ i r, 0 ≤ q i r) ∧
      (∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (q i) unitUniform))))
        (tailQuantile (Measure.map (q i) unitUniform)) p = {a i}) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun r => F (fun i => q i r)) unitUniform))))
        (tailQuantile (Measure.map (fun r => F (fun i => q i r)) unitUniform)) p = {z} ∧
      (1-ε)*(∑ j, F (v j)) ≤ z :=
  geometric_step_hardy_lower_model hF hFc hp hε hv hva


-- Comonotone representation in joint law, with no uniform variable on the original space.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {X : Ω → (Fin n → ℝ)} (hXm : AEMeasurable X μ) (hX : ∀ ω, 0 ≤ X ω)
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hlaw : Measure.map X μ = Measure.map (fun u i => q i u) unitUniform)
    {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) :
    tailQuantile (Measure.map (fun ω => F (X ω)) μ) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (fun ω => X ω i) μ)) :=
  comonotone_aggregation_quantile_joint_law hXm hX hq hlaw hF hFc

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {X : Ω → (Fin n → ℝ)} (hXm : AEMeasurable X μ) (hX : ∀ ω, 0 ≤ X ω)
    {q : Fin n → ℝ → ℝ} (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1))
    (hlaw : Measure.map X μ = Measure.map (fun u i => q i u) unitUniform)
    {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : Fin n → ℝ}
    (hQa : ∀ i, tailQuantile (Measure.map (fun ω => X ω i) μ) p = {a i}) :
    tailQuantile (Measure.map (fun ω => F (X ω)) μ) p = {F a} :=
  comonotone_fixed_quantile_joint_law hXm hX hq hlaw hF hFc hp hQa

-- Prescribed marginal Hardy values are derived from explicit finite steps.
example {m : ℕ} {p a : ℝ} (hp : p ∈ Ioo 0 1) {v s : Fin m → ℝ}
    (hv : ∀ j, 0 ≤ v j) (hva : (∑ j, v j) ≤ a) (hs : ∀ j, 0 < s j ∧ s j ≤ p) :
    ∃ q : ℝ → ℝ, Measurable q ∧ Antitone q ∧ (Set.range q).Finite ∧
      (∀ u, 0 ≤ q u) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map q unitUniform))))
        (tailQuantile (Measure.map q unitUniform)) p = {a} ∧
      ∀ j u, u ≤ s j → p*v j/s j ≤ q u :=
  finite_steps_prescribed_hardy hp hv hva hs

example {p ε : ℝ} (hp : 0 ≤ p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (m j : ℕ) :
    0 ≤ geometricScale p ε m j-geometricScale p ε m (j+1) ∧
      (1-ε)*geometricScale p ε m j ≤
        geometricScale p ε m j-geometricScale p ε m (j+1) :=
  geometricBand_length_lower hp hε0 hε1 m j

example {a b p : ℝ} (h0a : 0 ≤ a) (hab : a ≤ b) (hbp : b ≤ p) (c : ℝ) :
    (∫ u in (0 : ℝ)..p, (Ioc a b).indicator (fun _ => c) u) = (b-a)*c :=
  interval_indicator_band_integral h0a hab hbp c

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hm : AEMeasurable X μ) (hn : ∀ ω, 0 ≤ X ω) (hf : (Set.range X).Finite) :
    Integrable X μ := finite_nonnegative_range_integrable hm hn hf


-- A genuine finite-valued nonnegative pair on the same two-atom original law.
example : ∃ X Y : ℝ → ℝ, Measurable X ∧ Measurable Y ∧
    (∀ ω, 0 ≤ X ω ∧ 0 ≤ Y ω) ∧ (Set.range X).Finite ∧ (Set.range Y).Finite ∧
    tailQuantile (Measure.map X symmetricBernoulli) (3/4) = {0} ∧
    tailQuantile (Measure.map Y symmetricBernoulli) (3/4) = {0} ∧
    tailQuantile (Measure.map (fun ω => X ω+Y ω) symmetricBernoulli) (3/4) = {1} ∧
    tailQuantile (Measure.map (fun ω => X ω+Y ω) symmetricBernoulli) (3/4) ≠ {(0 : ℝ)+0} :=
  quantile_sharpness_fails_without_comonotonicity

-- The standing strictly-positive homogeneity assumption suffices for the whole graph identity.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}
    (hU : AEMeasurable U μ) (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hm : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hh : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1)) (hX : ∀ ω i, 0 ≤ q i (U ω)) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (fun ω => q i (U ω)) μ)) :=
  comonotone_aggregation_nonnegative_original_space hU hUlaw
    (aggregationAxioms_of_positive_homogeneity hn hm hh) hFc hq hX


-- Nonnegativity is imposed only on actual variables on the original space.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}
    (hU : AEMeasurable U μ) (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1)) (hX : ∀ ω i, 0 ≤ q i (U ω)) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) =
      aggregationOperator F (Ioo 0 1)
        (fun i => tailQuantile (Measure.map (fun ω => q i (U ω)) μ)) :=
  comonotone_aggregation_nonnegative_original_space hU hUlaw hF hFc hq hX

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}
    (hU : AEMeasurable U μ) (hUlaw : Measure.map U μ = unitUniform)
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {q : Fin n → ℝ → ℝ}
    (hq : ∀ i, AntitoneOn (q i) (Ioo 0 1)) (hX : ∀ ω i, 0 ≤ q i (U ω))
    {p : ℝ} (hp : p ∈ Ioo 0 1) {a : Fin n → ℝ}
    (hQa : ∀ i, tailQuantile (Measure.map (fun ω => q i (U ω)) μ) p = {a i}) :
    tailQuantile (Measure.map (fun ω => F (fun i => q i (U ω))) μ) p = {F a} :=
  comonotone_fixed_quantile_original_space hU hUlaw hF hFc hq hX hp hQa

-- Literal finite-valued, nonnegative common-uniform candidates; constants attain the maximum.
example {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : AggregationAxioms F)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {a : Fin n → ℝ} (ha : 0 ≤ a) :
    IsGreatest {b : ℝ | ∃ q : Fin n → ℝ → ℝ,
      (∀ i, AntitoneOn (q i) (Ioo 0 1)) ∧ (∀ i u, 0 ≤ q i u) ∧
      (∀ i, (Set.range (q i)).Finite) ∧
      (∀ i, tailQuantile (Measure.map (q i) unitUniform) p = {a i}) ∧
      b ∈ tailQuantile (Measure.map (fun u => F (fun i => q i u)) unitUniform) p} (F a) :=
  comonotone_quantile_sharp_isGreatest hF hFc hp ha

example {ι : Type*} [Nonempty ι] (f : ι → IncGraph)
    (hb : BddAbove (Set.range f)) (h : IncGraph) :
    h = ⨆ i, f i ↔ (∀ i, f i ≤ h) ∧
      ∀ g : IncGraph, (∀ i, f i ≤ g) → h ≤ g := inc_sup_universal_property f hb h

example {ι : Type*} [Nonempty ι] (f : ι → DecGraph)
    (hb : BddAbove (Set.range f)) (h : DecGraph) :
    h = ⨆ i, f i ↔ (∀ i, f i ≤ h) ∧
      ∀ g : DecGraph, (∀ i, f i ≤ g) → h ≤ g := dec_sup_universal_property f hb h

example (f g h : IncGraph) :
    f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) ∧
      f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) := inc_graph_distributivity f g h

example (f g h : DecGraph) :
    f ⊓ (g ⊔ h) = (f ⊓ g) ⊔ (f ⊓ h) ∧
      f ⊔ (g ⊓ h) = (f ⊔ g) ⊓ (f ⊔ h) := dec_graph_distributivity f g h

example {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → IncGraph) (x u : ℝ) :
    (u ∈ (⨅ i, f i).val x → ∃ i, u ∈ (f i).val x) ∧
      (u ∈ (⨆ i, f i).val x → ∃ i, u ∈ (f i).val x) := inc_finite_extremum_graph_points f x u

example {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → DecGraph) (x u : ℝ) :
    (u ∈ (⨅ i, f i).val x → ∃ i, u ∈ (f i).val x) ∧
      (u ∈ (⨆ i, f i).val x → ∃ i, u ∈ (f i).val x) := dec_finite_extremum_graph_points f x u

example : IncGraph.vertical 0 ⊓ IncGraph.vertical 1 = IncGraph.vertical 1 ∧
    (IncGraph.vertical 0).val 1 = ∅ ∧
    (∀ n : ℕ, (IncGraph.step (1/((n : ℝ)+1))).val 0 = {0}) ∧
    (⨆ n : ℕ, IncGraph.step (1/((n : ℝ)+1))).val 0 = Icc (0 : ℝ) 1 :=
  ⟨IncGraph.inf_vertical_zero_one, IncGraph.vertical_zero_empty_at_one,
    IncGraph.infinite_fiber_completion_example⟩

-- L1 of the concave composition is derived before applying Jensen on a closed half-line.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} {D : Set ℝ} (hg : ConcaveOn ℝ D g) (hm : MonotoneOn g D)
    (hc : ContinuousOn g D) {a x₀ : ℝ} (ha : a ∈ D) (hx : x₀ ∈ D)
    (hax : a < x₀) (htail : Ici x₀ ⊆ D) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, x₀ ≤ X ω) (hXi : Integrable X μ) :
    Integrable (fun ω => g (X ω)) μ ∧ (∫ ω, g (X ω) ∂μ) ≤ g (∫ ω, X ω ∂μ) :=
  concave_monotone_jensen_derived_integrability hg hm hc ha hx hax htail hX hXi


-- Full completed operators, including their domains and boundary fibers.
example {κ p : ℝ} (hκ : 1 < κ) (hp : 0 < p) :
    MaximalDecreasing (powerProfile κ 1) ∧ MaximalDecreasing (exponentialProfile 1) ∧
      interior (dom (inverse (powerProfile κ 1))) = Ioi 0 ∧
      interior (dom (inverse (exponentialProfile 1))) = Ioi 0 ∧
      hardyFamilyIntegral (Ioi 0) (inverse (powerProfile κ 1)) p =
        {(κ/(κ-1))*p^((-1 : ℝ)/κ)} ∧
      hardyFamilyIntegral (Ioi 0) (inverse (exponentialProfile 1)) p = {1-Real.log p} :=
  hardy_profile_identities hκ hp

example {κ C : ℝ} (hκ : 1 < κ) (hC : 0 < C) :
    hardyTailTransform (outputScale C (powerProfile κ 1)) =
      outputScale (C*(κ/(κ-1))^κ) (powerProfile κ 1) ∧
    hardyTailTransform (outputScale C (exponentialProfile 1)) =
      outputScale (C*Real.exp 1) (exponentialProfile 1) :=
  hardy_regularized_profiles hκ hC

example {β : Operator} (hβ : MaximalDecreasing β)
    (hz : IsGLB (dom (inverse β)) 0) (hp : ∃ p ∈ dom (inverse β), 0 < p)
    {s : ℝ → ℝ} (hs : ∀ p ∈ interior (dom (inverse β)), s p ∈ inverse β p)
    (hi : ∀ p ∈ interior (dom (inverse β)), IntervalIntegrable s volume 0 p) :
    MaximalDecreasing (hardyTailTransform β) ∧
      inverse (hardyTailTransform β) =
        hardyFamilyIntegral (interior (dom (inverse β))) (inverse β) ∧
      interior (ran (hardyTailTransform β)) = interior (ran β) :=
  hardyTailTransform_well_defined hβ hz hp hs hi

-- The weighted mean itself is stated literally, with both endpoint weights allowed.
example {a b w : ℝ} (ha : 0 < a) (hb : 0 < b) (hw : w ∈ Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun κ : ℝ => (w*a^((-1 : ℝ)/κ)+(1-w)*b^((-1 : ℝ)/κ))^(-κ))
      Filter.atTop (𝓝 (a^w*b^(1-w))) :=
  weighted_power_geometric_limit ha hb hw

example {n : ℕ} {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {a : Fin n → ℝ} (ha : 0 ≤ a) :
    superadditiveTransform (fun x : Fin n → ℝ => (∑ i, (x i)^q)^(1/q)) a =
      (∑ i, (a i)^q)^(1/q) :=
  quasi_norm_superadditive_transform hq hq1 ha

example {n : ℕ} {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {x y : Fin n → ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∑ i, (x i)^q)^(1/q)+(∑ i, (y i)^q)^(1/q) ≤
      (∑ i, (x i+y i)^q)^(1/q) :=
  coordinateQuasiNorm_superadditive hq hq1 hx hy


-- The profile-specific scaled logarithmic limit and both convexity implications.
example {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun κ : ℝ => κ*(a^((-1 : ℝ)/κ)-1)) Filter.atTop
      (𝓝 (-Real.log a)) := scaled_power_log_limit ha

example {α : ℝ → ℝ} {D : Set ℝ} (hα : ∀ x ∈ D, 0 < α x)
    (hc : ConvexOn ℝ D (fun x => -Real.log (α x))) {κ : ℝ} (hκ : 0 < κ) :
    ConvexOn ℝ D (fun x => (α x)^((-1 : ℝ)/κ)) :=
  log_convex_implies_all_power_convex hα hc hκ

example {α : ℝ → ℝ} {D : Set ℝ} (hα : ∀ x ∈ D, 0 < α x)
    {κ : ℕ → ℝ} (hκpos : ∀ n, 0 < κ n) (hκ : Filter.Tendsto κ Filter.atTop Filter.atTop)
    (hc : ∀ n, ConvexOn ℝ D (fun x => (α x)^((-1 : ℝ)/κ n))) :
    ConvexOn ℝ D (fun x => -Real.log (α x)) :=
  limiting_power_convex_implies_log_convex hα hκpos hκ hc


-- Actual completed deterministic Hardy aggregation, from one finite prefix area.
example {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hm : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hh : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x)
    (hFc : ContinuousOn F {v | 0 ≤ v}) {L : EReal} (hL : 0 < L)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hIeq : ∀ i, interior (dom (f i)) = positiveInitialInterval L)
    (hpos : ∀ i, ∀ x ∈ positiveInitialInterval L, ∀ v ∈ f i x, 0 ≤ v)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, ∀ x ∈ positiveInitialInterval L, s i x ∈ f i x)
    {b : ℝ} (hb : 0 < b) (hbI : Ioo (0 : ℝ) b ⊆ positiveInitialInterval L)
    (hfinite : ∀ i, (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)) < ∞) :
    MaximalDecreasing (hardyFamilyIntegral (positiveInitialInterval L)
      (aggregationOperator F (positiveInitialInterval L) f)) ∧
      interior (dom (hardyFamilyIntegral (positiveInitialInterval L)
        (aggregationOperator F (positiveInitialInterval L) f))) = positiveInitialInterval L ∧
      ∀ p ∈ positiveInitialInterval L, ∃ a : Fin n → ℝ, ∃ v : ℝ,
        (∀ i, hardyFamilyIntegral (positiveInitialInterval L) (f i) p = {a i}) ∧
        hardyFamilyIntegral (positiveInitialInterval L) (aggregationOperator F (positiveInitialInterval L) f) p = {v} ∧
        v ≤ superadditiveTransform F a :=
  hardy_operator_aggregation_of_finite_area (aggregationAxioms_of_positive_homogeneity hn hm hh)
    hFc hL hf hIeq hpos hs hb hbI hfinite

-- All four implications, retaining exactly the two different monotonicity directions.
example {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Ioi 0)) :
    ((∀ κ : ℝ, 0 < κ → ConvexOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) →
      ConvexOn ℝ univ (fun x => φ (Real.exp (-x)))) ∧
      (MonotoneOn φ (Ioi 0) → ConvexOn ℝ univ (fun x => φ (Real.exp (-x))) →
        ∀ κ : ℝ, 0 < κ → ConvexOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) ∧
      ((∀ κ : ℝ, 0 < κ → ConcaveOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) →
        ConcaveOn ℝ univ (fun x => φ (Real.exp (-x)))) ∧
      (AntitoneOn φ (Ioi 0) → ConcaveOn ℝ univ (fun x => φ (Real.exp (-x))) →
        ∀ κ : ℝ, 0 < κ → ConcaveOn ℝ (Ioi 0) (fun x => φ (x^(-κ)))) :=
  power_exponential_convex_transforms hφ

example : Filter.Tendsto (fun κ : ℝ => (κ/(κ-1))^κ) Filter.atTop (𝓝 (Real.exp 1)) :=
  hardy_power_constant_limit


-- Convexity and actual one-sided derivatives on the original probability space.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hi : Integrable X μ) {p : ℝ} (hp : 0 < p) :
    ConvexOn ℝ univ (fun a => a+(∫ ω, max (X ω-a) 0 ∂μ)/p) :=
  shortfallObjective_convex hi hp

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ) {p : ℝ} (hp : 0 < p) (a : ℝ) :
    HasDerivWithinAt (fun b => b+(∫ ω, max (X ω-b) 0 ∂μ)/p)
      (1-μ.real {ω | a ≤ X ω}/p) (Iio a) a ∧
      HasDerivWithinAt (fun b => b+(∫ ω, max (X ω-b) 0 ∂μ)/p)
        (1-μ.real {ω | a < X ω}/p) (Ioi a) a :=
  shortfall_one_sided_derivatives hm hi hp a

-- The ordinary supporting-line definition, rather than an assumed subgradient.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ) {p : ℝ} (hp : 0 < p) (a : ℝ) :
    {d : ℝ | ∀ b : ℝ,
      a+(∫ ω, max (X ω-a) 0 ∂μ)/p+d*(b-a) ≤ b+(∫ ω, max (X ω-b) 0 ∂μ)/p} =
        Icc (1-μ.real {ω | a ≤ X ω}/p) (1-μ.real {ω | a < X ω}/p) :=
  shortfall_subgradient_interval hm hi hp a

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ) {p : ℝ} (hp : 0 < p) (a : ℝ) :
    {d : ℝ | ∀ b : ℝ,
      a+(∫ ω, max (X ω-a) 0 ∂μ)/p+d*(b-a) ≤ b+(∫ ω, max (X ω-b) 0 ∂μ)/p} =
        (fun u => 1-u/p) '' survival (Measure.map X μ) a :=
  shortfall_subgradient_survival hm hi hp a

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hm : Measurable X) (hi : Integrable X μ) {p : ℝ} (hp : 0 < p) (a : ℝ) :
    (∀ b : ℝ, a+(∫ ω, max (X ω-a) 0 ∂μ)/p ≤ b+(∫ ω, max (X ω-b) 0 ∂μ)/p) ↔
      a ∈ tailQuantile (Measure.map X μ) p := by
  simpa only [realSubgradient, mem_setOf_eq, zero_mul, add_zero] using
    shortfall_zero_subgradient_iff_quantile hm hi hp a


-- Finite nonnegative extended areas imply the full completed-operator area bound.
example {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hm : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hh : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x)
    (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i)) (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {b : ℝ} (hb : 0 < b) (hbI : Ioo (0 : ℝ) b ⊆ I)
    {s : Fin n → ℝ → ℝ} (hs : ∀ i, ∀ x ∈ I, s i x ∈ f i x)
    (hfinite : ∀ i, (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)) < ∞)
    {t : ℝ → ℝ} (ht : ∀ x ∈ I, t x ∈ aggregationOperator F I f x) :
    Integrable t (volume.restrict (Ioo (0 : ℝ) b)) ∧
      (∫ x in Ioo (0 : ℝ) b, t x) ≤ superadditiveTransform F
        (fun i => (∫⁻ x in Ioo (0 : ℝ) b, ENNReal.ofReal (s i x)).toReal) :=
  aggregation_area_finite_nonnegative (aggregationAxioms_of_positive_homogeneity hn hm hh)
    hFc hI hord hne hf hdom hpos hb hbI hs hfinite ht

-- Actual completed Hardy profiles; homogeneity is assumed only for c>0.
example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hmF : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hh : ∀ c : ℝ, 0 < c → ∀ x, 0 ≤ x → F (c • x) = c*F x)
    (hFc : ContinuousOn F {x | 0 ≤ x}) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → (Fin n → ℝ)} (hm : Measurable X) (hx : ∀ ω, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) {p : ℝ} (hp : 0 < p ∧ p < 1) :
    ∃ a : Fin n → ℝ, ∃ v : ℝ,
      (∀ i, hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => X ω i) μ))))
        (tailQuantile (Measure.map (fun ω => X ω i) μ)) p = {a i}) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (fun ω => F (X ω)) μ))))
        (tailQuantile (Measure.map (fun ω => F (X ω)) μ)) p = {v} ∧
      v ≤ superadditiveTransform F a :=
  hardy_tail_aggregation_of_positive_homogeneity hn hmF hh hFc μ hm hx hi hp

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : AEMeasurable X μ) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) {Z : Ω → ℝ}
    (hZ : AEMeasurable Z μ) (hz : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1)
    {p : ℝ} (hp : 0 < p) :
    (∫ ω, F (X ω)*Z ω ∂μ)/p ≤ superadditiveTransform F
      (fun i => (∫ ω, X ω i*Z ω ∂μ)/p) :=
  weighted_aggregation_bound hF hFc μ hm hx hi hZ hz hp

-- Strict and weak tails are the actual one-sided survival limits, including atoms.
example {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Filter.Tendsto (fun t => ν.real {ω | t < X ω}) (𝓝[<] a) (𝓝 (ν.real {ω | a ≤ X ω})) ∧
      Filter.Tendsto (fun t => ν.real {ω | t < X ω}) (𝓝[>] a) (𝓝 (ν.real {ω | a < X ω})) :=
  survival_random_variable_jump_limits ν hX a

example (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p ∧ p < 1) :
    (tailQuantile μ p).Nonempty ∧ IsClosed (tailQuantile μ p) ∧
      (tailQuantile μ p).OrdConnected ∧ ∃ a b : ℝ, tailQuantile μ p ⊆ Icc a b :=
  ⟨tailQuantile_fiber_nonempty μ hp, tailQuantile_fiber_closed μ p,
   tailQuantile_fiber_ordConnected μ p, tailQuantile_fiber_bounded μ hp⟩

example {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {q : ℝ → ℝ} {V : Ω → ℝ}
    (hV : Measurable V) (hq : Measurable q) (hVlaw : Measure.map V ν = unitUniform)
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p) :
    Measure.map (q ∘ V) ν = μ := tailQuantile_selection_uniform_argument ν μ hV hq hVlaw hsel

example (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ → ℝ}
    (hsel : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile μ p) (t : ℝ) :
    volume ((q ⁻¹' Ioi t) ∩ Ioo 0 1) = μ (Ioi t) := tailQuantile_selection_tail_volume μ hsel t


-- General integral aggregation, including atoms and zero-mean coordinate faces.
example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {x | 0 ≤ x})
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → (Fin n → ℝ)}
    (hm : AEMeasurable X μ) (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hi : ∀ i, Integrable (fun ω => X ω i) μ) :
    Integrable (fun ω => F (X ω)) μ ∧
      (∫ ω, F (X ω) ∂μ) ≤ superadditiveTransform F (fun i => ∫ ω, X ω i ∂μ) :=
  ⟨aggregation_composition_integrable_ae hF hFc μ hm hx hi,
   aggregation_integral_bound_ae hF hFc μ hm hx hi⟩

example {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i)) (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v) :
    MaximalDecreasing (aggregationOperator F I f) ∧
      interior (dom (aggregationOperator F I f)) = I ∧
      dom (aggregationOperator F I f) ⊆ closure I ∧
      ∀ x ∈ I, aggregationOperator F I f x =
        Icc (F (fun i => sInf (f i x))) (F (fun i => sSup (f i x))) :=
  aggregationOperator_properties hF hFc hI hord hne hf hdom hpos

example {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : AggregationAxioms F) (hFc : ContinuousOn F {v | 0 ≤ v})
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    {f : Fin n → Operator} (hf : ∀ i, MaximalDecreasing (f i))
    (hdom : ∀ i, I ⊆ dom (f i)) (hpos : ∀ i, ∀ x ∈ I, ∀ v ∈ f i x, 0 ≤ v)
    {g : Operator} (hg : MaximalDecreasing g) (hgd : dom g ⊆ closure I)
    (hgv : ∀ x ∈ I, g x = Icc (F (fun i => sInf (f i x))) (F (fun i => sSup (f i x)))) :
    g = aggregationOperator F I f :=
  aggregationOperator_unique hF hFc hI hord hne hf hdom hpos hg hgd hgv


-- Both signed infinities are undefined; all other extended values are retained.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Ω → ℝ) :
    signedExtendedIntegral μ s = none ↔
      (∫⁻ x, ENNReal.ofReal (s x) ∂μ) = ∞ ∧
        (∫⁻ x, ENNReal.ofReal (-s x) ∂μ) = ∞ :=
  signedExtendedIntegral_eq_none_iff μ s

example (a b : EReal) (s : ℝ → ℝ) :
    orientedExtendedIntegral b a s = (orientedExtendedIntegral a b s).map (fun v => -v) ∧
      orientedExtendedIntegral a a s = some 0 :=
  ⟨orientedExtendedIntegral_reverse a b s, orientedExtendedIntegral_self a s⟩

example (μ : Measure ℝ) [NoAtoms μ] (a b : EReal) {J : Set ℝ}
    (hlo : {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} ⊆ J)
    (hhi : J ⊆ {x : ℝ | a ≤ (x : EReal) ∧ (x : EReal) ≤ b}) :
    μ.restrict {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} = μ.restrict J :=
  extendedInterval_restrict_between_endpoints μ a b hlo hhi

example {f : Operator} (hf : Increasing f ∨ Decreasing f)
    {I : Set ℝ} (hI : MeasurableSet I) (hdom : I ⊆ dom f) :
    ∃ s : ℝ → ℝ, Measurable s ∧ (∀ x ∈ I, s x ∈ f x) ∧
      ∀ t : ℝ → ℝ, (∀ x ∈ I, t x ∈ f x) →
        (Integrable t (volume.restrict I) ↔ (∫⁻ x in I, ENNReal.ofReal |s x|) < ∞) ∧
        (∀ ψ : ℝ → ℝ≥0∞, (∫⁻ x in I, ψ (s x)) = ∫⁻ x in I, ψ (t x)) ∧
        (∀ ψ : ℝ → ℝ, signedExtendedIntegral (volume.restrict I) (fun x => ψ (s x)) =
          signedExtendedIntegral (volume.restrict I) (fun x => ψ (t x))) ∧
        (Integrable s (volume.restrict I) → aumannIntegral (volume.restrict I) f = {∫ x in I, s x}) :=
  scalar_integration_well_defined hf hI hdom

example {μ : Measure ℝ} {s : ℝ → ℝ} (hs : Integrable s μ) :
    signedExtendedIntegral μ s = some (Real.toEReal (∫ x, s x ∂μ)) :=
  signedExtendedIntegral_of_integrable hs


-- Local L1 is sufficient for every whole-operator Hardy calculus identity.
example {f g : Operator} (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hpg : ∃ a ∈ dom g, 0 < a)
    {sf sg : ℝ → ℝ} (hsf : ∀ p ∈ interior (dom f), sf p ∈ f p)
    (hsg : ∀ p ∈ interior (dom g), sg p ∈ g p)
    (hiF : ∀ p ∈ interior (dom f), IntervalIntegrable sf volume 0 p)
    (hiG : ∀ p ∈ interior (dom g), IntervalIntegrable sg volume 0 p) :
    DecLE f (hardyFamilyIntegral (interior (dom f)) f) ∧
      (DecLE f g → DecLE (hardyFamilyIntegral (interior (dom f)) f)
        (hardyFamilyIntegral (interior (dom g)) g)) ∧
      (interior (dom g) = interior (dom f) →
        hardyFamilyIntegral (interior (dom (add f g))) (add f g) =
          add (hardyFamilyIntegral (interior (dom f)) f)
            (hardyFamilyIntegral (interior (dom g)) g)) ∧
      ∀ c : ℝ, 0 < c →
        hardyFamilyIntegral (interior (dom (outputScale c f))) (outputScale c f) =
          outputScale c (hardyFamilyIntegral (interior (dom f)) f) :=
  hardyFamilyIntegral_calculus_locally_integrable hf hg hzf hpf hzg hpg hsf hsg hiF hiG

example {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    {s φ : ℝ → ℝ} (hs : ∀ p ∈ interior (dom f), s p ∈ f p)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    (hφ : ConvexOn ℝ (interior (dom f)) φ)
    (hφsel : ∀ p ∈ interior (dom f), φ p ∈ f p) :
    ∃ ψ : ℝ → ℝ,
      ConvexOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      ∀ p ∈ interior (dom (hardyFamilyIntegral (interior (dom f)) f)),
        ψ p ∈ hardyFamilyIntegral (interior (dom f)) f p :=
  hardyFamilyIntegral_preserves_convexity_locally_integrable hf hz hp hs hi hφ hφsel

example {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    {s φ : ℝ → ℝ} (hs : ∀ p ∈ interior (dom f), s p ∈ f p)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    (hφ : ConcaveOn ℝ (interior (dom f)) φ)
    (hφsel : ∀ p ∈ interior (dom f), φ p ∈ f p) :
    ∃ ψ : ℝ → ℝ,
      ConcaveOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      ∀ p ∈ interior (dom (hardyFamilyIntegral (interior (dom f)) f)),
        ψ p ∈ hardyFamilyIntegral (interior (dom f)) f p :=
  hardyFamilyIntegral_preserves_concavity_locally_integrable hf hz hp hs hi hφ hφsel


-- The actual completed Hardy graph and literal original-space product supremum.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : Measurable X) (hXi : Integrable X μ)
    {p : ℝ} (hp : 0 < p ∧ p < 1) :
    ∃ v : ℝ,
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map X μ))))
        (tailQuantile (Measure.map X μ)) p = {v} ∧
      IsLeast (Set.range (fun a => a + (∫ ω, max (X ω-a) 0 ∂μ)/p)) v ∧
      IsGreatest (dualCandidates μ X p) v ∧
      IsGreatest {w | ∃ Z : Ω → ℝ, AEMeasurable Z μ ∧
        (∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) ∧
        (∫ ω, Z ω ∂μ) = p ∧ w = ∫ ω, X ω*Z ω ∂μ} (p*v) ∧
      v = sSup {w | ∃ Z : Ω → ℝ, AEMeasurable Z μ ∧
        (∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ 1) ∧
        (∫ ω, Z ω ∂μ) = p ∧ w = ∫ ω, X ω*Z ω ∂μ} / p ∧
      {a | ∀ b : ℝ, a + (∫ ω, max (X ω-a) 0 ∂μ)/p ≤
        b + (∫ ω, max (X ω-b) 0 ∂μ)/p} = tailQuantile (Measure.map X μ) p :=
  hardy_quantile_original_variational hXm hXi hp


-- Literal hit-open formulation and genuine extended-real endpoints.
example {Θ : Type*} [MeasurableSpace Θ] {h : Θ → Set ℝ}
    (hn : ∀ θ, (h θ).Nonempty) (hord : ∀ θ, (h θ).OrdConnected) :
    (∀ O : Set ℝ, IsOpen O → MeasurableSet {θ | (h θ ∩ O).Nonempty}) ↔
      Measurable (fun θ => sInf ((fun x : ℝ => (x : EReal)) '' h θ)) ∧
        Measurable (fun θ => sSup ((fun x : ℝ => (x : EReal)) '' h θ)) :=
  hitOpenMeasurable_iff_endpoints hn hord

example {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) {l u : Θ → ℝ}
    (hl : Integrable l μ) (hu : Integrable u μ) (hlu : l ≤ᵐ[μ] u) :
    aumannIntegral μ (fun θ => Icc (l θ) (u θ)) =
      Icc (∫ θ, l θ ∂μ) (∫ θ, u θ ∂μ) := by
  rw [aumannIntegral_interval, aumannInterval_eq μ hl hu hlu]


-- Complete Hardy calculus: shared domain for addition; different domains for order.
example {f g : Operator} (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hpg : ∃ a ∈ dom g, 0 < a)
    {sf sg : ℝ → ℝ} (hsf : ∀ p ∈ interior (dom f), sf p ∈ f p)
    (hsg : ∀ p ∈ interior (dom g), sg p ∈ g p)
    (hiF : Integrable sf (volume.restrict (interior (dom f))))
    (hiG : Integrable sg (volume.restrict (interior (dom g)))) :
    DecLE f (hardyFamilyIntegral (interior (dom f)) f) ∧
      (DecLE f g → DecLE (hardyFamilyIntegral (interior (dom f)) f)
        (hardyFamilyIntegral (interior (dom g)) g)) ∧
      (interior (dom g) = interior (dom f) →
        hardyFamilyIntegral (interior (dom (add f g))) (add f g) =
          add (hardyFamilyIntegral (interior (dom f)) f)
            (hardyFamilyIntegral (interior (dom g)) g)) ∧
      ∀ c : ℝ, 0 < c →
        hardyFamilyIntegral (interior (dom (outputScale c f))) (outputScale c f) =
          outputScale c (hardyFamilyIntegral (interior (dom f)) f) :=
  hardyFamilyIntegral_calculus hf hg hzf hpf hzg hpg hsf hsg hiF hiG


-- The actual Aumann dilation family, with the scalar identity derived, not defined.
example {f : Operator} (hf : MaximalDecreasing f) (hz : IsGLB (dom f) 0)
    (hp : ∃ a ∈ dom f, 0 < a) {s : ℝ → ℝ}
    (hs : ∀ p ∈ interior (dom f), s p ∈ f p)
    (hi : Integrable s (volume.restrict (interior (dom f)))) :
    let I := interior (dom f)
    MaximalDecreasing (hardyFamilyIntegral I f) ∧
      interior (dom (hardyFamilyIntegral I f)) = I ∧
      dom (hardyFamilyIntegral I f) ⊆ closure I ∧
      (∀ p ∈ I, hardyFamilyIntegral I f p = {(∫ u in (0 : ℝ)..p, s u)/p}) ∧
      ∀ g : Operator, MaximalDecreasing g → dom g ⊆ closure I →
        (∀ p ∈ I, g p = {(∫ u in (0 : ℝ)..p, s u)/p}) →
        g = hardyFamilyIntegral I f := by
  simpa only [hardyScalar] using hardyFamilyIntegral_of_integrable hf hz hp hs hi

example (I : Set ℝ) (f : Operator) :
    hardyFamilyIntegral I f = decreasingFamilyIntegral unitUniform I
      (fun r => negOut (completion I (restrictOperator (negOut (fun x => f (r*x))) I))) :=
  hardyFamilyIntegral_eq_actual_dilations I f

example {f : Operator} (hf : MaximalDecreasing f) (hz : IsGLB (dom f) 0)
    (hp : ∃ a ∈ dom f, 0 < a) {s φ : ℝ → ℝ}
    (hs : ∀ p ∈ interior (dom f), s p ∈ f p)
    (hi : Integrable s (volume.restrict (interior (dom f))))
    (hφ : ConvexOn ℝ (interior (dom f)) φ)
    (hsel : ∀ p ∈ interior (dom f), φ p ∈ f p) :
    ∃ ψ : ℝ → ℝ,
      ConvexOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      (∀ p ∈ interior (dom (hardyFamilyIntegral (interior (dom f)) f)),
        ψ p ∈ hardyFamilyIntegral (interior (dom f)) f p) :=
  hardyFamilyIntegral_preserves_convexity hf hz hp hs hi hφ hsel

example {f : Operator} (hf : MaximalDecreasing f) (hz : IsGLB (dom f) 0)
    (hp : ∃ a ∈ dom f, 0 < a) {s φ : ℝ → ℝ}
    (hs : ∀ p ∈ interior (dom f), s p ∈ f p)
    (hi : Integrable s (volume.restrict (interior (dom f))))
    (hφ : ConcaveOn ℝ (interior (dom f)) φ)
    (hsel : ∀ p ∈ interior (dom f), φ p ∈ f p) :
    ∃ ψ : ℝ → ℝ,
      ConcaveOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      (∀ p ∈ interior (dom (hardyFamilyIntegral (interior (dom f)) f)),
        ψ p ∈ hardyFamilyIntegral (interior (dom f)) f p) :=
  hardyFamilyIntegral_preserves_concavity hf hz hp hs hi hφ hsel

example {f : Operator} (hf : MaximalDecreasing f) (hz : IsGLB (dom f) 0)
    (hp : ∃ a ∈ dom f, 0 < a) {s : ℝ → ℝ}
    (hs : ∀ p ∈ interior (dom f), s p ∈ f p)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {p b₁ b₂ : ℝ} (hb₁ : b₁ ∈ interior (dom f)) (hb₂ : b₂ ∈ interior (dom f))
    (hp₁ : p ∈ Ioo 0 b₁) (hp₂ : p ∈ Ioo 0 b₂) :
    hardyFamilyIntegral (Ioo 0 b₁) (completedDecreasingRestriction (Ioo 0 b₁) f) p =
      hardyFamilyIntegral (Ioo 0 b₂) (completedDecreasingRestriction (Ioo 0 b₂) f) p :=
  hardyFamilyIntegral_local_independence hf hz hp hs hi hb₁ hb₂ hp₁ hp₂


-- Current moments: arbitrary selections, original probability space, possibly infinite areas.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : 0 ≤ᵐ[μ] Y) {r : ℝ} (hr : 0 < r)
    {s q : ℝ → ℝ} (hs : ∀ t > 0, s t ∈ survival (Measure.map Y μ) t)
    (hq : ∀ p ∈ Ioo 0 1, q p ∈ tailQuantile (Measure.map Y μ) p) :
    ((∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) = ENNReal.ofReal r *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^(r-1)*s t)) ∧
    ((∫⁻ ω, ENNReal.ofReal ((Y ω)^r) ∂μ) =
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((q p)^r)) :=
  moment_identities_of_selections μ hY hY0 hr hs hq

example (r : ℕ) (a : Fin (2*r+1) → ℝ) (ha : 0 ≤ a) :
    superadditiveTransform (scalarMedian r) a =
      ⨅ ℓ : Fin (r+1),
        (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
          a (Tuple.sort a i)) / ((ℓ.val+1 : ℕ) : ℝ) :=
  median_transform_formula r a ha

example (r : ℕ) (a : Fin (2*r+1) → ℝ) (ha : 0 ≤ a) :
    let t : ℝ := ⨅ ℓ : Fin (r+1),
      (∑ i ∈ Finset.univ.filter (fun i : Fin (2*r+1) => i.val < r+(ℓ.val+1)),
        a (Tuple.sort a i)) / ((ℓ.val+1 : ℕ) : ℝ)
    (∑ i, min (a i) t) = ((r+1 : ℕ) : ℝ)*t :=
  median_transform_truncation_identity r a ha (Tuple.sort a) (Tuple.monotone_sort a)

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (c : ℝ) {β : Operator}
    (hβ : MaximalDecreasing β)
    (hbound : DecLE (survival (Measure.map (fun ω => |X ω-c|) μ)) β)
    (hβ0 : ∀ t > 0, ∀ v ∈ β t, 0 ≤ v) {b : ℝ → ℝ}
    (hb : ∀ t > 0, b t ∈ β t)
    (hf : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (b t)) < ∞) :
    let M : ℝ := ∫ t in Ioi (0 : ℝ), b t
    Integrable b (volume.restrict (Ioi (0 : ℝ))) ∧ Integrable X μ ∧
      |(∫ ω, X ω ∂μ)-c| ≤ M ∧ MaximalDecreasing (fun t => β (t-M)) ∧
      DecLE (survival (Measure.map (fun ω => |X ω-(∫ ω, X ω ∂μ)|) μ))
        (fun t => β (t-M)) :=
  finite_operator_tail_area_mean_pivot μ hX c hβ hbound hβ0 hb hf

-- Actual ell-p norms, including p=infinity; no axis identity is a premise.
example (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] {a : Fin n → ℝ} (ha : 0 ≤ a) :
    superadditiveTransform (fun x : Fin n → ℝ =>
      ‖(WithLp.equiv p (Fin n → ℝ)).symm x‖) a = ∑ i, a i :=
  ellp_superadditive_transform n p ha

example (n : ℕ) {a : Fin n → ℝ} (ha : 0 ≤ a) :
    ‖(WithLp.equiv 1 (Fin n → ℝ)).symm a‖ = ∑ i, a i := by
  rw [PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro i _
  simp only [WithLp.equiv_symm_pi_apply, Real.norm_eq_abs, abs_of_nonneg (ha i)]


-- Current range envelopes: arbitrary finite nonempty family, either common direction.
example {ι : Type*} [Finite ι] [Nonempty ι] (q : ι → ℝ → ℝ)
    (hm : (∀ i, Monotone (q i)) ∨ (∀ i, Antitone (q i)))
    (hc : ∀ i, Continuous (q i)) :
    range (fun s => ⨅ i, q i s) = intervalInf (fun i => range (q i)) ∧
      range (fun s => ⨆ i, q i s) = intervalSup (fun i => range (q i)) :=
  ⟨range_ciInf_eq_intervalInf_continuous q hm hc,
   range_ciSup_eq_intervalSup_continuous q hm hc⟩

example (n k : ℕ) :
    {x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = (k : ℝ)} =
      convexHull ℝ {x : Fin n → ℝ | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i = (k : ℝ)} :=
  hypersimplex_eq_convexHull_binary n k

-- The quadrant hypothesis is exactly the paper's graph-containment assumption.
example {f : Operator} (hf : MaximalDecreasing f)
    (hquad : ∀ ⦃x u : ℝ⦄, u ∈ f x → 0 ≤ x ∧ 0 ≤ u)
    (hd : Ioi 0 ⊆ dom f)
    (hdecay : Filter.Tendsto (fun x => sSup (f x)) Filter.atTop (𝓝 0)) :
    Ioi 0 ⊆ dom (inverse f) ∧
      ∃ s q : ℝ → ℝ, Measurable s ∧ Measurable q ∧
        (∀ x > 0, s x ∈ f x) ∧ (∀ p > 0, p ∈ f (q p)) ∧
        (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (s x)) =
          ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal (q p) := by
  have hd₀ : dom f ⊆ Ici 0 := by
    rintro x ⟨u, hu⟩
    exact (hquad hu).1
  have hn : Nonnegative f := by
    intro x u hu
    exact (hquad hu).2
  exact inverse_area_identity hf hd₀ hn hd hdecay

example {φ : ℝ → ℝ} {I : Set ℝ} (hφ : MonotoneOn φ I)
    (ho : I.OrdConnected) (hI : IsOpen I) (hne : I.Nonempty) :
    let C := completion I (restrictOperator (ofFun φ) I)
    MaximalIncreasing C ∧ dom C ⊆ closure I ∧ ∀ x ∈ I,
      ∃ l r : ℝ, Filter.Tendsto φ (𝓝[<] x) (𝓝 l) ∧
        Filter.Tendsto φ (𝓝[>] x) (𝓝 r) ∧ C x = Icc l r := by
  let C := completion I (restrictOperator (ofFun φ) I)
  obtain ⟨hm, hd, hl⟩ := scalar_completion_interior_limits hφ ho hI hne
  refine ⟨hm, hd, ?_⟩
  intro x hx
  exact ⟨sInf (C x), sSup (C x), hl x hx⟩

example {n m : ℕ} (hmn : m ≤ n) (a : Fin n → ℝ) (ha : Monotone a)
    (I : Finset (Fin n)) (hcard : I.card = m) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), a i) ≤ ∑ i ∈ I, a i :=
  monotone_prefix_sum_le_subset hmn a ha I hcard

example (φ : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hφ : MonotoneOn φ (Ioo a b)) :
    ∃ l : EReal, Filter.Tendsto (fun y => (φ y : EReal)) (𝓝[>] a) (𝓝 l) ∧
      completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) a =
        {u : ℝ | (u : EReal) ≤ l} :=
  ⟨_, tendsto_upperEndpoint_Ioo_left hab hφ, completion_Ioo_left_extended φ hab⟩

example (φ : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hφ : MonotoneOn φ (Ioo a b)) :
    ∃ l : EReal, Filter.Tendsto (fun y => (φ y : EReal)) (𝓝[<] b) (𝓝 l) ∧
      completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) b =
        {u : ℝ | l ≤ (u : EReal)} :=
  ⟨_, tendsto_lowerEndpoint_Ioo_right hab hφ, completion_Ioo_right_extended φ hab⟩

example (φ : ℝ → ℝ) (a : ℝ) (hφ : MonotoneOn φ (Ioi a)) :
    ∃ l : EReal, Filter.Tendsto (fun y => (φ y : EReal)) (𝓝[>] a) (𝓝 l) ∧
      completion (Ioi a) (restrictOperator (ofFun φ) (Ioi a)) a =
        {u : ℝ | (u : EReal) ≤ l} :=
  ⟨_, tendsto_upperEndpoint_Ioi hφ, completion_Ioi_left_extended φ a⟩

example (φ : ℝ → ℝ) (b : ℝ) (hφ : MonotoneOn φ (Iio b)) :
    ∃ l : EReal, Filter.Tendsto (fun y => (φ y : EReal)) (𝓝[<] b) (𝓝 l) ∧
      completion (Iio b) (restrictOperator (ofFun φ) (Iio b)) b =
        {u : ℝ | l ≤ (u : EReal)} :=
  ⟨_, tendsto_lowerEndpoint_Iio hφ, completion_Iio_right_extended φ b⟩

example (f : Operator) : MaximalIncreasing f ↔
    ∃ J : ℝ → ℝ, Monotone J ∧ LipschitzWith 1 J ∧
      ∀ x u, u ∈ f x ↔ J (x + u) = x :=
  maximal_iff_resolvent

example (f : Operator) : MaximalDecreasing f ↔
    ∃ J : ℝ → ℝ, Monotone J ∧ LipschitzWith 1 J ∧
      ∀ x u, u ∈ f x ↔ J (x - u) = x :=
  maximal_decreasing_iff_resolvent

example {f : Operator} (hf : MaximalDecreasing f) {I : Set ℝ}
    (hI : I.OrdConnected) (hopen : IsOpen I) (hne : I.Nonempty) (hd : I ⊆ interior (dom f)) :
    ∃! g : Operator, MaximalDecreasing g ∧ (∀ x ∈ I, g x = f x) ∧ dom g ⊆ closure I :=
  unique_completed_decreasing_restriction_values hf hI hopen hne (hd.trans interior_subset)

example {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (l u : Θ → ℝ)
    (hl : Integrable l μ) (hu : Integrable u μ) (hle : l ≤ᵐ[μ] u) :
    aumannIntegral μ (fun θ => Icc (l θ) (u θ)) =
      Icc (∫ θ, l θ ∂μ) (∫ θ, u θ ∂μ) := by
  rw [aumannIntegral_interval]
  exact aumannInterval_eq μ hl hu hle

example {f : Operator} (hf : Increasing f ∨ Decreasing f) {I : Set ℝ}
    (hI : MeasurableSet I) (hdom : I ⊆ dom f) :
    ∃ s : ℝ → ℝ, Measurable s ∧ ∀ x ∈ I, s x ∈ f x :=
  exists_global_measurable_selection hf hI hdom

example {f : Operator} (hf : Increasing f ∨ Decreasing f) (μ : Measure ℝ)
    [NoAtoms μ] {I : Set ℝ} (hI : MeasurableSet I) {s t : ℝ → ℝ}
    (hs : ∀ x ∈ I, s x ∈ f x) (ht : ∀ x ∈ I, t x ∈ f x)
    (ψ : ℝ → ℝ≥0∞) :
    (∫⁻ x in I, ψ (s x) ∂μ) = ∫⁻ x in I, ψ (t x) ∂μ :=
  selection_lintegral_comp_eq hf hI hs ht μ ψ

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hi : Integrable X μ) (p : ℝ)
    (hp : 0 < p ∧ p < 1) :
    {a : ℝ | ∀ b : ℝ,
      a + (∫ ω, max (X ω - a) 0 ∂μ) / p ≤
      b + (∫ ω, max (X ω - b) 0 ∂μ) / p} =
      tailQuantile (Measure.map X μ) p :=
  shortfall_minimizers_eq_tailQuantile hX hi hp

/-! Declaration navigation; the complete manuscript-facing expected types are checked above. -/

-- Definition 1.35 / Proposition 1.36: geometry is discharged from the common
-- domain-interior hypothesis; finiteness and positive total mass are the paper's.
example {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) [IsFiniteMeasure μ]
    (hμ : 0 < μ univ) (f : Θ → Operator) (hf : ∀ θ, MaximalIncreasing (f θ))
    (I : Set ℝ) (hne : I.Nonempty) (hi : ∀ θ, interior (dom (f θ)) = I)
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ) :
    ∃! g : Operator, MaximalIncreasing g ∧ interior (dom g) = I ∧
      dom g ⊆ closure I ∧ ∀ x ∈ I,
        g x = aumannIntegral μ (fun θ => f θ x) ∧
        g x = Icc (∫ θ, sInf (f θ x) ∂μ) (∫ θ, sSup (f θ x) ∂μ) := by
  obtain ⟨θ₀, _⟩ := nonempty_of_measure_ne_zero (ne_of_gt hμ)
  have hI : IsOpen I := by rw [← hi θ₀]; exact isOpen_interior
  have hc : Convex ℝ (dom (f θ₀)) := (dom_ordConnected (hf θ₀)).convex
  have ho : I.OrdConnected := by rw [← hi θ₀]; exact hc.interior.ordConnected
  have hd (θ) : I ⊆ dom (f θ) := by rw [← hi θ]; exact interior_subset
  obtain ⟨hm, hcl, huniq⟩ := increasingFamilyIntegral_unique μ hf hI ho hne hd hl hu
  refine ⟨increasingFamilyIntegral μ I f, ⟨hm,
    increasingFamilyIntegral_domain_interior μ hf hI ho hne hd hl hu, hcl, ?_⟩, ?_⟩
  · intro x hx
    exact ⟨increasingFamilyIntegral_aumann μ hf hI hd hl hu hx,
      increasingFamilyIntegral_value μ hf hI hd hl hu hx⟩
  · rintro g ⟨hgm, _, hgd, hgv⟩
    exact huniq g hgm hgd (fun x hx => (hgv x hx).1)

example {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) [IsFiniteMeasure μ]
    (hμ : 0 < μ univ) (f : Θ → Operator) (hf : ∀ θ, MaximalDecreasing (f θ))
    (I : Set ℝ) (hne : I.Nonempty) (hi : ∀ θ, interior (dom (f θ)) = I)
    (hl : ∀ x ∈ I, Integrable (fun θ => sInf (f θ x)) μ)
    (hu : ∀ x ∈ I, Integrable (fun θ => sSup (f θ x)) μ) :
    ∃! g : Operator, MaximalDecreasing g ∧ interior (dom g) = I ∧
      dom g ⊆ closure I ∧ ∀ x ∈ I,
        g x = aumannIntegral μ (fun θ => f θ x) ∧
        g x = Icc (∫ θ, sInf (f θ x) ∂μ) (∫ θ, sSup (f θ x) ∂μ) := by
  obtain ⟨θ₀, _⟩ := nonempty_of_measure_ne_zero (ne_of_gt hμ)
  have hI : IsOpen I := by rw [← hi θ₀]; exact isOpen_interior
  have hc : Convex ℝ (dom (f θ₀)) := (decreasing_dom_ordConnected (hf θ₀)).convex
  have ho : I.OrdConnected := by rw [← hi θ₀]; exact hc.interior.ordConnected
  have hd (θ) : I ⊆ dom (f θ) := by rw [← hi θ]; exact interior_subset
  obtain ⟨hm, hcl, huniq⟩ := decreasingFamilyIntegral_unique μ hf hI ho hne hd hl hu
  refine ⟨decreasingFamilyIntegral μ I f, ⟨hm,
    decreasingFamilyIntegral_domain_interior μ hf hI ho hne hd hl hu, hcl, ?_⟩, ?_⟩
  · intro x hx
    exact ⟨decreasingFamilyIntegral_aumann μ hf hI hd hl hu hx,
      decreasingFamilyIntegral_value μ hf hI hd hl hu hx⟩
  · rintro g ⟨hgm, _, hgd, hgv⟩
    exact huniq g hgm hgd (fun x hx => (hgv x hx).1)

-- 1.1 statement:1.1 [declaration navigation; full expected types above]
#check ScalarMonotone.Increasing
#check ScalarMonotone.Decreasing
#check ScalarMonotone.MaximalIncreasing
#check ScalarMonotone.MaximalDecreasing
#check ScalarMonotone.maximal_iff_no_extension
#check ScalarMonotone.maximal_iff_negative_witness
#check ScalarMonotone.maximalDecreasing_iff_no_extension
#check ScalarMonotone.maximalDecreasing_iff_positive_witness

-- 1.2 prop:minty [declaration navigation; full expected types above]
#check ScalarMonotone.maximal_iff_minty
#check ScalarMonotone.maximal_iff_resolvent
#check ScalarMonotone.maximal_decreasing_iff_resolvent
#check ScalarMonotone.mintyHomeomorph
#check ScalarMonotone.decreasingMintyHomeomorph
#check ScalarMonotone.inverse_identity_add_eq_resolvent
#check ScalarMonotone.inverse_identity_sub_eq_decreasingResolvent
#check ScalarMonotone.firmly_nonexpansive_iff_monotone_lipschitz

-- 1.3 prop:pointwisemaximality [declaration navigation; full expected types above]
#check ScalarMonotone.maximal_iff_fibers
#check ScalarMonotone.maximal_fiber_eq_extended_interval

-- 1.4 def:completedrestriction [declaration navigation; full expected types above]
#check ScalarMonotone.unique_maximal_completion
#check ScalarMonotone.unique_maximal_decreasing_completion
#check ScalarMonotone.unique_completion_of_monotoneOn
#check ScalarMonotone.unique_completed_restriction
#check ScalarMonotone.completion_Ioo_left_of_finite_limit
#check ScalarMonotone.completion_Ioo_right_of_finite_limit
#check ScalarMonotone.completion_Ioo_left_of_infinite_limit
#check ScalarMonotone.completion_Ioo_right_of_infinite_limit
#check ScalarMonotone.completion_Ioo_interior_of_limits
#check ScalarMonotone.completion_Ioo_interior_limits
#check ScalarMonotone.completion_Ioi_left_of_finite_limit
#check ScalarMonotone.completion_Ioi_left_of_infinite_limit
#check ScalarMonotone.completion_Iio_right_of_finite_limit
#check ScalarMonotone.completion_Iio_right_of_infinite_limit

-- 1.5 ex:survival [declaration navigation; full expected types above]
#check ScalarMonotone.survival_maximal
#check ScalarMonotone.tailQuantile_maximal
#check ScalarMonotone.tailQuantile_symmetricBernoulli_half
#check ScalarMonotone.tailQuantile_selection_law
#check ScalarMonotone.tailQuantile_selection_uniform_argument
#check ScalarMonotone.tailQuantile_selection_law_ae
#check ScalarMonotone.tailQuantile_fiber_eq
#check ScalarMonotone.tailQuantile_fiber_closed
#check ScalarMonotone.tailQuantile_fiber_ordConnected
#check ScalarMonotone.tailQuantile_fiber_nonempty
#check ScalarMonotone.tailQuantile_fiber_bounded
#check ScalarMonotone.tailQuantile_fiber_compact

-- 1.6 prop:sums [declaration navigation; full expected types above]
#check ScalarMonotone.add_maximal
#check ScalarMonotone.add_maximal_decreasing
#check ScalarMonotone.ran_add_eq
#check ScalarMonotone.ran_add_eq_decreasing
#check ScalarMonotone.parallelAdd_maximal
#check ScalarMonotone.parallelAdd_maximal_decreasing
#check ScalarMonotone.dom_parallelAdd_eq
#check ScalarMonotone.dom_parallelAdd_eq_decreasing
#check ScalarMonotone.maximal_iff_domain_range
#check ScalarMonotone.maximalDecreasing_iff_domain_range

-- 1.9 prop:products [declaration navigation; full expected types above]
#check ScalarMonotone.mul_maximal_iff
#check ScalarMonotone.mul_maximal_decreasing_iff
#check ScalarMonotone.ran_mul_eq
#check ScalarMonotone.ran_mul_eq_decreasing
#check ScalarMonotone.parallelMul_maximal_iff
#check ScalarMonotone.parallelMul_maximal_decreasing_iff
#check ScalarMonotone.dom_parallelMul_eq
#check ScalarMonotone.dom_parallelMul_eq_decreasing

-- 1.8 lem:logmaximal [declaration navigation; full expected types above]
#check ScalarMonotone.logOp_maximal
#check ScalarMonotone.logOp_maximal_decreasing

-- 1.10 ex:zero [declaration navigation; full expected types above]
#check ScalarMonotone.relu
#check ScalarMonotone.relu_nonnegative
#check ScalarMonotone.relu_increasing
#check ScalarMonotone.relu_maximal
#check ScalarMonotone.relu_mul_reciprocalBarrier
#check ScalarMonotone.relu_mul_reciprocalBarrier_not_maximal
#check ScalarMonotone.relu_mul_reciprocalBarrier_range_identity_fails
#check ScalarMonotone.reciprocalBarrier
#check ScalarMonotone.reciprocalBarrier_nonnegative
#check ScalarMonotone.reciprocalBarrier_input_neg
#check ScalarMonotone.reciprocalBarrier_increasing
#check ScalarMonotone.reciprocalBarrier_maximal
#check ScalarMonotone.reciprocalBarrier_eq

-- 1.7 prop:composition [declaration navigation; full expected types above]
#check ScalarMonotone.increasing_comp_iff_noRectangle
#check ScalarMonotone.comp_maximal_iff_of_increasing_increasing
#check ScalarMonotone.comp_maximal_iff_of_decreasing_decreasing
#check ScalarMonotone.comp_maximal_iff_of_increasing_decreasing
#check ScalarMonotone.comp_maximal_iff_of_decreasing_increasing

-- Previous-snapshot helper mapping: prop:distribution (not a current numbered claim)
#check ScalarMonotone.comp_parallelAdd_le
#check ScalarMonotone.comp_parallelMul_le
#check ScalarMonotone.comp_parallelAdd_eq_of_singleValued
#check ScalarMonotone.comp_parallelAdd_eq_of_maximal
#check ScalarMonotone.comp_parallelAdd_eq_of_maximalDecreasing
#check ScalarMonotone.comp_parallelMul_eq_of_singleValued
#check ScalarMonotone.comp_parallelMul_eq_of_maximal
#check ScalarMonotone.comp_parallelMul_eq_of_maximalDecreasing
#check ScalarMonotone.parallelMul_parallelAdd
#check ScalarMonotone.parallelAdd_translate
#check ScalarMonotone.parallelMul_scale

-- 1.11 def:order [declaration navigation; full expected types above]
#check ScalarMonotone.IncLE
#check ScalarMonotone.DecLE
#check ScalarMonotone.IncGraph
#check ScalarMonotone.DecGraph
#check ScalarMonotone.IncGraph.le_iff_J
#check ScalarMonotone.DecGraph.le_iff_J
#check ScalarMonotone.incLE_vertical_iff
#check ScalarMonotone.decLE_vertical_iff

-- 1.12 prop:comparison [declaration navigation; full expected types above]
#check ScalarMonotone.incLE_iff_resolvent
#check ScalarMonotone.decLE_iff_resolvent
#check ScalarMonotone.resolvent_scale_order_iff
#check ScalarMonotone.decreasingResolvent_scale_order_iff
#check ScalarMonotone.incLE_fiber_endpoints
#check ScalarMonotone.decLE_fiber_endpoints
#check ScalarMonotone.incLE_iff_endpoints_of_dom_eq
#check ScalarMonotone.decLE_iff_endpoints_of_dom_eq

-- 1.13 lem:resolventvalue [declaration navigation; full expected types above]
#check ScalarMonotone.resolvent_le_iff_lowerHull
#check ScalarMonotone.resolvent_ge_iff_upperHull
#check ScalarMonotone.decreasingResolvent_ge_iff_lowerHull
#check ScalarMonotone.decreasingResolvent_le_iff_upperHull

-- 1.14 def:intervalorder [declaration navigation; full expected types above]
#check ScalarMonotone.IntervalLE
#check ScalarMonotone.intervalLE_refl
#check ScalarMonotone.IntervalLE.trans
#check ScalarMonotone.intervalLE_antisymm
#check ScalarMonotone.intervalLE_Icc_iff
#check ScalarMonotone.lowerHull_eq_setAdd
#check ScalarMonotone.upperHull_eq_setAdd

-- 1.15 prop:orderdomains [declaration navigation; full expected types above]
#check ScalarMonotone.incLE_domains
#check ScalarMonotone.incLE_ranges
#check ScalarMonotone.decLE_domains
#check ScalarMonotone.decLE_ranges
#check ScalarMonotone.incLE_fiber
#check ScalarMonotone.decLE_fiber

-- 1.16 prop:inversion [declaration navigation; full expected types above]
#check ScalarMonotone.incLE_inverse_iff
#check ScalarMonotone.decLE_inverse_iff
#check ScalarMonotone.IncLE.add_right
#check ScalarMonotone.IncLE.add_left
#check ScalarMonotone.DecLE.add_right
#check ScalarMonotone.DecLE.add_left
#check ScalarMonotone.IncLE.mul_right
#check ScalarMonotone.IncLE.mul_left
#check ScalarMonotone.DecLE.mul_right
#check ScalarMonotone.DecLE.mul_left
#check ScalarMonotone.IncLE.parallelAdd_right
#check ScalarMonotone.IncLE.parallelMul_right
#check ScalarMonotone.DecLE.parallelAdd_right
#check ScalarMonotone.DecLE.parallelMul_right
#check ScalarMonotone.IncLE.comp_right_of_increasing
#check ScalarMonotone.IncLE.comp_right_of_decreasing
#check ScalarMonotone.IncLE.comp_left_of_increasing
#check ScalarMonotone.IncLE.comp_left_of_decreasing
#check ScalarMonotone.DecLE.comp_right_of_increasing
#check ScalarMonotone.DecLE.comp_right_of_decreasing
#check ScalarMonotone.DecLE.comp_left_of_increasing
#check ScalarMonotone.DecLE.comp_left_of_decreasing

-- 1.17 lem:survivalcomparison [declaration navigation; full expected types above]
#check ScalarMonotone.survival_comparison_iff
#check ScalarMonotone.survival_map_comparison_iff
#check ScalarMonotone.survival_le_iff_tailQuantile_le

-- 1.26 prop:probability [declaration navigation; full expected types above]
#check ScalarMonotone.finite_sum_tail_bound
#check ScalarMonotone.finite_product_tail_bound
#check ScalarMonotone.survival_finite_sum_bound
#check ScalarMonotone.survival_finite_product_bound

-- 1.27 cor:centered [declaration navigation; full expected types above]
#check ScalarMonotone.survival_centered_sum_bound
#check ScalarMonotone.survival_centered_product_bound
#check ScalarMonotone.centeredProductProfile_eq_parallel
#check ScalarMonotone.centeredProductProfile_zero_left
#check ScalarMonotone.centeredProductProfile_zero_right
#check ScalarMonotone.centeredProductProfile_zero_zero

-- 1.18 thm:lattice [declaration navigation; full expected types above]
#check ScalarMonotone.inc_exists_isGLB_iff
#check ScalarMonotone.inc_exists_isLUB_iff
#check ScalarMonotone.dec_exists_isGLB_iff
#check ScalarMonotone.dec_exists_isLUB_iff
#check ScalarMonotone.IncGraph.J_iInf
#check ScalarMonotone.IncGraph.J_iSup
#check ScalarMonotone.DecGraph.J_iInf
#check ScalarMonotone.DecGraph.J_iSup
#check ScalarMonotone.IncGraph.constants_not_bddAbove
#check ScalarMonotone.DecGraph.constants_not_bddAbove

-- 1.19 lem:inverseextrema [declaration navigation; full expected types above]
#check ScalarMonotone.IncGraph.inv_iInf
#check ScalarMonotone.IncGraph.inv_iSup
#check ScalarMonotone.DecGraph.inv_iInf
#check ScalarMonotone.DecGraph.inv_iSup

-- 1.21 def:intervalextrema [declaration navigation; full expected types above]
#check ScalarMonotone.intervalInf
#check ScalarMonotone.intervalSup
#check ScalarMonotone.intervalInf_universal
#check ScalarMonotone.intervalSup_universal
#check ScalarMonotone.upperHull_intervalInf
#check ScalarMonotone.lowerHull_intervalInf
#check ScalarMonotone.upperHull_intervalSup
#check ScalarMonotone.lowerHull_intervalSup

-- 1.22 prop:finitevalues [declaration navigation; full expected types above]
#check ScalarMonotone.IncGraph.dom_iInf
#check ScalarMonotone.IncGraph.dom_iSup
#check ScalarMonotone.DecGraph.dom_iInf
#check ScalarMonotone.DecGraph.dom_iSup
#check ScalarMonotone.IncGraph.ran_iInf
#check ScalarMonotone.IncGraph.ran_iSup
#check ScalarMonotone.DecGraph.ran_iInf
#check ScalarMonotone.DecGraph.ran_iSup
#check ScalarMonotone.IncGraph.fiber_iInf
#check ScalarMonotone.IncGraph.fiber_iInf_endpoints
#check ScalarMonotone.IncGraph.fiber_iInf_active
#check ScalarMonotone.IncGraph.fiber_iSup
#check ScalarMonotone.IncGraph.fiber_iSup_endpoints
#check ScalarMonotone.IncGraph.fiber_iSup_active
#check ScalarMonotone.DecGraph.fiber_iInf
#check ScalarMonotone.DecGraph.fiber_iInf_endpoints
#check ScalarMonotone.DecGraph.fiber_iInf_active
#check ScalarMonotone.DecGraph.fiber_iSup
#check ScalarMonotone.DecGraph.fiber_iSup_endpoints
#check ScalarMonotone.DecGraph.fiber_iSup_active

-- 1.23 prop:latticemedian [declaration navigation; full expected types above]
#check ScalarMonotone.inc_lattice_median
#check ScalarMonotone.dec_lattice_median
#check ScalarMonotone.inc_lattice_median_resolvent_scale
#check ScalarMonotone.dec_lattice_median_resolvent_scale
#check ScalarMonotone.inc_lattice_median_majority
#check ScalarMonotone.dec_lattice_median_majority

-- 1.20 prop:extremaoperations [declaration navigation; full expected types above]
#check ScalarMonotone.partial_orderPreserving_inf_bound
#check ScalarMonotone.partial_orderPreserving_sup_bound
#check ScalarMonotone.partial_orderReversing_inf_bound
#check ScalarMonotone.partial_orderReversing_sup_bound

-- 1.24 prop:finiteextremaoperations [declaration navigation; full expected types above]
#check ScalarMonotone.inc_add_iInf
#check ScalarMonotone.inc_add_iSup
#check ScalarMonotone.dec_add_iInf
#check ScalarMonotone.dec_add_iSup
#check ScalarMonotone.inc_mul_iInf
#check ScalarMonotone.inc_mul_iSup
#check ScalarMonotone.dec_mul_iInf
#check ScalarMonotone.dec_mul_iSup
#check ScalarMonotone.inc_parallelAdd_iInf
#check ScalarMonotone.inc_parallelAdd_iSup
#check ScalarMonotone.dec_parallelAdd_iInf
#check ScalarMonotone.dec_parallelAdd_iSup
#check ScalarMonotone.inc_parallelMul_iInf
#check ScalarMonotone.inc_parallelMul_iSup
#check ScalarMonotone.dec_parallelMul_iInf
#check ScalarMonotone.dec_parallelMul_iSup

-- 1.25 prop:extremacomposition [declaration navigation; full expected types above]
#check ScalarMonotone.inc_comp_right_iInf_inc
#check ScalarMonotone.inc_comp_right_iSup_inc
#check ScalarMonotone.inc_comp_right_iInf_dec
#check ScalarMonotone.inc_comp_right_iSup_dec
#check ScalarMonotone.dec_comp_right_iInf_inc
#check ScalarMonotone.dec_comp_right_iSup_inc
#check ScalarMonotone.dec_comp_right_iInf_dec
#check ScalarMonotone.dec_comp_right_iSup_dec
#check ScalarMonotone.inc_comp_left_iInf_inc
#check ScalarMonotone.inc_comp_left_iSup_inc
#check ScalarMonotone.inc_comp_left_iInf_dec
#check ScalarMonotone.inc_comp_left_iSup_dec
#check ScalarMonotone.dec_comp_left_iInf_inc
#check ScalarMonotone.dec_comp_left_iSup_inc
#check ScalarMonotone.dec_comp_left_iInf_dec
#check ScalarMonotone.dec_comp_left_iSup_dec

-- 1.28 prop:envelopes [declaration navigation; full expected types above]
#check ScalarMonotone.IncGraph.parallelSum_envelopes
#check ScalarMonotone.DecGraph.parallelSum_envelopes
#check ScalarMonotone.IncGraph.optimized_parallelSum_envelopes
#check ScalarMonotone.DecGraph.optimized_parallelSum_envelopes

-- Previous-snapshot helper mapping: rem:cubictransformation (not a current numbered claim)
#check ScalarMonotone.cubic_parallel_transformation
#check ScalarMonotone.cubic_parallel_terms_maximal
#check ScalarMonotone.cubic_multilevel_bound
#check ScalarMonotone.positiveConstantProfile_zero
#check ScalarMonotone.inverse_positiveConstantProfile_negative
#check ScalarMonotone.inverse_positiveConstantProfile_zero
#check ScalarMonotone.inverse_positiveConstantProfile_interior
#check ScalarMonotone.inverse_positiveConstantProfile_one
#check ScalarMonotone.inverse_positiveConstantProfile_above_one

-- Previous-snapshot helper mapping: def:stepoperator (not a current numbered claim)
#check ScalarMonotone.EndOfPaper.stepArea
#check ScalarMonotone.EndOfPaper.split_step_area
#check ScalarMonotone.EndOfPaper.integral_eq_off_finite
#check ScalarMonotone.EndOfPaper.integral_step_eq_area
#check ScalarMonotone.EndOfPaper.integral_partition

-- 1.31 def:area [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.countable_jumpInputs
#check ScalarMonotone.EndOfPaper.fiber_subsingleton_off_jumps
#check ScalarMonotone.EndOfPaper.selections_ae_eq
#check ScalarMonotone.EndOfPaper.decreasing_selections_ae_eq
#check ScalarMonotone.EndOfPaper.selection_integral_eq
#check ScalarMonotone.EndOfPaper.decreasing_selection_integral_eq
#check ScalarMonotone.EndOfPaper.selection_intervalIntegrable
#check ScalarMonotone.EndOfPaper.darboux_gap_bound
#check ScalarMonotone.EndOfPaper.stepArea_upper_sub_lower

-- Previous-snapshot helper mapping: def:piecewisearea (not a current numbered claim)

-- 1.32 prop:area [declaration navigation; full expected types above]

-- Previous-snapshot helper mapping: prop:changevariables (not a current numbered claim)

-- 1.33 cor:moments [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.moment_tail_area
#check ScalarMonotone.EndOfPaper.moment_le_capped_tail_area
#check ScalarMonotone.EndOfPaper.centered_moment_le_capped_tail_area

-- 1.34 prop:pivots [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.mean_pivot_distance
#check ScalarMonotone.EndOfPaper.pointwise_mean_pivot

-- Previous-snapshot helper mapping: def:measurableoperator (not a current numbered claim)

-- Previous-snapshot helper mapping: lem:measurableendpoints (not a current numbered claim)

-- Previous-snapshot helper mapping: def:measurablefamilyintegral (not a current numbered claim)
#check ScalarMonotone.EndOfPaper.integratedFiberGraph
#check ScalarMonotone.EndOfPaper.integratedFiberGraph_dom
#check ScalarMonotone.EndOfPaper.integratedFiberGraph_increasing
#check ScalarMonotone.EndOfPaper.integratedFiberGraph_has_maximal_completion

-- 1.36 thm:familyintegral [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.increasingFamilyIntegral_unique
#check ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_unique
#check ScalarMonotone.EndOfPaper.increasingFamilyIntegral_value
#check ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_value
#check ScalarMonotone.EndOfPaper.increasingFamilyIntegral_mono
#check ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_mono
#check ScalarMonotone.EndOfPaper.increasingFamilyIntegral_add
#check ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_add
#check ScalarMonotone.EndOfPaper.increasingFamilyIntegral_outputScale
#check ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_outputScale
#check ScalarMonotone.EndOfPaper.aumannInterval
#check ScalarMonotone.EndOfPaper.aumannInterval_eq
#check ScalarMonotone.EndOfPaper.aumannInterval_mono
#check ScalarMonotone.EndOfPaper.integrated_endpoints_add
#check ScalarMonotone.EndOfPaper.integrated_endpoints_scale

-- Previous-snapshot helper mapping: rem:boundedfamilyintegral (not a current numbered claim)

-- Previous-snapshot helper mapping: statement:4.13 (not a current numbered claim)

-- 2.1 def:hardytransform [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.hardyScalar
#check ScalarMonotone.EndOfPaper.hardyScalar_unique_completion
#check ScalarMonotone.EndOfPaper.hardyScalar_unique_completion_Ioi

-- Previous-snapshot helper mapping: lem:hardyscalar (not a current numbered claim)
#check ScalarMonotone.EndOfPaper.hardyScalar_dilation
#check ScalarMonotone.EndOfPaper.hardyScalar_dilation_integrable

-- 2.2 prop:hardycalculus [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.hardyScalar_add
#check ScalarMonotone.EndOfPaper.hardyScalar_smul
#check ScalarMonotone.EndOfPaper.hardyScalar_mono
#check ScalarMonotone.EndOfPaper.le_hardyScalar
#check ScalarMonotone.EndOfPaper.hardyScalar_antitoneOn
#check ScalarMonotone.EndOfPaper.hardyScalar_separated

-- 2.3 lem:hardyconvexity [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.hardyScalar_convexOn
#check ScalarMonotone.EndOfPaper.hardyScalar_concaveOn
#check ScalarMonotone.EndOfPaper.hardyScalar_convexOn_Ioi
#check ScalarMonotone.EndOfPaper.hardyScalar_concaveOn_Ioi

-- 2.4 lem:hardyvariational [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.shortfall_weak_duality
#check ScalarMonotone.EndOfPaper.exists_atom_fraction
#check ScalarMonotone.EndOfPaper.shortfall_attainment
#check ScalarMonotone.EndOfPaper.quantile_excess_area
#check ScalarMonotone.EndOfPaper.hardyScalar_quantile_variational
#check ScalarMonotone.EndOfPaper.hardyScalar_quantile_eq_dualShortfall

-- 2.5 ex:normtransform [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.superadditiveTransform_eq_mass_of_axes
#check ScalarMonotone.EndOfPaper.superadditiveTransform_eq_self

-- 2.6 prop:mediantransform [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.median_subset_sum_bound
#check ScalarMonotone.EndOfPaper.median_transform_subset_upper
#check ScalarMonotone.EndOfPaper.median_transform_common_upper

-- 2.7 lem:aggregationarea [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.aggregation_step_bound
#check ScalarMonotone.EndOfPaper.aggregation_finset_bound
#check ScalarMonotone.EndOfPaper.superadditiveTransform_concaveOn

-- 2.8 prop:hardytailaggregation [declaration navigation; full expected types above]

-- 2.11 thm:hardytailaggregationsharp [declaration navigation; full expected types above]

-- 2.12 cor:hardymedian [declaration navigation; full expected types above]

-- Previous-snapshot helper mapping: cor:tailmediancommon (not a current numbered claim)

-- 2.14 prop:hardyoptimality [declaration navigation; full expected types above]

-- 2.9 prop:hardyprofiles [declaration navigation; full expected types above]
#check ScalarMonotone.EndOfPaper.concave_integral_upper
#check ScalarMonotone.EndOfPaper.hardyScalar_power_profile
#check ScalarMonotone.EndOfPaper.hardyScalar_exponential_profile

-- 2.10 prop:convextransforms [declaration navigation; full expected types above]

-- A.1 lem:powergeometric [declaration navigation; full expected types above]

