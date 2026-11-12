# Notation dictionary

This table explains the source representation; it does not certify coverage of
any manuscript proposition. Actual operator integrals and completed Hardy
constructors are included; the result dictionary records each claim's scope.

| Paper notation/concept | Existing Lean representation |
|---|---|
| Set-valued operator f : R -> subsets of R | `ScalarMonotone.Operator`, an abbreviation for `ℝ → Set ℝ` |
| u belongs to f(x) | `u ∈ f x` |
| Graph, domain, range | `graph f`, `dom f`, `ran f` |
| Inverse relation | `inverse f` |
| Increasing/decreasing graph | `Increasing f`, `Decreasing f` |
| Maximal increasing/decreasing graph | `MaximalIncreasing f`, `MaximalDecreasing f` |
| Bundled maximal graph | `IncGraph`, `DecGraph` |
| Graph inclusion | `f ≤ g` for raw `Operator` values |
| Pointwise resolvent order | `IncLE f g`, `DecLE f g`; `≤` on the corresponding bundled types |
| Resolvent | `resolvent`, `decreasingResolvent`; `J` in bundled interfaces |
| Scalar function as singleton graph | `ofFun` |
| Identity graph | `identity` |
| Output negation, input reflection | `negOut f`, `reflect f` |
| Ordinary sum and product | `add f g`, `mul f g` |
| g composed with f | `comp g f` (outer argument first) |
| Parallel sum and product | `parallelAdd f g`, `parallelMul f g` |
| Nonnegative range | `Nonnegative f` |
| Nonnegative domain | `Nonnegative (inverse f)` |
| No multivalued rectangle in composition | `NoRectangle f g` |
| Interval property | `Set.OrdConnected` |
| Upward/downward interval hull | `upperHull`, `lowerHull` |
| Interval comparison | `IntervalLE` |
| Extended interval endpoints | `EReal`-valued endpoint functions |
| Survival and tail-quantile graphs | `survival μ`, `tailQuantile μ` for a probability law `μ` |
| Survival completed on the positive half-line | `positiveSurvivalCompletion μ`; its zero fiber is `Ici (μ.real (Ioi 0))`, its inverse retains whole quantile fibers on `(0,1)` and is `{0}` above one |
| Extended and signed expectation-area formulas | `positive_survival_expectation_area`, `signed_expectation_quantile_area`; arbitrary selections, atoms and infinite nonnegative expectations are retained |
| Probability-one operator cap | `α ⊓ DecGraph.constant 1`, equal to `sInf {α, DecGraph.constant 1}` by `csInf_pair`; `centered_moment_operator_cap` proves the exact extended formula |
| Original local logarithmic mean | `local_logarithmic_mean`; the single Option-indexed product area derives individual L1 and the exact prefix product-log integral |
| Probability law of a random variable | `Measure.map X μ`, with the measurability hypotheses in the theorem |
| Scalar selection of a graph | `EndOfPaper.SelectionOn`; `scalarSelection` chooses values on the domain |
| Measurable selection on an integration set | `EndOfPaper.exists_global_measurable_selection` |
| Nonnegative extended expectation/area | `MeasureTheory.lintegral`, values in `ENNReal`; selection independence is `selection_lintegral_comp_eq` |
| Finite expectation of the nonnegative logarithmic control | `(∫⁻ ω, ENNReal.ofReal (U (Z ω)) ∂μ) < ∞`; `logarithmic_endpoint_control` derives ordinary L1 before using the real mean |
| Original-space logarithmic endpoint tail | `logarithmic_endpoint_control`, the exact strict-tail bound `a + 2 * (∫ ω, U (Z ω) ∂μ) / s`; the profile domain condition is an inclusion |
| Finite product converted to a separated logarithmic modulus | `randomized_modulus_logarithmic_form`, with `U z = ∑ i, max (Real.log (Λ i z / c i)) 0` |
| Signed extended integral convention | `selection_signed_parts_eq` identifies positive and negative extended parts separately; their simultaneous divergence is excluded by the paper |
| Aumann integral | `EndOfPaper.aumannIntegral μ h`, integrals of integrable almost-everywhere selections |
| Integrable interval-valued Aumann integral | `aumannIntegral_interval` and `aumannInterval_eq` give the exact endpoint interval |
| Interval multifunction measurability | `HitOpenMeasurable h` iff measurability of `intervalLowerExtended`/`intervalUpperExtended` in `EReal` |
| Extended signed scalar area | `signedExtendedIntegral μ s : Option EReal`; `none` iff both signed parts are infinite; integrable values equal the Bochner integral |
| Infinite integration endpoints | `extendedOpenInterval a b` for `a b : EReal`; `orientedExtendedIntegral` has proved reversal, equal-limit and choice conventions |
| Local Hardy integrability | `∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p`; all completed Hardy calculus and shape properties hold without global L1 |
| Original-space Hardy variational lemma | `hardy_quantile_original_variational` uses the actual completed `hardyFamilyIntegral`, original-space weights, literal product supremum, and full argmin |
| Completed increasing/decreasing family integral | `increasingFamilyIntegral`, `decreasingFamilyIntegral`; `_value`, `_aumann`, `_unique`, `_domain_interior`, `_mono`, `_add`, `_outputScale` prove the full construction and algebra |
| Actual finite interior endpoints | `sInf (f x)`, `sSup (f x)` with boundedness/attainment from `maximal_interior_fiber_bounded`, `maximal_interior_fiber_endpoints_mem` |
| Convex/concave selections and singleton fibers | `fiber_of_convex_selection`, `fiber_of_concave_selection`, retaining maximality and the open-interior hypothesis |
| All expected-shortfall minimizers | `shortfall_minimizers_eq_tailQuantile`, on the original probability space with law `Measure.map X μ` |
| Scalar Hardy average | `EndOfPaper.hardyScalar`; `hardyFamilyIntegral_of_integrable` proves the scalar formula for the actual completed operator |
| Completed Hardy operator | `EndOfPaper.hardyFamilyIntegral`; `_eq_actual_dilations`, `_well_defined`, `_of_integrable`, shape-preservation and local-compatibility theorems |
| Whole Hardy calculus | `hardyFamilyIntegral_calculus`, `_mono`, `_add`, `_outputScale`, and `le_hardyFamilyIntegral`; order permits different initial domains and the algebraic equalities include boundary fibers |
| Zero lower domain endpoint, positive upper endpoint | `IsGLB (dom f) 0` and `∃ a ∈ dom f, 0 < a`; this order formulation permits an infinite upper endpoint and derives the initial domain geometry |
| Expected-shortfall objective | `EndOfPaper.shortfallObjective` |
| Feasible-weight dual shortfall | `EndOfPaper.dualShortfall` |
| Ordinary real convex subdifferential | `realSubgradient φ a = {d | ∀ b, φ a+d*(b-a) ≤ φ b}`; `shortfall_subgradient_survival` proves the full affine survival interval |
| Shortfall one-sided derivatives | `shortfall_one_sided_derivatives` uses `HasDerivWithinAt` on `Iio a`/`Ioi a`, with weak/strict tails respectively |
| Actual completed aggregation | `aggregationOperator F I f`; exact full interior interval endpoints, domain and whole-graph uniqueness |
| General integral aggregation | `aggregation_integral_bound_ae` for finite measures and ae-nonnegative L1 vectors; no boundary continuity of F-sharp is assumed |
| Finite nonnegative operator areas | `aggregation_area_finite_nonnegative` derives L1 from finite ENNReal areas and applies the actual completed aggregation selection bridge |
| Hardy tail aggregation | `hardy_tail_aggregation_of_positive_homogeneity` uses actual completed Hardy fibers and the literal strictly positive homogeneity assumption |
| Survival aggregation by admissible envelopes | `tail_envelope_aggregation`, the inverse actual completed F-sharp aggregation; `admissible_tail_hardy_data` derives domains, nonnegative values and L1 from the original assumptions |
| Common-envelope strict tail | `common_envelope_survival_bound`, with exact positive coefficient F-sharp(ones), actual domain scaling and infimum over the full completed fiber; `zero_aggregation_law` handles the zero case |
| Ordinary-sum Hardy survival bound | `hardy_sum_survival_of_envelopes`, with the literal coordinate-witness graph sum and all original L1 derived |
| Actual Hilbert--Schmidt matrix space | `HSMatrix m n = EuclideanSpace ℝ (m × n)`; `hsMatrixOp` is the actual matrix linear map, with proved operator/HS norm bounds |
| Network parameter metric and layer recursion | `NetworkParameters`, `network_parameter_norm_sq`, `networkLayer`, `finiteNetworkMap`; the metric is the literal finite Euclidean product of HS blocks |
| Network max-controls and dimension factor | `networkControl`, `networkPrefactor`; `network_two_point_bound` proves the exact manuscript formula, allowing controls to vanish |
| Network measurability | `finite_network_continuous`, `finite_network_borel_measurable`; both are derived from the original activation assumptions |
| Original completed network tail profile | `networkTailProfile`, the literal completed finite product of qDelta(u/6) and actual geometric affine-input graphs at u/12, followed by the exact D output scaling; `network_tail_profiles` derives every control/area and the full original comparison |
| Median control profiles | `halfAffineProfile`, `network_control_quantile_bound`; the one-sided median comparison and two-event union give exactly qDelta(v/2), with no independence between norm observations |
| Affine-power geometric bound | `affinePowerProfile`, `affine_power_geometric_bound`; the actual completion and whole geometric comparison hold for every alpha>0, with zero parameters allowed and logarithmic L1 derived |
| Exact power-network upper profile | `powerNetworkBound`, `powerNetworkProfile`, `network_power_tails`; literal D*A*exp(alpha*L) and dimension factors, full completed comparison and strict tails. `network_power_far_tail` gives the positive limit after multiplication by u^(alpha*(L+1)) |
| Exact subgaussian depth radius and maximum | `networkDepthRadius u = sqrt(log(24*exp(1)/u))`, `networkMedianMaximum`; `network_subgaussian_depth` retains every exact dimension and confidence factor, including A=0 |
| Uniform depth tail rate | `networkRatePower L d t = min(t^2,d^(L/(L+1))*t^(2/(L+1)))`; `network_subgaussian_two_regime_tail` uses the explicit uniform coefficient A*sqrt(1+c*L/2)*(M+A)^L when N/d<=c and all norm medians<=M |
| F sharp | `EndOfPaper.superadditiveTransform`; `median_transform_formula` proves the full odd-median formula and `ellp_superadditive_transform` covers exponents from one through infinity; `hardy_tail_aggregation_sharp` proves both exact fixed-level probabilistic suprema |
| Finite product of initial profiles | `completedFiniteProfileProduct`: the literal interior graph product followed by its unique maximal completion; `randomizedInputProduct` includes the baseline and every control |
| Finite geometric product law | `geometric_hardy_finite_product`, with zeros, arbitrary selections and infinite negative-log area retained |
| Whole randomized geometric comparison | `randomized_lipschitz_geometric_bound`, with the actual completed probability dilation by one third and a single combined positive-log area |
| Logarithmic profile convexity | `log_convex_implies_all_power_convex`, `limiting_power_convex_implies_log_convex` and the actual `scaled_power_log_limit`; distinct from the scalar transformation proposition |
| Actual Hardy tail transform | `hardyTailTransform beta = inverse (hardyFamilyIntegral (interior (dom (inverse beta))) (inverse beta))`; local well-definedness and whole-graph power/exponential identities are proved |
| Uncapped explicit profiles | `powerProfile kappa C` is empty for t<=0 and has value C*t^(-kappa) for t>0; `exponentialProfile C` has value C*exp(-t) on all real inputs |
| Weighted power--geometric mean | `weightedPowerMean`; its exact real-exponent limit includes both endpoint weights |
| Quasi-norm | `coordinateQuasiNorm q x = (sum_i (x_i)^q)^(1/q)`; reverse Minkowski and the unchanged sharp transform hold for every 0<q<=1 |
| Finite decomposition constraint | `EndOfPaper.AdmissibleDecomposition` |
| Actual Gaussian product | `gaussianProductMeasure n` is the finite product of standard real Gaussian laws; `gaussianProductVector` supplies its actual Euclidean coordinate vector and `gaussianExpIntegral` its exponential integral |
| Gaussian input profile | `gaussian_input_profile` proves the whole comparison with `affineSqrtLogProfile 0 2`, whose interior fibers equal `{2*sqrt(log(2/u))}`; `gaussian_lipschitz_copy_weak_tail` gives the exact weak tail `2*exp(-t^2/4)` for all real one-Lipschitz observations on the original space |
| Gaussian data norm median | `gaussian_hs_normalized_median` proves every actual median of `norm(X)/sqrt(N*d)` is at most `1+sqrt(2*log(2)/(N*d))`; `gaussian_euclidean_norm_mgf` gives the exact exponential norm bound |
| Actual Gaussian matrix comparison samples | `gaussianJointMatrix`, `gaussianJointScalar`, `gaussianJointLeftVector`, `gaussianJointRightVector` are actual disjoint coordinate blocks of one standard Gaussian product; their laws and the required independence are proved |
| Deterministic operator-norm approximation | `gaussian_unit_pair_value_isLUB` and `gaussian_operator_dense_maximum_tendsto` identify the actual operator norm by increasing maxima along one fixed dense unit-pair sequence |
| Sharp Gaussian matrix norm moment and tail | `gaussian_matrix_operator_norm_mgf` gives `E exp(a*norm(T)) <= exp(a*(sqrt(m)+sqrt(n))+a^2/2)` for `a>=0`; `gaussian_matrix_operator_norm_tail` gives the weak upper tail `exp(-s^2/2)` above `sqrt(m)+sqrt(n)+s`, on every original probability space with independent standard Gaussian entries |
| Exact Gaussian network median constants | `gaussian_network_norm_medians` derives both actual network medians simultaneously: `mx<=1+sqrt(2*log(2)/(N*d))` and every `ml<=sqrt(2)+sqrt(log(2)/d)`; `gaussian_matrix_median_normalization` proves the exact scalar normalization |

Most displayed names lie in `ScalarMonotone`; `EndOfPaper` entries lie in
`ScalarMonotone.EndOfPaper`. For every name, consult `docs/declarations.json`
or VS Code for its exact parameter order and full type. In particular, do not
replace a positive-half-line graph by a full-domain scalar function, conflate
raw graph inclusion with resolvent order, or treat a real Bochner integral as
an extended-valued nonnegative integral without the appropriate hypotheses.
