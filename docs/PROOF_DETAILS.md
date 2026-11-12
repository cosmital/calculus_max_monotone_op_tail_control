# Detailed Lean correspondence

Result numbers and pages refer to the [submitted PDF](../manuscript/monotone_calculus.pdf). Author correspondence review recorded.

These are existing proofs and supporting declarations. Routine helpers are kept out of the main reader index.

<a id="result-1-1"></a>

## Definition 1.1

[PDF page 6](../manuscript/monotone_calculus.pdf#page=6). Monotonicity, maximality, and the compatible-point characterization in both orientations.

Arbitrary real set-valued graph, with either orientation specified separately; empty fibers are permitted. Increasing/Decreasing encode exactly the signed pairwise graph inequalities. Maximality is equivalent to no proper monotone extension and to a strict opposite-sign witness for every excluded point in both orientations. negOut reverses outputs and is involutive. Operator ≤ is graph inclusion only inside the extension characterization; no resolvent order is used. maximal_iff_no_extension, maximal_iff_negative_witness, maximalDecreasing_iff_no_extension, maximalDecreasing_iff_positive_witness. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.Increasing` | [MonotoneOperators/Defs.lean:25](../MonotoneOperators/Defs.lean#L25) |
| `ScalarMonotone.Decreasing` | [MonotoneOperators/Defs.lean:34](../MonotoneOperators/Defs.lean#L34) |
| `ScalarMonotone.MaximalIncreasing` | [MonotoneOperators/Defs.lean:31](../MonotoneOperators/Defs.lean#L31) |
| `ScalarMonotone.MaximalDecreasing` | [MonotoneOperators/Defs.lean:35](../MonotoneOperators/Defs.lean#L35) |
| `ScalarMonotone.maximal_iff_no_extension` | [MonotoneOperators/Basic.lean:76](../MonotoneOperators/Basic.lean#L76) |
| `ScalarMonotone.maximal_iff_negative_witness` | [MonotoneOperators/Basic.lean:96](../MonotoneOperators/Basic.lean#L96) |
| `ScalarMonotone.maximalDecreasing_iff_no_extension` | [MonotoneOperators/Interface.lean:48](../MonotoneOperators/Interface.lean#L48) |
| `ScalarMonotone.maximalDecreasing_iff_positive_witness` | [MonotoneOperators/Interface.lean:68](../MonotoneOperators/Interface.lean#L68) |
<a id="result-1-2"></a>

## Proposition 1.2

[PDF page 6](../manuscript/monotone_calculus.pdf#page=6). Scalar Minty representation

No maximality is assumed on the reverse direction of maximal_iff_resolvent or maximal_decreasing_iff_resolvent. J is defined on all real s, monotone and LipschitzWith 1. Both signed graph parametrizations and homeomorphisms are supplied. ofResolvent_maximal and resolvent_ofResolvent prove the arbitrary prospective-J converse; the decreasing case is output negation. The inverse identity graph equalities identify the actual resolvents. The increasing parameter is x+u and decreasing parameter is x-u; the output coordinates are s-J(s) and J(s)-s respectively. ofResolvent, ofResolvent_maximal, resolvent_ofResolvent, maximal_iff_resolvent, maximal_decreasing_iff_resolvent, mintyHomeomorph, decreasingMintyHomeomorph. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.maximal_iff_minty` | [MonotoneOperators/Minty.lean:66](../MonotoneOperators/Minty.lean#L66) |
| `ScalarMonotone.maximal_iff_resolvent` | [MonotoneOperators/Minty.lean:237](../MonotoneOperators/Minty.lean#L237) |
| `ScalarMonotone.maximal_decreasing_iff_resolvent` | [MonotoneOperators/Minty.lean:275](../MonotoneOperators/Minty.lean#L275) |
| `ScalarMonotone.mintyHomeomorph` | [MonotoneOperators/Minty.lean:187](../MonotoneOperators/Minty.lean#L187) |
| `ScalarMonotone.decreasingMintyHomeomorph` | [MonotoneOperators/Minty.lean:351](../MonotoneOperators/Minty.lean#L351) |
| `ScalarMonotone.inverse_identity_add_eq_resolvent` | [MonotoneOperators/Interface.lean:21](../MonotoneOperators/Interface.lean#L21) |
| `ScalarMonotone.inverse_identity_sub_eq_decreasingResolvent` | [MonotoneOperators/Interface.lean:36](../MonotoneOperators/Interface.lean#L36) |
| `ScalarMonotone.firmly_nonexpansive_iff_monotone_lipschitz` | [MonotoneOperators/Misc.lean:56](../MonotoneOperators/Misc.lean#L56) |
| `ScalarMonotone.ofResolvent` | [MonotoneOperators/Minty.lean:205](../MonotoneOperators/Minty.lean#L205) |
| `ScalarMonotone.ofResolvent_maximal` | [MonotoneOperators/Minty.lean:223](../MonotoneOperators/Minty.lean#L223) |
| `ScalarMonotone.resolvent_ofResolvent` | [MonotoneOperators/Minty.lean:229](../MonotoneOperators/Minty.lean#L229) |
<a id="result-1-3"></a>

## Proposition 1.3

[PDF page 7](../manuscript/monotone_calculus.pdf#page=7). Pointwise characterization of maximality

Increasing f, with arbitrary empty fibers and no domain-interior or endpoint finiteness restriction. maximal_iff_fibers is the full iff for all x,u. maximal_fiber_eq_extended_interval identifies the EReal neighboring supremum/infimum formula; EReal completeness retains empty and infinite endpoint cases. lowerEndpoint/upperEndpoint range over all y<x and y>x graph values respectively, rather than merely taking the current fiber infimum/supremum. compatible_iff_bounds translates the graph compatibility predicate into precisely the two endpoint bounds; the iff supplies the converse maximality claim. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.maximal_iff_fibers` | [MonotoneOperators/Basic.lean:173](../MonotoneOperators/Basic.lean#L173) |
| `ScalarMonotone.maximal_fiber_eq_extended_interval` | [MonotoneOperators/Basic.lean:214](../MonotoneOperators/Basic.lean#L214) |
<a id="result-1-4"></a>

## Definition 1.4

[PDF page 7](../manuscript/monotone_calculus.pdf#page=7). Maximal completion and completed restriction

An arbitrary nonempty open interval, including bounded intervals, either half-line or all of R; scalar monotonicity only on that interval. Completed restrictions retain the full maximal graph and the paper interval subset of its domain interior. The scalar completion is maximal and unique with domain in the closure. At every interior point its whole fiber is exactly the closed interval between the two finite one-sided limits. All finite boundary positions have the stated extended endpoint rays, allowing empty fibers when the inward limit diverges. Outside the closure the graph is empty. Exact completed restrictions are unique in both orientations and preserve every interior fiber, including jumps. The new arbitrary-interval interior theorem removes the earlier bounded-interval qualification. Each extended boundary formula is paired in PaperChecks with the analytic EReal one-sided limit for Ioo, Ioi or Iio. Negation is the stated decreasing-completion convention, with involutivity and decreasing uniqueness supplied. The total scalar representative is used only through restrictOperator on I; values outside I are unconstrained. lowerEndpoint/upperEndpoint are extended neighboring graph endpoints, while sInf/sSup of the completed interior fiber are finite attained real endpoints. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.unique_completion_of_monotoneOn` | [MonotoneOperators/Completion.lean:170](../MonotoneOperators/Completion.lean#L170) |
| `ScalarMonotone.unique_maximal_completion` | [MonotoneOperators/Completion.lean:135](../MonotoneOperators/Completion.lean#L135) |
| `ScalarMonotone.unique_maximal_decreasing_completion` | [MonotoneOperators/Completion.lean:220](../MonotoneOperators/Completion.lean#L220) |
| `ScalarMonotone.completion_maximal` | [MonotoneOperators/Completion.lean:89](../MonotoneOperators/Completion.lean#L89) |
| `ScalarMonotone.completion_dom_subset` | [MonotoneOperators/Completion.lean:131](../MonotoneOperators/Completion.lean#L131) |
| `ScalarMonotone.completion_fiber_eq` | [MonotoneOperators/Completion.lean:185](../MonotoneOperators/Completion.lean#L185) |
| `ScalarMonotone.negOut_negOut` | [MonotoneOperators/Basic.lean:12](../MonotoneOperators/Basic.lean#L12) |
| `ScalarMonotone.tendsto_upperEndpoint_Ioo_left` | [MonotoneOperators/CompletionLimits.lean:73](../MonotoneOperators/CompletionLimits.lean#L73) |
| `ScalarMonotone.tendsto_lowerEndpoint_Ioo_right` | [MonotoneOperators/CompletionLimits.lean:82](../MonotoneOperators/CompletionLimits.lean#L82) |
| `ScalarMonotone.tendsto_upperEndpoint_Ioi` | [MonotoneOperators/CompletionLimits.lean:90](../MonotoneOperators/CompletionLimits.lean#L90) |
| `ScalarMonotone.tendsto_lowerEndpoint_Iio` | [MonotoneOperators/CompletionLimits.lean:97](../MonotoneOperators/CompletionLimits.lean#L97) |
| `ScalarMonotone.EndOfPaper.scalar_completion_interior_limits` | [EndOfPaper/CompletionSelectionLimits.lean:18](../EndOfPaper/CompletionSelectionLimits.lean#L18) |
| `ScalarMonotone.EndOfPaper.completion_Ioo_left_extended` | [EndOfPaper/CompletionSelectionLimits.lean:44](../EndOfPaper/CompletionSelectionLimits.lean#L44) |
| `ScalarMonotone.EndOfPaper.completion_Ioo_right_extended` | [EndOfPaper/CompletionSelectionLimits.lean:54](../EndOfPaper/CompletionSelectionLimits.lean#L54) |
| `ScalarMonotone.EndOfPaper.completion_Ioi_left_extended` | [EndOfPaper/CompletionSelectionLimits.lean:64](../EndOfPaper/CompletionSelectionLimits.lean#L64) |
| `ScalarMonotone.EndOfPaper.completion_Iio_right_extended` | [EndOfPaper/CompletionSelectionLimits.lean:75](../EndOfPaper/CompletionSelectionLimits.lean#L75) |
| `ScalarMonotone.EndOfPaper.antitoneOn_unique_completion` | [EndOfPaper/HardyScalar.lean:148](../EndOfPaper/HardyScalar.lean#L148) |
| `ScalarMonotone.EndOfPaper.completion_restriction_value` | [EndOfPaper/ScalarIntegration.lean:21](../EndOfPaper/ScalarIntegration.lean#L21) |
| `ScalarMonotone.EndOfPaper.unique_completed_restriction_values` | [EndOfPaper/ScalarIntegration.lean:49](../EndOfPaper/ScalarIntegration.lean#L49) |
| `ScalarMonotone.EndOfPaper.unique_completed_decreasing_restriction_values` | [EndOfPaper/ScalarIntegration.lean:69](../EndOfPaper/ScalarIntegration.lean#L69) |
<a id="result-1-5"></a>

## Example 1.5

[PDF page 8](../manuscript/monotone_calculus.pdf#page=8). Survival and tail quantile operators

Every real random variable on an arbitrary original probability space, equivalently its law; no L1 or atomlessness is assumed. The quantile conclusions apply to every 0<p<1 and every measurable selection, with any measurable uniform argument of the specified law. The strict survival function is antitone and its actual left/right limits are the weak/strict tails. The completed strict/weak interval survival graph and its inverse are maximal decreasing. Interior quantile fibers are nonempty bounded closed order intervals. Every measurable quantile selection of every uniform argument has the original law, and the precise upper-tail parameter set has the asserted length. The original survival module supplies full maximality, quantile interval geometry and the uniform-selection law/tail-volume results. New theorems prove the actual strict/weak one-sided limits using maximal-graph selection limits and exact interval endpoints, then explicitly transfer the laws back to the original measurable space. Independent expected types cover both original-space limits, quantile geometry, arbitrary uniform arguments and exact tail-set measure. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.survival_maximal` | [MonotoneOperators/Survival.lean:86](../MonotoneOperators/Survival.lean#L86) |
| `ScalarMonotone.tailQuantile_maximal` | [MonotoneOperators/Survival.lean:99](../MonotoneOperators/Survival.lean#L99) |
| `ScalarMonotone.tailQuantile_symmetricBernoulli_half` | [MonotoneOperators/Survival.lean:228](../MonotoneOperators/Survival.lean#L228) |
| `ScalarMonotone.tailQuantile_selection_law` | [MonotoneOperators/Survival.lean:283](../MonotoneOperators/Survival.lean#L283) |
| `ScalarMonotone.tailQuantile_selection_uniform_argument` | [MonotoneOperators/Survival.lean:306](../MonotoneOperators/Survival.lean#L306) |
| `ScalarMonotone.tailQuantile_selection_law_ae` | [MonotoneOperators/ProbabilityInterface.lean:14](../MonotoneOperators/ProbabilityInterface.lean#L14) |
| `ScalarMonotone.tailQuantile_fiber_eq` | [MonotoneOperators/Survival.lean:103](../MonotoneOperators/Survival.lean#L103) |
| `ScalarMonotone.tailQuantile_fiber_closed` | [MonotoneOperators/Survival.lean:108](../MonotoneOperators/Survival.lean#L108) |
| `ScalarMonotone.tailQuantile_fiber_ordConnected` | [MonotoneOperators/Survival.lean:113](../MonotoneOperators/Survival.lean#L113) |
| `ScalarMonotone.tailQuantile_fiber_nonempty` | [MonotoneOperators/Survival.lean:126](../MonotoneOperators/Survival.lean#L126) |
| `ScalarMonotone.tailQuantile_fiber_bounded` | [MonotoneOperators/Survival.lean:136](../MonotoneOperators/Survival.lean#L136) |
| `ScalarMonotone.tailQuantile_fiber_compact` | [MonotoneOperators/Survival.lean:155](../MonotoneOperators/Survival.lean#L155) |
| `ScalarMonotone.tailQuantile_selection_tail_volume` | [MonotoneOperators/Survival.lean:249](../MonotoneOperators/Survival.lean#L249) |
| `ScalarMonotone.EndOfPaper.survival_strict_antitone` | [EndOfPaper/SurvivalJumpLimits.lean:15](../EndOfPaper/SurvivalJumpLimits.lean#L15) |
| `ScalarMonotone.EndOfPaper.survival_full_domain` | [EndOfPaper/SurvivalJumpLimits.lean:20](../EndOfPaper/SurvivalJumpLimits.lean#L20) |
| `ScalarMonotone.EndOfPaper.survival_strict_jump_limits` | [EndOfPaper/SurvivalJumpLimits.lean:25](../EndOfPaper/SurvivalJumpLimits.lean#L25) |
| `ScalarMonotone.EndOfPaper.survival_random_variable_jump_limits` | [EndOfPaper/SurvivalJumpLimits.lean:40](../EndOfPaper/SurvivalJumpLimits.lean#L40) |
<a id="result-1-6"></a>

## Proposition 1.6

[PDF page 8](../manuscript/monotone_calculus.pdf#page=8). Sums and domain–range characterization

Both summands maximal in the same orientation; only nonempty domain intersection, including a singleton intersection. No interior-intersection or range-integrability assumption is added. add_maximal and ran_add_eq prove maximality and the entire Minkowski range equality; their decreasing versions give the other orientation. maximal_iff_domain_range and maximalDecreasing_iff_domain_range prove both directions of the interval/full-sum characterization. add is pointwise Minkowski addition; OrdConnected is the scalar interval condition, and setAdd (ran f) (setNeg (dom f)) is ran f-dom f. The scalar diagonal-surjectivity argument replaces the paper citation to a Hilbert-space sum theorem and explicitly covers singleton intersections. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.add_maximal` | [MonotoneOperators/Sums.lean:95](../MonotoneOperators/Sums.lean#L95) |
| `ScalarMonotone.add_maximal_decreasing` | [MonotoneOperators/Sums.lean:280](../MonotoneOperators/Sums.lean#L280) |
| `ScalarMonotone.ran_add_eq` | [MonotoneOperators/Sums.lean:111](../MonotoneOperators/Sums.lean#L111) |
| `ScalarMonotone.ran_add_eq_decreasing` | [MonotoneOperators/Sums.lean:287](../MonotoneOperators/Sums.lean#L287) |
| `ScalarMonotone.parallelAdd_maximal` | [MonotoneOperators/Sums.lean:195](../MonotoneOperators/Sums.lean#L195) |
| `ScalarMonotone.parallelAdd_maximal_decreasing` | [MonotoneOperators/Sums.lean:301](../MonotoneOperators/Sums.lean#L301) |
| `ScalarMonotone.dom_parallelAdd_eq` | [MonotoneOperators/Sums.lean:201](../MonotoneOperators/Sums.lean#L201) |
| `ScalarMonotone.dom_parallelAdd_eq_decreasing` | [MonotoneOperators/Sums.lean:308](../MonotoneOperators/Sums.lean#L308) |
| `ScalarMonotone.maximal_iff_domain_range` | [MonotoneOperators/Sums.lean:166](../MonotoneOperators/Sums.lean#L166) |
| `ScalarMonotone.maximalDecreasing_iff_domain_range` | [MonotoneOperators/Sums.lean:317](../MonotoneOperators/Sums.lean#L317) |
<a id="result-1-7"></a>

## Proposition 1.7

[PDF page 9](../manuscript/monotone_calculus.pdf#page=9). Composition

All four pairs of maximal orientations are represented. Nonempty dom(comp g f) is exactly nonempty composite graph; comp_nonempty_iff_common_domain proves its common-intermediate-domain equivalent. Composition.lean supplies monotonicity iff NoRectangle for all four signs, even without maximality. CompositionMaximal.lean proves the maximality iff with expected sign and full domain-range condition in each case. NoRectangle f g says each inverse f z or g z is subsingleton, including empty fibers. The final sum is dom f+ran g for equal signs and dom f-ran g for opposite signs. ran_identity_add_comp and the oriented sum-range identities discharge the diagonal Minty criterion; the rectangle hypothesis is retained. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.increasing_comp_iff_noRectangle` | [MonotoneOperators/Composition.lean:45](../MonotoneOperators/Composition.lean#L45) |
| `ScalarMonotone.comp_maximal_iff_of_increasing_increasing` | [MonotoneOperators/CompositionMaximal.lean:37](../MonotoneOperators/CompositionMaximal.lean#L37) |
| `ScalarMonotone.comp_maximal_iff_of_decreasing_decreasing` | [MonotoneOperators/CompositionMaximal.lean:46](../MonotoneOperators/CompositionMaximal.lean#L46) |
| `ScalarMonotone.comp_maximal_iff_of_increasing_decreasing` | [MonotoneOperators/CompositionMaximal.lean:55](../MonotoneOperators/CompositionMaximal.lean#L55) |
| `ScalarMonotone.comp_maximal_iff_of_decreasing_increasing` | [MonotoneOperators/CompositionMaximal.lean:66](../MonotoneOperators/CompositionMaximal.lean#L66) |
| `ScalarMonotone.increasing_comp_iff_noRectangle_of_decreasing_decreasing` | [MonotoneOperators/Composition.lean:89](../MonotoneOperators/Composition.lean#L89) |
| `ScalarMonotone.decreasing_comp_iff_noRectangle_of_increasing_decreasing` | [MonotoneOperators/Composition.lean:75](../MonotoneOperators/Composition.lean#L75) |
| `ScalarMonotone.decreasing_comp_iff_noRectangle_of_decreasing_increasing` | [MonotoneOperators/Composition.lean:81](../MonotoneOperators/Composition.lean#L81) |
| `ScalarMonotone.comp_nonempty_iff_common_domain` | [MonotoneOperators/CompositionMaximal.lean:29](../MonotoneOperators/CompositionMaximal.lean#L29) |
<a id="result-1-8"></a>

## Lemma 1.8

[PDF page 10](../manuscript/monotone_calculus.pdf#page=10). Maximality under logarithms

Maximal in the specified orientation, Nonnegative f, and a strictly positive attained range value. No strict positivity of every graph value is imposed. logOp_maximal and logOp_maximal_decreasing give the same orientation and maximality. logOp retains only positive input values, exactly as the paper. Nonnegative f is equivalent by unpacking ran to ran f⊆[0,∞); ∃c∈ran f,0<c is the paper positive-range hypothesis. The zero-range exception is separately inventoried; it is not removed by strengthening the lemma hypothesis to positivity everywhere. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.logOp_maximal` | [MonotoneOperators/Products.lean:48](../MonotoneOperators/Products.lean#L48) |
| `ScalarMonotone.logOp_maximal_decreasing` | [MonotoneOperators/ProductsDual.lean:43](../MonotoneOperators/ProductsDual.lean#L43) |
<a id="result-1-9"></a>

## Proposition 1.9

[PDF page 10](../manuscript/monotone_calculus.pdf#page=10). Nonnegative products

Both factors maximal of the same orientation, and both entire ranges nonnegative. No common-domain or strict-positivity assumption is added. Increasing.mul and mul_decreasing give monotonicity; mul_maximal_iff and mul_maximal_decreasing_iff retain exactly the full-domain OR nonzero-range criterion. ran_mul_eq and its decreasing version prove the full Minkowski product range only under maximality. ran(mul f g)≠{0} is retained verbatim, rather than assumed to be a positive witness in the final statement. Internal positive/zero case lemmas discharge that alternative. The zero-degeneracy case and missing-domain failure are not suppressed; the relu/reciprocalBarrier example remains separately mapped. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.mul_maximal_iff` | [MonotoneOperators/Products.lean:229](../MonotoneOperators/Products.lean#L229) |
| `ScalarMonotone.mul_maximal_decreasing_iff` | [MonotoneOperators/ProductsDual.lean:57](../MonotoneOperators/ProductsDual.lean#L57) |
| `ScalarMonotone.ran_mul_eq` | [MonotoneOperators/Products.lean:261](../MonotoneOperators/Products.lean#L261) |
| `ScalarMonotone.ran_mul_eq_decreasing` | [MonotoneOperators/ProductsDual.lean:65](../MonotoneOperators/ProductsDual.lean#L65) |
| `ScalarMonotone.parallelMul_maximal_iff` | [MonotoneOperators/ProductsDual.lean:98](../MonotoneOperators/ProductsDual.lean#L98) |
| `ScalarMonotone.parallelMul_maximal_decreasing_iff` | [MonotoneOperators/ProductsDual.lean:107](../MonotoneOperators/ProductsDual.lean#L107) |
| `ScalarMonotone.dom_parallelMul_eq` | [MonotoneOperators/ProductsDual.lean:116](../MonotoneOperators/ProductsDual.lean#L116) |
| `ScalarMonotone.dom_parallelMul_eq_decreasing` | [MonotoneOperators/ProductsDual.lean:125](../MonotoneOperators/ProductsDual.lean#L125) |
| `ScalarMonotone.Increasing.mul` | [MonotoneOperators/Algebra.lean:119](../MonotoneOperators/Algebra.lean#L119) |
| `ScalarMonotone.mul_decreasing` | [MonotoneOperators/ProductsDual.lean:49](../MonotoneOperators/ProductsDual.lean#L49) |
<a id="result-1-10"></a>

## Example 1.10

[PDF page 12](../manuscript/monotone_calculus.pdf#page=12). A zero-degeneracy obstruction

The exact increasing relu and reciprocal-barrier graphs of the example; both maximal with entire ranges nonnegative. reciprocalBarrier_eq identifies g(x)={-1/x} for x<0 and empty otherwise. relu_mul_reciprocalBarrier identifies the zero graph precisely on x<0. The separate nonmaximality and range-identity-failure theorems prove both claimed obstructions. All equalities and counterexamples concern full set-valued graphs, including emptiness at zero; no endpoint completion of the product is substituted. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.relu` | [MonotoneOperators/Examples.lean:67](../MonotoneOperators/Examples.lean#L67) |
| `ScalarMonotone.relu_nonnegative` | [MonotoneOperators/Examples.lean:69](../MonotoneOperators/Examples.lean#L69) |
| `ScalarMonotone.relu_increasing` | [MonotoneOperators/Examples.lean:75](../MonotoneOperators/Examples.lean#L75) |
| `ScalarMonotone.relu_maximal` | [MonotoneOperators/Examples.lean:83](../MonotoneOperators/Examples.lean#L83) |
| `ScalarMonotone.relu_mul_reciprocalBarrier` | [MonotoneOperators/Examples.lean:144](../MonotoneOperators/Examples.lean#L144) |
| `ScalarMonotone.relu_mul_reciprocalBarrier_not_maximal` | [MonotoneOperators/Examples.lean:161](../MonotoneOperators/Examples.lean#L161) |
| `ScalarMonotone.relu_mul_reciprocalBarrier_range_identity_fails` | [MonotoneOperators/Examples.lean:170](../MonotoneOperators/Examples.lean#L170) |
| `ScalarMonotone.reciprocalBarrier` | [MonotoneOperators/Examples.lean:96](../MonotoneOperators/Examples.lean#L96) |
| `ScalarMonotone.reciprocalBarrier_nonnegative` | [MonotoneOperators/Examples.lean:98](../MonotoneOperators/Examples.lean#L98) |
| `ScalarMonotone.reciprocalBarrier_input_neg` | [MonotoneOperators/Examples.lean:101](../MonotoneOperators/Examples.lean#L101) |
| `ScalarMonotone.reciprocalBarrier_increasing` | [MonotoneOperators/Examples.lean:106](../MonotoneOperators/Examples.lean#L106) |
| `ScalarMonotone.reciprocalBarrier_maximal` | [MonotoneOperators/Examples.lean:116](../MonotoneOperators/Examples.lean#L116) |
| `ScalarMonotone.reciprocalBarrier_eq` | [MonotoneOperators/Examples.lean:131](../MonotoneOperators/Examples.lean#L131) |
<a id="result-1-11"></a>

## Definition 1.11

[PDF page 12](../manuscript/monotone_calculus.pdf#page=12). Pointwise resolvent order

Maximal real graphs of one fixed orientation, represented by the separate IncGraph and DecGraph bundles. The bundled PartialOrder instances use IncLE and DecLE, with reflexivity, transitivity and antisymmetry proved. IncGraph.le_iff_J and DecGraph.le_iff_J give exactly the two opposite resolvent conventions. The graph-inclusion order on raw Operator is retained separately. Nothing identifies its ≤ with the manuscript comparison. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncLE` | [MonotoneOperators/Order.lean:16](../MonotoneOperators/Order.lean#L16) |
| `ScalarMonotone.DecLE` | [MonotoneOperators/Order.lean:19](../MonotoneOperators/Order.lean#L19) |
| `ScalarMonotone.IncGraph` | [MonotoneOperators/Order.lean:122](../MonotoneOperators/Order.lean#L122) |
| `ScalarMonotone.DecGraph` | [MonotoneOperators/Order.lean:126](../MonotoneOperators/Order.lean#L126) |
| `ScalarMonotone.IncGraph.le_iff_J` | [MonotoneOperators/Extrema.lean:30](../MonotoneOperators/Extrema.lean#L30) |
| `ScalarMonotone.DecGraph.le_iff_J` | [MonotoneOperators/Extrema.lean:32](../MonotoneOperators/Extrema.lean#L32) |
| `ScalarMonotone.incLE_vertical_iff` | [MonotoneOperators/OrderGeometry.lean:121](../MonotoneOperators/OrderGeometry.lean#L121) |
| `ScalarMonotone.decLE_vertical_iff` | [MonotoneOperators/OrderGeometry.lean:135](../MonotoneOperators/OrderGeometry.lean#L135) |
<a id="result-1-12"></a>

## Proposition 1.12

[PDF page 12](../manuscript/monotone_calculus.pdf#page=12). Separated-graph characterization

Both graphs maximal of the same orientation. Fiber endpoint comparison is asserted only at common domain points; its converse retains equality of the entire domains. Both separated-graph iff statements, all positive-scale iff statements, endpoint inequalities at common points and the common-domain converse are supplied. setLowerEndpoint/setUpperEndpoint are actual fiber extrema in EReal, retaining unbounded rays and endpoint inclusion. They are different from neighboring-graph lowerEndpoint/upperEndpoint. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.incLE_iff_resolvent` | [MonotoneOperators/Order.lean:72](../MonotoneOperators/Order.lean#L72) |
| `ScalarMonotone.decLE_iff_resolvent` | [MonotoneOperators/Order.lean:87](../MonotoneOperators/Order.lean#L87) |
| `ScalarMonotone.resolvent_scale_order_iff` | [MonotoneOperators/OrderConsequences.lean:87](../MonotoneOperators/OrderConsequences.lean#L87) |
| `ScalarMonotone.decreasingResolvent_scale_order_iff` | [MonotoneOperators/OrderConsequences.lean:94](../MonotoneOperators/OrderConsequences.lean#L94) |
| `ScalarMonotone.incLE_fiber_endpoints` | [MonotoneOperators/OrderConsequences.lean:26](../MonotoneOperators/OrderConsequences.lean#L26) |
| `ScalarMonotone.decLE_fiber_endpoints` | [MonotoneOperators/OrderConsequences.lean:33](../MonotoneOperators/OrderConsequences.lean#L33) |
| `ScalarMonotone.incLE_iff_endpoints_of_dom_eq` | [MonotoneOperators/OrderConsequences.lean:40](../MonotoneOperators/OrderConsequences.lean#L40) |
| `ScalarMonotone.decLE_iff_endpoints_of_dom_eq` | [MonotoneOperators/OrderConsequences.lean:53](../MonotoneOperators/OrderConsequences.lean#L53) |
<a id="result-1-13"></a>

## Lemma 1.13

[PDF page 13](../manuscript/monotone_calculus.pdf#page=13). Resolvent comparison with an operator value

Maximal graph in either orientation, x in its domain, and arbitrary real u. The domain condition ensures a nonempty fiber, with no boundedness assumed. resolvent_le_iff_lowerHull, resolvent_ge_iff_upperHull, decreasingResolvent_ge_iff_lowerHull and decreasingResolvent_le_iff_upperHull supply all four equivalences. lowerHull is the downward hull I_-, upperHull is the upward hull I_+; decreasing resolvents are evaluated at x-u and the inequality direction changes exactly as in the paper. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.resolvent_le_iff_lowerHull` | [MonotoneOperators/Order.lean:267](../MonotoneOperators/Order.lean#L267) |
| `ScalarMonotone.resolvent_ge_iff_upperHull` | [MonotoneOperators/Order.lean:281](../MonotoneOperators/Order.lean#L281) |
| `ScalarMonotone.decreasingResolvent_ge_iff_lowerHull` | [MonotoneOperators/Order.lean:295](../MonotoneOperators/Order.lean#L295) |
| `ScalarMonotone.decreasingResolvent_le_iff_upperHull` | [MonotoneOperators/Order.lean:309](../MonotoneOperators/Order.lean#L309) |
<a id="result-1-14"></a>

## Definition 1.14

[PDF page 14](../manuscript/monotone_calculus.pdf#page=14). Order on intervals

Nonempty intervals; the predicate and its order laws are in fact valid for arbitrary OrdConnected sets, including empty ones. IntervalLE is exactly upperHull B⊆upperHull A and lowerHull A⊆lowerHull B. Reflexivity, transitivity and antisymmetry on intervals are proved via hull_inter_eq. Adjacent half-open interval examples are separately inventoried, rather than inferred solely from the closed-bounded endpoint formula. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IntervalLE` | [MonotoneOperators/Order.lean:24](../MonotoneOperators/Order.lean#L24) |
| `ScalarMonotone.intervalLE_refl` | [MonotoneOperators/Order.lean:42](../MonotoneOperators/Order.lean#L42) |
| `ScalarMonotone.IntervalLE.trans` | [MonotoneOperators/Order.lean:44](../MonotoneOperators/Order.lean#L44) |
| `ScalarMonotone.intervalLE_antisymm` | [MonotoneOperators/Order.lean:48](../MonotoneOperators/Order.lean#L48) |
| `ScalarMonotone.intervalLE_Icc_iff` | [MonotoneOperators/IntervalExtrema.lean:204](../MonotoneOperators/IntervalExtrema.lean#L204) |
| `ScalarMonotone.lowerHull_eq_setAdd` | [MonotoneOperators/OrderConsequences.lean:10](../MonotoneOperators/OrderConsequences.lean#L10) |
| `ScalarMonotone.upperHull_eq_setAdd` | [MonotoneOperators/OrderConsequences.lean:18](../MonotoneOperators/OrderConsequences.lean#L18) |
<a id="result-1-15"></a>

## Proposition 1.15

[PDF page 14](../manuscript/monotone_calculus.pdf#page=14). Domains and ranges under comparison

Maximal same-orientation graphs with IncLE or DecLE comparison. Fiber comparison retains both common-domain membership hypotheses. incLE_domains reverses the domain order, decLE_domains preserves it, and incLE_ranges/decLE_ranges preserve range order. incLE_fiber/decLE_fiber prove the interval comparison of whole common fibers. All domain/range/value comparisons use IntervalLE hull inclusions, retaining open/closed endpoints rather than replacing them by scalar endpoint bounds. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.incLE_domains` | [MonotoneOperators/OrderGeometry.lean:18](../MonotoneOperators/OrderGeometry.lean#L18) |
| `ScalarMonotone.incLE_ranges` | [MonotoneOperators/OrderGeometry.lean:23](../MonotoneOperators/OrderGeometry.lean#L23) |
| `ScalarMonotone.decLE_domains` | [MonotoneOperators/OrderGeometry.lean:51](../MonotoneOperators/OrderGeometry.lean#L51) |
| `ScalarMonotone.decLE_ranges` | [MonotoneOperators/OrderGeometry.lean:56](../MonotoneOperators/OrderGeometry.lean#L56) |
| `ScalarMonotone.incLE_fiber` | [MonotoneOperators/Order.lean:323](../MonotoneOperators/Order.lean#L323) |
| `ScalarMonotone.decLE_fiber` | [MonotoneOperators/Order.lean:339](../MonotoneOperators/Order.lean#L339) |
<a id="result-1-16"></a>

## Proposition 1.16

[PDF page 15](../manuscript/monotone_calculus.pdf#page=15). Inversion and elementary compatibility

Maximal f,g in the same orientation. For sums/products h has that orientation and products retain nonnegativity of all ranges. Composite maximality assumptions imply the weaker monotonicity hypotheses used by the helper theorems. incLE_inverse_iff reverses order and decLE_inverse_iff preserves it. Addition/product comparison holds in both orientations. Eight left/right composition theorems cover every inner/outer orientation, with reversal exactly for a decreasing outer map. At an equal intermediate value, NoRectangle follows from monotonicity of the composite and forces the relevant outer fiber to be subsingleton. le_at_of_subsingleton_left justifies equal-input comparison; it is not silently inferred from separated comparison. resolvent_inverse and decreasingResolvent_inverse retain J_inv(s)=s-J(s) and J_inv(s)=s+J(-s), respectively. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.incLE_inverse_iff` | [MonotoneOperators/Order.lean:159](../MonotoneOperators/Order.lean#L159) |
| `ScalarMonotone.decLE_inverse_iff` | [MonotoneOperators/Order.lean:170](../MonotoneOperators/Order.lean#L170) |
| `ScalarMonotone.IncLE.add_right` | [MonotoneOperators/OrderOperations.lean:26](../MonotoneOperators/OrderOperations.lean#L26) |
| `ScalarMonotone.IncLE.add_left` | [MonotoneOperators/OrderOperations.lean:36](../MonotoneOperators/OrderOperations.lean#L36) |
| `ScalarMonotone.DecLE.add_right` | [MonotoneOperators/OrderOperations.lean:31](../MonotoneOperators/OrderOperations.lean#L31) |
| `ScalarMonotone.DecLE.add_left` | [MonotoneOperators/OrderOperations.lean:40](../MonotoneOperators/OrderOperations.lean#L40) |
| `ScalarMonotone.IncLE.mul_right` | [MonotoneOperators/OrderOperations.lean:44](../MonotoneOperators/OrderOperations.lean#L44) |
| `ScalarMonotone.IncLE.mul_left` | [MonotoneOperators/OrderOperations.lean:57](../MonotoneOperators/OrderOperations.lean#L57) |
| `ScalarMonotone.DecLE.mul_right` | [MonotoneOperators/OrderOperations.lean:50](../MonotoneOperators/OrderOperations.lean#L50) |
| `ScalarMonotone.DecLE.mul_left` | [MonotoneOperators/OrderOperations.lean:62](../MonotoneOperators/OrderOperations.lean#L62) |
| `ScalarMonotone.IncLE.parallelAdd_right` | [MonotoneOperators/OrderOperations.lean:67](../MonotoneOperators/OrderOperations.lean#L67) |
| `ScalarMonotone.IncLE.parallelMul_right` | [MonotoneOperators/OrderOperations.lean:77](../MonotoneOperators/OrderOperations.lean#L77) |
| `ScalarMonotone.DecLE.parallelAdd_right` | [MonotoneOperators/OrderOperations.lean:72](../MonotoneOperators/OrderOperations.lean#L72) |
| `ScalarMonotone.DecLE.parallelMul_right` | [MonotoneOperators/OrderOperations.lean:84](../MonotoneOperators/OrderOperations.lean#L84) |
| `ScalarMonotone.IncLE.comp_right_of_increasing` | [MonotoneOperators/OrderOperations.lean:115](../MonotoneOperators/OrderOperations.lean#L115) |
| `ScalarMonotone.IncLE.comp_right_of_decreasing` | [MonotoneOperators/OrderOperations.lean:127](../MonotoneOperators/OrderOperations.lean#L127) |
| `ScalarMonotone.IncLE.comp_left_of_increasing` | [MonotoneOperators/OrderOperations.lean:165](../MonotoneOperators/OrderOperations.lean#L165) |
| `ScalarMonotone.IncLE.comp_left_of_decreasing` | [MonotoneOperators/OrderOperations.lean:174](../MonotoneOperators/OrderOperations.lean#L174) |
| `ScalarMonotone.DecLE.comp_right_of_increasing` | [MonotoneOperators/OrderOperations.lean:140](../MonotoneOperators/OrderOperations.lean#L140) |
| `ScalarMonotone.DecLE.comp_right_of_decreasing` | [MonotoneOperators/OrderOperations.lean:153](../MonotoneOperators/OrderOperations.lean#L153) |
| `ScalarMonotone.DecLE.comp_left_of_increasing` | [MonotoneOperators/OrderOperations.lean:183](../MonotoneOperators/OrderOperations.lean#L183) |
| `ScalarMonotone.DecLE.comp_left_of_decreasing` | [MonotoneOperators/OrderOperations.lean:192](../MonotoneOperators/OrderOperations.lean#L192) |
| `ScalarMonotone.resolvent_inverse` | [MonotoneOperators/OrderConsequences.lean:101](../MonotoneOperators/OrderConsequences.lean#L101) |
| `ScalarMonotone.decreasingResolvent_inverse` | [MonotoneOperators/OrderConsequences.lean:106](../MonotoneOperators/OrderConsequences.lean#L106) |
<a id="result-1-17"></a>

## Lemma 1.17

[PDF page 16](../manuscript/monotone_calculus.pdf#page=16). Survival comparison

Arbitrary measurable real X on an arbitrary probability space, and target maximal decreasing alpha. The helper strict-tail graph test is actually valid for any target graph, so imposes no additional hypothesis. survival_map_comparison_iff gives exactly P(X>t)≤u for every (t,u) in alpha. survival_le_iff_tailQuantile_le supplies the inverse-quantile equivalence, with atoms retained. Strict-tail right continuity gives necessity at each threshold, rather than merely almost everywhere. The map-measure identity transfers the canonical real-law test to the original probability space. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.survival_comparison_iff` | [MonotoneOperators/ProbabilityBounds.lean:33](../MonotoneOperators/ProbabilityBounds.lean#L33) |
| `ScalarMonotone.survival_map_comparison_iff` | [MonotoneOperators/ProbabilityBounds.lean:51](../MonotoneOperators/ProbabilityBounds.lean#L51) |
| `ScalarMonotone.survival_le_iff_tailQuantile_le` | [MonotoneOperators/ProbabilityBounds.lean:46](../MonotoneOperators/ProbabilityBounds.lean#L46) |
<a id="result-1-18"></a>

## Theorem 1.18

[PDF page 16](../manuscript/monotone_calculus.pdf#page=16). Conditional completeness

Arbitrary nonempty index type; no countability or finiteness. BddBelow/BddAbove of the family are exactly the existence qualifications, in the actual resolvent partial order. inc_exists_isGLB_iff/inc_exists_isLUB_iff and the decreasing analogues prove both directions of conditional completeness. Four explicit incInf/decInf/incSup/decSup constructions have universal properties and the exact four pointwise resolvent formulas. ConditionallyCompleteLattice instances have total default operations, but meaningful formula theorems retain the correct boundedness hypothesis. They do not assert unrestricted completeness. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.inc_exists_isGLB_iff` | [MonotoneOperators/Extrema.lean:246](../MonotoneOperators/Extrema.lean#L246) |
| `ScalarMonotone.inc_exists_isLUB_iff` | [MonotoneOperators/Extrema.lean:254](../MonotoneOperators/Extrema.lean#L254) |
| `ScalarMonotone.dec_exists_isGLB_iff` | [MonotoneOperators/Extrema.lean:262](../MonotoneOperators/Extrema.lean#L262) |
| `ScalarMonotone.dec_exists_isLUB_iff` | [MonotoneOperators/Extrema.lean:270](../MonotoneOperators/Extrema.lean#L270) |
| `ScalarMonotone.IncGraph.J_iInf` | [MonotoneOperators/ExtremaComplete.lean:103](../MonotoneOperators/ExtremaComplete.lean#L103) |
| `ScalarMonotone.IncGraph.J_iSup` | [MonotoneOperators/ExtremaComplete.lean:105](../MonotoneOperators/ExtremaComplete.lean#L105) |
| `ScalarMonotone.DecGraph.J_iInf` | [MonotoneOperators/ExtremaComplete.lean:107](../MonotoneOperators/ExtremaComplete.lean#L107) |
| `ScalarMonotone.DecGraph.J_iSup` | [MonotoneOperators/ExtremaComplete.lean:109](../MonotoneOperators/ExtremaComplete.lean#L109) |
| `ScalarMonotone.IncGraph.constants_not_bddAbove` | [MonotoneOperators/ExtremaExamples.lean:22](../MonotoneOperators/ExtremaExamples.lean#L22) |
| `ScalarMonotone.DecGraph.constants_not_bddAbove` | [MonotoneOperators/ExtremaExamples.lean:31](../MonotoneOperators/ExtremaExamples.lean#L31) |
<a id="result-1-19"></a>

## Lemma 1.19

[PDF page 17](../manuscript/monotone_calculus.pdf#page=17). Inversion and extrema

Arbitrary nonempty family in either orientation. The existence of the other side is justified by all four bddAbove_inv_iff/bddBelow_inv_iff equivalences, not assumed. The increasing inverseOrderIso targets OrderDual and exchanges inf/sup. The decreasing inverseOrderIso preserves them. Four inv_iInf/inv_iSup theorems and bound-existence iff statements cover every table entry and both existence directions. The involutive inverse is the entire relational inverse, including all boundary and vertical fibers. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncGraph.inv_iInf` | [MonotoneOperators/ExtremaComplete.lean:197](../MonotoneOperators/ExtremaComplete.lean#L197) |
| `ScalarMonotone.IncGraph.inv_iSup` | [MonotoneOperators/ExtremaComplete.lean:199](../MonotoneOperators/ExtremaComplete.lean#L199) |
| `ScalarMonotone.DecGraph.inv_iInf` | [MonotoneOperators/ExtremaComplete.lean:201](../MonotoneOperators/ExtremaComplete.lean#L201) |
| `ScalarMonotone.DecGraph.inv_iSup` | [MonotoneOperators/ExtremaComplete.lean:203](../MonotoneOperators/ExtremaComplete.lean#L203) |
<a id="result-1-20"></a>

## Proposition 1.20

[PDF page 17](../manuscript/monotone_calculus.pdf#page=17). Order bounds for extrema

An arbitrary nonempty family in either bundled maximal orientation, with exactly the existence of the displayed extrema and maximality of the displayed images. No boundedness, finiteness or total admissibility assumption is substituted. The four partial_orderPreserving/partial_orderReversing inf/sup bounds prove every preserving and reversing inequality. Their arbitrary source/target preorders include both same-orientation and cross-orientation choices. Instantiate alpha and beta by IncGraph or DecGraph, and P x by maximality of the raw image Phi(x). The dependent map bundles that raw image only when P x holds. Its hF and hf hypotheses are exactly maximality of the displayed images, while IsGLB/IsLUB express the existing extrema. The separately established bundled order instances identify their comparisons with IncLE/DecLE. The four MonotoneOn/AntitoneOn variants give the equivalent admissible-set formulation. No order property is assumed for inadmissible images. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.partial_orderPreserving_inf_bound` | [MonotoneOperators/ExtremaOperations.lean:63](../MonotoneOperators/ExtremaOperations.lean#L63) |
| `ScalarMonotone.partial_orderPreserving_sup_bound` | [MonotoneOperators/ExtremaOperations.lean:71](../MonotoneOperators/ExtremaOperations.lean#L71) |
| `ScalarMonotone.partial_orderReversing_inf_bound` | [MonotoneOperators/ExtremaOperations.lean:79](../MonotoneOperators/ExtremaOperations.lean#L79) |
| `ScalarMonotone.partial_orderReversing_sup_bound` | [MonotoneOperators/ExtremaOperations.lean:87](../MonotoneOperators/ExtremaOperations.lean#L87) |
| `ScalarMonotone.monotoneOn_inf_bound` | [MonotoneOperators/ExtremaOperations.lean:21](../MonotoneOperators/ExtremaOperations.lean#L21) |
| `ScalarMonotone.monotoneOn_sup_bound` | [MonotoneOperators/ExtremaOperations.lean:29](../MonotoneOperators/ExtremaOperations.lean#L29) |
| `ScalarMonotone.antitoneOn_inf_bound` | [MonotoneOperators/ExtremaOperations.lean:37](../MonotoneOperators/ExtremaOperations.lean#L37) |
| `ScalarMonotone.antitoneOn_sup_bound` | [MonotoneOperators/ExtremaOperations.lean:45](../MonotoneOperators/ExtremaOperations.lean#L45) |
<a id="result-1-21"></a>

## Definition 1.21

[PDF page 18](../manuscript/monotone_calculus.pdf#page=18). Infimum and supremum of intervals

Finite nonempty family of nonempty intervals, with arbitrary open, closed or infinite endpoints. intervalInf/intervalSup use the exact union/intersection hull formulas. Their nonemptiness, interval property, GLB/LUB universal properties and both binary equality iff characterizations are proved. These are interval-order extrema of sets, not scalar min/max and not selections from the family. Pair equalities use Bool only to index the same unordered two-element family. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.intervalInf` | [MonotoneOperators/IntervalExtrema.lean:17](../MonotoneOperators/IntervalExtrema.lean#L17) |
| `ScalarMonotone.intervalSup` | [MonotoneOperators/IntervalExtrema.lean:20](../MonotoneOperators/IntervalExtrema.lean#L20) |
| `ScalarMonotone.intervalInf_universal` | [MonotoneOperators/IntervalExtrema.lean:150](../MonotoneOperators/IntervalExtrema.lean#L150) |
| `ScalarMonotone.intervalSup_universal` | [MonotoneOperators/IntervalExtrema.lean:158](../MonotoneOperators/IntervalExtrema.lean#L158) |
| `ScalarMonotone.upperHull_intervalInf` | [MonotoneOperators/IntervalExtrema.lean:64](../MonotoneOperators/IntervalExtrema.lean#L64) |
| `ScalarMonotone.lowerHull_intervalInf` | [MonotoneOperators/IntervalExtrema.lean:82](../MonotoneOperators/IntervalExtrema.lean#L82) |
| `ScalarMonotone.upperHull_intervalSup` | [MonotoneOperators/IntervalExtrema.lean:98](../MonotoneOperators/IntervalExtrema.lean#L98) |
| `ScalarMonotone.lowerHull_intervalSup` | [MonotoneOperators/IntervalExtrema.lean:114](../MonotoneOperators/IntervalExtrema.lean#L114) |
<a id="result-1-22"></a>

## Proposition 1.22

[PDF page 19](../manuscript/monotone_calculus.pdf#page=19). Domains, ranges, and values of finite extrema

Finite nonempty arbitrary maximal family, in either orientation. Fiber identities retain the common-domain condition ∀i,x∈dom(f_i). No common-domain restriction is imposed on the global domain/range formulas. Four domain formulas, four range formulas, all interval-valued fiber identities and all four EReal endpoint expressions are supplied. Closure and endpoint inclusion are retained globally. Increasing domain inf/sup reverses the interval extrema; decreasing domain inf/sup preserves them. Ranges preserve inf/sup in both orientations, exactly as the table. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncGraph.dom_iInf` | [MonotoneOperators/ExtremaFinite.lean:153](../MonotoneOperators/ExtremaFinite.lean#L153) |
| `ScalarMonotone.IncGraph.dom_iSup` | [MonotoneOperators/ExtremaFinite.lean:162](../MonotoneOperators/ExtremaFinite.lean#L162) |
| `ScalarMonotone.DecGraph.dom_iInf` | [MonotoneOperators/ExtremaFinite.lean:171](../MonotoneOperators/ExtremaFinite.lean#L171) |
| `ScalarMonotone.DecGraph.dom_iSup` | [MonotoneOperators/ExtremaFinite.lean:180](../MonotoneOperators/ExtremaFinite.lean#L180) |
| `ScalarMonotone.IncGraph.ran_iInf` | [MonotoneOperators/ExtremaFinite.lean:189](../MonotoneOperators/ExtremaFinite.lean#L189) |
| `ScalarMonotone.IncGraph.ran_iSup` | [MonotoneOperators/ExtremaFinite.lean:194](../MonotoneOperators/ExtremaFinite.lean#L194) |
| `ScalarMonotone.DecGraph.ran_iInf` | [MonotoneOperators/ExtremaFinite.lean:199](../MonotoneOperators/ExtremaFinite.lean#L199) |
| `ScalarMonotone.DecGraph.ran_iSup` | [MonotoneOperators/ExtremaFinite.lean:204](../MonotoneOperators/ExtremaFinite.lean#L204) |
| `ScalarMonotone.IncGraph.fiber_iInf` | [MonotoneOperators/ExtremaFinite.lean:229](../MonotoneOperators/ExtremaFinite.lean#L229) |
| `ScalarMonotone.IncGraph.fiber_iInf_endpoints` | [MonotoneOperators/ExtremaFinite.lean:289](../MonotoneOperators/ExtremaFinite.lean#L289) |
| `ScalarMonotone.IncGraph.fiber_iInf_active` | [MonotoneOperators/ExtremaActive.lean:48](../MonotoneOperators/ExtremaActive.lean#L48) |
| `ScalarMonotone.IncGraph.fiber_iSup` | [MonotoneOperators/ExtremaFinite.lean:243](../MonotoneOperators/ExtremaFinite.lean#L243) |
| `ScalarMonotone.IncGraph.fiber_iSup_endpoints` | [MonotoneOperators/ExtremaFinite.lean:297](../MonotoneOperators/ExtremaFinite.lean#L297) |
| `ScalarMonotone.IncGraph.fiber_iSup_active` | [MonotoneOperators/ExtremaActive.lean:75](../MonotoneOperators/ExtremaActive.lean#L75) |
| `ScalarMonotone.DecGraph.fiber_iInf` | [MonotoneOperators/ExtremaFinite.lean:257](../MonotoneOperators/ExtremaFinite.lean#L257) |
| `ScalarMonotone.DecGraph.fiber_iInf_endpoints` | [MonotoneOperators/ExtremaFinite.lean:305](../MonotoneOperators/ExtremaFinite.lean#L305) |
| `ScalarMonotone.DecGraph.fiber_iInf_active` | [MonotoneOperators/ExtremaActive.lean:102](../MonotoneOperators/ExtremaActive.lean#L102) |
| `ScalarMonotone.DecGraph.fiber_iSup` | [MonotoneOperators/ExtremaFinite.lean:273](../MonotoneOperators/ExtremaFinite.lean#L273) |
| `ScalarMonotone.DecGraph.fiber_iSup_endpoints` | [MonotoneOperators/ExtremaFinite.lean:313](../MonotoneOperators/ExtremaFinite.lean#L313) |
| `ScalarMonotone.DecGraph.fiber_iSup_active` | [MonotoneOperators/ExtremaActive.lean:130](../MonotoneOperators/ExtremaActive.lean#L130) |
<a id="result-1-23"></a>

## Proposition 1.23

[PDF page 21](../manuscript/monotone_calculus.pdf#page=21). Lattice median

Every natural r, including r=0; family indexed by Fin(2*r+1); both maximal orientations. Majority r indexes exact r+1-element subsets, the existential form of having at least r+1 qualifying entries. Both finite lattice expressions coincide. The same median, formed before scaling, has the scalar median resolvent at every real argument and every positive output scale. Majority bounds hold in both orientations. The positive scaleOrderIso transports the fixed lattice median; no scale-dependent choice of operator is substituted. scalar_median_minmax_eq_maxmin supplies the scalar two-formula equivalence. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.inc_lattice_median` | [MonotoneOperators/Median.lean:146](../MonotoneOperators/Median.lean#L146) |
| `ScalarMonotone.dec_lattice_median` | [MonotoneOperators/Median.lean:153](../MonotoneOperators/Median.lean#L153) |
| `ScalarMonotone.inc_lattice_median_resolvent_scale` | [MonotoneOperators/Median.lean:169](../MonotoneOperators/Median.lean#L169) |
| `ScalarMonotone.dec_lattice_median_resolvent_scale` | [MonotoneOperators/Median.lean:176](../MonotoneOperators/Median.lean#L176) |
| `ScalarMonotone.inc_lattice_median_majority` | [MonotoneOperators/Median.lean:183](../MonotoneOperators/Median.lean#L183) |
| `ScalarMonotone.dec_lattice_median_majority` | [MonotoneOperators/Median.lean:188](../MonotoneOperators/Median.lean#L188) |
<a id="result-1-24"></a>

## Proposition 1.24

[PDF page 21](../manuscript/monotone_calculus.pdf#page=21). Finite algebraic identities

Finite nonempty arbitrary-domain maximal family and maximal h of the same orientation; each displayed h+f_i or h*f_i is maximal. For products only ran h⊆[0,∞) is required, not nonnegativity of every f_i. All eight addition/product, infimum/supremum and increasing/decreasing identities are equalities of entire operators. Neither only common-interior values nor additional common-domain hypotheses are substituted. Domain intersections are justified from nonempty maximal summands/products; active-index formulas handle points absent from some input domains, and interval product arithmetic retains boundary fibers. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.inc_add_iInf` | [MonotoneOperators/ExtremaIdentities.lean:104](../MonotoneOperators/ExtremaIdentities.lean#L104) |
| `ScalarMonotone.inc_add_iSup` | [MonotoneOperators/ExtremaIdentities.lean:114](../MonotoneOperators/ExtremaIdentities.lean#L114) |
| `ScalarMonotone.dec_add_iInf` | [MonotoneOperators/ExtremaIdentities.lean:124](../MonotoneOperators/ExtremaIdentities.lean#L124) |
| `ScalarMonotone.dec_add_iSup` | [MonotoneOperators/ExtremaIdentities.lean:139](../MonotoneOperators/ExtremaIdentities.lean#L139) |
| `ScalarMonotone.inc_mul_iInf` | [MonotoneOperators/ExtremaProducts.lean:37](../MonotoneOperators/ExtremaProducts.lean#L37) |
| `ScalarMonotone.inc_mul_iSup` | [MonotoneOperators/ExtremaProducts.lean:77](../MonotoneOperators/ExtremaProducts.lean#L77) |
| `ScalarMonotone.dec_mul_iInf` | [MonotoneOperators/ExtremaProducts.lean:117](../MonotoneOperators/ExtremaProducts.lean#L117) |
| `ScalarMonotone.dec_mul_iSup` | [MonotoneOperators/ExtremaProducts.lean:135](../MonotoneOperators/ExtremaProducts.lean#L135) |
| `ScalarMonotone.inc_parallelAdd_iInf` | [MonotoneOperators/ExtremaInversionIdentities.lean:38](../MonotoneOperators/ExtremaInversionIdentities.lean#L38) |
| `ScalarMonotone.inc_parallelAdd_iSup` | [MonotoneOperators/ExtremaInversionIdentities.lean:51](../MonotoneOperators/ExtremaInversionIdentities.lean#L51) |
| `ScalarMonotone.dec_parallelAdd_iInf` | [MonotoneOperators/ExtremaInversionIdentities.lean:64](../MonotoneOperators/ExtremaInversionIdentities.lean#L64) |
| `ScalarMonotone.dec_parallelAdd_iSup` | [MonotoneOperators/ExtremaInversionIdentities.lean:77](../MonotoneOperators/ExtremaInversionIdentities.lean#L77) |
| `ScalarMonotone.inc_parallelMul_iInf` | [MonotoneOperators/ExtremaProducts.lean:153](../MonotoneOperators/ExtremaProducts.lean#L153) |
| `ScalarMonotone.inc_parallelMul_iSup` | [MonotoneOperators/ExtremaProducts.lean:168](../MonotoneOperators/ExtremaProducts.lean#L168) |
| `ScalarMonotone.dec_parallelMul_iInf` | [MonotoneOperators/ExtremaProducts.lean:183](../MonotoneOperators/ExtremaProducts.lean#L183) |
| `ScalarMonotone.dec_parallelMul_iSup` | [MonotoneOperators/ExtremaProducts.lean:198](../MonotoneOperators/ExtremaProducts.lean#L198) |
<a id="result-1-25"></a>

## Proposition 1.25

[PDF page 22](../manuscript/monotone_calculus.pdf#page=22). Composition and extrema

Finite nonempty family in either maximal orientation, maximal h in either orientation, and only the manuscript componentwise maximality assumptions for the respective compositions. All eight right-composition and eight left-composition identities hold as whole-operator equalities. Right composition preserves inf/sup; a decreasing outer h swaps them for left composition, including when the input family is decreasing. The finite resolvent selector/rectangle arguments give whole-graph equalities. Relational inversion proves the left-composition cases without assuming common domains or single-valued operators. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.inc_comp_right_iInf_inc` | [MonotoneOperators/ExtremaIdentities.lean:154](../MonotoneOperators/ExtremaIdentities.lean#L154) |
| `ScalarMonotone.inc_comp_right_iSup_inc` | [MonotoneOperators/ExtremaIdentities.lean:164](../MonotoneOperators/ExtremaIdentities.lean#L164) |
| `ScalarMonotone.inc_comp_right_iInf_dec` | [MonotoneOperators/ExtremaIdentities.lean:174](../MonotoneOperators/ExtremaIdentities.lean#L174) |
| `ScalarMonotone.inc_comp_right_iSup_dec` | [MonotoneOperators/ExtremaIdentities.lean:189](../MonotoneOperators/ExtremaIdentities.lean#L189) |
| `ScalarMonotone.dec_comp_right_iInf_inc` | [MonotoneOperators/ExtremaIdentities.lean:204](../MonotoneOperators/ExtremaIdentities.lean#L204) |
| `ScalarMonotone.dec_comp_right_iSup_inc` | [MonotoneOperators/ExtremaIdentities.lean:218](../MonotoneOperators/ExtremaIdentities.lean#L218) |
| `ScalarMonotone.dec_comp_right_iInf_dec` | [MonotoneOperators/ExtremaIdentities.lean:232](../MonotoneOperators/ExtremaIdentities.lean#L232) |
| `ScalarMonotone.dec_comp_right_iSup_dec` | [MonotoneOperators/ExtremaIdentities.lean:244](../MonotoneOperators/ExtremaIdentities.lean#L244) |
| `ScalarMonotone.inc_comp_left_iInf_inc` | [MonotoneOperators/ExtremaInversionIdentities.lean:90](../MonotoneOperators/ExtremaInversionIdentities.lean#L90) |
| `ScalarMonotone.inc_comp_left_iSup_inc` | [MonotoneOperators/ExtremaInversionIdentities.lean:106](../MonotoneOperators/ExtremaInversionIdentities.lean#L106) |
| `ScalarMonotone.inc_comp_left_iInf_dec` | [MonotoneOperators/ExtremaInversionIdentities.lean:122](../MonotoneOperators/ExtremaInversionIdentities.lean#L122) |
| `ScalarMonotone.inc_comp_left_iSup_dec` | [MonotoneOperators/ExtremaInversionIdentities.lean:138](../MonotoneOperators/ExtremaInversionIdentities.lean#L138) |
| `ScalarMonotone.dec_comp_left_iInf_inc` | [MonotoneOperators/ExtremaInversionIdentities.lean:154](../MonotoneOperators/ExtremaInversionIdentities.lean#L154) |
| `ScalarMonotone.dec_comp_left_iSup_inc` | [MonotoneOperators/ExtremaInversionIdentities.lean:170](../MonotoneOperators/ExtremaInversionIdentities.lean#L170) |
| `ScalarMonotone.dec_comp_left_iInf_dec` | [MonotoneOperators/ExtremaInversionIdentities.lean:186](../MonotoneOperators/ExtremaInversionIdentities.lean#L186) |
| `ScalarMonotone.dec_comp_left_iSup_dec` | [MonotoneOperators/ExtremaInversionIdentities.lean:202](../MonotoneOperators/ExtremaInversionIdentities.lean#L202) |
<a id="result-1-26"></a>

## Proposition 1.26

[PDF page 25](../manuscript/monotone_calculus.pdf#page=25). Sums and nonnegative products

Arbitrary measurable real random variables on one arbitrary probability space, with a finite nonempty index set and no independence. The sum retains exactly the common-range condition. The product retains ae nonnegativity and maximality of the inverse product; its helper proves a stronger statement without separately needing nonnegative domains. survival_finite_sum_bound and survival_finite_product_bound prove both entire-profile comparisons with coefficient card(index), together with maximality of those profiles. finiteParallelAdd/finiteParallelMul are inverses of the finite Minkowski sum/product of the inverse fibers. Fin n identifies their cardinal coefficient with n; the paper uses a nonempty list of variables. survival_map_comparison_iff transfers the graph-wise strict-tail union bound to DecLE. Almost-sure nonnegativity is used through an ae event inclusion, so exceptional null sets are retained. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.finite_sum_tail_bound` | [MonotoneOperators/ProbabilityCore.lean:114](../MonotoneOperators/ProbabilityCore.lean#L114) |
| `ScalarMonotone.finite_product_tail_bound` | [MonotoneOperators/ProbabilityCore.lean:137](../MonotoneOperators/ProbabilityCore.lean#L137) |
| `ScalarMonotone.survival_finite_sum_bound` | [MonotoneOperators/ProbabilityBounds.lean:71](../MonotoneOperators/ProbabilityBounds.lean#L71) |
| `ScalarMonotone.survival_finite_product_bound` | [MonotoneOperators/ProbabilityBounds.lean:93](../MonotoneOperators/ProbabilityBounds.lean#L93) |
| `ScalarMonotone.finiteParallelAdd` | [MonotoneOperators/ProbabilityCore.lean:32](../MonotoneOperators/ProbabilityCore.lean#L32) |
| `ScalarMonotone.finiteParallelMul` | [MonotoneOperators/ProbabilityCore.lean:36](../MonotoneOperators/ProbabilityCore.lean#L36) |
| `ScalarMonotone.finiteParallelAdd_maximal_decreasing` | [MonotoneOperators/ProbabilityCore.lean:101](../MonotoneOperators/ProbabilityCore.lean#L101) |
<a id="result-1-27"></a>

## Corollary 1.27

[PDF page 26](../manuscript/monotone_calculus.pdf#page=26). Centered sums and products

Arbitrary measurable X,Y on one probability space, arbitrary real pivots, nonnegative comparison domains for the product, and maximality of each displayed final profile. The stronger helper conclusions do not need the additional common-range condition once this maximality is provided. survival_centered_sum_bound and survival_centered_product_bound give the full graph comparisons and maximality with coefficient 2. centeredProductProfile_eq_parallel gives the exact displayed parallel formula when both pivots are nonzero; zero_left, zero_right and zero_zero prove the exact deletion conventions as equalities of entire graphs. inputDivide c f is f composed with id/c, proved in inputDivide_eq_comp. Output scaling by the absolute pivot is converted by inverse_outputScale_inverse, with its nonzero condition discharged in the nonzero-pivot case. The product proof permits separate witnesses for the three inverse-polynomial summands, then chooses the smaller threshold from each original inverse fiber. This proves the same whole-profile bound directly, retaining boundary fibers without assuming the interval-image identity as a hypothesis. Only the two original exceptional events are counted. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.survival_centered_sum_bound` | [MonotoneOperators/ProbabilityBounds.lean:114](../MonotoneOperators/ProbabilityBounds.lean#L114) |
| `ScalarMonotone.survival_centered_product_bound` | [MonotoneOperators/ProbabilityBounds.lean:246](../MonotoneOperators/ProbabilityBounds.lean#L246) |
| `ScalarMonotone.centeredProductProfile_eq_parallel` | [MonotoneOperators/ProbabilityBounds.lean:157](../MonotoneOperators/ProbabilityBounds.lean#L157) |
| `ScalarMonotone.centeredProductProfile_zero_left` | [MonotoneOperators/ProbabilityBounds.lean:168](../MonotoneOperators/ProbabilityBounds.lean#L168) |
| `ScalarMonotone.centeredProductProfile_zero_right` | [MonotoneOperators/ProbabilityBounds.lean:184](../MonotoneOperators/ProbabilityBounds.lean#L184) |
| `ScalarMonotone.centeredProductProfile_zero_zero` | [MonotoneOperators/ProbabilityBounds.lean:198](../MonotoneOperators/ProbabilityBounds.lean#L198) |
| `ScalarMonotone.centeredProductProfile` | [MonotoneOperators/ProbabilityBounds.lean:151](../MonotoneOperators/ProbabilityBounds.lean#L151) |
| `ScalarMonotone.inputDivide_eq_comp` | [MonotoneOperators/ProbabilityBounds.lean:134](../MonotoneOperators/ProbabilityBounds.lean#L134) |
| `ScalarMonotone.inverse_outputScale_inverse` | [MonotoneOperators/ProbabilityBounds.lean:139](../MonotoneOperators/ProbabilityBounds.lean#L139) |
<a id="result-1-28"></a>

## Proposition 1.28

[PDF page 26](../manuscript/monotone_calculus.pdf#page=26). Weighted parallel-sum envelopes

Finite nonempty decreasing maximal family with common range D, arbitrary strictly positive real weights summing to one. The common range is not required bounded or closed. DecGraph.parallelSum_envelopes proves both bounds for the entire parallel sum. weightedProfile represents precisely alpha_i composed with theta_i*id via inversion of positive output scaling. Optimized-weight equalities are additional supporting results and are not used to change this proposition or add their positivity hypotheses to its fixed-weight bounds. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncGraph.parallelSum_envelopes` | [MonotoneOperators/Envelopes.lean:414](../MonotoneOperators/Envelopes.lean#L414) |
| `ScalarMonotone.DecGraph.parallelSum_envelopes` | [MonotoneOperators/Envelopes.lean:400](../MonotoneOperators/Envelopes.lean#L400) |
| `ScalarMonotone.IncGraph.optimized_parallelSum_envelopes` | [MonotoneOperators/Envelopes.lean:467](../MonotoneOperators/Envelopes.lean#L467) |
| `ScalarMonotone.DecGraph.optimized_parallelSum_envelopes` | [MonotoneOperators/Envelopes.lean:429](../MonotoneOperators/Envelopes.lean#L429) |
<a id="result-1-29"></a>

## Example 1.29

[PDF page 27](../manuscript/monotone_calculus.pdf#page=27). Multilevel concentration for a product

Arbitrary n>=1, nonzero real pivots and strictly positive scales, measurable random tuple on any original probability space, and the literal common-profile marginal survival comparisons. The reader explicitly assumes the manuscript nonnegative half-line domain and, for the final illustration, the Gaussian positive-input singleton profile. No independence, original-space uniform variable, or L1 is added. The arbitrary-n proof supplies every conclusion: the pointwise deviation estimate and exact cardinality-grouped polynomial; positive coefficients and increasing nonnegative bijection; the ordinary inverse-polynomial parallel-root identity before composition; the entire composed parallel-monomial identity including jumps and zero; the original-space survival comparison and weighted lattice supremum; and the exact capped Gaussian multilevel rate with d equal to the number of positive coefficients. Under the original nonzero-pivot assumptions every coefficient is positive, and d=n is proved explicitly. Reuse the exact finite subset expansion and group by cardinality. The inverse of the literal nonnegative polynomial graph is the finite parallel sum of its ordinary positive-degree roots, by the graph inverse algebra and the existing monomial root theorem. An interval-diagonal intermediate-value argument proves the composed identity even at jumps. A finite union bound gives the survival graph order and the weighted envelope. For the Gaussian rate choose the least positive root threshold; each polynomial summand is at most t/d, and the finite union bound gives exactly the uniform-weight rate, with the cap supplied by probability normalization. This is an alternative direct proof of the same stated Gaussian consequence. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.productDeviation` | [EndOfPaper/ProductExpansion.lean:15](../EndOfPaper/ProductExpansion.lean#L15) |
| `ScalarMonotone.EndOfPaper.centered_product_finset_bound` | [EndOfPaper/ProductExpansion.lean:18](../EndOfPaper/ProductExpansion.lean#L18) |
| `ScalarMonotone.EndOfPaper.product_deviation_bound` | [EndOfPaper/ProductExpansion.lean:34](../EndOfPaper/ProductExpansion.lean#L34) |
| `ScalarMonotone.EndOfPaper.productSubsetCoefficient` | [EndOfPaper/ProductExpansion.lean:39](../EndOfPaper/ProductExpansion.lean#L39) |
| `ScalarMonotone.EndOfPaper.productCoefficient` | [EndOfPaper/ProductExpansion.lean:42](../EndOfPaper/ProductExpansion.lean#L42) |
| `ScalarMonotone.EndOfPaper.productDeviation_powerset_expansion` | [EndOfPaper/ProductExpansion.lean:45](../EndOfPaper/ProductExpansion.lean#L45) |
| `ScalarMonotone.EndOfPaper.productCoefficient_nonnegative` | [EndOfPaper/ProductExpansion.lean:67](../EndOfPaper/ProductExpansion.lean#L67) |
| `ScalarMonotone.EndOfPaper.productCoefficient_top` | [EndOfPaper/ProductExpansion.lean:74](../EndOfPaper/ProductExpansion.lean#L74) |
| `ScalarMonotone.EndOfPaper.productCoefficient_top_positive` | [EndOfPaper/ProductExpansion.lean:81](../EndOfPaper/ProductExpansion.lean#L81) |
| `ScalarMonotone.EndOfPaper.productCoefficient_zero` | [EndOfPaper/ProductPolynomial.lean:14](../EndOfPaper/ProductPolynomial.lean#L14) |
| `ScalarMonotone.EndOfPaper.productCoefficient_positive` | [EndOfPaper/ProductPolynomial.lean:18](../EndOfPaper/ProductPolynomial.lean#L18) |
| `ScalarMonotone.EndOfPaper.product_polynomial_expansion` | [EndOfPaper/ProductPolynomial.lean:27](../EndOfPaper/ProductPolynomial.lean#L27) |
| `ScalarMonotone.EndOfPaper.productDeviation_zero` | [EndOfPaper/ProductPolynomial.lean:54](../EndOfPaper/ProductPolynomial.lean#L54) |
| `ScalarMonotone.EndOfPaper.productDeviation_continuous` | [EndOfPaper/ProductPolynomial.lean:57](../EndOfPaper/ProductPolynomial.lean#L57) |
| `ScalarMonotone.EndOfPaper.productDeviation_strictMonoOn` | [EndOfPaper/ProductPolynomial.lean:62](../EndOfPaper/ProductPolynomial.lean#L62) |
| `ScalarMonotone.EndOfPaper.productDeviation_linear_lower` | [EndOfPaper/ProductPolynomial.lean:74](../EndOfPaper/ProductPolynomial.lean#L74) |
| `ScalarMonotone.EndOfPaper.productDeviation_nonnegative` | [EndOfPaper/ProductPolynomial.lean:84](../EndOfPaper/ProductPolynomial.lean#L84) |
| `ScalarMonotone.EndOfPaper.productDeviation_surjOn` | [EndOfPaper/ProductPolynomial.lean:91](../EndOfPaper/ProductPolynomial.lean#L91) |
| `ScalarMonotone.EndOfPaper.productDeviation_bijOn` | [EndOfPaper/ProductPolynomial.lean:110](../EndOfPaper/ProductPolynomial.lean#L110) |
| `ScalarMonotone.EndOfPaper.product_interval_diagonal` | [EndOfPaper/ProductProfiles.lean:17](../EndOfPaper/ProductProfiles.lean#L17) |
| `ScalarMonotone.EndOfPaper.productProfile` | [EndOfPaper/ProductProfiles.lean:47](../EndOfPaper/ProductProfiles.lean#L47) |
| `ScalarMonotone.EndOfPaper.inverse_productProfile` | [EndOfPaper/ProductProfiles.lean:50](../EndOfPaper/ProductProfiles.lean#L50) |
| `ScalarMonotone.EndOfPaper.productProfile_parallel_monomials` | [EndOfPaper/ProductProfiles.lean:59](../EndOfPaper/ProductProfiles.lean#L59) |
| `ScalarMonotone.EndOfPaper.productProfile_range` | [EndOfPaper/ProductProfiles.lean:84](../EndOfPaper/ProductProfiles.lean#L84) |
| `ScalarMonotone.EndOfPaper.monomialProfile_range` | [EndOfPaper/ProductProfiles.lean:93](../EndOfPaper/ProductProfiles.lean#L93) |
| `ScalarMonotone.EndOfPaper.productMonomialGraphs` | [EndOfPaper/ProductProfiles.lean:102](../EndOfPaper/ProductProfiles.lean#L102) |
| `ScalarMonotone.EndOfPaper.productMonomialGraphs_range` | [EndOfPaper/ProductProfiles.lean:109](../EndOfPaper/ProductProfiles.lean#L109) |
| `ScalarMonotone.EndOfPaper.productProfile_maximal` | [EndOfPaper/ProductProfiles.lean:116](../EndOfPaper/ProductProfiles.lean#L116) |
| `ScalarMonotone.EndOfPaper.productProfile_weighted_envelope` | [EndOfPaper/ProductProfiles.lean:128](../EndOfPaper/ProductProfiles.lean#L128) |
| `ScalarMonotone.EndOfPaper.productProfile_root_representation` | [EndOfPaper/ProductInverse.lean:14](../EndOfPaper/ProductInverse.lean#L14) |
| `ScalarMonotone.EndOfPaper.productWeightedProfile_mem_iff` | [EndOfPaper/ProductInverse.lean:52](../EndOfPaper/ProductInverse.lean#L52) |
| `ScalarMonotone.EndOfPaper.product_common_level_tail_bound` | [EndOfPaper/ProductProbability.lean:15](../EndOfPaper/ProductProbability.lean#L15) |
| `ScalarMonotone.EndOfPaper.product_error_measurable` | [EndOfPaper/ProductProbability.lean:41](../EndOfPaper/ProductProbability.lean#L41) |
| `ScalarMonotone.EndOfPaper.survival_product_profile_bound` | [EndOfPaper/ProductProbability.lean:46](../EndOfPaper/ProductProbability.lean#L46) |
| `ScalarMonotone.EndOfPaper.multilevel_product_operator_bound` | [EndOfPaper/ProductProbability.lean:59](../EndOfPaper/ProductProbability.lean#L59) |
| `ScalarMonotone.EndOfPaper.positiveProductDegreeCount` | [EndOfPaper/ProductGaussian.lean:14](../EndOfPaper/ProductGaussian.lean#L14) |
| `ScalarMonotone.EndOfPaper.positiveProductDegreeCount_eq` | [EndOfPaper/ProductGaussian.lean:17](../EndOfPaper/ProductGaussian.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_product_tail_bound` | [EndOfPaper/ProductGaussian.lean:23](../EndOfPaper/ProductGaussian.lean#L23) |
| `ScalarMonotone.EndOfPaper.multilevel_product_gaussian_bound` | [EndOfPaper/ProductGaussian.lean:94](../EndOfPaper/ProductGaussian.lean#L94) |
| `ScalarMonotone.EndOfPaper.product_positive_polynomial_graph_sum` | [EndOfPaper/ProductRootMaps.lean:17](../EndOfPaper/ProductRootMaps.lean#L17) |
| `ScalarMonotone.EndOfPaper.inverse_nonnegative_monomial_graph` | [EndOfPaper/ProductRootMaps.lean:36](../EndOfPaper/ProductRootMaps.lean#L36) |
| `ScalarMonotone.EndOfPaper.product_inverse_parallel_root_maps` | [EndOfPaper/ProductRootMaps.lean:71](../EndOfPaper/ProductRootMaps.lean#L71) |
<a id="result-1-30"></a>

## Definition 1.30

[PDF page 28](../manuscript/monotone_calculus.pdf#page=28). Aumann integral

Arbitrary measure and measurable spaces, with nonempty interval values. The endpoint equivalence permits infinite endpoints and does not need closedness, hence applies to the paper closed intervals. The exact interval integral assumes precisely integrable real endpoints and their almost-everywhere order; no atomlessness or finite measure is imposed. The Aumann integral is exactly the set of Bochner integrals of integrable almost-everywhere selections. The literal hit-open definition is equivalent to measurability of the true EReal infimum and supremum of the fibers. Integrable endpoint intervals integrate to the closed interval between the endpoint integrals. Half-line hit events are exactly strict cuts of the extended endpoints. OrdConnected fibers turn hits of a bounded open interval into two endpoint cuts; a countable rational interval basis then handles arbitrary open sets, without assuming rational points lie in a fiber. Constant convex interpolation gives all values of the interval integral. HitOpenMeasurable is the paper open-set condition. intervalLowerExtended and intervalUpperExtended are sInf and sSup in the complete extended-real order. aumannIntegral uses L1 integrability and almost-everywhere membership, not pointwise membership or an atomless relaxation. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.aumannIntegral` | [EndOfPaper/Aumann.lean:22](../EndOfPaper/Aumann.lean#L22) |
| `ScalarMonotone.EndOfPaper.aumannIntegral_congr_ae` | [EndOfPaper/Aumann.lean:28](../EndOfPaper/Aumann.lean#L28) |
| `ScalarMonotone.EndOfPaper.aumannIntegral_interval` | [EndOfPaper/Aumann.lean:48](../EndOfPaper/Aumann.lean#L48) |
| `ScalarMonotone.EndOfPaper.aumannInterval_eq` | [EndOfPaper/Aumann.lean:53](../EndOfPaper/Aumann.lean#L53) |
| `ScalarMonotone.EndOfPaper.intervalLowerExtended` | [EndOfPaper/MeasurableIntervals.lean:16](../EndOfPaper/MeasurableIntervals.lean#L16) |
| `ScalarMonotone.EndOfPaper.intervalUpperExtended` | [EndOfPaper/MeasurableIntervals.lean:17](../EndOfPaper/MeasurableIntervals.lean#L17) |
| `ScalarMonotone.EndOfPaper.lowerExtended_lt_iff_hit_Iio` | [EndOfPaper/MeasurableIntervals.lean:19](../EndOfPaper/MeasurableIntervals.lean#L19) |
| `ScalarMonotone.EndOfPaper.lt_upperExtended_iff_hit_Ioi` | [EndOfPaper/MeasurableIntervals.lean:35](../EndOfPaper/MeasurableIntervals.lean#L35) |
| `ScalarMonotone.EndOfPaper.interval_hit_Ioo_iff` | [EndOfPaper/MeasurableIntervals.lean:51](../EndOfPaper/MeasurableIntervals.lean#L51) |
| `ScalarMonotone.EndOfPaper.HitOpenMeasurable` | [EndOfPaper/MeasurableIntervals.lean:69](../EndOfPaper/MeasurableIntervals.lean#L69) |
| `ScalarMonotone.EndOfPaper.hitOpenMeasurable_endpoints` | [EndOfPaper/MeasurableIntervals.lean:74](../EndOfPaper/MeasurableIntervals.lean#L74) |
| `ScalarMonotone.EndOfPaper.hitOpenMeasurable_of_endpoints` | [EndOfPaper/MeasurableIntervals.lean:117](../EndOfPaper/MeasurableIntervals.lean#L117) |
| `ScalarMonotone.EndOfPaper.hitOpenMeasurable_iff_endpoints` | [EndOfPaper/MeasurableIntervals.lean:155](../EndOfPaper/MeasurableIntervals.lean#L155) |
<a id="result-1-31"></a>

## Definition 1.31

[PDF page 29](../manuscript/monotone_calculus.pdf#page=29). Scalar integration

Either increasing or decreasing monotone graph, in particular the paper maximal graphs, on any measurable subset of the domain. The completed open domain interval is measurable, including intervals with infinite endpoints. No finiteness of a signed or nonnegative integral is assumed for selection independence; finite absolute area is used precisely when invoking L1 or the singleton Aumann integral. Measurable selections exist, and the two countability/ae-selection results give independence of every scalar-expression nonnegative integral and both signed parts. The explicit Option EReal integral is undefined exactly when both parts are infinite, otherwise it is their extended-real difference; integrable values equal the Bochner integral. Absolute area is finite exactly for L1 selections. Every choice of adding or deleting finite/infinite interval endpoints has identical restricted measure, including half-open choices. Reversed limits negate the defined extended value and preserve undefinedness; equal limits give zero. The integrable Aumann integral is precisely the singleton scalar area. Reuse the countable-jump and measurable-selection theorems in both orientations. Prove equality of both signed parts before forming their guarded extended difference. Derive integrability from the exact norm/lintegral criterion and selection measurability. Atomlessness makes the preimage of each actual extended endpoint null; sandwiching any endpoint convention gives equal restricted measures. Whole signed orientation and equal-endpoint identities follow without assigning a value to infinity minus infinity. signedExtendedIntegral:Option EReal uses none only for undefined signed integration. extendedOpenInterval a b is the real preimage of the true EReal open interval (a,b). orientedExtendedIntegral implements the paper sign convention. scalar_integration_well_defined bundles choice independence, absolute-integrability equivalence and the actual Aumann singleton; no convenient scalar equality is assumed. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.scalarSelection` | [EndOfPaper/ScalarIntegration.lean:99](../EndOfPaper/ScalarIntegration.lean#L99) |
| `ScalarMonotone.EndOfPaper.scalarSelection_mem` | [EndOfPaper/ScalarIntegration.lean:103](../EndOfPaper/ScalarIntegration.lean#L103) |
| `ScalarMonotone.EndOfPaper.scalarSelection_on` | [EndOfPaper/ScalarIntegration.lean:109](../EndOfPaper/ScalarIntegration.lean#L109) |
| `ScalarMonotone.EndOfPaper.exists_measurable_selection` | [EndOfPaper/ScalarIntegration.lean:126](../EndOfPaper/ScalarIntegration.lean#L126) |
| `ScalarMonotone.EndOfPaper.selection_antitoneOn` | [EndOfPaper/ScalarIntegration.lean:113](../EndOfPaper/ScalarIntegration.lean#L113) |
| `ScalarMonotone.EndOfPaper.ae_selections_ae_eq` | [EndOfPaper/ScalarIntegration.lean:153](../EndOfPaper/ScalarIntegration.lean#L153) |
| `ScalarMonotone.EndOfPaper.selection_lintegral_comp_eq` | [EndOfPaper/ScalarIntegration.lean:172](../EndOfPaper/ScalarIntegration.lean#L172) |
| `ScalarMonotone.EndOfPaper.selection_signed_parts_eq` | [EndOfPaper/ScalarIntegration.lean:185](../EndOfPaper/ScalarIntegration.lean#L185) |
| `ScalarMonotone.EndOfPaper.aumannIntegral_monotone_singleton` | [EndOfPaper/ScalarIntegration.lean:197](../EndOfPaper/ScalarIntegration.lean#L197) |
| `ScalarMonotone.EndOfPaper.countable_jumpInputs` | [EndOfPaper/Area.lean:31](../EndOfPaper/Area.lean#L31) |
| `ScalarMonotone.EndOfPaper.selections_ae_eq` | [EndOfPaper/Area.lean:66](../EndOfPaper/Area.lean#L66) |
| `ScalarMonotone.EndOfPaper.decreasing_selections_ae_eq` | [EndOfPaper/Area.lean:75](../EndOfPaper/Area.lean#L75) |
| `ScalarMonotone.EndOfPaper.selection_integral_eq` | [EndOfPaper/Area.lean:92](../EndOfPaper/Area.lean#L92) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_integral_eq` | [EndOfPaper/Area.lean:98](../EndOfPaper/Area.lean#L98) |
| `ScalarMonotone.EndOfPaper.exists_global_measurable_selection` | [EndOfPaper/ScalarIntegration.lean:141](../EndOfPaper/ScalarIntegration.lean#L141) |
| `ScalarMonotone.EndOfPaper.signedExtendedIntegral` | [EndOfPaper/ScalarIntegralConventions.lean:20](../EndOfPaper/ScalarIntegralConventions.lean#L20) |
| `ScalarMonotone.EndOfPaper.signedExtendedIntegral_eq_none_iff` | [EndOfPaper/ScalarIntegralConventions.lean:26](../EndOfPaper/ScalarIntegralConventions.lean#L26) |
| `ScalarMonotone.EndOfPaper.signedExtendedIntegral_congr_ae` | [EndOfPaper/ScalarIntegralConventions.lean:33](../EndOfPaper/ScalarIntegralConventions.lean#L33) |
| `ScalarMonotone.EndOfPaper.signedExtendedIntegral_neg` | [EndOfPaper/ScalarIntegralConventions.lean:41](../EndOfPaper/ScalarIntegralConventions.lean#L41) |
| `ScalarMonotone.EndOfPaper.signedExtendedIntegral_zero_measure` | [EndOfPaper/ScalarIntegralConventions.lean:63](../EndOfPaper/ScalarIntegralConventions.lean#L63) |
| `ScalarMonotone.EndOfPaper.signedExtendedIntegral_of_integrable` | [EndOfPaper/ScalarIntegralConventions.lean:67](../EndOfPaper/ScalarIntegralConventions.lean#L67) |
| `ScalarMonotone.EndOfPaper.selection_aemeasurable` | [EndOfPaper/ScalarIntegralConventions.lean:84](../EndOfPaper/ScalarIntegralConventions.lean#L84) |
| `ScalarMonotone.EndOfPaper.selection_integrable_iff_absolute_area_finite` | [EndOfPaper/ScalarIntegralConventions.lean:91](../EndOfPaper/ScalarIntegralConventions.lean#L91) |
| `ScalarMonotone.EndOfPaper.selection_signedExtendedIntegral_eq` | [EndOfPaper/ScalarIntegralConventions.lean:100](../EndOfPaper/ScalarIntegralConventions.lean#L100) |
| `ScalarMonotone.EndOfPaper.extendedOpenInterval` | [EndOfPaper/ScalarIntegralConventions.lean:109](../EndOfPaper/ScalarIntegralConventions.lean#L109) |
| `ScalarMonotone.EndOfPaper.extendedOpenInterval_measurable` | [EndOfPaper/ScalarIntegralConventions.lean:111](../EndOfPaper/ScalarIntegralConventions.lean#L111) |
| `ScalarMonotone.EndOfPaper.extended_endpoint_ae_ne` | [EndOfPaper/ScalarIntegralConventions.lean:114](../EndOfPaper/ScalarIntegralConventions.lean#L114) |
| `ScalarMonotone.EndOfPaper.extendedInterval_restrict_endpoints` | [EndOfPaper/ScalarIntegralConventions.lean:125](../EndOfPaper/ScalarIntegralConventions.lean#L125) |
| `ScalarMonotone.EndOfPaper.orientedExtendedIntegral` | [EndOfPaper/ScalarIntegralConventions.lean:139](../EndOfPaper/ScalarIntegralConventions.lean#L139) |
| `ScalarMonotone.EndOfPaper.orientedExtendedIntegral_self` | [EndOfPaper/ScalarIntegralConventions.lean:143](../EndOfPaper/ScalarIntegralConventions.lean#L143) |
| `ScalarMonotone.EndOfPaper.orientedExtendedIntegral_reverse` | [EndOfPaper/ScalarIntegralConventions.lean:151](../EndOfPaper/ScalarIntegralConventions.lean#L151) |
| `ScalarMonotone.EndOfPaper.orientedExtendedIntegral_selection_eq` | [EndOfPaper/ScalarIntegralConventions.lean:159](../EndOfPaper/ScalarIntegralConventions.lean#L159) |
| `ScalarMonotone.EndOfPaper.orientedExtendedIntegral_finite_of_integrable` | [EndOfPaper/ScalarIntegralConventions.lean:178](../EndOfPaper/ScalarIntegralConventions.lean#L178) |
| `ScalarMonotone.EndOfPaper.extendedInterval_restrict_between_endpoints` | [EndOfPaper/ScalarIntegralConventions.lean:188](../EndOfPaper/ScalarIntegralConventions.lean#L188) |
| `ScalarMonotone.EndOfPaper.selection_borel_expression_aemeasurable` | [EndOfPaper/ScalarIntegralConventions.lean:200](../EndOfPaper/ScalarIntegralConventions.lean#L200) |
| `ScalarMonotone.EndOfPaper.scalar_integration_well_defined` | [EndOfPaper/ScalarIntegralConventions.lean:210](../EndOfPaper/ScalarIntegralConventions.lean#L210) |
<a id="result-1-32"></a>

## Proposition 1.32

[PDF page 29](../manuscript/monotone_calculus.pdf#page=29). Inverse-area identity

Exactly maximal decreasing f, graph contained in the nonnegative quadrant, all positive inputs in its domain, and Tendsto of its actual fiber supremum to zero at infinity. PaperChecks derives Nonnegative f and the domain lower bound from the single graph-containment hypothesis. Every positive inverse level is derived to be attained. Measurable selections of f and its inverse are constructed and have equal ENNReal areas on (0,infinity), including infinity. decreasing_selection_inverse_area proves equality for arbitrary selections, so no convenient endpoint or finite-area variant replaces the paper integral. A negative-input compatible-point argument forces the range unbounded above; decay and interval range give the inverse domain. Outside countably many inverse jump levels, the strict superlevel region lies between Ioo(0,b) and Ioc(0,b), hence has length b. Layer cake/Tonelli proves the area equality. Nonnegative graph values make the scalar areas exactly lintegrals of ENNReal.ofReal of a selection. The atomless measure used for exceptional fibers is Lebesgue measure, not an extra assumption on a probability law. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.decreasing_quadrant_range_above` | [EndOfPaper/InverseArea.lean:18](../EndOfPaper/InverseArea.lean#L18) |
| `ScalarMonotone.EndOfPaper.decreasing_positive_fiber_bddAbove` | [EndOfPaper/InverseArea.lean:30](../EndOfPaper/InverseArea.lean#L30) |
| `ScalarMonotone.EndOfPaper.decreasing_inverse_positive_domain` | [EndOfPaper/InverseArea.lean:37](../EndOfPaper/InverseArea.lean#L37) |
| `ScalarMonotone.EndOfPaper.decreasing_level_region_volume` | [EndOfPaper/InverseArea.lean:54](../EndOfPaper/InverseArea.lean#L54) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_inverse_area` | [EndOfPaper/InverseArea.lean:84](../EndOfPaper/InverseArea.lean#L84) |
| `ScalarMonotone.EndOfPaper.inverse_area_identity` | [EndOfPaper/InverseArea.lean:108](../EndOfPaper/InverseArea.lean#L108) |
<a id="result-1-33"></a>

## Corollary 1.33

[PDF page 30](../manuscript/monotone_calculus.pdf#page=30). Moments

A measurable nonnegative random variable on an arbitrary original probability space and every real exponent r>0. Nonnegativity may hold only almost everywhere. The distribution may have atoms. Survival and quantile selections are arbitrary; their required measurability is derived, not an additional final hypothesis. The extended r-th moment equals r times the positive-half-line weighted survival integral and the (0,1) quantile-power integral. All integrals are ENNReal and may be infinite. The equality is independent of either selection. Layer cake gives the survival expression; Lebesgue ae uniqueness replaces the strict tail by every completed survival selection. The already proved quantile pushforward law transfers every nonnegative measurable expression on the original probability space. Antitonicity proves measurability of every quantile selection on (0,1). ENNReal.ofReal represents nonnegative scalar values. unitUniform is Lebesgue measure restricted to (0,1), so no global measurability outside that interval is needed. The following display eq:moment is proved and tracked separately in the supplemental inventory; it is outside this numbered corollary. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.moment_tail_area` | [EndOfPaper/Moments.lean:30](../EndOfPaper/Moments.lean#L30) |
| `ScalarMonotone.EndOfPaper.quantile_selection_lintegral_comp` | [EndOfPaper/QuantileMoments.lean:19](../EndOfPaper/QuantileMoments.lean#L19) |
| `ScalarMonotone.EndOfPaper.randomVariable_quantile_lintegral_comp` | [EndOfPaper/QuantileMoments.lean:30](../EndOfPaper/QuantileMoments.lean#L30) |
| `ScalarMonotone.EndOfPaper.moment_tail_area_factored` | [EndOfPaper/QuantileMoments.lean:42](../EndOfPaper/QuantileMoments.lean#L42) |
| `ScalarMonotone.EndOfPaper.strict_tail_survival_selection` | [EndOfPaper/QuantileMoments.lean:57](../EndOfPaper/QuantileMoments.lean#L57) |
| `ScalarMonotone.EndOfPaper.moment_tail_selection_identity` | [EndOfPaper/QuantileMoments.lean:69](../EndOfPaper/QuantileMoments.lean#L69) |
| `ScalarMonotone.EndOfPaper.moment_tail_quantile_identity` | [EndOfPaper/QuantileMoments.lean:89](../EndOfPaper/QuantileMoments.lean#L89) |
| `ScalarMonotone.EndOfPaper.moment_identities_of_selections` | [EndOfPaper/QuantileMoments.lean:106](../EndOfPaper/QuantileMoments.lean#L106) |
<a id="result-1-34"></a>

## Corollary 1.34

[PDF page 30](../manuscript/monotone_calculus.pdf#page=30). Change of pivot to the mean

The actual maximal decreasing nonnegative envelope on all positive inputs dominates the completed survival of |X-c|. Its nonnegative extended selection area is finite. X is measurable on the original probability space; integrability of X is not assumed. The chosen envelope selection and X are integrable, |E X-c| is at most its real area M, and the survival of |X-E X| is below the whole translated operator t↦beta(t-M). The translated graph is proved maximal decreasing, including its boundary fibers. The extended tail-area inequality first proves finite absolute expectation and hence L1. Only then are the Bochner mean and real area used. The pointwise triangle inequality gives the translated strict-tail comparison at every input, and the existing survival comparison equivalence yields DecLE. The premise hfinite is the finite ENNReal area specified by Definition def:area, not the automatically finite value of a totalized real Bochner integral. Integrability and nonnegativity are proved before identifying M with that real integral. A selection exists from the paper domain assumption by ScalarIntegration. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.expectation_tail_area` | [EndOfPaper/Area.lean:198](../EndOfPaper/Area.lean#L198) |
| `ScalarMonotone.EndOfPaper.expectation_le_tail_area` | [EndOfPaper/Area.lean:206](../EndOfPaper/Area.lean#L206) |
| `ScalarMonotone.EndOfPaper.mean_pivot_distance` | [EndOfPaper/Shortfall.lean:208](../EndOfPaper/Shortfall.lean#L208) |
| `ScalarMonotone.EndOfPaper.pointwise_mean_pivot` | [EndOfPaper/Shortfall.lean:218](../EndOfPaper/Shortfall.lean#L218) |
| `ScalarMonotone.EndOfPaper.maximal_decreasing_input_translate` | [EndOfPaper/MeanPivot.lean:16](../EndOfPaper/MeanPivot.lean#L16) |
| `ScalarMonotone.EndOfPaper.finite_operator_tail_area_mean_pivot` | [EndOfPaper/MeanPivot.lean:41](../EndOfPaper/MeanPivot.lean#L41) |
<a id="result-1-35"></a>

## Definition 1.35

[PDF page 31](../manuscript/monotone_calculus.pdf#page=31). Integration of a family

The complete family-integral proof is supplied in both orientations: finite interior endpoints, local domination, one-sided dominated convergence, exact Aumann fibers after completion, maximality, uniqueness, domain interior, whole-graph resolvent order, additivity and positive scaling. The results allow arbitrary parameter measures whenever the endpoint maps are integrable, so they include the paper finite positive measure case without atomlessness. PaperChecks discharges open-interval geometry from the common-domain-interior hypothesis. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.maximal_interior_fiber_bounded` | [EndOfPaper/FamilyIntegral.lean:18](../EndOfPaper/FamilyIntegral.lean#L18) |
| `ScalarMonotone.EndOfPaper.maximal_interior_fiber_endpoints_mem` | [EndOfPaper/FamilyIntegral.lean:29](../EndOfPaper/FamilyIntegral.lean#L29) |
| `ScalarMonotone.EndOfPaper.maximal_interior_fiber_eq_Icc` | [EndOfPaper/FamilyIntegral.lean:37](../EndOfPaper/FamilyIntegral.lean#L37) |
| `ScalarMonotone.EndOfPaper.selection_tendsto_left` | [EndOfPaper/FamilyIntegral.lean:46](../EndOfPaper/FamilyIntegral.lean#L46) |
| `ScalarMonotone.EndOfPaper.selection_tendsto_right` | [EndOfPaper/FamilyIntegral.lean:77](../EndOfPaper/FamilyIntegral.lean#L77) |
| `ScalarMonotone.EndOfPaper.interior_fiber_abs_bound` | [EndOfPaper/FamilyIntegral.lean:108](../EndOfPaper/FamilyIntegral.lean#L108) |
| `ScalarMonotone.EndOfPaper.family_integral_endpoint_limits` | [EndOfPaper/FamilyIntegral.lean:121](../EndOfPaper/FamilyIntegral.lean#L121) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral` | [EndOfPaper/FamilyIntegral.lean:171](../EndOfPaper/FamilyIntegral.lean#L171) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_value` | [EndOfPaper/FamilyIntegral.lean:178](../EndOfPaper/FamilyIntegral.lean#L178) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_aumann` | [EndOfPaper/FamilyIntegral.lean:228](../EndOfPaper/FamilyIntegral.lean#L228) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_unique` | [EndOfPaper/FamilyIntegral.lean:248](../EndOfPaper/FamilyIntegral.lean#L248) |
| `ScalarMonotone.EndOfPaper.decreasing_interior_neg_endpoints` | [EndOfPaper/FamilyIntegral.lean:290](../EndOfPaper/FamilyIntegral.lean#L290) |
| `ScalarMonotone.EndOfPaper.aumannIntegral_neg` | [EndOfPaper/FamilyIntegral.lean:313](../EndOfPaper/FamilyIntegral.lean#L313) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral` | [EndOfPaper/FamilyIntegral.lean:329](../EndOfPaper/FamilyIntegral.lean#L329) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_value` | [EndOfPaper/FamilyIntegral.lean:333](../EndOfPaper/FamilyIntegral.lean#L333) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_aumann` | [EndOfPaper/FamilyIntegral.lean:355](../EndOfPaper/FamilyIntegral.lean#L355) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_unique` | [EndOfPaper/FamilyIntegral.lean:377](../EndOfPaper/FamilyIntegral.lean#L377) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_endpoints_mem` | [EndOfPaper/FamilyIntegral.lean:410](../EndOfPaper/FamilyIntegral.lean#L410) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_mono` | [EndOfPaper/FamilyIntegral.lean:429](../EndOfPaper/FamilyIntegral.lean#L429) |
| `ScalarMonotone.EndOfPaper.domain_interior_of_open_interval` | [EndOfPaper/FamilyIntegral.lean:462](../EndOfPaper/FamilyIntegral.lean#L462) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_domain_interior` | [EndOfPaper/FamilyIntegral.lean:472](../EndOfPaper/FamilyIntegral.lean#L472) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_mono` | [EndOfPaper/FamilyIntegral.lean:483](../EndOfPaper/FamilyIntegral.lean#L483) |
| `ScalarMonotone.EndOfPaper.interior_endpoints_add` | [EndOfPaper/FamilyIntegral.lean:513](../EndOfPaper/FamilyIntegral.lean#L513) |
| `ScalarMonotone.EndOfPaper.setAdd_Icc_real` | [EndOfPaper/FamilyIntegral.lean:532](../EndOfPaper/FamilyIntegral.lean#L532) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_add` | [EndOfPaper/FamilyIntegral.lean:548](../EndOfPaper/FamilyIntegral.lean#L548) |
| `ScalarMonotone.EndOfPaper.interior_endpoints_outputScale` | [EndOfPaper/FamilyIntegral.lean:596](../EndOfPaper/FamilyIntegral.lean#L596) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_outputScale` | [EndOfPaper/FamilyIntegral.lean:612](../EndOfPaper/FamilyIntegral.lean#L612) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_add` | [EndOfPaper/FamilyIntegral.lean:643](../EndOfPaper/FamilyIntegral.lean#L643) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_outputScale` | [EndOfPaper/FamilyIntegral.lean:675](../EndOfPaper/FamilyIntegral.lean#L675) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_domain_interior` | [EndOfPaper/FamilyIntegral.lean:698](../EndOfPaper/FamilyIntegral.lean#L698) |
<a id="result-1-36"></a>

## Proposition 1.36

[PDF page 31](../manuscript/monotone_calculus.pdf#page=31). Aumann integration of a monotone family

The complete family-integral proof is supplied in both orientations: finite interior endpoints, local domination, one-sided dominated convergence, exact Aumann fibers after completion, maximality, uniqueness, domain interior, whole-graph resolvent order, additivity and positive scaling. The results allow arbitrary parameter measures whenever the endpoint maps are integrable, so they include the paper finite positive measure case without atomlessness. PaperChecks discharges open-interval geometry from the common-domain-interior hypothesis. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.maximal_interior_fiber_bounded` | [EndOfPaper/FamilyIntegral.lean:18](../EndOfPaper/FamilyIntegral.lean#L18) |
| `ScalarMonotone.EndOfPaper.maximal_interior_fiber_endpoints_mem` | [EndOfPaper/FamilyIntegral.lean:29](../EndOfPaper/FamilyIntegral.lean#L29) |
| `ScalarMonotone.EndOfPaper.maximal_interior_fiber_eq_Icc` | [EndOfPaper/FamilyIntegral.lean:37](../EndOfPaper/FamilyIntegral.lean#L37) |
| `ScalarMonotone.EndOfPaper.selection_tendsto_left` | [EndOfPaper/FamilyIntegral.lean:46](../EndOfPaper/FamilyIntegral.lean#L46) |
| `ScalarMonotone.EndOfPaper.selection_tendsto_right` | [EndOfPaper/FamilyIntegral.lean:77](../EndOfPaper/FamilyIntegral.lean#L77) |
| `ScalarMonotone.EndOfPaper.interior_fiber_abs_bound` | [EndOfPaper/FamilyIntegral.lean:108](../EndOfPaper/FamilyIntegral.lean#L108) |
| `ScalarMonotone.EndOfPaper.family_integral_endpoint_limits` | [EndOfPaper/FamilyIntegral.lean:121](../EndOfPaper/FamilyIntegral.lean#L121) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral` | [EndOfPaper/FamilyIntegral.lean:171](../EndOfPaper/FamilyIntegral.lean#L171) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_value` | [EndOfPaper/FamilyIntegral.lean:178](../EndOfPaper/FamilyIntegral.lean#L178) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_aumann` | [EndOfPaper/FamilyIntegral.lean:228](../EndOfPaper/FamilyIntegral.lean#L228) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_unique` | [EndOfPaper/FamilyIntegral.lean:248](../EndOfPaper/FamilyIntegral.lean#L248) |
| `ScalarMonotone.EndOfPaper.decreasing_interior_neg_endpoints` | [EndOfPaper/FamilyIntegral.lean:290](../EndOfPaper/FamilyIntegral.lean#L290) |
| `ScalarMonotone.EndOfPaper.aumannIntegral_neg` | [EndOfPaper/FamilyIntegral.lean:313](../EndOfPaper/FamilyIntegral.lean#L313) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral` | [EndOfPaper/FamilyIntegral.lean:329](../EndOfPaper/FamilyIntegral.lean#L329) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_value` | [EndOfPaper/FamilyIntegral.lean:333](../EndOfPaper/FamilyIntegral.lean#L333) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_aumann` | [EndOfPaper/FamilyIntegral.lean:355](../EndOfPaper/FamilyIntegral.lean#L355) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_unique` | [EndOfPaper/FamilyIntegral.lean:377](../EndOfPaper/FamilyIntegral.lean#L377) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_endpoints_mem` | [EndOfPaper/FamilyIntegral.lean:410](../EndOfPaper/FamilyIntegral.lean#L410) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_mono` | [EndOfPaper/FamilyIntegral.lean:429](../EndOfPaper/FamilyIntegral.lean#L429) |
| `ScalarMonotone.EndOfPaper.domain_interior_of_open_interval` | [EndOfPaper/FamilyIntegral.lean:462](../EndOfPaper/FamilyIntegral.lean#L462) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_domain_interior` | [EndOfPaper/FamilyIntegral.lean:472](../EndOfPaper/FamilyIntegral.lean#L472) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_mono` | [EndOfPaper/FamilyIntegral.lean:483](../EndOfPaper/FamilyIntegral.lean#L483) |
| `ScalarMonotone.EndOfPaper.interior_endpoints_add` | [EndOfPaper/FamilyIntegral.lean:513](../EndOfPaper/FamilyIntegral.lean#L513) |
| `ScalarMonotone.EndOfPaper.setAdd_Icc_real` | [EndOfPaper/FamilyIntegral.lean:532](../EndOfPaper/FamilyIntegral.lean#L532) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_add` | [EndOfPaper/FamilyIntegral.lean:548](../EndOfPaper/FamilyIntegral.lean#L548) |
| `ScalarMonotone.EndOfPaper.interior_endpoints_outputScale` | [EndOfPaper/FamilyIntegral.lean:596](../EndOfPaper/FamilyIntegral.lean#L596) |
| `ScalarMonotone.EndOfPaper.increasingFamilyIntegral_outputScale` | [EndOfPaper/FamilyIntegral.lean:612](../EndOfPaper/FamilyIntegral.lean#L612) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_add` | [EndOfPaper/FamilyIntegral.lean:643](../EndOfPaper/FamilyIntegral.lean#L643) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_outputScale` | [EndOfPaper/FamilyIntegral.lean:675](../EndOfPaper/FamilyIntegral.lean#L675) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_domain_interior` | [EndOfPaper/FamilyIntegral.lean:698](../EndOfPaper/FamilyIntegral.lean#L698) |
<a id="result-2-1"></a>

## Definition 2.1

[PDF page 32](../manuscript/monotone_calculus.pdf#page=32). Hardy transform

The paper maximal decreasing graph, integrability of a scalar selection, and zero lower domain endpoint with a positive domain point. IsGLB(dom f,0) expresses the actual greatest lower bound; existence of a positive domain point expresses positivity of the possibly infinite supremum. No finite upper endpoint, common-domain geometry or integrability of endpoint maps is assumed. The actual completed Aumann integral of restricted positive dilations is well defined and maximal decreasing. Its domain interior equals the original interior, its domain lies in that closure, and every interior fiber is the singleton (integral from 0 to p of s)/p. The full completed graph is unique, including every boundary fiber. It is independent of the integrable selection because the operator definition contains only I and f. Derive a nonempty positive initial interval from the domain greatest lower bound and maximality. Prove positive dilations and their completed restrictions maximal with the exact common interior. Affine substitution and ae selection equality prove both endpoint maps integrable and give the same scalar area. The full FamilyIntegral theorems then preserve those singleton fibers and prove whole-graph uniqueness. hardyFamilyIntegral is defined by decreasingFamilyIntegral of the actual completed dilations, not by the desired scalar formula. hardyFamilyIntegral_eq_actual_dilations proves equality of the entire completed integral with the literal r-dilation family. The harmless parameter extension outside (0,1) is eliminated by a proved ae family-congruence theorem. Integrability on the domain implies integrability on its interior. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.positiveInputDilation` | [EndOfPaper/HardyIntegral.lean:18](../EndOfPaper/HardyIntegral.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveInputDilation_maximal` | [EndOfPaper/HardyIntegral.lean:20](../EndOfPaper/HardyIntegral.lean#L20) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction` | [EndOfPaper/HardyIntegral.lean:47](../EndOfPaper/HardyIntegral.lean#L47) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_value` | [EndOfPaper/HardyIntegral.lean:50](../EndOfPaper/HardyIntegral.lean#L50) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_maximal` | [EndOfPaper/HardyIntegral.lean:61](../EndOfPaper/HardyIntegral.lean#L61) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_domain` | [EndOfPaper/HardyIntegral.lean:70](../EndOfPaper/HardyIntegral.lean#L70) |
| `ScalarMonotone.EndOfPaper.hardyParameter` | [EndOfPaper/HardyIntegral.lean:87](../EndOfPaper/HardyIntegral.lean#L87) |
| `ScalarMonotone.EndOfPaper.hardyParameter_bounds` | [EndOfPaper/HardyIntegral.lean:89](../EndOfPaper/HardyIntegral.lean#L89) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily` | [EndOfPaper/HardyIntegral.lean:95](../EndOfPaper/HardyIntegral.lean#L95) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily_properties` | [EndOfPaper/HardyIntegral.lean:98](../EndOfPaper/HardyIntegral.lean#L98) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral` | [EndOfPaper/HardyIntegral.lean:116](../EndOfPaper/HardyIntegral.lean#L116) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_congr_ae` | [EndOfPaper/HardyIntegral.lean:121](../EndOfPaper/HardyIntegral.lean#L121) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_eq_actual_dilations` | [EndOfPaper/HardyIntegral.lean:135](../EndOfPaper/HardyIntegral.lean#L135) |
| `ScalarMonotone.EndOfPaper.decreasing_zero_inf_domain_geometry` | [EndOfPaper/HardyIntegral.lean:144](../EndOfPaper/HardyIntegral.lean#L144) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily_endpoint_areas` | [EndOfPaper/HardyIntegral.lean:179](../EndOfPaper/HardyIntegral.lean#L179) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_well_defined` | [EndOfPaper/HardyIntegral.lean:205](../EndOfPaper/HardyIntegral.lean#L205) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_of_integrable` | [EndOfPaper/HardyIntegral.lean:248](../EndOfPaper/HardyIntegral.lean#L248) |
<a id="result-2-2"></a>

## Proposition 2.2

[PDF page 33](../manuscript/monotone_calculus.pdf#page=33). Order and algebraic properties of the Hardy transform

The original maximal decreasing integrable graphs with zero lower domain endpoints and positive upper domain endpoints. A common domain interior is required only for addition. Positive scaling is for every real c>0. Both finite and infinite upper endpoints are permitted. The combined manuscript-facing theorem proves f<=H(f), order preservation for possibly different initial intervals, addition on the common interior, and positive-scaling identities. Both algebraic identities are equalities of entire completed graphs. Derive interior domain inclusion from the original DecLE and domain hull order. Integrate separated scalar selections, then use interval closure geometry and graph monotonicity to compare every boundary fiber. For addition/scaling, prove the candidate completed graph maximal, with the correct closure/domain and scalar fibers, and apply whole-operator uniqueness. DecLE is the paper resolvent order, not raw graph inclusion. IsGLB(dom f,0) and a positive domain point state the actual lower endpoint and positive possibly infinite upper endpoint. All local integrability used in the proof is derived from the paper integrability assumptions. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.decreasing_dom_subset_closure_interior` | [EndOfPaper/HardyCalculus.lean:17](../EndOfPaper/HardyCalculus.lean#L17) |
| `ScalarMonotone.EndOfPaper.zero_mem_closure_decreasing_domain_interior` | [EndOfPaper/HardyCalculus.lean:24](../EndOfPaper/HardyCalculus.lean#L24) |
| `ScalarMonotone.EndOfPaper.Ioo_between_closure_subset_open_interval` | [EndOfPaper/HardyCalculus.lean:31](../EndOfPaper/HardyCalculus.lean#L31) |
| `ScalarMonotone.EndOfPaper.decLE_of_initial_interior` | [EndOfPaper/HardyCalculus.lean:46](../EndOfPaper/HardyCalculus.lean#L46) |
| `ScalarMonotone.EndOfPaper.decreasing_initial_domain_inclusion` | [EndOfPaper/HardyCalculus.lean:66](../EndOfPaper/HardyCalculus.lean#L66) |
| `ScalarMonotone.EndOfPaper.hardyScalar_le_of_decLE` | [EndOfPaper/HardyCalculus.lean:85](../EndOfPaper/HardyCalculus.lean#L85) |
| `ScalarMonotone.EndOfPaper.graph_value_le_hardyScalar` | [EndOfPaper/HardyCalculus.lean:99](../EndOfPaper/HardyCalculus.lean#L99) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_mono` | [EndOfPaper/HardyCalculus.lean:114](../EndOfPaper/HardyCalculus.lean#L114) |
| `ScalarMonotone.EndOfPaper.le_hardyFamilyIntegral` | [EndOfPaper/HardyCalculus.lean:158](../EndOfPaper/HardyCalculus.lean#L158) |
| `ScalarMonotone.EndOfPaper.add_fiber_singleton` | [EndOfPaper/HardyCalculus.lean:185](../EndOfPaper/HardyCalculus.lean#L185) |
| `ScalarMonotone.EndOfPaper.outputScale_fiber_singleton` | [EndOfPaper/HardyCalculus.lean:190](../EndOfPaper/HardyCalculus.lean#L190) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_add` | [EndOfPaper/HardyCalculus.lean:198](../EndOfPaper/HardyCalculus.lean#L198) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_outputScale` | [EndOfPaper/HardyCalculus.lean:262](../EndOfPaper/HardyCalculus.lean#L262) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_calculus` | [EndOfPaper/HardyCalculus.lean:294](../EndOfPaper/HardyCalculus.lean#L294) |
<a id="result-2-3"></a>

## Lemma 2.3

[PDF page 33](../manuscript/monotone_calculus.pdf#page=33). Convexity and concavity of the Hardy transform

The same integrable maximal decreasing graph and domain hypotheses, and existence of a convex or concave selection on its actual domain interior, exactly as in the manuscript definition. The actual completed Hardy operator admits the corresponding convex or concave selection on its own domain interior. Both orientations of shape are supplied, with no finite upper-domain assumption. Selection ae uniqueness derives integrability of the convex/concave selection from the paper integrability hypothesis. Dilation and integration preserve its defining convexity/concavity inequality on the derived initial interval. The exact singleton Hardy fibers and exact domain identity make the scalar Hardy average a selection of the whole constructed operator. Convexity/concavity is expressed by existence of a scalar selection on interior(dom H); it is not replaced by a scalar-only assertion on an assumed averaging interval. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.decreasing_selections_ae_eq` | [EndOfPaper/Area.lean:75](../EndOfPaper/Area.lean#L75) |
| `ScalarMonotone.EndOfPaper.hardyScalar_convexOn_initial` | [EndOfPaper/HardyIntegral.lean:268](../EndOfPaper/HardyIntegral.lean#L268) |
| `ScalarMonotone.EndOfPaper.hardyScalar_concaveOn_initial` | [EndOfPaper/HardyIntegral.lean:297](../EndOfPaper/HardyIntegral.lean#L297) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_preserves_convexity` | [EndOfPaper/HardyIntegral.lean:309](../EndOfPaper/HardyIntegral.lean#L309) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_preserves_concavity` | [EndOfPaper/HardyIntegral.lean:334](../EndOfPaper/HardyIntegral.lean#L334) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_of_integrable` | [EndOfPaper/HardyIntegral.lean:248](../EndOfPaper/HardyIntegral.lean#L248) |
<a id="result-2-4"></a>

## Lemma 2.4

[PDF page 34](../manuscript/monotone_calculus.pdf#page=34). Variational formulas for the Hardy transform

Every measurable integrable real random variable on its arbitrary original probability space and every 0<p<1. No atomlessness, randomizer, integrable quantile selection or scalar Hardy identity is added as a hypothesis. The actual completed Hardy quantile integral has the attained primal minimum and attained original-space dual maximum, including the literal unnormalized product supremum divided by p. The whole argmin is the completed quantile interval. The separately inventoried proof assertions now also have full convexity, strict/weak one-sided derivative, ordinary subdifferential and zero/quantile theorems. The completed Hardy constructor, measurable quantile selection and law transfer identify the actual scalar value with the original-space threshold objective. Atom-aware fractional feasible weights attain equality and the converse minimizer theorem identifies the full argmin. The new difference-quotient dominated-convergence proof and global supporting-line theorem additionally verify the derivative/subdifferential route written in the manuscript. All boundary/choice and normalization bridges remain included in the existing mapping. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.shortfall_weak_duality` | [EndOfPaper/Shortfall.lean:60](../EndOfPaper/Shortfall.lean#L60) |
| `ScalarMonotone.EndOfPaper.exists_atom_fraction` | [EndOfPaper/Shortfall.lean:86](../EndOfPaper/Shortfall.lean#L86) |
| `ScalarMonotone.EndOfPaper.shortfall_attainment` | [EndOfPaper/Shortfall.lean:169](../EndOfPaper/Shortfall.lean#L169) |
| `ScalarMonotone.EndOfPaper.quantile_excess_area` | [EndOfPaper/QuantileArea.lean:89](../EndOfPaper/QuantileArea.lean#L89) |
| `ScalarMonotone.EndOfPaper.hardyScalar_quantile_variational` | [EndOfPaper/QuantileArea.lean:128](../EndOfPaper/QuantileArea.lean#L128) |
| `ScalarMonotone.EndOfPaper.hardyScalar_quantile_eq_dualShortfall` | [EndOfPaper/QuantileArea.lean:149](../EndOfPaper/QuantileArea.lean#L149) |
| `ScalarMonotone.EndOfPaper.tailQuantile_map_mem_iff` | [EndOfPaper/ShortfallMinimizers.lean:19](../EndOfPaper/ShortfallMinimizers.lean#L19) |
| `ScalarMonotone.EndOfPaper.shortfall_equality_brackets` | [EndOfPaper/ShortfallMinimizers.lean:30](../EndOfPaper/ShortfallMinimizers.lean#L30) |
| `ScalarMonotone.EndOfPaper.shortfall_minimizer_iff_quantile` | [EndOfPaper/ShortfallMinimizers.lean:90](../EndOfPaper/ShortfallMinimizers.lean#L90) |
| `ScalarMonotone.EndOfPaper.shortfall_minimizers_eq_tailQuantile` | [EndOfPaper/ShortfallMinimizers.lean:110](../EndOfPaper/ShortfallMinimizers.lean#L110) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_well_defined` | [EndOfPaper/HardyIntegral.lean:205](../EndOfPaper/HardyIntegral.lean#L205) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_of_integrable` | [EndOfPaper/HardyIntegral.lean:248](../EndOfPaper/HardyIntegral.lean#L248) |
| `ScalarMonotone.EndOfPaper.tailQuantile_domain_interior` | [EndOfPaper/HardyVariational.lean:17](../EndOfPaper/HardyVariational.lean#L17) |
| `ScalarMonotone.EndOfPaper.hardy_tailQuantile_fiber` | [EndOfPaper/HardyVariational.lean:27](../EndOfPaper/HardyVariational.lean#L27) |
| `ScalarMonotone.EndOfPaper.shortfallObjective_map` | [EndOfPaper/HardyVariational.lean:46](../EndOfPaper/HardyVariational.lean#L46) |
| `ScalarMonotone.EndOfPaper.hardyScalar_quantile_original_variational` | [EndOfPaper/HardyVariational.lean:57](../EndOfPaper/HardyVariational.lean#L57) |
| `ScalarMonotone.EndOfPaper.weightedProductCandidates` | [EndOfPaper/HardyVariational.lean:75](../EndOfPaper/HardyVariational.lean#L75) |
| `ScalarMonotone.EndOfPaper.dualCandidates_greatest_unnormalized` | [EndOfPaper/HardyVariational.lean:80](../EndOfPaper/HardyVariational.lean#L80) |
| `ScalarMonotone.EndOfPaper.hardy_quantile_original_variational` | [EndOfPaper/HardyVariational.lean:95](../EndOfPaper/HardyVariational.lean#L95) |
| `ScalarMonotone.EndOfPaper.excessSlope` | [EndOfPaper/ShortfallDerivatives.lean:19](../EndOfPaper/ShortfallDerivatives.lean#L19) |
| `ScalarMonotone.EndOfPaper.excessSlope_abs_le_one` | [EndOfPaper/ShortfallDerivatives.lean:21](../EndOfPaper/ShortfallDerivatives.lean#L21) |
| `ScalarMonotone.EndOfPaper.excessSlope_tendsto_right` | [EndOfPaper/ShortfallDerivatives.lean:29](../EndOfPaper/ShortfallDerivatives.lean#L29) |
| `ScalarMonotone.EndOfPaper.excessSlope_tendsto_left` | [EndOfPaper/ShortfallDerivatives.lean:48](../EndOfPaper/ShortfallDerivatives.lean#L48) |
| `ScalarMonotone.EndOfPaper.excessSlope_integral_right` | [EndOfPaper/ShortfallDerivatives.lean:69](../EndOfPaper/ShortfallDerivatives.lean#L69) |
| `ScalarMonotone.EndOfPaper.excessSlope_integral_left` | [EndOfPaper/ShortfallDerivatives.lean:92](../EndOfPaper/ShortfallDerivatives.lean#L92) |
| `ScalarMonotone.EndOfPaper.shortfall_slope_eq` | [EndOfPaper/ShortfallDerivatives.lean:115](../EndOfPaper/ShortfallDerivatives.lean#L115) |
| `ScalarMonotone.EndOfPaper.shortfall_one_sided_derivatives` | [EndOfPaper/ShortfallDerivatives.lean:130](../EndOfPaper/ShortfallDerivatives.lean#L130) |
| `ScalarMonotone.EndOfPaper.realSubgradient` | [EndOfPaper/ShortfallDerivatives.lean:152](../EndOfPaper/ShortfallDerivatives.lean#L152) |
| `ScalarMonotone.EndOfPaper.shortfallObjective_convex` | [EndOfPaper/ShortfallDerivatives.lean:157](../EndOfPaper/ShortfallDerivatives.lean#L157) |
| `ScalarMonotone.EndOfPaper.realSubgradient_eq_Icc` | [EndOfPaper/ShortfallDerivatives.lean:190](../EndOfPaper/ShortfallDerivatives.lean#L190) |
| `ScalarMonotone.EndOfPaper.shortfall_subgradient_interval` | [EndOfPaper/ShortfallDerivatives.lean:221](../EndOfPaper/ShortfallDerivatives.lean#L221) |
| `ScalarMonotone.EndOfPaper.shortfall_subgradient_survival` | [EndOfPaper/ShortfallDerivatives.lean:229](../EndOfPaper/ShortfallDerivatives.lean#L229) |
| `ScalarMonotone.EndOfPaper.shortfall_zero_subgradient_iff_quantile` | [EndOfPaper/ShortfallDerivatives.lean:259](../EndOfPaper/ShortfallDerivatives.lean#L259) |
<a id="result-2-5"></a>

## Example 2.5

[PDF page 36](../manuscript/monotone_calculus.pdf#page=36). The sharp transform of an ℓq norm is ℓ1, giving the sharp Hardy tail bound for n ≥ 1.

Actual PiLp norms for every exponent 1<=q<=infinity, any finite dimension, arbitrary original probability spaces, measurable coordinate tuples with integrable marginals and almost-sure nonnegativity. Both exact sharp suprema retain every measurable original space in an arbitrary universe and finite-valued comonotone competitors. No atomless assumption is imposed. The author confirmed n>=1 for the norm example on 2026-11-06; the ordinary finite-sum operator theorem has exactly this dimension range. All five conclusions are supplied: the actual ell-p sharp transform for 1<=q<=infinity, the whole Hardy comparison with the ordinary finite Minkowski graph sum for every n>=1, both exact suprema over arbitrary probability spaces and over finite-valued comonotone tuples, the quasi-norm superadditivity/fixed-point formula for every 0<q<=1, and the Euclidean ones values sqrt(n) and n. Almost-sure nonnegativity is allowed. Full endpoint fibers are retained. Zero dimension is additionally treated for scalar formulas/suprema and for the completed common-interval sum, without identifying it with the raw empty graph sum. Measurable positive-part clipping preserves laws and derives nonnegative marginal Hardy values through original-space feasible weights. Norm continuity and the exact coordinate-axis sharp transform give scalar comparison. Initial-domain separated comparison extends interior inequalities to all completed endpoint fibers. Finite Minkowski sums are maximal and have the exact singleton sums; whole-graph uniqueness identifies the aggregation constructor, with the empty family completion kept explicit. The general geometric-band sharpness theorem gives both exact norm suprema. The scalar/quasi-norm formulas and both suprema include n=0; the ordinary-sum operator comparison is explicitly nonempty. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.superadditiveTransform_eq_mass_of_axes` | [EndOfPaper/Superadditive.lean:368](../EndOfPaper/Superadditive.lean#L368) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_eq_self` | [EndOfPaper/Superadditive.lean:302](../EndOfPaper/Superadditive.lean#L302) |
| `ScalarMonotone.EndOfPaper.aggregation_finset_subadditive_bound` | [EndOfPaper/NormTransform.lean:15](../EndOfPaper/NormTransform.lean#L15) |
| `ScalarMonotone.EndOfPaper.coordinateLpNorm` | [EndOfPaper/NormTransform.lean:30](../EndOfPaper/NormTransform.lean#L30) |
| `ScalarMonotone.EndOfPaper.coordinateLpNorm_mono` | [EndOfPaper/NormTransform.lean:33](../EndOfPaper/NormTransform.lean#L33) |
| `ScalarMonotone.EndOfPaper.coordinateLpNorm_aggregation_axioms` | [EndOfPaper/NormTransform.lean:57](../EndOfPaper/NormTransform.lean#L57) |
| `ScalarMonotone.EndOfPaper.coordinateLpNorm_axis` | [EndOfPaper/NormTransform.lean:64](../EndOfPaper/NormTransform.lean#L64) |
| `ScalarMonotone.EndOfPaper.coordinateLpNorm_le_mass` | [EndOfPaper/NormTransform.lean:73](../EndOfPaper/NormTransform.lean#L73) |
| `ScalarMonotone.EndOfPaper.ellp_superadditive_transform` | [EndOfPaper/NormTransform.lean:92](../EndOfPaper/NormTransform.lean#L92) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm` | [EndOfPaper/QuasiNormTransform.lean:16](../EndOfPaper/QuasiNormTransform.lean#L16) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_nonneg` | [EndOfPaper/QuasiNormTransform.lean:19](../EndOfPaper/QuasiNormTransform.lean#L19) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_rpow` | [EndOfPaper/QuasiNormTransform.lean:23](../EndOfPaper/QuasiNormTransform.lean#L23) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_zero` | [EndOfPaper/QuasiNormTransform.lean:29](../EndOfPaper/QuasiNormTransform.lean#L29) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_eq_zero` | [EndOfPaper/QuasiNormTransform.lean:34](../EndOfPaper/QuasiNormTransform.lean#L34) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_smul` | [EndOfPaper/QuasiNormTransform.lean:44](../EndOfPaper/QuasiNormTransform.lean#L44) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_aggregation_axioms` | [EndOfPaper/QuasiNormTransform.lean:53](../EndOfPaper/QuasiNormTransform.lean#L53) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_normalized_power_sum` | [EndOfPaper/QuasiNormTransform.lean:62](../EndOfPaper/QuasiNormTransform.lean#L62) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_superadditive` | [EndOfPaper/QuasiNormTransform.lean:69](../EndOfPaper/QuasiNormTransform.lean#L69) |
| `ScalarMonotone.EndOfPaper.quasi_norm_superadditive_transform` | [EndOfPaper/QuasiNormTransform.lean:114](../EndOfPaper/QuasiNormTransform.lean#L114) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation_ae` | [EndOfPaper/NormExamples.lean:21](../EndOfPaper/NormExamples.lean#L21) |
| `ScalarMonotone.EndOfPaper.coordinateLpNorm_continuous` | [EndOfPaper/NormExamples.lean:62](../EndOfPaper/NormExamples.lean#L62) |
| `ScalarMonotone.EndOfPaper.euclidean_norm_sharp_ones` | [EndOfPaper/NormExamples.lean:66](../EndOfPaper/NormExamples.lean#L66) |
| `ScalarMonotone.EndOfPaper.hardy_tail_norm_bound` | [EndOfPaper/NormExamples.lean:78](../EndOfPaper/NormExamples.lean#L78) |
| `ScalarMonotone.EndOfPaper.ellp_hardy_tail_sharp` | [EndOfPaper/NormExamples.lean:97](../EndOfPaper/NormExamples.lean#L97) |
| `ScalarMonotone.EndOfPaper.quantileHardy_properties` | [EndOfPaper/NormExamples.lean:106](../EndOfPaper/NormExamples.lean#L106) |
| `ScalarMonotone.EndOfPaper.quantileHardy_nonnegative` | [EndOfPaper/NormExamples.lean:130](../EndOfPaper/NormExamples.lean#L130) |
| `ScalarMonotone.EndOfPaper.coordinateMass_aggregation_axioms` | [EndOfPaper/NormExamples.lean:148](../EndOfPaper/NormExamples.lean#L148) |
| `ScalarMonotone.EndOfPaper.coordinateMass_continuous` | [EndOfPaper/NormExamples.lean:154](../EndOfPaper/NormExamples.lean#L154) |
| `ScalarMonotone.EndOfPaper.hardy_tail_operator_bound` | [EndOfPaper/NormExamples.lean:159](../EndOfPaper/NormExamples.lean#L159) |
| `ScalarMonotone.EndOfPaper.hardy_tail_norm_operator_bound` | [EndOfPaper/NormExamples.lean:211](../EndOfPaper/NormExamples.lean#L211) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum` | [EndOfPaper/NormExamples.lean:226](../EndOfPaper/NormExamples.lean#L226) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum_singleton` | [EndOfPaper/NormExamples.lean:230](../EndOfPaper/NormExamples.lean#L230) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum_properties` | [EndOfPaper/NormExamples.lean:240](../EndOfPaper/NormExamples.lean#L240) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum_dom_subset` | [EndOfPaper/NormExamples.lean:257](../EndOfPaper/NormExamples.lean#L257) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum_completed_aggregation` | [EndOfPaper/NormExamples.lean:267](../EndOfPaper/NormExamples.lean#L267) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum_eq_aggregation` | [EndOfPaper/NormExamples.lean:288](../EndOfPaper/NormExamples.lean#L288) |
| `ScalarMonotone.EndOfPaper.quantileHardy_original_properties` | [EndOfPaper/NormExamples.lean:303](../EndOfPaper/NormExamples.lean#L303) |
| `ScalarMonotone.EndOfPaper.quantileHardy_sum_graphs` | [EndOfPaper/NormExamples.lean:313](../EndOfPaper/NormExamples.lean#L313) |
| `ScalarMonotone.EndOfPaper.hardy_tail_norm_sum_bound` | [EndOfPaper/NormExamples.lean:346](../EndOfPaper/NormExamples.lean#L346) |
<a id="result-2-6"></a>

## Proposition 2.6

[PDF page 37](../manuscript/monotone_calculus.pdf#page=37). Superadditive transformation of an odd median

Every integer r>=0, arity 2r+1, every nonnegative coordinate vector, including all zero and tied coordinates. The sorting permutation is constructed by Tuple.sort; it is not an added final hypothesis. The finite cut families have proved nonemptiness and finiteness. The existing full ordered-coordinate formula retains both inequalities and the exact truncation identity. The new cut formula proves exact equality with the nested minimum over 1<=ell<=r+1 and every J of size r+ell. Median continuity and continuity/nonnegative aggregation axioms of that scalar cut bound are also proved. Preserve and reuse the checked hypersimplex decomposition and truncation-capacity reverse inequality. Each subset gives an upper bound; a sorted prefix realizes each ordered partial sum and proves the converse cut-minimum bridge. Finite nonempty scalar extrema of continuous coordinate functions prove actual median continuity. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.median_transform_subset_upper` | [EndOfPaper/MedianBounds.lean:151](../EndOfPaper/MedianBounds.lean#L151) |
| `ScalarMonotone.EndOfPaper.hypersimplex_finite_decomposition` | [EndOfPaper/Hypersimplex.lean:199](../EndOfPaper/Hypersimplex.lean#L199) |
| `ScalarMonotone.EndOfPaper.odd_median_truncation_capacity` | [EndOfPaper/MedianCapacity.lean:72](../EndOfPaper/MedianCapacity.lean#L72) |
| `ScalarMonotone.EndOfPaper.monotone_prefix_sum_le_subset` | [EndOfPaper/MedianCapacity.lean:110](../EndOfPaper/MedianCapacity.lean#L110) |
| `ScalarMonotone.EndOfPaper.median_binary_majority` | [EndOfPaper/MedianTransform.lean:17](../EndOfPaper/MedianTransform.lean#L17) |
| `ScalarMonotone.EndOfPaper.median_transform_ge_hypersimplex` | [EndOfPaper/MedianTransform.lean:40](../EndOfPaper/MedianTransform.lean#L40) |
| `ScalarMonotone.EndOfPaper.median_transform_lower_of_capacity` | [EndOfPaper/MedianTransform.lean:73](../EndOfPaper/MedianTransform.lean#L73) |
| `ScalarMonotone.EndOfPaper.median_transform_ordered_coordinates` | [EndOfPaper/MedianTransform.lean:105](../EndOfPaper/MedianTransform.lean#L105) |
| `ScalarMonotone.EndOfPaper.median_transform_formula` | [EndOfPaper/MedianTransform.lean:155](../EndOfPaper/MedianTransform.lean#L155) |
| `ScalarMonotone.EndOfPaper.median_transform_truncation_identity` | [EndOfPaper/MedianTransform.lean:164](../EndOfPaper/MedianTransform.lean#L164) |
| `ScalarMonotone.EndOfPaper.continuous_finite_ciInf` | [EndOfPaper/MedianSharpness.lean:17](../EndOfPaper/MedianSharpness.lean#L17) |
| `ScalarMonotone.EndOfPaper.continuous_finite_ciSup` | [EndOfPaper/MedianSharpness.lean:25](../EndOfPaper/MedianSharpness.lean#L25) |
| `ScalarMonotone.EndOfPaper.scalarMedian_continuous` | [EndOfPaper/MedianSharpness.lean:33](../EndOfPaper/MedianSharpness.lean#L33) |
| `ScalarMonotone.EndOfPaper.medianCutSets` | [EndOfPaper/MedianSharpness.lean:39](../EndOfPaper/MedianSharpness.lean#L39) |
| `ScalarMonotone.EndOfPaper.medianCutSets_finite` | [EndOfPaper/MedianSharpness.lean:42](../EndOfPaper/MedianSharpness.lean#L42) |
| `ScalarMonotone.EndOfPaper.medianCutSets_nonempty` | [EndOfPaper/MedianSharpness.lean:46](../EndOfPaper/MedianSharpness.lean#L46) |
| `ScalarMonotone.EndOfPaper.medianCutBound` | [EndOfPaper/MedianSharpness.lean:53](../EndOfPaper/MedianSharpness.lean#L53) |
| `ScalarMonotone.EndOfPaper.median_transform_cut_formula` | [EndOfPaper/MedianSharpness.lean:59](../EndOfPaper/MedianSharpness.lean#L59) |
| `ScalarMonotone.EndOfPaper.medianCutBound_continuous` | [EndOfPaper/MedianSharpness.lean:86](../EndOfPaper/MedianSharpness.lean#L86) |
| `ScalarMonotone.EndOfPaper.medianCutBound_aggregation_axioms` | [EndOfPaper/MedianSharpness.lean:96](../EndOfPaper/MedianSharpness.lean#L96) |
| `ScalarMonotone.EndOfPaper.median_hardy_tail_sharp` | [EndOfPaper/MedianSharpness.lean:112](../EndOfPaper/MedianSharpness.lean#L112) |
| `ScalarMonotone.EndOfPaper.median_comonotone_near_sharp` | [EndOfPaper/MedianSharpness.lean:123](../EndOfPaper/MedianSharpness.lean#L123) |
<a id="result-2-7"></a>

## Lemma 2.7

[PDF page 37](../manuscript/monotone_calculus.pdf#page=37). Area inequality for monotone aggregation

The standing continuous, coordinatewise monotone, positively homogeneous nonnegative F and maximal decreasing input graphs nonnegative on their common open interval. Every finite b>0 with (0,b) contained in that interval is allowed, including b at its finite upper endpoint. The final theorem assumes precisely finite extended nonnegative scalar areas, not L1 as an extra hypothesis. Strictly positive homogeneity suffices via the proved zero-scalar bridge; PaperChecks applies that bridge from the literal paper assumptions. Every scalar selection of the actual completed aggregation graph is integrable on (0,b), and its area is bounded by F-sharp of the finite input areas. All input and aggregate selections are arbitrary. The theorem states the finite nonnegative input areas as ENNReal integrals and uses their toReal values only after proving finiteness and L1. No continuity of F-sharp on boundary faces is assumed. Prove the full finite-measure integral inequality by lower simple approximations and dominated convergence, keeping each approximate mean below the exact mean. Construct measurable representatives for arbitrary ae-nonnegative vectors and derive aggregate integrability from the linear bound. The completed aggregation constructor preserves full jump intervals. Its scalar-selection bridge and ae uniqueness identify all actual operator areas with the scalar integral inequality. Absolute-area equivalence discharges L1 from the paper finite nonnegative areas. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.aggregation_step_bound` | [EndOfPaper/Superadditive.lean:326](../EndOfPaper/Superadditive.lean#L326) |
| `ScalarMonotone.EndOfPaper.aggregation_finset_bound` | [EndOfPaper/Superadditive.lean:335](../EndOfPaper/Superadditive.lean#L335) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_concaveOn` | [EndOfPaper/Superadditive.lean:311](../EndOfPaper/Superadditive.lean#L311) |
| `ScalarMonotone.EndOfPaper.intervalGraphOn` | [EndOfPaper/AggregationOperator.lean:15](../EndOfPaper/AggregationOperator.lean#L15) |
| `ScalarMonotone.EndOfPaper.intervalCompletionI` | [EndOfPaper/AggregationOperator.lean:19](../EndOfPaper/AggregationOperator.lean#L19) |
| `ScalarMonotone.EndOfPaper.intervalCompletionI_properties` | [EndOfPaper/AggregationOperator.lean:21](../EndOfPaper/AggregationOperator.lean#L21) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_tendsto_left` | [EndOfPaper/AggregationOperator.lean:91](../EndOfPaper/AggregationOperator.lean#L91) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_tendsto_right` | [EndOfPaper/AggregationOperator.lean:104](../EndOfPaper/AggregationOperator.lean#L104) |
| `ScalarMonotone.EndOfPaper.aggregationOperator` | [EndOfPaper/AggregationOperator.lean:117](../EndOfPaper/AggregationOperator.lean#L117) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_properties` | [EndOfPaper/AggregationOperator.lean:122](../EndOfPaper/AggregationOperator.lean#L122) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_unique` | [EndOfPaper/AggregationOperator.lean:188](../EndOfPaper/AggregationOperator.lean#L188) |
| `ScalarMonotone.EndOfPaper.decreasing_interior_value_bounds` | [EndOfPaper/AggregationOperator.lean:211](../EndOfPaper/AggregationOperator.lean#L211) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_selection` | [EndOfPaper/AggregationOperator.lean:224](../EndOfPaper/AggregationOperator.lean#L224) |
| `ScalarMonotone.EndOfPaper.simple_aggregation_integral_bound` | [EndOfPaper/IntegralAggregation.lean:18](../EndOfPaper/IntegralAggregation.lean#L18) |
| `ScalarMonotone.EndOfPaper.lowerScalarSimple` | [EndOfPaper/IntegralAggregation.lean:41](../EndOfPaper/IntegralAggregation.lean#L41) |
| `ScalarMonotone.EndOfPaper.lowerScalarSimple_bounds` | [EndOfPaper/IntegralAggregation.lean:44](../EndOfPaper/IntegralAggregation.lean#L44) |
| `ScalarMonotone.EndOfPaper.lowerScalarSimple_tendsto` | [EndOfPaper/IntegralAggregation.lean:55](../EndOfPaper/IntegralAggregation.lean#L55) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple` | [EndOfPaper/IntegralAggregation.lean:63](../EndOfPaper/IntegralAggregation.lean#L63) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple_apply` | [EndOfPaper/IntegralAggregation.lean:66](../EndOfPaper/IntegralAggregation.lean#L66) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple_bounds` | [EndOfPaper/IntegralAggregation.lean:80](../EndOfPaper/IntegralAggregation.lean#L80) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple_tendsto` | [EndOfPaper/IntegralAggregation.lean:87](../EndOfPaper/IntegralAggregation.lean#L87) |
| `ScalarMonotone.EndOfPaper.simpleVector_integral_apply` | [EndOfPaper/IntegralAggregation.lean:95](../EndOfPaper/IntegralAggregation.lean#L95) |
| `ScalarMonotone.EndOfPaper.aggregation_positiveExtension_continuous` | [EndOfPaper/IntegralAggregation.lean:101](../EndOfPaper/IntegralAggregation.lean#L101) |
| `ScalarMonotone.EndOfPaper.aggregation_composition_integrable` | [EndOfPaper/IntegralAggregation.lean:108](../EndOfPaper/IntegralAggregation.lean#L108) |
| `ScalarMonotone.EndOfPaper.aggregation_integral_bound` | [EndOfPaper/IntegralAggregation.lean:133](../EndOfPaper/IntegralAggregation.lean#L133) |
| `ScalarMonotone.EndOfPaper.exists_nonnegative_measurable_representative` | [EndOfPaper/IntegralAggregation.lean:173](../EndOfPaper/IntegralAggregation.lean#L173) |
| `ScalarMonotone.EndOfPaper.aggregation_composition_integrable_ae` | [EndOfPaper/IntegralAggregation.lean:190](../EndOfPaper/IntegralAggregation.lean#L190) |
| `ScalarMonotone.EndOfPaper.aggregation_integral_bound_ae` | [EndOfPaper/IntegralAggregation.lean:199](../EndOfPaper/IntegralAggregation.lean#L199) |
| `ScalarMonotone.EndOfPaper.aggregation_area_bound_on` | [EndOfPaper/AggregationArea.lean:16](../EndOfPaper/AggregationArea.lean#L16) |
| `ScalarMonotone.EndOfPaper.aggregation_area_bound` | [EndOfPaper/AggregationArea.lean:55](../EndOfPaper/AggregationArea.lean#L55) |
| `ScalarMonotone.EndOfPaper.aggregation_area_finite_nonnegative` | [EndOfPaper/AggregationArea.lean:72](../EndOfPaper/AggregationArea.lean#L72) |
| `ScalarMonotone.EndOfPaper.aggregationAxioms_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:20](../EndOfPaper/HardyTailAggregation.lean#L20) |
| `ScalarMonotone.EndOfPaper.weighted_aggregation_bound` | [EndOfPaper/HardyTailAggregation.lean:36](../EndOfPaper/HardyTailAggregation.lean#L36) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation` | [EndOfPaper/HardyTailAggregation.lean:74](../EndOfPaper/HardyTailAggregation.lean#L74) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:120](../EndOfPaper/HardyTailAggregation.lean#L120) |
<a id="result-2-8"></a>

## Proposition 2.8

[PDF page 38](../manuscript/monotone_calculus.pdf#page=38). Aggregation of Hardy tail profiles

Arbitrary jointly defined nonnegative measurable integrable random variables, with no independence or atomlessness. F has exactly the standing nonnegative codomain, coordinate monotonicity, continuity on the nonnegative cone and homogeneity for every positive scalar. The harmless zero-scalar case is derived, rather than imposed. Every p in (0,1) is allowed, including arbitrary atomic marginal laws. The full theorem supplies the unique scalar values of the actual completed Hardy integrals of each marginal quantile and of the aggregate quantile, and bounds the latter by F-sharp of the former. The original-space feasible-weight aggregation inequality is proved separately. Integrability and measurability of F(X) are derived; no scalar replacement for the completed graph is assumed. Apply the general integral aggregation theorem to the weighted vector Z*X on the original space, then use homogeneity to normalize by p. This proves the needed weighted Jensen inequality without requiring boundary continuity of F-sharp. The attained original-space variational formula supplies an aggregate optimizer. Its marginal weighted expectations are bounded by the individual Hardy values; monotonicity of F-sharp finishes the exact completed-profile inequality. Zero coordinates and F=0 are retained. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.intervalGraphOn` | [EndOfPaper/AggregationOperator.lean:15](../EndOfPaper/AggregationOperator.lean#L15) |
| `ScalarMonotone.EndOfPaper.intervalCompletionI` | [EndOfPaper/AggregationOperator.lean:19](../EndOfPaper/AggregationOperator.lean#L19) |
| `ScalarMonotone.EndOfPaper.intervalCompletionI_properties` | [EndOfPaper/AggregationOperator.lean:21](../EndOfPaper/AggregationOperator.lean#L21) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_tendsto_left` | [EndOfPaper/AggregationOperator.lean:91](../EndOfPaper/AggregationOperator.lean#L91) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_tendsto_right` | [EndOfPaper/AggregationOperator.lean:104](../EndOfPaper/AggregationOperator.lean#L104) |
| `ScalarMonotone.EndOfPaper.aggregationOperator` | [EndOfPaper/AggregationOperator.lean:117](../EndOfPaper/AggregationOperator.lean#L117) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_properties` | [EndOfPaper/AggregationOperator.lean:122](../EndOfPaper/AggregationOperator.lean#L122) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_unique` | [EndOfPaper/AggregationOperator.lean:188](../EndOfPaper/AggregationOperator.lean#L188) |
| `ScalarMonotone.EndOfPaper.decreasing_interior_value_bounds` | [EndOfPaper/AggregationOperator.lean:211](../EndOfPaper/AggregationOperator.lean#L211) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_selection` | [EndOfPaper/AggregationOperator.lean:224](../EndOfPaper/AggregationOperator.lean#L224) |
| `ScalarMonotone.EndOfPaper.simple_aggregation_integral_bound` | [EndOfPaper/IntegralAggregation.lean:18](../EndOfPaper/IntegralAggregation.lean#L18) |
| `ScalarMonotone.EndOfPaper.lowerScalarSimple` | [EndOfPaper/IntegralAggregation.lean:41](../EndOfPaper/IntegralAggregation.lean#L41) |
| `ScalarMonotone.EndOfPaper.lowerScalarSimple_bounds` | [EndOfPaper/IntegralAggregation.lean:44](../EndOfPaper/IntegralAggregation.lean#L44) |
| `ScalarMonotone.EndOfPaper.lowerScalarSimple_tendsto` | [EndOfPaper/IntegralAggregation.lean:55](../EndOfPaper/IntegralAggregation.lean#L55) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple` | [EndOfPaper/IntegralAggregation.lean:63](../EndOfPaper/IntegralAggregation.lean#L63) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple_apply` | [EndOfPaper/IntegralAggregation.lean:66](../EndOfPaper/IntegralAggregation.lean#L66) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple_bounds` | [EndOfPaper/IntegralAggregation.lean:80](../EndOfPaper/IntegralAggregation.lean#L80) |
| `ScalarMonotone.EndOfPaper.lowerVectorSimple_tendsto` | [EndOfPaper/IntegralAggregation.lean:87](../EndOfPaper/IntegralAggregation.lean#L87) |
| `ScalarMonotone.EndOfPaper.simpleVector_integral_apply` | [EndOfPaper/IntegralAggregation.lean:95](../EndOfPaper/IntegralAggregation.lean#L95) |
| `ScalarMonotone.EndOfPaper.aggregation_positiveExtension_continuous` | [EndOfPaper/IntegralAggregation.lean:101](../EndOfPaper/IntegralAggregation.lean#L101) |
| `ScalarMonotone.EndOfPaper.aggregation_composition_integrable` | [EndOfPaper/IntegralAggregation.lean:108](../EndOfPaper/IntegralAggregation.lean#L108) |
| `ScalarMonotone.EndOfPaper.aggregation_integral_bound` | [EndOfPaper/IntegralAggregation.lean:133](../EndOfPaper/IntegralAggregation.lean#L133) |
| `ScalarMonotone.EndOfPaper.exists_nonnegative_measurable_representative` | [EndOfPaper/IntegralAggregation.lean:173](../EndOfPaper/IntegralAggregation.lean#L173) |
| `ScalarMonotone.EndOfPaper.aggregation_composition_integrable_ae` | [EndOfPaper/IntegralAggregation.lean:190](../EndOfPaper/IntegralAggregation.lean#L190) |
| `ScalarMonotone.EndOfPaper.aggregation_integral_bound_ae` | [EndOfPaper/IntegralAggregation.lean:199](../EndOfPaper/IntegralAggregation.lean#L199) |
| `ScalarMonotone.EndOfPaper.aggregationAxioms_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:20](../EndOfPaper/HardyTailAggregation.lean#L20) |
| `ScalarMonotone.EndOfPaper.weighted_aggregation_bound` | [EndOfPaper/HardyTailAggregation.lean:36](../EndOfPaper/HardyTailAggregation.lean#L36) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation` | [EndOfPaper/HardyTailAggregation.lean:74](../EndOfPaper/HardyTailAggregation.lean#L74) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:120](../EndOfPaper/HardyTailAggregation.lean#L120) |
<a id="result-2-9"></a>

## Proposition 2.9

[PDF page 40](../manuscript/monotone_calculus.pdf#page=40). Hardy bounds from convex transformations

The actual maximally decreasing profile is single-valued and strictly decreasing on its open domain, with range (0,L) for extended-real 0<L<=infinity. The reader checks separately assume the manuscript continuity and open-domain conditions and bridge single-valuedness plus a selection to the singleton-fiber representation. The proved theorem permits omission of those two regularity premises, so it adds no hypothesis. Power convexity uses kappa>1; logarithmic convexity uses the positive profile derived from its range. Negative inverse values and lack of global inverse L1 are allowed. hardy_profiles_power and hardy_profiles_exponential prove well-definedness/maximality of the actual Hardy tail transform and the whole DecLE bounds by (kappa/(kappa-1))^kappa alpha and exp(1) alpha. The prefix theorems separately exhibit a measurable inverse selection and derive absolute integrability on every prefix before Jensen. hardy_regularized_profiles proves both literal completed equality cases for C P_kappa and C E, C>0. Every domain boundary fiber and finite/infinite range endpoint is retained. Use singleton inverse fibers, strict increase of the convex forward transform and the actual open convex upper substitution domain to derive inverse concavity. A supporting affine upper bound and monotone lower bound derive composition L1. Jensen and exact power/logarithmic Hardy averages give the precise scalar inverse-dilation inequalities. Initial-domain separated comparison extends them to whole completed Hardy graphs on potentially different domains. Decreasing inversion and exact inverse input-dilation scaling give the stated constants. The existing completed-profile identities supply the equality cases. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.concave_integral_upper` | [EndOfPaper/Profiles.lean:90](../EndOfPaper/Profiles.lean#L90) |
| `ScalarMonotone.EndOfPaper.hardyScalar_power_profile` | [EndOfPaper/Profiles.lean:37](../EndOfPaper/Profiles.lean#L37) |
| `ScalarMonotone.EndOfPaper.hardyScalar_exponential_profile` | [EndOfPaper/Profiles.lean:62](../EndOfPaper/Profiles.lean#L62) |
| `ScalarMonotone.EndOfPaper.concave_monotone_affine_bounds` | [EndOfPaper/ConcaveGrowth.lean:15](../EndOfPaper/ConcaveGrowth.lean#L15) |
| `ScalarMonotone.EndOfPaper.concave_monotone_comp_integrable` | [EndOfPaper/ConcaveGrowth.lean:34](../EndOfPaper/ConcaveGrowth.lean#L34) |
| `ScalarMonotone.EndOfPaper.concave_monotone_jensen_derived_integrability` | [EndOfPaper/ConcaveGrowth.lean:59](../EndOfPaper/ConcaveGrowth.lean#L59) |
| `ScalarMonotone.EndOfPaper.hardy_regularized_profiles` | [EndOfPaper/CompletedProfiles.lean:304](../EndOfPaper/CompletedProfiles.lean#L304) |
| `ScalarMonotone.EndOfPaper.inverse_selection_singleton_of_strictAnti` | [EndOfPaper/ProfileGeometry.lean:15](../EndOfPaper/ProfileGeometry.lean#L15) |
| `ScalarMonotone.EndOfPaper.profile_range_initial_geometry` | [EndOfPaper/ProfileGeometry.lean:33](../EndOfPaper/ProfileGeometry.lean#L33) |
| `ScalarMonotone.EndOfPaper.positive_initial_le_mem` | [EndOfPaper/ProfileGeometry.lean:42](../EndOfPaper/ProfileGeometry.lean#L42) |
| `ScalarMonotone.EndOfPaper.power_transform_strictMono` | [EndOfPaper/ProfileGeometry.lean:49](../EndOfPaper/ProfileGeometry.lean#L49) |
| `ScalarMonotone.EndOfPaper.logarithmic_transform_strictMono` | [EndOfPaper/ProfileGeometry.lean:56](../EndOfPaper/ProfileGeometry.lean#L56) |
| `ScalarMonotone.EndOfPaper.powerSubstitutionDomain` | [EndOfPaper/ProfileGeometry.lean:62](../EndOfPaper/ProfileGeometry.lean#L62) |
| `ScalarMonotone.EndOfPaper.exponentialSubstitutionDomain` | [EndOfPaper/ProfileGeometry.lean:65](../EndOfPaper/ProfileGeometry.lean#L65) |
| `ScalarMonotone.EndOfPaper.powerSubstitutionDomain_geometry` | [EndOfPaper/ProfileGeometry.lean:68](../EndOfPaper/ProfileGeometry.lean#L68) |
| `ScalarMonotone.EndOfPaper.exponentialSubstitutionDomain_geometry` | [EndOfPaper/ProfileGeometry.lean:83](../EndOfPaper/ProfileGeometry.lean#L83) |
| `ScalarMonotone.EndOfPaper.powerSubstitutionDomain_point` | [EndOfPaper/ProfileGeometry.lean:94](../EndOfPaper/ProfileGeometry.lean#L94) |
| `ScalarMonotone.EndOfPaper.exponentialSubstitutionDomain_point` | [EndOfPaper/ProfileGeometry.lean:102](../EndOfPaper/ProfileGeometry.lean#L102) |
| `ScalarMonotone.EndOfPaper.monotoneOn_of_strictMonoOn_right_inverse` | [EndOfPaper/ProfileInverseConcavity.lean:15](../EndOfPaper/ProfileInverseConcavity.lean#L15) |
| `ScalarMonotone.EndOfPaper.concaveOn_of_convexOn_right_inverse` | [EndOfPaper/ProfileInverseConcavity.lean:22](../EndOfPaper/ProfileInverseConcavity.lean#L22) |
| `ScalarMonotone.EndOfPaper.convex_inverse_jensen_derived_integrability` | [EndOfPaper/ProfileInverseConcavity.lean:37](../EndOfPaper/ProfileInverseConcavity.lean#L37) |
| `ScalarMonotone.EndOfPaper.inverse_positiveInputDilation` | [EndOfPaper/ProfileInverseConcavity.lean:51](../EndOfPaper/ProfileInverseConcavity.lean#L51) |
| `ScalarMonotone.EndOfPaper.hardyScalar_concave_composition` | [EndOfPaper/ProfileScalarJensen.lean:15](../EndOfPaper/ProfileScalarJensen.lean#L15) |
| `ScalarMonotone.EndOfPaper.power_inverse_profile_jensen` | [EndOfPaper/ProfileScalarJensen.lean:44](../EndOfPaper/ProfileScalarJensen.lean#L44) |
| `ScalarMonotone.EndOfPaper.exponential_inverse_profile_jensen` | [EndOfPaper/ProfileScalarJensen.lean:57](../EndOfPaper/ProfileScalarJensen.lean#L57) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_le_inputDilation` | [EndOfPaper/ProfileOrder.lean:14](../EndOfPaper/ProfileOrder.lean#L14) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_bound_of_scalar` | [EndOfPaper/ProfileOrder.lean:44](../EndOfPaper/ProfileOrder.lean#L44) |
| `ScalarMonotone.EndOfPaper.positiveInitialInterval_isGLB` | [EndOfPaper/ProfilePrefixBounds.lean:17](../EndOfPaper/ProfilePrefixBounds.lean#L17) |
| `ScalarMonotone.EndOfPaper.prefix_congr_positive` | [EndOfPaper/ProfilePrefixBounds.lean:35](../EndOfPaper/ProfilePrefixBounds.lean#L35) |
| `ScalarMonotone.EndOfPaper.hardy_profile_power_prefix` | [EndOfPaper/ProfilePrefixBounds.lean:47](../EndOfPaper/ProfilePrefixBounds.lean#L47) |
| `ScalarMonotone.EndOfPaper.hardy_profile_exponential_prefix` | [EndOfPaper/ProfilePrefixBounds.lean:102](../EndOfPaper/ProfilePrefixBounds.lean#L102) |
| `ScalarMonotone.EndOfPaper.hardy_profiles_power` | [EndOfPaper/HardyProfileBounds.lean:15](../EndOfPaper/HardyProfileBounds.lean#L15) |
| `ScalarMonotone.EndOfPaper.hardy_profiles_exponential` | [EndOfPaper/HardyProfileBounds.lean:39](../EndOfPaper/HardyProfileBounds.lean#L39) |
<a id="result-2-10"></a>

## Proposition 2.10

[PDF page 40](../manuscript/monotone_calculus.pdf#page=40). Power and exponential convex transformations

An arbitrary continuous real scalar transformation on (0,infinity). Its values outside that interval are unrestricted and never used in the conclusions. Every real kappa>0 is retained. No monotonicity is required for either forward implication; the convex converse uses the paper nondecreasing assumption and the concave converse the paper nonincreasing assumption. All power convexities imply exponential convexity on the entire real line. Exponential convexity implies all positive power convexities under the exact nondecreasing hypothesis. Both corresponding concave conclusions hold, with the stated nonincreasing hypothesis only for the concave converse. The combined manuscript-facing theorem states all four implications explicitly. The negative powers (1+x/kappa)^(-kappa) tend to exp(-x), and continuity transfers the limit through phi. For any fixed convex combination, the affine inputs are eventually positive, so the power convexity inequality passes to the limit without assuming convexity on an incorrectly enlarged domain. The convex converse composes a convex decreasing function phi(exp(-x)) with the concave kappa*log(x). Negation yields the concave cases with the correct reversed monotonicity. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.eventually_positive_one_add_div` | [EndOfPaper/ConvexTransforms.lean:15](../EndOfPaper/ConvexTransforms.lean#L15) |
| `ScalarMonotone.EndOfPaper.negative_power_exponential_limit` | [EndOfPaper/ConvexTransforms.lean:21](../EndOfPaper/ConvexTransforms.lean#L21) |
| `ScalarMonotone.EndOfPaper.continuous_power_exponential_limit` | [EndOfPaper/ConvexTransforms.lean:28](../EndOfPaper/ConvexTransforms.lean#L28) |
| `ScalarMonotone.EndOfPaper.all_power_convex_implies_exponential_convex` | [EndOfPaper/ConvexTransforms.lean:35](../EndOfPaper/ConvexTransforms.lean#L35) |
| `ScalarMonotone.EndOfPaper.exponential_convex_implies_power_convex` | [EndOfPaper/ConvexTransforms.lean:55](../EndOfPaper/ConvexTransforms.lean#L55) |
| `ScalarMonotone.EndOfPaper.all_power_concave_implies_exponential_concave` | [EndOfPaper/ConvexTransforms.lean:76](../EndOfPaper/ConvexTransforms.lean#L76) |
| `ScalarMonotone.EndOfPaper.exponential_concave_implies_power_concave` | [EndOfPaper/ConvexTransforms.lean:85](../EndOfPaper/ConvexTransforms.lean#L85) |
| `ScalarMonotone.EndOfPaper.power_exponential_convex_transforms` | [EndOfPaper/ConvexTransforms.lean:98](../EndOfPaper/ConvexTransforms.lean#L98) |
| `ScalarMonotone.EndOfPaper.hardy_power_constant_limit` | [EndOfPaper/ConvexTransforms.lean:115](../EndOfPaper/ConvexTransforms.lean#L115) |
<a id="result-2-11"></a>

## Theorem 2.11

[PDF page 41](../manuscript/monotone_calculus.pdf#page=41). Sharpness of Hardy tail aggregation

Every finite dimension, every fixed p in (0,1), every prescribed nonnegative marginal-average vector, and the exact continuous coordinatewise monotone positively homogeneous nonnegative F. Strictly positive homogeneity supplies the zero case through the checked bridge. The literal admissible classes quantify over every measurable sample space and every probability measure in an arbitrary universe, not a fixed or atomless original space. Finite ranges are explicit, and almost-sure nonnegativity is allowed. No L1 or aggregate-measurability premise is silently added: finite ranges and clipping discharge those conditions. The supremum of actual completed aggregate Hardy quantile values with exactly the prescribed marginal Hardy values equals F-sharp(a). The same exact supremum holds for finite-valued comonotone variables. Both candidate classes are nonempty and bounded above before their real suprema are used. The theorem asserts neither general attainment nor one coupling extremizing every p. All four numbered conclusions are supplied by the named manuscript-facing theorem and its explicit lower models. For an arbitrary original-space candidate, measurable positive-part clipping preserves every marginal law and the aggregate law, including on incomplete spaces. It derives L1 from finite ranges and then applies the checked general Hardy tail upper bound. For each admissible finite decomposition and each epsilon in (0,1), construct globally measurable nonnegative finite step profiles. Exact interval areas give the prescribed actual completed marginal Hardy values. Disjoint geometric bands, including the last band ending at zero, give the aggregate lower value (1-epsilon)*sum F(v_j). A universe-lifted uniform model realizes these laws in the same arbitrary universe as the competing spaces; this is a lower example, not an atomless restriction on the upper theorem. Pass epsilon to zero with a typed kernel-checked filter limit, convert the finite list decomposition to Fin-indexed sums, and take the exact finite-decomposition sharp supremum. Independent reader types expand the actual Hardy graphs and check both exact suprema with the literal paper homogeneity convention. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation` | [EndOfPaper/HardyTailAggregation.lean:74](../EndOfPaper/HardyTailAggregation.lean#L74) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile_joint_law` | [EndOfPaper/ComonotoneLawRepresentation.lean:92](../EndOfPaper/ComonotoneLawRepresentation.lean#L92) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep` | [EndOfPaper/FiniteStepProfiles.lean:17](../EndOfPaper/FiniteStepProfiles.lean#L17) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep_measurable` | [EndOfPaper/FiniteStepProfiles.lean:19](../EndOfPaper/FiniteStepProfiles.lean#L19) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep_nonnegative` | [EndOfPaper/FiniteStepProfiles.lean:22](../EndOfPaper/FiniteStepProfiles.lean#L22) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep_antitone` | [EndOfPaper/FiniteStepProfiles.lean:26](../EndOfPaper/FiniteStepProfiles.lean#L26) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep_integrable` | [EndOfPaper/FiniteStepProfiles.lean:34](../EndOfPaper/FiniteStepProfiles.lean#L34) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep_intervalIntegrable` | [EndOfPaper/FiniteStepProfiles.lean:38](../EndOfPaper/FiniteStepProfiles.lean#L38) |
| `ScalarMonotone.EndOfPaper.hardyInitialStep_integral` | [EndOfPaper/FiniteStepProfiles.lean:44](../EndOfPaper/FiniteStepProfiles.lean#L44) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile` | [EndOfPaper/FiniteStepProfiles.lean:51](../EndOfPaper/FiniteStepProfiles.lean#L51) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_measurable` | [EndOfPaper/FiniteStepProfiles.lean:54](../EndOfPaper/FiniteStepProfiles.lean#L54) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_antitone` | [EndOfPaper/FiniteStepProfiles.lean:59](../EndOfPaper/FiniteStepProfiles.lean#L59) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_nonnegative` | [EndOfPaper/FiniteStepProfiles.lean:65](../EndOfPaper/FiniteStepProfiles.lean#L65) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_finite_range` | [EndOfPaper/FiniteStepProfiles.lean:70](../EndOfPaper/FiniteStepProfiles.lean#L70) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_integrable` | [EndOfPaper/FiniteStepProfiles.lean:84](../EndOfPaper/FiniteStepProfiles.lean#L84) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_intervalIntegrable` | [EndOfPaper/FiniteStepProfiles.lean:89](../EndOfPaper/FiniteStepProfiles.lean#L89) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_integral` | [EndOfPaper/FiniteStepProfiles.lean:96](../EndOfPaper/FiniteStepProfiles.lean#L96) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_hardy_quantile` | [EndOfPaper/FiniteStepProfiles.lean:108](../EndOfPaper/FiniteStepProfiles.lean#L108) |
| `ScalarMonotone.EndOfPaper.finiteStepProfile_dominates_step` | [EndOfPaper/FiniteStepProfiles.lean:125](../EndOfPaper/FiniteStepProfiles.lean#L125) |
| `ScalarMonotone.EndOfPaper.finite_steps_prescribed_hardy` | [EndOfPaper/FiniteStepProfiles.lean:139](../EndOfPaper/FiniteStepProfiles.lean#L139) |
| `ScalarMonotone.EndOfPaper.geometricScale` | [EndOfPaper/GeometricBands.lean:16](../EndOfPaper/GeometricBands.lean#L16) |
| `ScalarMonotone.EndOfPaper.geometricBand` | [EndOfPaper/GeometricBands.lean:18](../EndOfPaper/GeometricBands.lean#L18) |
| `ScalarMonotone.EndOfPaper.geometricScale_nonnegative` | [EndOfPaper/GeometricBands.lean:21](../EndOfPaper/GeometricBands.lean#L21) |
| `ScalarMonotone.EndOfPaper.geometricScale_positive` | [EndOfPaper/GeometricBands.lean:26](../EndOfPaper/GeometricBands.lean#L26) |
| `ScalarMonotone.EndOfPaper.geometricScale_succ_le_mul` | [EndOfPaper/GeometricBands.lean:31](../EndOfPaper/GeometricBands.lean#L31) |
| `ScalarMonotone.EndOfPaper.geometricScale_antitone` | [EndOfPaper/GeometricBands.lean:42](../EndOfPaper/GeometricBands.lean#L42) |
| `ScalarMonotone.EndOfPaper.geometricScale_le_initial` | [EndOfPaper/GeometricBands.lean:49](../EndOfPaper/GeometricBands.lean#L49) |
| `ScalarMonotone.EndOfPaper.geometricBand_length_lower` | [EndOfPaper/GeometricBands.lean:55](../EndOfPaper/GeometricBands.lean#L55) |
| `ScalarMonotone.EndOfPaper.geometricBands_disjoint` | [EndOfPaper/GeometricBands.lean:64](../EndOfPaper/GeometricBands.lean#L64) |
| `ScalarMonotone.EndOfPaper.geometricBand_subset_prefix` | [EndOfPaper/GeometricBands.lean:75](../EndOfPaper/GeometricBands.lean#L75) |
| `ScalarMonotone.EndOfPaper.geometricBand_sum_lower` | [EndOfPaper/GeometricBands.lean:81](../EndOfPaper/GeometricBands.lean#L81) |
| `ScalarMonotone.EndOfPaper.interval_indicator_band_integrable` | [EndOfPaper/GeometricBands.lean:105](../EndOfPaper/GeometricBands.lean#L105) |
| `ScalarMonotone.EndOfPaper.interval_indicator_band_integral` | [EndOfPaper/GeometricBands.lean:111](../EndOfPaper/GeometricBands.lean#L111) |
| `ScalarMonotone.EndOfPaper.finite_nonnegative_range_integrable` | [EndOfPaper/GeometricBands.lean:121](../EndOfPaper/GeometricBands.lean#L121) |
| `ScalarMonotone.EndOfPaper.aggregationAxioms_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:20](../EndOfPaper/HardyTailAggregation.lean#L20) |
| `ScalarMonotone.EndOfPaper.quantileHardy` | [EndOfPaper/HardySharpness.lean:20](../EndOfPaper/HardySharpness.lean#L20) |
| `ScalarMonotone.EndOfPaper.finite_vector_steps_prescribed` | [EndOfPaper/HardySharpness.lean:23](../EndOfPaper/HardySharpness.lean#L23) |
| `ScalarMonotone.EndOfPaper.finite_profile_aggregation_properties` | [EndOfPaper/HardySharpness.lean:41](../EndOfPaper/HardySharpness.lean#L41) |
| `ScalarMonotone.EndOfPaper.geometric_scaled_band_mass` | [EndOfPaper/HardySharpness.lean:65](../EndOfPaper/HardySharpness.lean#L65) |
| `ScalarMonotone.EndOfPaper.geometric_step_hardy_lower_model` | [EndOfPaper/HardySharpness.lean:76](../EndOfPaper/HardySharpness.lean#L76) |
| `ScalarMonotone.EndOfPaper.hardyTailValues` | [EndOfPaper/HardySharpness.lean:152](../EndOfPaper/HardySharpness.lean#L152) |
| `ScalarMonotone.EndOfPaper.comonotoneHardyTailValues` | [EndOfPaper/HardySharpness.lean:164](../EndOfPaper/HardySharpness.lean#L164) |
| `ScalarMonotone.EndOfPaper.comonotoneHardyTailValues_subset` | [EndOfPaper/HardySharpness.lean:176](../EndOfPaper/HardySharpness.lean#L176) |
| `ScalarMonotone.EndOfPaper.hardyTailValues_le` | [EndOfPaper/HardySharpness.lean:182](../EndOfPaper/HardySharpness.lean#L182) |
| `ScalarMonotone.EndOfPaper.hardyTailValues_bddAbove` | [EndOfPaper/HardySharpness.lean:219](../EndOfPaper/HardySharpness.lean#L219) |
| `ScalarMonotone.EndOfPaper.comonotoneHardyTailValues_bddAbove` | [EndOfPaper/HardySharpness.lean:225](../EndOfPaper/HardySharpness.lean#L225) |
| `ScalarMonotone.EndOfPaper.uniform_lift_profile_law` | [EndOfPaper/HardySharpness.lean:234](../EndOfPaper/HardySharpness.lean#L234) |
| `ScalarMonotone.EndOfPaper.uniform_profiles_mem_comonotone_values` | [EndOfPaper/HardySharpness.lean:243](../EndOfPaper/HardySharpness.lean#L243) |
| `ScalarMonotone.EndOfPaper.finite_decomposition_comonotone_model` | [EndOfPaper/HardySharpness.lean:274](../EndOfPaper/HardySharpness.lean#L274) |
| `ScalarMonotone.EndOfPaper.comonotoneHardyTailValues_nonempty` | [EndOfPaper/HardySharpness.lean:284](../EndOfPaper/HardySharpness.lean#L284) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_le_comonotone_values` | [EndOfPaper/HardySharpness.lean:295](../EndOfPaper/HardySharpness.lean#L295) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation_sharp` | [EndOfPaper/HardySharpness.lean:325](../EndOfPaper/HardySharpness.lean#L325) |
<a id="result-2-12"></a>

## Corollary 2.12

[PDF page 42](../manuscript/monotone_calculus.pdf#page=42). Sharp Hardy bound for an odd median

All integers r>=0, every arity 2r+1, arbitrary original probability spaces, measurable coordinate tuples with integrable marginals and almost-sure nonnegativity. The finite cut families have proved nonemptiness and finiteness; no sorting assumption or auxiliary-uniform variable is imposed on the original space. sharp_hardy_median proves the whole DecLE comparison with the literal nested lattice infimum of positive reciprocals times ordinary finite Minkowski graph sums, and both exact suprema at every fixed p and prescribed nonnegative marginal Hardy means. medianHardyBound_value identifies the literal right-hand graph at p with exactly the scalar cut minimum. The epsilon-optimal finite-valued comonotone existence theorem retains the exact marginal constraints. All endpoint fibers and the r=0 case are included; general attainment is not asserted. Positive-size cuts guarantee that the ordinary subset sum has domain in the common closure even though unused coordinates contribute global zero graphs. Prove maximality, domain and singleton fibers of each scaled ordinary sum, then identify it with the actual completed linear aggregation by whole-graph uniqueness. Apply the original-space aggregation bound and the initial-domain separated comparison to each cut; the conditional-lattice universal property gives the literal nested infimum. The existing finite graph-fiber theorem separately proves that its scalar value is exactly the nested cut minimum. The already checked hypersimplex reverse inequality and geometric finite-step models supply both sharp suprema. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.median_transform_subset_upper` | [EndOfPaper/MedianBounds.lean:151](../EndOfPaper/MedianBounds.lean#L151) |
| `ScalarMonotone.EndOfPaper.geometric_step_hardy_lower_model` | [EndOfPaper/HardySharpness.lean:76](../EndOfPaper/HardySharpness.lean#L76) |
| `ScalarMonotone.EndOfPaper.hardy_tail_aggregation_sharp` | [EndOfPaper/HardySharpness.lean:325](../EndOfPaper/HardySharpness.lean#L325) |
| `ScalarMonotone.EndOfPaper.continuous_finite_ciInf` | [EndOfPaper/MedianSharpness.lean:17](../EndOfPaper/MedianSharpness.lean#L17) |
| `ScalarMonotone.EndOfPaper.continuous_finite_ciSup` | [EndOfPaper/MedianSharpness.lean:25](../EndOfPaper/MedianSharpness.lean#L25) |
| `ScalarMonotone.EndOfPaper.scalarMedian_continuous` | [EndOfPaper/MedianSharpness.lean:33](../EndOfPaper/MedianSharpness.lean#L33) |
| `ScalarMonotone.EndOfPaper.medianCutSets` | [EndOfPaper/MedianSharpness.lean:39](../EndOfPaper/MedianSharpness.lean#L39) |
| `ScalarMonotone.EndOfPaper.medianCutSets_finite` | [EndOfPaper/MedianSharpness.lean:42](../EndOfPaper/MedianSharpness.lean#L42) |
| `ScalarMonotone.EndOfPaper.medianCutSets_nonempty` | [EndOfPaper/MedianSharpness.lean:46](../EndOfPaper/MedianSharpness.lean#L46) |
| `ScalarMonotone.EndOfPaper.medianCutBound` | [EndOfPaper/MedianSharpness.lean:53](../EndOfPaper/MedianSharpness.lean#L53) |
| `ScalarMonotone.EndOfPaper.median_transform_cut_formula` | [EndOfPaper/MedianSharpness.lean:59](../EndOfPaper/MedianSharpness.lean#L59) |
| `ScalarMonotone.EndOfPaper.medianCutBound_continuous` | [EndOfPaper/MedianSharpness.lean:86](../EndOfPaper/MedianSharpness.lean#L86) |
| `ScalarMonotone.EndOfPaper.medianCutBound_aggregation_axioms` | [EndOfPaper/MedianSharpness.lean:96](../EndOfPaper/MedianSharpness.lean#L96) |
| `ScalarMonotone.EndOfPaper.median_hardy_tail_sharp` | [EndOfPaper/MedianSharpness.lean:112](../EndOfPaper/MedianSharpness.lean#L112) |
| `ScalarMonotone.EndOfPaper.median_comonotone_near_sharp` | [EndOfPaper/MedianSharpness.lean:123](../EndOfPaper/MedianSharpness.lean#L123) |
| `ScalarMonotone.EndOfPaper.median_transform_formula` | [EndOfPaper/MedianTransform.lean:155](../EndOfPaper/MedianTransform.lean#L155) |
| `ScalarMonotone.EndOfPaper.medianCutLinear` | [EndOfPaper/MedianHardy.lean:17](../EndOfPaper/MedianHardy.lean#L17) |
| `ScalarMonotone.EndOfPaper.medianCutLinear_axioms` | [EndOfPaper/MedianHardy.lean:21](../EndOfPaper/MedianHardy.lean#L21) |
| `ScalarMonotone.EndOfPaper.medianCutLinear_continuous` | [EndOfPaper/MedianHardy.lean:35](../EndOfPaper/MedianHardy.lean#L35) |
| `ScalarMonotone.EndOfPaper.medianCutSum` | [EndOfPaper/MedianHardy.lean:39](../EndOfPaper/MedianHardy.lean#L39) |
| `ScalarMonotone.EndOfPaper.finiteOperatorSum_dom_component` | [EndOfPaper/MedianHardy.lean:44](../EndOfPaper/MedianHardy.lean#L44) |
| `ScalarMonotone.EndOfPaper.medianCutSum_maximal` | [EndOfPaper/MedianHardy.lean:55](../EndOfPaper/MedianHardy.lean#L55) |
| `ScalarMonotone.EndOfPaper.medianCutSum_dom_subset` | [EndOfPaper/MedianHardy.lean:71](../EndOfPaper/MedianHardy.lean#L71) |
| `ScalarMonotone.EndOfPaper.medianCutSum_singleton` | [EndOfPaper/MedianHardy.lean:83](../EndOfPaper/MedianHardy.lean#L83) |
| `ScalarMonotone.EndOfPaper.medianCutSum_eq_aggregation` | [EndOfPaper/MedianHardy.lean:98](../EndOfPaper/MedianHardy.lean#L98) |
| `ScalarMonotone.EndOfPaper.medianCutGraph` | [EndOfPaper/MedianHardy.lean:114](../EndOfPaper/MedianHardy.lean#L114) |
| `ScalarMonotone.EndOfPaper.medianHardyBound` | [EndOfPaper/MedianHardy.lean:119](../EndOfPaper/MedianHardy.lean#L119) |
| `ScalarMonotone.EndOfPaper.hardy_tail_median_bound` | [EndOfPaper/MedianHardy.lean:131](../EndOfPaper/MedianHardy.lean#L131) |
| `ScalarMonotone.EndOfPaper.hardy_tail_median_operator_bound` | [EndOfPaper/MedianHardy.lean:144](../EndOfPaper/MedianHardy.lean#L144) |
| `ScalarMonotone.EndOfPaper.sharp_hardy_median` | [EndOfPaper/MedianHardy.lean:191](../EndOfPaper/MedianHardy.lean#L191) |
| `ScalarMonotone.EndOfPaper.finite_decGraph_iInf_singleton` | [EndOfPaper/MedianHardy.lean:202](../EndOfPaper/MedianHardy.lean#L202) |
| `ScalarMonotone.EndOfPaper.medianHardyBound_value` | [EndOfPaper/MedianHardy.lean:219](../EndOfPaper/MedianHardy.lean#L219) |
<a id="result-2-13"></a>

## Example 2.13

[PDF page 43](../manuscript/monotone_calculus.pdf#page=43). Heterogeneous estimators: median and normalized sum

Arbitrary probability spaces, measurable integrable scalar estimators and arbitrary dependence, with every real target theta and 0<p<1. The concrete construction assumes only measurable Z>=0 almost surely and literal extended nonnegative expectation 0<EZ<infinity; L1 is derived. One h is chosen before all b>6. heterogeneous_estimators_bound proves both actual estimation-error upper-tail means with a common vector a of marginal error Hardy means: the exact ternary sorted-pair/half-total minimum for the median, and total/3 for the normalized sum. heterogeneous_estimators_concrete derives input integrability and actual marginal means [h,2h,bh], proves exact median error 2h and mean error (b+3)h/3 after every permutation, identifies the respective bounds 3h and (b+3)h/3, and proves the latter unbounded while h remains fixed and positive. Derive error L1 from deterministic domination before applying original-space Hardy monotonicity. Identify marginal singleton values between the median and sum applications, then use the full ternary transform formula and the normalized-sum linear transform. For the example, derive L1 and positive real mean from the positive finite lintegral, obtain h>0 from the mean lower bound, identify the actual error laws almost surely, and apply nonnegative Hardy homogeneity. Deterministic median/mean permutation invariance retains every reordered input. An explicit b=max(7,3M/h)+1 proves unboundedness. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.median_error_domination` | [EndOfPaper/MedianBounds.lean:105](../EndOfPaper/MedianBounds.lean#L105) |
| `ScalarMonotone.EndOfPaper.dualShortfall_add_le` | [EndOfPaper/Shortfall.lean:257](../EndOfPaper/Shortfall.lean#L257) |
| `ScalarMonotone.EndOfPaper.meanThree` | [EndOfPaper/EstimatorScalar.lean:16](../EndOfPaper/EstimatorScalar.lean#L16) |
| `ScalarMonotone.EndOfPaper.meanThree_continuous` | [EndOfPaper/EstimatorScalar.lean:18](../EndOfPaper/EstimatorScalar.lean#L18) |
| `ScalarMonotone.EndOfPaper.meanThree_aggregation_axioms` | [EndOfPaper/EstimatorScalar.lean:21](../EndOfPaper/EstimatorScalar.lean#L21) |
| `ScalarMonotone.EndOfPaper.meanThree_sharp_transform` | [EndOfPaper/EstimatorScalar.lean:34](../EndOfPaper/EstimatorScalar.lean#L34) |
| `ScalarMonotone.EndOfPaper.meanThree_error_domination` | [EndOfPaper/EstimatorScalar.lean:41](../EndOfPaper/EstimatorScalar.lean#L41) |
| `ScalarMonotone.EndOfPaper.majority_reindex` | [EndOfPaper/EstimatorScalar.lean:52](../EndOfPaper/EstimatorScalar.lean#L52) |
| `ScalarMonotone.EndOfPaper.scalarMedian_perm` | [EndOfPaper/EstimatorScalar.lean:63](../EndOfPaper/EstimatorScalar.lean#L63) |
| `ScalarMonotone.EndOfPaper.scalarMedian_add_const` | [EndOfPaper/EstimatorScalar.lean:69](../EndOfPaper/EstimatorScalar.lean#L69) |
| `ScalarMonotone.EndOfPaper.meanThree_perm` | [EndOfPaper/EstimatorScalar.lean:77](../EndOfPaper/EstimatorScalar.lean#L77) |
| `ScalarMonotone.EndOfPaper.median_three_sharp_formula` | [EndOfPaper/EstimatorScalar.lean:83](../EndOfPaper/EstimatorScalar.lean#L83) |
| `ScalarMonotone.EndOfPaper.median_three_scaled_exact` | [EndOfPaper/EstimatorScalar.lean:113](../EndOfPaper/EstimatorScalar.lean#L113) |
| `ScalarMonotone.EndOfPaper.meanThree_scaled_exact` | [EndOfPaper/EstimatorScalar.lean:128](../EndOfPaper/EstimatorScalar.lean#L128) |
| `ScalarMonotone.EndOfPaper.median_three_scale_bound` | [EndOfPaper/EstimatorScalar.lean:133](../EndOfPaper/EstimatorScalar.lean#L133) |
| `ScalarMonotone.EndOfPaper.quantileHardy_mono_values` | [EndOfPaper/HardyDomination.lean:15](../EndOfPaper/HardyDomination.lean#L15) |
| `ScalarMonotone.EndOfPaper.quantileHardy_original_mono` | [EndOfPaper/HardyDomination.lean:37](../EndOfPaper/HardyDomination.lean#L37) |
| `ScalarMonotone.EndOfPaper.quantileHardy_smul_value` | [EndOfPaper/HardyDomination.lean:56](../EndOfPaper/HardyDomination.lean#L56) |
| `ScalarMonotone.EndOfPaper.quantileHardy_mean_le` | [EndOfPaper/HardyDomination.lean:83](../EndOfPaper/HardyDomination.lean#L83) |
| `ScalarMonotone.EndOfPaper.hardy_tail_median_bound` | [EndOfPaper/MedianHardy.lean:131](../EndOfPaper/MedianHardy.lean#L131) |
| `ScalarMonotone.EndOfPaper.heterogeneous_estimators_bound` | [EndOfPaper/HeterogeneousEstimators.lean:17](../EndOfPaper/HeterogeneousEstimators.lean#L17) |
| `ScalarMonotone.EndOfPaper.integrable_positive_mean_of_lintegral` | [EndOfPaper/HeterogeneousEstimators.lean:74](../EndOfPaper/HeterogeneousEstimators.lean#L74) |
| `ScalarMonotone.EndOfPaper.normalized_sum_scale_unbounded` | [EndOfPaper/HeterogeneousEstimators.lean:83](../EndOfPaper/HeterogeneousEstimators.lean#L83) |
| `ScalarMonotone.EndOfPaper.heterogeneous_estimators_concrete` | [EndOfPaper/HeterogeneousEstimators.lean:98](../EndOfPaper/HeterogeneousEstimators.lean#L98) |
<a id="result-2-14"></a>

## Proposition 2.14

[PDF page 44](../manuscript/monotone_calculus.pdf#page=44). Universal quantile envelope as a lattice supremum

Exactly the fixed integrable real probability laws and positive dimension of the manuscript. The competing class explicitly ranges over all positive finite replication counts, every original measurable space and probability measure in an arbitrary universe, measurable repeated coordinates and literal prescribed marginal-law equalities. There is no sign, independence, atomlessness, original-space uniform variable, coordinate L1, or near-optimality premise. Coordinate integrability and all lower witnesses are derived. The full literal averaged ordinary sum of the actual completed Hardy quantile graphs equals the lattice supremum of the exact competing quantile family. The named theorem proves equality of whole graphs, not just interior values, and replicated_quantile_envelope_isLUB supplies the universal property. The reader expands the entire competing class independently and checks the supremum domain interior (0,1) and its containment in [0,1]. Actual Hardy graph fibers, raw positive scaling and maximality retain both boundary fibers. All five numbered conclusions are supplied. Use the original-space attained dual Hardy bound and exact repeated-average normalization for the upper inequality, deriving L1 from each marginal law. Construct shared-branch quantile segments with exactly the full prescribed laws. IID columns, with allowed within-column dependence, satisfy the actual L1 strong law and give finite-replication strict-tail witnesses. Lift the constructed auxiliary model to every competing universe without changing any marginal or aggregate law. Strict-tail probabilities bound every quantile fiber. Separated graph inequalities force every upper bound above the completed averaged Hardy graph, including the endpoints. The existing conditional completeness theorem identifies its lattice supremum. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.iidUniformMeasure` | [EndOfPaper/IIDUniformAverage.lean:16](../EndOfPaper/IIDUniformAverage.lean#L16) |
| `ScalarMonotone.EndOfPaper.iidUniformMeasure_probability` | [EndOfPaper/IIDUniformAverage.lean:19](../EndOfPaper/IIDUniformAverage.lean#L19) |
| `ScalarMonotone.EndOfPaper.iid_uniform_eval_law` | [EndOfPaper/IIDUniformAverage.lean:23](../EndOfPaper/IIDUniformAverage.lean#L23) |
| `ScalarMonotone.EndOfPaper.iid_uniform_coordinates_independent` | [EndOfPaper/IIDUniformAverage.lean:38](../EndOfPaper/IIDUniformAverage.lean#L38) |
| `ScalarMonotone.EndOfPaper.iid_uniform_average_ae` | [EndOfPaper/IIDUniformAverage.lean:55](../EndOfPaper/IIDUniformAverage.lean#L55) |
| `ScalarMonotone.EndOfPaper.strict_tail_probability_tendsto_one` | [EndOfPaper/ProbabilityLowerLimit.lean:15](../EndOfPaper/ProbabilityLowerLimit.lean#L15) |
| `ScalarMonotone.EndOfPaper.exists_strict_tail_probability_of_ae_limit` | [EndOfPaper/ProbabilityLowerLimit.lean:44](../EndOfPaper/ProbabilityLowerLimit.lean#L44) |
| `ScalarMonotone.EndOfPaper.signed_hardy_sum_values` | [EndOfPaper/SignedHardySum.lean:15](../EndOfPaper/SignedHardySum.lean#L15) |
| `ScalarMonotone.EndOfPaper.finiteSum_singletons` | [EndOfPaper/SignedHardySum.lean:41](../EndOfPaper/SignedHardySum.lean#L41) |
| `ScalarMonotone.EndOfPaper.signed_hardy_sum_operator_bound` | [EndOfPaper/SignedHardySum.lean:52](../EndOfPaper/SignedHardySum.lean#L52) |
| `ScalarMonotone.EndOfPaper.tail_probability_lt_quantile` | [EndOfPaper/QuantileEnvelopeCriterion.lean:14](../EndOfPaper/QuantileEnvelopeCriterion.lean#L14) |
| `ScalarMonotone.EndOfPaper.decGraph_upper_domain_nonnegative` | [EndOfPaper/QuantileEnvelopeCriterion.lean:24](../EndOfPaper/QuantileEnvelopeCriterion.lean#L24) |
| `ScalarMonotone.EndOfPaper.quantile_family_isLUB` | [EndOfPaper/QuantileEnvelopeCriterion.lean:34](../EndOfPaper/QuantileEnvelopeCriterion.lean#L34) |
| `ScalarMonotone.EndOfPaper.uniform_prefix_integrable` | [EndOfPaper/QuantileSegmentIntegrals.lean:15](../EndOfPaper/QuantileSegmentIntegrals.lean#L15) |
| `ScalarMonotone.EndOfPaper.uniform_top_segment_integrable` | [EndOfPaper/QuantileSegmentIntegrals.lean:22](../EndOfPaper/QuantileSegmentIntegrals.lean#L22) |
| `ScalarMonotone.EndOfPaper.uniform_top_segment_mean` | [EndOfPaper/QuantileSegmentIntegrals.lean:30](../EndOfPaper/QuantileSegmentIntegrals.lean#L30) |
| `ScalarMonotone.EndOfPaper.uniform_top_average_integrable` | [EndOfPaper/QuantileSegmentIntegrals.lean:36](../EndOfPaper/QuantileSegmentIntegrals.lean#L36) |
| `ScalarMonotone.EndOfPaper.uniform_top_average_mean` | [EndOfPaper/QuantileSegmentIntegrals.lean:41](../EndOfPaper/QuantileSegmentIntegrals.lean#L41) |
| `ScalarMonotone.EndOfPaper.twoBranchMeasure` | [EndOfPaper/TwoBranchProbability.lean:13](../EndOfPaper/TwoBranchProbability.lean#L13) |
| `ScalarMonotone.EndOfPaper.twoBranchFunction` | [EndOfPaper/TwoBranchProbability.lean:18](../EndOfPaper/TwoBranchProbability.lean#L18) |
| `ScalarMonotone.EndOfPaper.twoBranchFunction_measurable` | [EndOfPaper/TwoBranchProbability.lean:21](../EndOfPaper/TwoBranchProbability.lean#L21) |
| `ScalarMonotone.EndOfPaper.twoBranchMeasure_probability` | [EndOfPaper/TwoBranchProbability.lean:27](../EndOfPaper/TwoBranchProbability.lean#L27) |
| `ScalarMonotone.EndOfPaper.twoBranchFunction_law` | [EndOfPaper/TwoBranchProbability.lean:41](../EndOfPaper/TwoBranchProbability.lean#L41) |
| `ScalarMonotone.EndOfPaper.twoBranchMeasure_real` | [EndOfPaper/TwoBranchProbability.lean:58](../EndOfPaper/TwoBranchProbability.lean#L58) |
| `ScalarMonotone.EndOfPaper.twoBranchMeasure_lower` | [EndOfPaper/TwoBranchProbability.lean:75](../EndOfPaper/TwoBranchProbability.lean#L75) |
| `ScalarMonotone.EndOfPaper.affine_uniform_segment` | [EndOfPaper/UniformTailMixture.lean:14](../EndOfPaper/UniformTailMixture.lean#L14) |
| `ScalarMonotone.EndOfPaper.uniform_split` | [EndOfPaper/UniformTailMixture.lean:46](../EndOfPaper/UniformTailMixture.lean#L46) |
| `ScalarMonotone.EndOfPaper.quantile_law_split` | [EndOfPaper/UniformTailMixture.lean:74](../EndOfPaper/UniformTailMixture.lean#L74) |
| `ScalarMonotone.EndOfPaper.replicatedHardyEnvelope` | [EndOfPaper/ReplicatedHardyEnvelope.lean:15](../EndOfPaper/ReplicatedHardyEnvelope.lean#L15) |
| `ScalarMonotone.EndOfPaper.replicatedHardyEnvelope_properties` | [EndOfPaper/ReplicatedHardyEnvelope.lean:18](../EndOfPaper/ReplicatedHardyEnvelope.lean#L18) |
| `ScalarMonotone.EndOfPaper.replicatedHardyEnvelope_singletons` | [EndOfPaper/ReplicatedHardyEnvelope.lean:44](../EndOfPaper/ReplicatedHardyEnvelope.lean#L44) |
| `ScalarMonotone.EndOfPaper.replicatedHardyEnvelope_selection_value` | [EndOfPaper/ReplicatedHardyEnvelope.lean:50](../EndOfPaper/ReplicatedHardyEnvelope.lean#L50) |
| `ScalarMonotone.EndOfPaper.tailQuantile_le_quantileHardy` | [EndOfPaper/ReplicatedHardyEnvelope.lean:60](../EndOfPaper/ReplicatedHardyEnvelope.lean#L60) |
| `ScalarMonotone.EndOfPaper.replicated_average_hardy_values` | [EndOfPaper/ReplicatedHardyValues.lean:14](../EndOfPaper/ReplicatedHardyValues.lean#L14) |
| `ScalarMonotone.EndOfPaper.quantileReplica` | [EndOfPaper/ReplicatedQuantileCoupling.lean:18](../EndOfPaper/ReplicatedQuantileCoupling.lean#L18) |
| `ScalarMonotone.EndOfPaper.replicaAverage` | [EndOfPaper/ReplicatedQuantileCoupling.lean:22](../EndOfPaper/ReplicatedQuantileCoupling.lean#L22) |
| `ScalarMonotone.EndOfPaper.quantileReplica_measurable` | [EndOfPaper/ReplicatedQuantileCoupling.lean:26](../EndOfPaper/ReplicatedQuantileCoupling.lean#L26) |
| `ScalarMonotone.EndOfPaper.quantileReplica_law` | [EndOfPaper/ReplicatedQuantileCoupling.lean:33](../EndOfPaper/ReplicatedQuantileCoupling.lean#L33) |
| `ScalarMonotone.EndOfPaper.quantileReplica_integrable` | [EndOfPaper/ReplicatedQuantileCoupling.lean:56](../EndOfPaper/ReplicatedQuantileCoupling.lean#L56) |
| `ScalarMonotone.EndOfPaper.replicaAverage_measurable` | [EndOfPaper/ReplicatedQuantileCoupling.lean:66](../EndOfPaper/ReplicatedQuantileCoupling.lean#L66) |
| `ScalarMonotone.EndOfPaper.replicaAverage_true` | [EndOfPaper/ReplicatedQuantileCoupling.lean:72](../EndOfPaper/ReplicatedQuantileCoupling.lean#L72) |
| `ScalarMonotone.EndOfPaper.replicaAverage_true_limit` | [EndOfPaper/ReplicatedQuantileCoupling.lean:81](../EndOfPaper/ReplicatedQuantileCoupling.lean#L81) |
| `ScalarMonotone.EndOfPaper.replicaAverage_near_mean` | [EndOfPaper/ReplicatedQuantileCoupling.lean:93](../EndOfPaper/ReplicatedQuantileCoupling.lean#L93) |
| `ScalarMonotone.EndOfPaper.replicated_average_operator_bound` | [EndOfPaper/ReplicatedHardyUpper.lean:15](../EndOfPaper/ReplicatedHardyUpper.lean#L15) |
| `ScalarMonotone.EndOfPaper.replicatedQuantileFamily` | [EndOfPaper/ReplicatedQuantileFamily.lean:17](../EndOfPaper/ReplicatedQuantileFamily.lean#L17) |
| `ScalarMonotone.EndOfPaper.lift_probability_profile_law` | [EndOfPaper/ReplicatedQuantileFamily.lean:26](../EndOfPaper/ReplicatedQuantileFamily.lean#L26) |
| `ScalarMonotone.EndOfPaper.replicatedQuantileFamily_of_model` | [EndOfPaper/ReplicatedQuantileFamily.lean:34](../EndOfPaper/ReplicatedQuantileFamily.lean#L34) |
| `ScalarMonotone.EndOfPaper.replicatedQuantileFamily_nonempty` | [EndOfPaper/ReplicatedQuantileFamily.lean:56](../EndOfPaper/ReplicatedQuantileFamily.lean#L56) |
| `ScalarMonotone.EndOfPaper.replicatedQuantileFamily_domains` | [EndOfPaper/ReplicatedQuantileFamily.lean:78](../EndOfPaper/ReplicatedQuantileFamily.lean#L78) |
| `ScalarMonotone.EndOfPaper.replicatedQuantileFamily_upper` | [EndOfPaper/ReplicatedQuantileFamily.lean:92](../EndOfPaper/ReplicatedQuantileFamily.lean#L92) |
| `ScalarMonotone.EndOfPaper.replicatedQuantileFamily_near` | [EndOfPaper/ReplicatedQuantileEnvelope.lean:16](../EndOfPaper/ReplicatedQuantileEnvelope.lean#L16) |
| `ScalarMonotone.EndOfPaper.replicated_quantile_envelope_isLUB` | [EndOfPaper/ReplicatedQuantileEnvelope.lean:68](../EndOfPaper/ReplicatedQuantileEnvelope.lean#L68) |
| `ScalarMonotone.EndOfPaper.universal_replicated_quantile_envelope` | [EndOfPaper/ReplicatedQuantileEnvelope.lean:79](../EndOfPaper/ReplicatedQuantileEnvelope.lean#L79) |
<a id="result-3-1"></a>

## Definition 3.1

[PDF page 46](../manuscript/monotone_calculus.pdf#page=46). Geometric Hardy transform

Exactly the original maximal nonnegative interior profile with domain interior (0,1) and finite positive-log area for an arbitrary scalar selection. The auxiliary construction works on every finite initial interval. No global measurability, global log L1, strict positivity or endpoint sign is imposed on the original selection/profile. The actual zero-floor/logarithm/Hardy/exponential construction has its unique maximal nonnegative extension and literal zero convention. geometric_hardy_scalar_completion identifies its whole graph with the maximal completion on the closed initial interval of the classical extended-log geometric mean. Every admissible prefix excludes the undefined infinity-minus-infinity case. geometricPrefixValue_of_extended_integral identifies the expression exactly with exp(A/p), where negative-infinite area gives zero. The correspondence includes both outward endpoints and internal jump intervals. Derive local logarithmic L1 from finite log parts; use closed-graph limits for finite-negative-area boundaries and zero continuation outside the logarithmic interior for infinite negative area. Transfer every prefix integral between selections by AE equality. Identify the entire graph by the unique maximal completion of the scalar selection. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.zero_mem_of_equal_positive_parts` | [EndOfPaper/NonnegativeGraphFibers.lean:14](../EndOfPaper/NonnegativeGraphFibers.lean#L14) |
| `ScalarMonotone.EndOfPaper.nonnegative_closed_intervals_eq` | [EndOfPaper/NonnegativeGraphFibers.lean:31](../EndOfPaper/NonnegativeGraphFibers.lean#L31) |
| `ScalarMonotone.EndOfPaper.maximal_decreasing_bounded_dom_range` | [EndOfPaper/NonnegativeGraphFibers.lean:49](../EndOfPaper/NonnegativeGraphFibers.lean#L49) |
| `ScalarMonotone.EndOfPaper.nonnegative_initial_graph_eq_of_log_eq` | [EndOfPaper/NonnegativeGraphFibers.lean:62](../EndOfPaper/NonnegativeGraphFibers.lean#L62) |
| `ScalarMonotone.EndOfPaper.logarithmicInputGraph` | [EndOfPaper/ExponentialCompletion.lean:15](../EndOfPaper/ExponentialCompletion.lean#L15) |
| `ScalarMonotone.EndOfPaper.logarithmicInputGraph_decreasing` | [EndOfPaper/ExponentialCompletion.lean:18](../EndOfPaper/ExponentialCompletion.lean#L18) |
| `ScalarMonotone.EndOfPaper.logarithmicInputGraph_dom` | [EndOfPaper/ExponentialCompletion.lean:35](../EndOfPaper/ExponentialCompletion.lean#L35) |
| `ScalarMonotone.EndOfPaper.nonnegative_exponential_completion` | [EndOfPaper/ExponentialCompletion.lean:52](../EndOfPaper/ExponentialCompletion.lean#L52) |
| `ScalarMonotone.EndOfPaper.initial_exponential_completion_exists` | [EndOfPaper/ExponentialCompletion.lean:141](../EndOfPaper/ExponentialCompletion.lean#L141) |
| `ScalarMonotone.EndOfPaper.initial_exponential_completion_unique` | [EndOfPaper/ExponentialCompletion.lean:229](../EndOfPaper/ExponentialCompletion.lean#L229) |
| `ScalarMonotone.EndOfPaper.unique_initial_exponential_completion` | [EndOfPaper/ExponentialCompletion.lean:250](../EndOfPaper/ExponentialCompletion.lean#L250) |
| `ScalarMonotone.EndOfPaper.nonnegativeFloorGraph` | [EndOfPaper/LogGeometricDomain.lean:17](../EndOfPaper/LogGeometricDomain.lean#L17) |
| `ScalarMonotone.EndOfPaper.nonnegativeFloorGraph_resolvent` | [EndOfPaper/LogGeometricDomain.lean:19](../EndOfPaper/LogGeometricDomain.lean#L19) |
| `ScalarMonotone.EndOfPaper.nonnegativeFloorGraph_nonnegative` | [EndOfPaper/LogGeometricDomain.lean:27](../EndOfPaper/LogGeometricDomain.lean#L27) |
| `ScalarMonotone.EndOfPaper.nonnegativeFloorGraph_positive_fibers` | [EndOfPaper/LogGeometricDomain.lean:36](../EndOfPaper/LogGeometricDomain.lean#L36) |
| `ScalarMonotone.EndOfPaper.logarithm_nonnegative_floor` | [EndOfPaper/LogGeometricDomain.lean:52](../EndOfPaper/LogGeometricDomain.lean#L52) |
| `ScalarMonotone.EndOfPaper.bounded_domain_logarithm_maximal` | [EndOfPaper/LogGeometricDomain.lean:59](../EndOfPaper/LogGeometricDomain.lean#L59) |
| `ScalarMonotone.EndOfPaper.logarithm_dom_subset` | [EndOfPaper/LogGeometricDomain.lean:72](../EndOfPaper/LogGeometricDomain.lean#L72) |
| `ScalarMonotone.EndOfPaper.positive_initial_interval_in_log_dom` | [EndOfPaper/LogGeometricDomain.lean:76](../EndOfPaper/LogGeometricDomain.lean#L76) |
| `ScalarMonotone.EndOfPaper.logarithm_initial_domain` | [EndOfPaper/LogGeometricDomain.lean:87](../EndOfPaper/LogGeometricDomain.lean#L87) |
| `ScalarMonotone.EndOfPaper.positive_log_integrable_of_lintegral` | [EndOfPaper/LogGeometricDomain.lean:117](../EndOfPaper/LogGeometricDomain.lean#L117) |
| `ScalarMonotone.EndOfPaper.logarithmic_prefix_integrable_of_positive_part` | [EndOfPaper/LogGeometricDomain.lean:127](../EndOfPaper/LogGeometricDomain.lean#L127) |
| `ScalarMonotone.EndOfPaper.logarithmic_selection_on_interior` | [EndOfPaper/LogGeometricDomain.lean:155](../EndOfPaper/LogGeometricDomain.lean#L155) |
| `ScalarMonotone.EndOfPaper.logarithmic_prefix_integrability` | [EndOfPaper/LogGeometricDomain.lean:173](../EndOfPaper/LogGeometricDomain.lean#L173) |
| `ScalarMonotone.EndOfPaper.raw_exponential_le_iff` | [EndOfPaper/GeometricHardy.lean:15](../EndOfPaper/GeometricHardy.lean#L15) |
| `ScalarMonotone.EndOfPaper.positive_geometric_hardy_extension` | [EndOfPaper/GeometricHardy.lean:26](../EndOfPaper/GeometricHardy.lean#L26) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_extension_of_nonzero` | [EndOfPaper/GeometricHardy.lean:63](../EndOfPaper/GeometricHardy.lean#L63) |
| `ScalarMonotone.EndOfPaper.geometricHardyExtensionPredicate` | [EndOfPaper/GeometricHardy.lean:82](../EndOfPaper/GeometricHardy.lean#L82) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform` | [EndOfPaper/GeometricHardy.lean:90](../EndOfPaper/GeometricHardy.lean#L90) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_zero` | [EndOfPaper/GeometricHardy.lean:95](../EndOfPaper/GeometricHardy.lean#L95) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_well_defined` | [EndOfPaper/GeometricHardy.lean:100](../EndOfPaper/GeometricHardy.lean#L100) |
| `ScalarMonotone.EndOfPaper.nonnegative_log_singleton_fiber` | [EndOfPaper/NonnegativeExponentialFibers.lean:13](../EndOfPaper/NonnegativeExponentialFibers.lean#L13) |
| `ScalarMonotone.EndOfPaper.nonnegative_log_empty_fiber` | [EndOfPaper/NonnegativeExponentialFibers.lean:29](../EndOfPaper/NonnegativeExponentialFibers.lean#L29) |
| `ScalarMonotone.EndOfPaper.nonnegative_log_upper_ray_fiber` | [EndOfPaper/NonnegativeExponentialFibers.lean:45](../EndOfPaper/NonnegativeExponentialFibers.lean#L45) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_logarithm` | [EndOfPaper/GeometricHardyOrder.lean:77](../EndOfPaper/GeometricHardyOrder.lean#L77) |
| `ScalarMonotone.EndOfPaper.measurable_selection_same_positive_log_area` | [EndOfPaper/GeometricHardySelections.lean:14](../EndOfPaper/GeometricHardySelections.lean#L14) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_extension_any_selection` | [EndOfPaper/GeometricHardySelections.lean:29](../EndOfPaper/GeometricHardySelections.lean#L29) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_well_defined_any_selection` | [EndOfPaper/GeometricHardySelections.lean:42](../EndOfPaper/GeometricHardySelections.lean#L42) |
| `ScalarMonotone.EndOfPaper.extendedLogIntegral` | [EndOfPaper/ExtendedLogMean.lean:21](../EndOfPaper/ExtendedLogMean.lean#L21) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue` | [EndOfPaper/ExtendedLogMean.lean:28](../EndOfPaper/ExtendedLogMean.lean#L28) |
| `ScalarMonotone.EndOfPaper.extendedLogIntegral_defined_of_finite_positive_area` | [EndOfPaper/ExtendedLogMean.lean:33](../EndOfPaper/ExtendedLogMean.lean#L33) |
| `ScalarMonotone.EndOfPaper.extendedLogIntegral_of_integrable` | [EndOfPaper/ExtendedLogMean.lean:40](../EndOfPaper/ExtendedLogMean.lean#L40) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_of_integrable` | [EndOfPaper/ExtendedLogMean.lean:57](../EndOfPaper/ExtendedLogMean.lean#L57) |
| `ScalarMonotone.EndOfPaper.extendedLogIntegral_of_negative_area_top` | [EndOfPaper/ExtendedLogMean.lean:66](../EndOfPaper/ExtendedLogMean.lean#L66) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_of_negative_area_top` | [EndOfPaper/ExtendedLogMean.lean:72](../EndOfPaper/ExtendedLogMean.lean#L72) |
| `ScalarMonotone.EndOfPaper.hardyScalar_tendsto_left_of_intervalIntegrable` | [EndOfPaper/HardyBoundaryContinuity.lean:14](../EndOfPaper/HardyBoundaryContinuity.lean#L14) |
| `ScalarMonotone.EndOfPaper.decreasing_right_boundary_fiber_of_tendsto` | [EndOfPaper/HardyBoundaryContinuity.lean:32](../EndOfPaper/HardyBoundaryContinuity.lean#L32) |
| `ScalarMonotone.EndOfPaper.positive_log_prefix_area_finite` | [EndOfPaper/LogarithmicFiniteParts.lean:22](../EndOfPaper/LogarithmicFiniteParts.lean#L22) |
| `ScalarMonotone.EndOfPaper.negative_log_area_finite_of_integrable` | [EndOfPaper/LogarithmicFiniteParts.lean:32](../EndOfPaper/LogarithmicFiniteParts.lean#L32) |
| `ScalarMonotone.EndOfPaper.positive_prefix_of_finite_negative_log_area` | [EndOfPaper/LogarithmicFiniteParts.lean:52](../EndOfPaper/LogarithmicFiniteParts.lean#L52) |
| `ScalarMonotone.EndOfPaper.logarithm_integrable_of_finite_log_parts` | [EndOfPaper/LogarithmicFiniteParts.lean:68](../EndOfPaper/LogarithmicFiniteParts.lean#L68) |
| `ScalarMonotone.EndOfPaper.prefix_log_domain_of_finite_negative_area` | [EndOfPaper/LogarithmicFiniteParts.lean:95](../EndOfPaper/LogarithmicFiniteParts.lean#L95) |
| `ScalarMonotone.EndOfPaper.logarithm_prefix_integrable_of_finite_negative_area` | [EndOfPaper/LogarithmicFiniteParts.lean:111](../EndOfPaper/LogarithmicFiniteParts.lean#L111) |
| `ScalarMonotone.EndOfPaper.initial_profile_eq_completed_scalar` | [EndOfPaper/GeometricScalarCompletion.lean:20](../EndOfPaper/GeometricScalarCompletion.lean#L20) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_congr_ae` | [EndOfPaper/GeometricScalarCompletion.lean:50](../EndOfPaper/GeometricScalarCompletion.lean#L50) |
| `ScalarMonotone.EndOfPaper.raw_positive_log_prefix_finite` | [EndOfPaper/GeometricScalarCompletion.lean:64](../EndOfPaper/GeometricScalarCompletion.lean#L64) |
| `ScalarMonotone.EndOfPaper.geometric_log_hardy_scalar_data` | [EndOfPaper/GeometricScalarCompletion.lean:72](../EndOfPaper/GeometricScalarCompletion.lean#L72) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_positive_interior_fiber` | [EndOfPaper/GeometricScalarCompletion.lean:101](../EndOfPaper/GeometricScalarCompletion.lean#L101) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_zero_mem_outside_log_interior` | [EndOfPaper/GeometricScalarCompletion.lean:118](../EndOfPaper/GeometricScalarCompletion.lean#L118) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_finite_prefix_mem` | [EndOfPaper/GeometricScalarCompletion.lean:157](../EndOfPaper/GeometricScalarCompletion.lean#L157) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_scalar_selection_measurable` | [EndOfPaper/GeometricScalarCompletion.lean:184](../EndOfPaper/GeometricScalarCompletion.lean#L184) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_scalar_selection` | [EndOfPaper/GeometricScalarCompletion.lean:218](../EndOfPaper/GeometricScalarCompletion.lean#L218) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_scalar_completion` | [EndOfPaper/GeometricScalarCompletion.lean:233](../EndOfPaper/GeometricScalarCompletion.lean#L233) |
| `ScalarMonotone.EndOfPaper.extendedLogIntegral_defined_on_admissible_prefix` | [EndOfPaper/GeometricScalarCompletion.lean:244](../EndOfPaper/GeometricScalarCompletion.lean#L244) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_of_extended_integral` | [EndOfPaper/GeometricScalarCompletion.lean:264](../EndOfPaper/GeometricScalarCompletion.lean#L264) |
<a id="result-3-2"></a>

## Example 3.2

[PDF page 47](../manuscript/monotone_calculus.pdf#page=47). A zero-induced jump of the geometric average

The actual maximal completion of max(1-2u,0) on (0,1), constructed explicitly, with its exact interior singleton fibers and positive-log area equal to zero. No assumption about the desired transform is used. The logarithmic interior is exactly (0,1/2). The actual geometric graph has the displayed exponential/power singleton on (0,1/2), left limit exp(-1), complete jump fiber [0,exp(-1)] at 1/2 and zero singleton afterward. The actual arithmetic Hardy graph has singleton values 1-u up to 1/2 and 1/(4u) afterward. The ordinary log integral to 1/2 is exactly -1/2, while every later negative-log area is infinite. The reader independently checks equality with the canonical whole maximal scalar completion. Use the continuous scalar completion and exact affine-log primitive. Identify the actual logarithmic Hardy fibers, pass to the full right endpoint ray Iic(-1), and recover the nonnegative exponential interval. The graph left limit follows from the checked scalar limit and actual interior fibers. Split the arithmetic prefix integral at 1/2. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.negativeLogWithZero` | [EndOfPaper/ExtendedLogZero.lean:14](../EndOfPaper/ExtendedLogZero.lean#L14) |
| `ScalarMonotone.EndOfPaper.negativeLogWithZero_zero` | [EndOfPaper/ExtendedLogZero.lean:17](../EndOfPaper/ExtendedLogZero.lean#L17) |
| `ScalarMonotone.EndOfPaper.negativeLogWithZero_of_pos` | [EndOfPaper/ExtendedLogZero.lean:20](../EndOfPaper/ExtendedLogZero.lean#L20) |
| `ScalarMonotone.EndOfPaper.negative_log_area_eq_top_of_zero_interval` | [EndOfPaper/ExtendedLogZero.lean:24](../EndOfPaper/ExtendedLogZero.lean#L24) |
| `ScalarMonotone.EndOfPaper.zero_ramp_negative_log_after_half` | [EndOfPaper/ExtendedLogZero.lean:50](../EndOfPaper/ExtendedLogZero.lean#L50) |
| `ScalarMonotone.EndOfPaper.zeroRamp` | [EndOfPaper/ZeroRampScalar.lean:15](../EndOfPaper/ZeroRampScalar.lean#L15) |
| `ScalarMonotone.EndOfPaper.zeroRamp_nonnegative` | [EndOfPaper/ZeroRampScalar.lean:17](../EndOfPaper/ZeroRampScalar.lean#L17) |
| `ScalarMonotone.EndOfPaper.zeroRamp_continuous` | [EndOfPaper/ZeroRampScalar.lean:19](../EndOfPaper/ZeroRampScalar.lean#L19) |
| `ScalarMonotone.EndOfPaper.zeroRamp_antitone` | [EndOfPaper/ZeroRampScalar.lean:23](../EndOfPaper/ZeroRampScalar.lean#L23) |
| `ScalarMonotone.EndOfPaper.zeroRamp_log_affine_integrable` | [EndOfPaper/ZeroRampScalar.lean:27](../EndOfPaper/ZeroRampScalar.lean#L27) |
| `ScalarMonotone.EndOfPaper.zeroRamp_log_affine_integral` | [EndOfPaper/ZeroRampScalar.lean:33](../EndOfPaper/ZeroRampScalar.lean#L33) |
| `ScalarMonotone.EndOfPaper.zeroRamp_log_half_integral` | [EndOfPaper/ZeroRampScalar.lean:41](../EndOfPaper/ZeroRampScalar.lean#L41) |
| `ScalarMonotone.EndOfPaper.zeroRamp_log_hardy_formula` | [EndOfPaper/ZeroRampScalar.lean:46](../EndOfPaper/ZeroRampScalar.lean#L46) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_prefix_formula` | [EndOfPaper/ZeroRampScalar.lean:53](../EndOfPaper/ZeroRampScalar.lean#L53) |
| `ScalarMonotone.EndOfPaper.initial_profile_eq_completed_scalar` | [EndOfPaper/GeometricScalarCompletion.lean:20](../EndOfPaper/GeometricScalarCompletion.lean#L20) |
| `ScalarMonotone.EndOfPaper.zeroRampOperator` | [EndOfPaper/ZeroRampModel.lean:20](../EndOfPaper/ZeroRampModel.lean#L20) |
| `ScalarMonotone.EndOfPaper.zeroRampOperator_properties` | [EndOfPaper/ZeroRampModel.lean:23](../EndOfPaper/ZeroRampModel.lean#L23) |
| `ScalarMonotone.EndOfPaper.zeroRampProfile` | [EndOfPaper/ZeroRampModel.lean:45](../EndOfPaper/ZeroRampModel.lean#L45) |
| `ScalarMonotone.EndOfPaper.zeroRampProfile_selection` | [EndOfPaper/ZeroRampModel.lean:47](../EndOfPaper/ZeroRampModel.lean#L47) |
| `ScalarMonotone.EndOfPaper.zeroRampProfile_nonnegative` | [EndOfPaper/ZeroRampModel.lean:52](../EndOfPaper/ZeroRampModel.lean#L52) |
| `ScalarMonotone.EndOfPaper.zeroRamp_positive_log_area` | [EndOfPaper/ZeroRampModel.lean:59](../EndOfPaper/ZeroRampModel.lean#L59) |
| `ScalarMonotone.EndOfPaper.zeroRampProfile_nonzero` | [EndOfPaper/ZeroRampModel.lean:69](../EndOfPaper/ZeroRampModel.lean#L69) |
| `ScalarMonotone.EndOfPaper.zeroRamp_log_domain` | [EndOfPaper/ZeroRampModel.lean:75](../EndOfPaper/ZeroRampModel.lean#L75) |
| `ScalarMonotone.EndOfPaper.zeroRamp_integral_before_half` | [EndOfPaper/ZeroRampModel.lean:105](../EndOfPaper/ZeroRampModel.lean#L105) |
| `ScalarMonotone.EndOfPaper.zeroRamp_integral_after_half` | [EndOfPaper/ZeroRampModel.lean:120](../EndOfPaper/ZeroRampModel.lean#L120) |
| `ScalarMonotone.EndOfPaper.zeroRamp_hardy_before_half` | [EndOfPaper/ZeroRampModel.lean:138](../EndOfPaper/ZeroRampModel.lean#L138) |
| `ScalarMonotone.EndOfPaper.zeroRamp_hardy_after_half` | [EndOfPaper/ZeroRampModel.lean:144](../EndOfPaper/ZeroRampModel.lean#L144) |
| `ScalarMonotone.EndOfPaper.zeroRamp_hardy_fibers` | [EndOfPaper/ZeroRampModel.lean:149](../EndOfPaper/ZeroRampModel.lean#L149) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_log_data` | [EndOfPaper/ZeroRampModel.lean:165](../EndOfPaper/ZeroRampModel.lean#L165) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_before_half` | [EndOfPaper/ZeroRampModel.lean:203](../EndOfPaper/ZeroRampModel.lean#L203) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_jump` | [EndOfPaper/ZeroRampModel.lean:220](../EndOfPaper/ZeroRampModel.lean#L220) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_after_half` | [EndOfPaper/ZeroRampModel.lean:250](../EndOfPaper/ZeroRampModel.lean#L250) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_left_limit` | [EndOfPaper/ZeroRampModel.lean:268](../EndOfPaper/ZeroRampModel.lean#L268) |
| `ScalarMonotone.EndOfPaper.zeroRamp_geometric_graph_left_limit` | [EndOfPaper/ZeroRampModel.lean:279](../EndOfPaper/ZeroRampModel.lean#L279) |
<a id="result-3-3"></a>

## Lemma 3.3

[PDF page 48](../manuscript/monotone_calculus.pdf#page=48). The geometric Hardy profile lies between the original and arithmetic Hardy profiles.

Exactly the manuscript nonnegative maximal profiles on the common initial interval with finite positive-log area for arbitrary selections. Ordinary integrability is existence of an integrable selection and is required only for the upper arithmetic comparison. The final statements add no global measurability, global log integrability, endpoint nonnegativity or strict positivity. Both whole completed inequalities q <= G(q) <= H(q), with the upper inequality conditional only on ordinary L1, and whole order preservation G(q) <= G(r) whenever q <= r. Zero profiles, internal zeros, jumps and outward endpoint fibers are included. Derive measurable representatives with exactly equal positive-log area and transfer ordinary L1 from any selection by AE equality. Apply logarithmic order reflection, actual Hardy domination and Jensen on positive prefixes. The manuscript-facing wrappers discharge all additional local hypotheses. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.geometric_average_le_arithmetic` | [EndOfPaper/GeometricMeanJensen.lean:16](../EndOfPaper/GeometricMeanJensen.lean#L16) |
| `ScalarMonotone.EndOfPaper.logarithm_preserves_decLE` | [EndOfPaper/GeometricHardyOrder.lean:14](../EndOfPaper/GeometricHardyOrder.lean#L14) |
| `ScalarMonotone.EndOfPaper.logarithm_reflects_initial_decLE` | [EndOfPaper/GeometricHardyOrder.lean:21](../EndOfPaper/GeometricHardyOrder.lean#L21) |
| `ScalarMonotone.EndOfPaper.nonzero_geometric_log_hardy_properties` | [EndOfPaper/GeometricHardyOrder.lean:57](../EndOfPaper/GeometricHardyOrder.lean#L57) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_logarithm` | [EndOfPaper/GeometricHardyOrder.lean:77](../EndOfPaper/GeometricHardyOrder.lean#L77) |
| `ScalarMonotone.EndOfPaper.le_geometricHardyTransform` | [EndOfPaper/GeometricHardyOrder.lean:94](../EndOfPaper/GeometricHardyOrder.lean#L94) |
| `ScalarMonotone.EndOfPaper.positive_graph_value_of_nonzero` | [EndOfPaper/GeometricHardyOrder.lean:111](../EndOfPaper/GeometricHardyOrder.lean#L111) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_mono` | [EndOfPaper/GeometricHardyOrder.lean:120](../EndOfPaper/GeometricHardyOrder.lean#L120) |
| `ScalarMonotone.EndOfPaper.measurable_selection_same_positive_log_area` | [EndOfPaper/GeometricHardySelections.lean:14](../EndOfPaper/GeometricHardySelections.lean#L14) |
| `ScalarMonotone.EndOfPaper.initial_profile_hardy_data` | [EndOfPaper/GeometricHardyArithmetic.lean:16](../EndOfPaper/GeometricHardyArithmetic.lean#L16) |
| `ScalarMonotone.EndOfPaper.initial_profile_hardy_nonnegative` | [EndOfPaper/GeometricHardyArithmetic.lean:47](../EndOfPaper/GeometricHardyArithmetic.lean#L47) |
| `ScalarMonotone.EndOfPaper.hardy_log_le_log_hardy` | [EndOfPaper/GeometricHardyArithmetic.lean:67](../EndOfPaper/GeometricHardyArithmetic.lean#L67) |
| `ScalarMonotone.EndOfPaper.geometricHardyTransform_le_hardy` | [EndOfPaper/GeometricHardyArithmetic.lean:122](../EndOfPaper/GeometricHardyArithmetic.lean#L122) |
| `ScalarMonotone.EndOfPaper.hardy_geometric_comparison` | [EndOfPaper/GeometricHardyArithmetic.lean:146](../EndOfPaper/GeometricHardyArithmetic.lean#L146) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_order_preserving` | [EndOfPaper/GeometricHardyArithmetic.lean:164](../EndOfPaper/GeometricHardyArithmetic.lean#L164) |
<a id="result-3-4"></a>

## Lemma 3.4

[PDF page 49](../manuscript/monotone_calculus.pdf#page=49). Pólya–Knopp inequality

Exactly the admissible nonnegative maximal profile on (0,1), finite positive-log area under an arbitrary input selection, every r>0 and every 0<a<=1. The auxiliary formulation works on any finite initial interval. Input and output selections are arbitrary. Neither a finite moment, global log L1, strict positivity nor global measurability of either original selection is imposed. polya_knopp proves the original extended nonnegative moment inequality integral_0^a G(q)^r <= e integral_0^a q^r, including infinite moments and zeros. Its actual completed transform is used; selection independence is derived by AE equality. ENNReal.ofReal represents the nonnegative powers, whose nonnegativity follows from the profile and transform interior properties. Apply weighted Jensen to x*s(x)^r on finite-negative-log prefixes, and use zero for infinite negative area. Derive all local power L1 only when the right-hand moment is finite. Prove the reciprocal-square kernel integral and use Tonelli for arbitrary extended nonnegative functions. Transfer the final scalar bound to arbitrary selections of the actual completed graphs by AE equality. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.weighted_log_prefix_integrable` | [EndOfPaper/KnoppWeightedJensen.lean:15](../EndOfPaper/KnoppWeightedJensen.lean#L15) |
| `ScalarMonotone.EndOfPaper.weighted_log_hardy_identity` | [EndOfPaper/KnoppWeightedJensen.lean:26](../EndOfPaper/KnoppWeightedJensen.lean#L26) |
| `ScalarMonotone.EndOfPaper.geometric_weighted_prefix_upper` | [EndOfPaper/KnoppWeightedJensen.lean:43](../EndOfPaper/KnoppWeightedJensen.lean#L43) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_scalar_completion` | [EndOfPaper/GeometricScalarCompletion.lean:233](../EndOfPaper/GeometricScalarCompletion.lean#L233) |
| `ScalarMonotone.EndOfPaper.knopp_kernel_integrable` | [EndOfPaper/PolyaKnopp.lean:17](../EndOfPaper/PolyaKnopp.lean#L17) |
| `ScalarMonotone.EndOfPaper.knopp_kernel_lintegral` | [EndOfPaper/PolyaKnopp.lean:23](../EndOfPaper/PolyaKnopp.lean#L23) |
| `ScalarMonotone.EndOfPaper.knopp_kernel_prefix_bound` | [EndOfPaper/PolyaKnopp.lean:39](../EndOfPaper/PolyaKnopp.lean#L39) |
| `ScalarMonotone.EndOfPaper.knopp_weighted_lintegral_bound` | [EndOfPaper/PolyaKnopp.lean:52](../EndOfPaper/PolyaKnopp.lean#L52) |
| `ScalarMonotone.EndOfPaper.logarithmic_power_prefix_integrable` | [EndOfPaper/PolyaKnopp.lean:104](../EndOfPaper/PolyaKnopp.lean#L104) |
| `ScalarMonotone.EndOfPaper.hardy_log_power_prefix` | [EndOfPaper/PolyaKnopp.lean:113](../EndOfPaper/PolyaKnopp.lean#L113) |
| `ScalarMonotone.EndOfPaper.geometric_power_weighted_prefix_upper` | [EndOfPaper/PolyaKnopp.lean:127](../EndOfPaper/PolyaKnopp.lean#L127) |
| `ScalarMonotone.EndOfPaper.knopp_weighted_ofReal_prefix` | [EndOfPaper/PolyaKnopp.lean:158](../EndOfPaper/PolyaKnopp.lean#L158) |
| `ScalarMonotone.EndOfPaper.polya_knopp_scalar_measurable` | [EndOfPaper/PolyaKnopp.lean:189](../EndOfPaper/PolyaKnopp.lean#L189) |
| `ScalarMonotone.EndOfPaper.polya_knopp` | [EndOfPaper/PolyaKnopp.lean:234](../EndOfPaper/PolyaKnopp.lean#L234) |
<a id="result-3-5"></a>

## Lemma 3.5

[PDF page 49](../manuscript/monotone_calculus.pdf#page=49). Logarithmic endpoint control

Exactly the original metric-valued measurable random variable and independent copy, maximal decreasing qDelta with (0,1) contained in its domain interior, interior nonnegativity, quantile comparison for every real 1-Lipschitz function, measurable h and nonnegative U with finite expectation, and C>0 with the original pointwise logarithmic modulus. Finite expectation is expressed as a finite nonnegative ENNReal integral; ordinary L1 is derived. No integrability of h, atomlessness, second countability or equality of the profile domain is added. logarithmic_endpoint_control proves the exact strict-tail probability bound a+2m/s for every 0<a<1, s>0 and t in qDelta(a), on the original probability space. Both independent copies retain their actual prescribed law. Construct both extremal extensions on each nonempty sublevel, treat the empty sublevel explicitly, and use the actual quantile tail test after positive Lipschitz normalization. Exchangeability and the pointwise two-tail count give the exact restricted bound a. Reflect the larger cutoffs, integrate all cutoff levels, and derive both L1 controls and equality of their means from identical distributions. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.upperLipschitzExtension` | [EndOfPaper/LipschitzBrackets.lean:15](../EndOfPaper/LipschitzBrackets.lean#L15) |
| `ScalarMonotone.EndOfPaper.upperLipschitzExtension_properties` | [EndOfPaper/LipschitzBrackets.lean:19](../EndOfPaper/LipschitzBrackets.lean#L19) |
| `ScalarMonotone.EndOfPaper.lipschitz_extremal_brackets` | [EndOfPaper/LipschitzBrackets.lean:52](../EndOfPaper/LipschitzBrackets.lean#L52) |
| `ScalarMonotone.EndOfPaper.multiplicative_control_lipschitz_on_sublevel` | [EndOfPaper/LipschitzBrackets.lean:83](../EndOfPaper/LipschitzBrackets.lean#L83) |
| `ScalarMonotone.EndOfPaper.two_level_lipschitz_brackets` | [EndOfPaper/LipschitzBrackets.lean:96](../EndOfPaper/LipschitzBrackets.lean#L96) |
| `ScalarMonotone.EndOfPaper.bracket_tail_implication` | [EndOfPaper/LipschitzBrackets.lean:115](../EndOfPaper/LipschitzBrackets.lean#L115) |
| `ScalarMonotone.EndOfPaper.bracket_two_tail_indicator_bound` | [EndOfPaper/LipschitzBrackets.lean:130](../EndOfPaper/LipschitzBrackets.lean#L130) |
| `ScalarMonotone.EndOfPaper.cutoff_interval_volume` | [EndOfPaper/CutoffLayerIntegral.lean:16](../EndOfPaper/CutoffLayerIntegral.lean#L16) |
| `ScalarMonotone.EndOfPaper.cutoff_weighted_tail_bound` | [EndOfPaper/CutoffLayerIntegral.lean:45](../EndOfPaper/CutoffLayerIntegral.lean#L45) |
| `ScalarMonotone.EndOfPaper.cutoff_layer_integral` | [EndOfPaper/CutoffLayerIntegral.lean:81](../EndOfPaper/CutoffLayerIntegral.lean#L81) |
| `ScalarMonotone.EndOfPaper.cutoff_averaging_tail_bound` | [EndOfPaper/CutoffLayerIntegral.lean:143](../EndOfPaper/CutoffLayerIntegral.lean#L143) |
| `ScalarMonotone.EndOfPaper.quantile_comparison_strict_tail` | [EndOfPaper/EndpointSymmetry.lean:15](../EndOfPaper/EndpointSymmetry.lean#L15) |
| `ScalarMonotone.EndOfPaper.scaled_lipschitz_tail_of_quantile_control` | [EndOfPaper/EndpointSymmetry.lean:23](../EndOfPaper/EndpointSymmetry.lean#L23) |
| `ScalarMonotone.EndOfPaper.independent_copy_exchangeable` | [EndOfPaper/EndpointSymmetry.lean:50](../EndOfPaper/EndpointSymmetry.lean#L50) |
| `ScalarMonotone.EndOfPaper.exchangeable_real_measure` | [EndOfPaper/EndpointSymmetry.lean:65](../EndOfPaper/EndpointSymmetry.lean#L65) |
| `ScalarMonotone.EndOfPaper.exchangeable_two_set_tail_bound` | [EndOfPaper/EndpointTwoSet.lean:17](../EndOfPaper/EndpointTwoSet.lean#L17) |
| `ScalarMonotone.EndOfPaper.exchangeable_cutoff_symmetry` | [EndOfPaper/EndpointTwoSet.lean:82](../EndOfPaper/EndpointTwoSet.lean#L82) |
| `ScalarMonotone.EndOfPaper.logarithmic_endpoint_cutoff_half` | [EndOfPaper/EndpointControl.lean:16](../EndOfPaper/EndpointControl.lean#L16) |
| `ScalarMonotone.EndOfPaper.logarithmic_endpoint_cutoff` | [EndOfPaper/EndpointControl.lean:54](../EndOfPaper/EndpointControl.lean#L54) |
| `ScalarMonotone.EndOfPaper.logarithmic_endpoint_control` | [EndOfPaper/EndpointControl.lean:73](../EndOfPaper/EndpointControl.lean#L73) |
<a id="result-3-6"></a>

## Theorem 3.6

[PDF page 50](../manuscript/monotone_calculus.pdf#page=50). Geometric Hardy profile and moment bounds for multiplicative random Lipschitz controls.

Exactly the original metric spaces, measurable maps and nonnegative controls, n>=1, independent identically distributed copy, baseline and marginal whole quantile comparisons, and one finite combined positive-log area on arbitrary input selections. Finite input Lr is required only for the moment conclusions, for every real r>0. Individual log areas, representative measurability, prefix integrability and output graph properties are derived. No separability, atomlessness or ordinary L1 of the output is imposed. randomized_lipschitz_control gives the complete original conjunction: the whole completed geometric graph bound at probability u/3 whenever no input vanishes on I, almost sure zero difference when any input vanishes on I, and the actual Lr bound with constant (3*exp(1))^(1/r), together with derived output MemLp. randomized_lipschitz_real_moment_bound gives the finite ordinary norm form. The graph product is the literal finite interior product followed by its unique maximal completion. Quantile jumps, atoms, both endpoints and zero values remain included. Optimized unequal-level estimates, centering and lower sharpness are separate dictionary claims. Combine the original two-parameter tail estimate, exact finite geometric multiplicativity and whole quantile completion. Handle both zero-profile cases by actual original-space arguments, including countable Lipschitz extensions for a zero baseline. For nonzero inputs apply the extended Polya-Knopp moment bound with exact dilation factor three; convert the nonnegative extended moment estimate to actual eLpNorm and MemLp, and then finite real norms. All proof dependencies undergo the unchanged transitive axiom audit. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.le_exp_log_positive_part` | [EndOfPaper/LogarithmicModulus.lean:17](../EndOfPaper/LogarithmicModulus.lean#L17) |
| `ScalarMonotone.EndOfPaper.logarithmic_two_endpoint_factor_bound` | [EndOfPaper/LogarithmicModulus.lean:26](../EndOfPaper/LogarithmicModulus.lean#L26) |
| `ScalarMonotone.EndOfPaper.logarithmic_product_bound` | [EndOfPaper/LogarithmicModulus.lean:38](../EndOfPaper/LogarithmicModulus.lean#L38) |
| `ScalarMonotone.EndOfPaper.logarithmic_control_measurable` | [EndOfPaper/LogarithmicModulus.lean:50](../EndOfPaper/LogarithmicModulus.lean#L50) |
| `ScalarMonotone.EndOfPaper.randomized_modulus_logarithmic_form` | [EndOfPaper/LogarithmicModulus.lean:56](../EndOfPaper/LogarithmicModulus.lean#L56) |
| `ScalarMonotone.EndOfPaper.decLE_selections_ae_le` | [EndOfPaper/ProfileMomentComparison.lean:16](../EndOfPaper/ProfileMomentComparison.lean#L16) |
| `ScalarMonotone.EndOfPaper.profile_selection_lintegral_mono` | [EndOfPaper/ProfileMomentComparison.lean:31](../EndOfPaper/ProfileMomentComparison.lean#L31) |
| `ScalarMonotone.EndOfPaper.random_variable_profile_lintegral_bound` | [EndOfPaper/ProfileMomentComparison.lean:40](../EndOfPaper/ProfileMomentComparison.lean#L40) |
| `ScalarMonotone.EndOfPaper.logarithmic_endpoint_control` | [EndOfPaper/EndpointControl.lean:73](../EndOfPaper/EndpointControl.lean#L73) |
| `ScalarMonotone.EndOfPaper.finite_antitone_common_positive_point` | [EndOfPaper/CommonPositivePrefix.lean:14](../EndOfPaper/CommonPositivePrefix.lean#L14) |
| `ScalarMonotone.EndOfPaper.nonzero_profiles_common_positive_point` | [EndOfPaper/CommonPositivePrefix.lean:39](../EndOfPaper/CommonPositivePrefix.lean#L39) |
| `ScalarMonotone.EndOfPaper.positive_log_part_monotoneOn_nonnegative` | [EndOfPaper/LogarithmicExpectations.lean:15](../EndOfPaper/LogarithmicExpectations.lean#L15) |
| `ScalarMonotone.EndOfPaper.clamped_log_excess_monotone` | [EndOfPaper/LogarithmicExpectations.lean:23](../EndOfPaper/LogarithmicExpectations.lean#L23) |
| `ScalarMonotone.EndOfPaper.logarithmic_excess_lintegral_bound` | [EndOfPaper/LogarithmicExpectations.lean:31](../EndOfPaper/LogarithmicExpectations.lean#L31) |
| `ScalarMonotone.EndOfPaper.logarithmic_excess_integrable` | [EndOfPaper/LogarithmicExpectations.lean:58](../EndOfPaper/LogarithmicExpectations.lean#L58) |
| `ScalarMonotone.EndOfPaper.logarithmic_excess_mean_bound` | [EndOfPaper/LogarithmicExpectations.lean:73](../EndOfPaper/LogarithmicExpectations.lean#L73) |
| `ScalarMonotone.EndOfPaper.positive_log_le_log_product_add` | [EndOfPaper/ProductLogAreas.lean:14](../EndOfPaper/ProductLogAreas.lean#L14) |
| `ScalarMonotone.EndOfPaper.positive_log_area_factor_finite` | [EndOfPaper/ProductLogAreas.lean:28](../EndOfPaper/ProductLogAreas.lean#L28) |
| `ScalarMonotone.EndOfPaper.positive_log_areas_of_finite_product` | [EndOfPaper/ProductLogAreas.lean:58](../EndOfPaper/ProductLogAreas.lean#L58) |
| `ScalarMonotone.EndOfPaper.profile_log_excess_integral` | [EndOfPaper/ProfileLogExcess.lean:15](../EndOfPaper/ProfileLogExcess.lean#L15) |
| `ScalarMonotone.EndOfPaper.strict_tail_bound_of_right_bounds` | [EndOfPaper/StrictTailLimits.lean:14](../EndOfPaper/StrictTailLimits.lean#L14) |
| `ScalarMonotone.EndOfPaper.strict_tail_bound_of_exponential_perturbations` | [EndOfPaper/StrictTailLimits.lean:28](../EndOfPaper/StrictTailLimits.lean#L28) |
| `ScalarMonotone.EndOfPaper.le_of_forall_positive_div_error` | [EndOfPaper/StrictTailLimits.lean:45](../EndOfPaper/StrictTailLimits.lean#L45) |
| `ScalarMonotone.EndOfPaper.logarithmic_tail_budget` | [EndOfPaper/StrictTailLimits.lean:57](../EndOfPaper/StrictTailLimits.lean#L57) |
| `ScalarMonotone.EndOfPaper.randomized_modulus_lipschitz_on_bounded_controls` | [EndOfPaper/BoundedControlExtensions.lean:15](../EndOfPaper/BoundedControlExtensions.lean#L15) |
| `ScalarMonotone.EndOfPaper.ae_difference_zero_of_bounded_control_extensions` | [EndOfPaper/BoundedControlExtensions.lean:33](../EndOfPaper/BoundedControlExtensions.lean#L33) |
| `ScalarMonotone.EndOfPaper.positive_cutoff_log_prefix_integrable` | [EndOfPaper/GeometricLogExcess.lean:15](../EndOfPaper/GeometricLogExcess.lean#L15) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_log_excess` | [EndOfPaper/GeometricLogExcess.lean:30](../EndOfPaper/GeometricLogExcess.lean#L30) |
| `ScalarMonotone.EndOfPaper.nonzero_profiles_individual_log_areas` | [EndOfPaper/ProfileLogAdmissibility.lean:15](../EndOfPaper/ProfileLogAdmissibility.lean#L15) |
| `ScalarMonotone.EndOfPaper.quantile_singleton_value_le_of_strict_tail` | [EndOfPaper/QuantileTailCompletion.lean:16](../EndOfPaper/QuantileTailCompletion.lean#L16) |
| `ScalarMonotone.EndOfPaper.quantile_selection_ae_le_of_tail_bounds` | [EndOfPaper/QuantileTailCompletion.lean:33](../EndOfPaper/QuantileTailCompletion.lean#L33) |
| `ScalarMonotone.EndOfPaper.tailQuantile_decLE_of_profile_selection_tail_bounds` | [EndOfPaper/QuantileTailCompletion.lean:49](../EndOfPaper/QuantileTailCompletion.lean#L49) |
| `ScalarMonotone.EndOfPaper.eq_zero_of_nonnegative_unit_interval_bounds` | [EndOfPaper/QuantileZero.lean:14](../EndOfPaper/QuantileZero.lean#L14) |
| `ScalarMonotone.EndOfPaper.ae_nonpositive_of_unit_interval_zero_tail_bounds` | [EndOfPaper/QuantileZero.lean:24](../EndOfPaper/QuantileZero.lean#L24) |
| `ScalarMonotone.EndOfPaper.ae_nonpositive_of_quantile_zero` | [EndOfPaper/QuantileZero.lean:32](../EndOfPaper/QuantileZero.lean#L32) |
| `ScalarMonotone.EndOfPaper.lipschitz_difference_zero_of_quantile_zero` | [EndOfPaper/QuantileZero.lean:40](../EndOfPaper/QuantileZero.lean#L40) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_logarithmic_tail` | [EndOfPaper/RandomizedLogTail.lean:17](../EndOfPaper/RandomizedLogTail.lean#L17) |
| `ScalarMonotone.EndOfPaper.randomized_control_zero_difference` | [EndOfPaper/ZeroControlTail.lean:15](../EndOfPaper/ZeroControlTail.lean#L15) |
| `ScalarMonotone.EndOfPaper.randomized_two_copy_zero_control_tail` | [EndOfPaper/ZeroControlTail.lean:26](../EndOfPaper/ZeroControlTail.lean#L26) |
| `ScalarMonotone.EndOfPaper.randomized_zero_cutoff_tail` | [EndOfPaper/ZeroControlTail.lean:56](../EndOfPaper/ZeroControlTail.lean#L56) |
| `ScalarMonotone.EndOfPaper.interiorFiniteProfileProduct` | [EndOfPaper/FiniteProfileProduct.lean:14](../EndOfPaper/FiniteProfileProduct.lean#L14) |
| `ScalarMonotone.EndOfPaper.interiorFiniteProfileProduct_decreasing` | [EndOfPaper/FiniteProfileProduct.lean:17](../EndOfPaper/FiniteProfileProduct.lean#L17) |
| `ScalarMonotone.EndOfPaper.interiorFiniteProfileProduct_domain` | [EndOfPaper/FiniteProfileProduct.lean:33](../EndOfPaper/FiniteProfileProduct.lean#L33) |
| `ScalarMonotone.EndOfPaper.completedFiniteProfileProduct` | [EndOfPaper/FiniteProfileProduct.lean:47](../EndOfPaper/FiniteProfileProduct.lean#L47) |
| `ScalarMonotone.EndOfPaper.completedFiniteProfileProduct_raw_inclusion` | [EndOfPaper/FiniteProfileProduct.lean:59](../EndOfPaper/FiniteProfileProduct.lean#L59) |
| `ScalarMonotone.EndOfPaper.completedFiniteProfileProduct_domain` | [EndOfPaper/FiniteProfileProduct.lean:77](../EndOfPaper/FiniteProfileProduct.lean#L77) |
| `ScalarMonotone.EndOfPaper.completedFiniteProfileProduct_nonnegative` | [EndOfPaper/FiniteProfileProduct.lean:97](../EndOfPaper/FiniteProfileProduct.lean#L97) |
| `ScalarMonotone.EndOfPaper.completedFiniteProfileProduct_selection` | [EndOfPaper/FiniteProfileProduct.lean:114](../EndOfPaper/FiniteProfileProduct.lean#L114) |
| `ScalarMonotone.EndOfPaper.completedFiniteProfileProduct_unique` | [EndOfPaper/FiniteProfileProduct.lean:125](../EndOfPaper/FiniteProfileProduct.lean#L125) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_nonnegative` | [EndOfPaper/GeometricPrefixLower.lean:15](../EndOfPaper/GeometricPrefixLower.lean#L15) |
| `ScalarMonotone.EndOfPaper.profile_value_le_geometricPrefixValue` | [EndOfPaper/GeometricPrefixLower.lean:20](../EndOfPaper/GeometricPrefixLower.lean#L20) |
| `ScalarMonotone.EndOfPaper.randomized_two_parameter_of_individual_areas` | [EndOfPaper/RandomizedTwoParameter.lean:18](../EndOfPaper/RandomizedTwoParameter.lean#L18) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_two_parameter` | [EndOfPaper/RandomizedTwoParameter.lean:77](../EndOfPaper/RandomizedTwoParameter.lean#L77) |
| `ScalarMonotone.EndOfPaper.zero_profile_mem` | [EndOfPaper/ZeroRandomizedLipschitz.lean:16](../EndOfPaper/ZeroRandomizedLipschitz.lean#L16) |
| `ScalarMonotone.EndOfPaper.randomized_zero_baseline_difference` | [EndOfPaper/ZeroRandomizedLipschitz.lean:23](../EndOfPaper/ZeroRandomizedLipschitz.lean#L23) |
| `ScalarMonotone.EndOfPaper.randomized_zero_marginal_difference` | [EndOfPaper/ZeroRandomizedLipschitz.lean:39](../EndOfPaper/ZeroRandomizedLipschitz.lean#L39) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_zero_input` | [EndOfPaper/ZeroRandomizedLipschitz.lean:60](../EndOfPaper/ZeroRandomizedLipschitz.lean#L60) |
| `ScalarMonotone.EndOfPaper.positive_log_area_finset_prod_finite` | [EndOfPaper/FiniteGeometricProduct.lean:15](../EndOfPaper/FiniteGeometricProduct.lean#L15) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_one` | [EndOfPaper/FiniteGeometricProduct.lean:30](../EndOfPaper/FiniteGeometricProduct.lean#L30) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_finset_prod` | [EndOfPaper/FiniteGeometricProduct.lean:36](../EndOfPaper/FiniteGeometricProduct.lean#L36) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_finite_product` | [EndOfPaper/FiniteGeometricProduct.lean:69](../EndOfPaper/FiniteGeometricProduct.lean#L69) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_finite_product` | [EndOfPaper/FiniteGeometricProduct.lean:95](../EndOfPaper/FiniteGeometricProduct.lean#L95) |
| `ScalarMonotone.EndOfPaper.geometric_quantile_moment_bound` | [EndOfPaper/GeometricMomentBound.lean:16](../EndOfPaper/GeometricMomentBound.lean#L16) |
| `ScalarMonotone.EndOfPaper.eLpNorm_nonnegative_eq_moment` | [EndOfPaper/NonnegativeMomentNorm.lean:15](../EndOfPaper/NonnegativeMomentNorm.lean#L15) |
| `ScalarMonotone.EndOfPaper.eLpNorm_le_of_nonnegative_moment_bound` | [EndOfPaper/NonnegativeMomentNorm.lean:26](../EndOfPaper/NonnegativeMomentNorm.lean#L26) |
| `ScalarMonotone.EndOfPaper.memLp_of_nonnegative_moment_bound` | [EndOfPaper/NonnegativeMomentNorm.lean:40](../EndOfPaper/NonnegativeMomentNorm.lean#L40) |
| `ScalarMonotone.EndOfPaper.randomizedInputProduct` | [EndOfPaper/RandomizedGeometricBound.lean:18](../EndOfPaper/RandomizedGeometricBound.lean#L18) |
| `ScalarMonotone.EndOfPaper.randomizedInputProduct_properties` | [EndOfPaper/RandomizedGeometricBound.lean:34](../EndOfPaper/RandomizedGeometricBound.lean#L34) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_geometric_bound` | [EndOfPaper/RandomizedGeometricBound.lean:70](../EndOfPaper/RandomizedGeometricBound.lean#L70) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_moment_bound` | [EndOfPaper/RandomizedMomentBound.lean:41](../EndOfPaper/RandomizedMomentBound.lean#L41) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_real_moment_bound` | [EndOfPaper/RandomizedMomentBound.lean:90](../EndOfPaper/RandomizedMomentBound.lean#L90) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_control` | [EndOfPaper/RandomizedMomentBound.lean:107](../EndOfPaper/RandomizedMomentBound.lean#L107) |
<a id="result-3-7"></a>

## Proposition 3.7

[PDF page 51](../manuscript/monotone_calculus.pdf#page=51). Lower bound for the moment scale

Exactly the original prescribed maximal decreasing profiles with domain interior (0,1), nonnegative interior values, n>=1, arbitrary original selections and the original finite combined positive-log area. No input Lr or ordinary L1, measurability of the original selections, strict positivity or nonzero-profile hypothesis is added. randomized_lipschitz_moment_lower constructs an actual metric space with its Borel measurable structure, a probability law and measurable controls and scalar map. On the actual product probability space, the two coordinate copies are independent and identically distributed, every original whole baseline and marginal quantile comparison holds, and the original multiplicative modulus holds with equality. The same single model gives the exact lower coefficient 2^(-1/r) for every r>0 simultaneously, including infinite norms. The separate universal optimality claim for r>=1 remains unfinished and its supplemental entry is unchanged. Choose globally measurable representatives of the original profile selections and prove AE equality, hence equality of every prescribed product norm. Use the literal positive coordinate vectors plus the origin, derive their total order and product injection, and construct the genuine weighted metric. Prove coordinate continuity off the origin, global Borel measurability and the continuous map from the ordinary coordinate subtype. The actual gated uniform sample has exactly the prescribed product, including zeros. Its half-origin mixture is a probability law with origin mass at least one half. Exact strict-tail estimates establish the original whole quantile comparisons, retaining all atoms, jump fibers and endpoints. For all r>0, retain both zero-copy contributions in the nonnegative product integral and pass to actual extended Lr norms. No approximation, changed final hypotheses or unproved construction properties are used. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.orderedChainGap` | [EndOfPaper/ChainMetricAlgebra.lean:12](../EndOfPaper/ChainMetricAlgebra.lean#L12) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_nonnegative` | [EndOfPaper/ChainMetricAlgebra.lean:14](../EndOfPaper/ChainMetricAlgebra.lean#L14) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_three_identities` | [EndOfPaper/ChainMetricAlgebra.lean:22](../EndOfPaper/ChainMetricAlgebra.lean#L22) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_metric_bounds` | [EndOfPaper/ChainMetricAlgebra.lean:32](../EndOfPaper/ChainMetricAlgebra.lean#L32) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_product_identity` | [EndOfPaper/ChainMetricLocalBounds.lean:12](../EndOfPaper/ChainMetricLocalBounds.lean#L12) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_le_right` | [EndOfPaper/ChainMetricLocalBounds.lean:17](../EndOfPaper/ChainMetricLocalBounds.lean#L17) |
| `ScalarMonotone.EndOfPaper.sub_le_orderedChainGap` | [EndOfPaper/ChainMetricLocalBounds.lean:23](../EndOfPaper/ChainMetricLocalBounds.lean#L23) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_small_implies_ratio_bound` | [EndOfPaper/ChainMetricLocalBounds.lean:29](../EndOfPaper/ChainMetricLocalBounds.lean#L29) |
| `ScalarMonotone.EndOfPaper.orderedChainGap_local_product_bound` | [EndOfPaper/ChainMetricLocalBounds.lean:39](../EndOfPaper/ChainMetricLocalBounds.lean#L39) |
| `ScalarMonotone.EndOfPaper.positive_product_strict_of_coordinate_lt` | [EndOfPaper/PositiveProductChain.lean:17](../EndOfPaper/PositiveProductChain.lean#L17) |
| `ScalarMonotone.EndOfPaper.product_injective_on_positive_or_zero_chain` | [EndOfPaper/PositiveProductChain.lean:35](../EndOfPaper/PositiveProductChain.lean#L35) |
| `ScalarMonotone.EndOfPaper.product_max_of_comparable` | [EndOfPaper/PositiveProductChain.lean:58](../EndOfPaper/PositiveProductChain.lean#L58) |
| `ScalarMonotone.EndOfPaper.coordinate_gap_mul_le_product_gap` | [EndOfPaper/PositiveProductChain.lean:71](../EndOfPaper/PositiveProductChain.lean#L71) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance` | [EndOfPaper/WeightedChainMetric.lean:13](../EndOfPaper/WeightedChainMetric.lean#L13) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_self` | [EndOfPaper/WeightedChainMetric.lean:16](../EndOfPaper/WeightedChainMetric.lean#L16) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_comm` | [EndOfPaper/WeightedChainMetric.lean:19](../EndOfPaper/WeightedChainMetric.lean#L19) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_nonnegative` | [EndOfPaper/WeightedChainMetric.lean:23](../EndOfPaper/WeightedChainMetric.lean#L23) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_ordered` | [EndOfPaper/WeightedChainMetric.lean:27](../EndOfPaper/WeightedChainMetric.lean#L27) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_ordered_bounds` | [EndOfPaper/WeightedChainMetric.lean:36](../EndOfPaper/WeightedChainMetric.lean#L36) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_triangle` | [EndOfPaper/WeightedChainMetric.lean:55](../EndOfPaper/WeightedChainMetric.lean#L55) |
| `ScalarMonotone.EndOfPaper.weightedChainDistance_eq_zero_iff` | [EndOfPaper/WeightedChainMetric.lean:85](../EndOfPaper/WeightedChainMetric.lean#L85) |
| `ScalarMonotone.EndOfPaper.weightedChainMetric` | [EndOfPaper/WeightedChainMetric.lean:99](../EndOfPaper/WeightedChainMetric.lean#L99) |
| `ScalarMonotone.EndOfPaper.PositiveProductPoint` | [EndOfPaper/PositiveChainSpace.lean:17](../EndOfPaper/PositiveChainSpace.lean#L17) |
| `ScalarMonotone.EndOfPaper.positiveProductPoint_ext` | [EndOfPaper/PositiveChainSpace.lean:21](../EndOfPaper/PositiveChainSpace.lean#L21) |
| `ScalarMonotone.EndOfPaper.positiveProductPoint_product_injective` | [EndOfPaper/PositiveChainSpace.lean:28](../EndOfPaper/PositiveChainSpace.lean#L28) |
| `ScalarMonotone.EndOfPaper.positiveProductPointLinearOrder` | [EndOfPaper/PositiveChainSpace.lean:36](../EndOfPaper/PositiveChainSpace.lean#L36) |
| `ScalarMonotone.EndOfPaper.positiveProductPoint_coordinate_monotone` | [EndOfPaper/PositiveChainSpace.lean:42](../EndOfPaper/PositiveChainSpace.lean#L42) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric` | [EndOfPaper/PositiveChainSpace.lean:58](../EndOfPaper/PositiveChainSpace.lean#L58) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_distance` | [EndOfPaper/PositiveChainSpace.lean:82](../EndOfPaper/PositiveChainSpace.lean#L82) |
| `ScalarMonotone.EndOfPaper.product_self_independent_copies` | [EndOfPaper/HalfMixtureCopyTail.lean:14](../EndOfPaper/HalfMixtureCopyTail.lean#L14) |
| `ScalarMonotone.EndOfPaper.halfOriginMixture_copy_tail` | [EndOfPaper/HalfMixtureCopyTail.lean:25](../EndOfPaper/HalfMixtureCopyTail.lean#L25) |
| `ScalarMonotone.EndOfPaper.halfOriginMixture` | [EndOfPaper/HalfOriginMixture.lean:14](../EndOfPaper/HalfOriginMixture.lean#L14) |
| `ScalarMonotone.EndOfPaper.halfOriginMixture_probability` | [EndOfPaper/HalfOriginMixture.lean:17](../EndOfPaper/HalfOriginMixture.lean#L17) |
| `ScalarMonotone.EndOfPaper.halfOriginMixture_origin_mass` | [EndOfPaper/HalfOriginMixture.lean:24](../EndOfPaper/HalfOriginMixture.lean#L24) |
| `ScalarMonotone.EndOfPaper.halfOriginMixture_lintegral` | [EndOfPaper/HalfOriginMixture.lean:36](../EndOfPaper/HalfOriginMixture.lean#L36) |
| `ScalarMonotone.EndOfPaper.halfOriginMixture_strict_tail` | [EndOfPaper/HalfOriginMixture.lean:43](../EndOfPaper/HalfOriginMixture.lean#L43) |
| `ScalarMonotone.EndOfPaper.positiveChainFromSubtype` | [EndOfPaper/PositiveChainEmbedding.lean:18](../EndOfPaper/PositiveChainEmbedding.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_fromSubtype_continuous` | [EndOfPaper/PositiveChainEmbedding.lean:20](../EndOfPaper/PositiveChainEmbedding.lean#L20) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_fromSubtype_measurable` | [EndOfPaper/PositiveChainEmbedding.lean:52](../EndOfPaper/PositiveChainEmbedding.lean#L52) |
| `ScalarMonotone.EndOfPaper.positiveChainOrigin` | [EndOfPaper/PositiveChainGeometry.lean:18](../EndOfPaper/PositiveChainGeometry.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_product_identity` | [EndOfPaper/PositiveChainGeometry.lean:21](../EndOfPaper/PositiveChainGeometry.lean#L21) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_origin_distance` | [EndOfPaper/PositiveChainGeometry.lean:47](../EndOfPaper/PositiveChainGeometry.lean#L47) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_le_max_baseline` | [EndOfPaper/PositiveChainGeometry.lean:68](../EndOfPaper/PositiveChainGeometry.lean#L68) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_le_product_gap` | [EndOfPaper/PositiveChainGeometry.lean:103](../EndOfPaper/PositiveChainGeometry.lean#L103) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_ordered_distance` | [EndOfPaper/PositiveCoordinateEstimates.lean:19](../EndOfPaper/PositiveCoordinateEstimates.lean#L19) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_local_weight_bound` | [EndOfPaper/PositiveCoordinateEstimates.lean:38](../EndOfPaper/PositiveCoordinateEstimates.lean#L38) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_local_coordinate_bound` | [EndOfPaper/PositiveCoordinateEstimates.lean:60](../EndOfPaper/PositiveCoordinateEstimates.lean#L60) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_coordinate_continuousAt` | [EndOfPaper/PositiveCoordinateEstimates.lean:89](../EndOfPaper/PositiveCoordinateEstimates.lean#L89) |
| `ScalarMonotone.EndOfPaper.positiveChainMetric_coordinate_measurable` | [EndOfPaper/PositiveCoordinateEstimates.lean:119](../EndOfPaper/PositiveCoordinateEstimates.lean#L119) |
| `ScalarMonotone.EndOfPaper.positiveProfileChain` | [EndOfPaper/PositiveProfileChain.lean:13](../EndOfPaper/PositiveProfileChain.lean#L13) |
| `ScalarMonotone.EndOfPaper.positiveProfileChain_zero` | [EndOfPaper/PositiveProfileChain.lean:16](../EndOfPaper/PositiveProfileChain.lean#L16) |
| `ScalarMonotone.EndOfPaper.positiveProfileChain_positive_or_zero` | [EndOfPaper/PositiveProfileChain.lean:19](../EndOfPaper/PositiveProfileChain.lean#L19) |
| `ScalarMonotone.EndOfPaper.positiveProfileChain_nonnegative` | [EndOfPaper/PositiveProfileChain.lean:25](../EndOfPaper/PositiveProfileChain.lean#L25) |
| `ScalarMonotone.EndOfPaper.positiveProfileChain_total` | [EndOfPaper/PositiveProfileChain.lean:32](../EndOfPaper/PositiveProfileChain.lean#L32) |
| `ScalarMonotone.EndOfPaper.positiveProfileChain_properties` | [EndOfPaper/PositiveProfileChain.lean:44](../EndOfPaper/PositiveProfileChain.lean#L44) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_moment_lower` | [EndOfPaper/PrescribedLowerModel.lean:12](../EndOfPaper/PrescribedLowerModel.lean#L12) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleVector` | [EndOfPaper/ProfileChainSample.lean:15](../EndOfPaper/ProfileChainSample.lean#L15) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleVector_mem` | [EndOfPaper/ProfileChainSample.lean:19](../EndOfPaper/ProfileChainSample.lean#L19) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleSubtype` | [EndOfPaper/ProfileChainSample.lean:27](../EndOfPaper/ProfileChainSample.lean#L27) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleVector_measurable` | [EndOfPaper/ProfileChainSample.lean:30](../EndOfPaper/ProfileChainSample.lean#L30) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleSubtype_measurable` | [EndOfPaper/ProfileChainSample.lean:42](../EndOfPaper/ProfileChainSample.lean#L42) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleVector_coordinate_le` | [EndOfPaper/ProfileChainSample.lean:47](../EndOfPaper/ProfileChainSample.lean#L47) |
| `ScalarMonotone.EndOfPaper.positiveProfileSampleVector_product` | [EndOfPaper/ProfileChainSample.lean:56](../EndOfPaper/ProfileChainSample.lean#L56) |
| `ScalarMonotone.EndOfPaper.positiveProfileChainMetric` | [EndOfPaper/ProfileChainSample.lean:72](../EndOfPaper/ProfileChainSample.lean#L72) |
| `ScalarMonotone.EndOfPaper.positiveProfilePointSample` | [EndOfPaper/ProfileChainSample.lean:77](../EndOfPaper/ProfileChainSample.lean#L77) |
| `ScalarMonotone.EndOfPaper.positiveProfilePointSample_measurable` | [EndOfPaper/ProfileChainSample.lean:80](../EndOfPaper/ProfileChainSample.lean#L80) |
| `ScalarMonotone.EndOfPaper.positiveProfileProductMap` | [EndOfPaper/ProfileLawMoments.lean:19](../EndOfPaper/ProfileLawMoments.lean#L19) |
| `ScalarMonotone.EndOfPaper.positiveProfileProductMap_measurable` | [EndOfPaper/ProfileLawMoments.lean:21](../EndOfPaper/ProfileLawMoments.lean#L21) |
| `ScalarMonotone.EndOfPaper.positiveProfileProductMap_zero` | [EndOfPaper/ProfileLawMoments.lean:29](../EndOfPaper/ProfileLawMoments.lean#L29) |
| `ScalarMonotone.EndOfPaper.positiveProfileProductMap_modulus` | [EndOfPaper/ProfileLawMoments.lean:32](../EndOfPaper/ProfileLawMoments.lean#L32) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_product_moment` | [EndOfPaper/ProfileLawMoments.lean:40](../EndOfPaper/ProfileLawMoments.lean#L40) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_lower_moment` | [EndOfPaper/ProfileLawMoments.lean:68](../EndOfPaper/ProfileLawMoments.lean#L68) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_lower_norm` | [EndOfPaper/ProfileLawMoments.lean:110](../EndOfPaper/ProfileLawMoments.lean#L110) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfOrigin` | [EndOfPaper/ProfileLawTails.lean:20](../EndOfPaper/ProfileLawTails.lean#L20) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw` | [EndOfPaper/ProfileLawTails.lean:22](../EndOfPaper/ProfileLawTails.lean#L22) |
| `ScalarMonotone.EndOfPaper.positiveProfilePoint_coordinate_measurable` | [EndOfPaper/ProfileLawTails.lean:31](../EndOfPaper/ProfileLawTails.lean#L31) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_probability` | [EndOfPaper/ProfileLawTails.lean:41](../EndOfPaper/ProfileLawTails.lean#L41) |
| `ScalarMonotone.EndOfPaper.positiveProfileSample_coordinate_tail` | [EndOfPaper/ProfileLawTails.lean:52](../EndOfPaper/ProfileLawTails.lean#L52) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_coordinate_tail` | [EndOfPaper/ProfileLawTails.lean:70](../EndOfPaper/ProfileLawTails.lean#L70) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_marginal` | [EndOfPaper/ProfileLawTails.lean:84](../EndOfPaper/ProfileLawTails.lean#L84) |
| `ScalarMonotone.EndOfPaper.positiveProfileHalfLaw_baseline` | [EndOfPaper/ProfileLawTails.lean:114](../EndOfPaper/ProfileLawTails.lean#L114) |
| `ScalarMonotone.EndOfPaper.eLpNorm_ge_of_nonnegative_moment_bound` | [EndOfPaper/ProfileLowerNorm.lean:12](../EndOfPaper/ProfileLowerNorm.lean#L12) |
| `ScalarMonotone.EndOfPaper.zero_atom_product_moment_lower` | [EndOfPaper/ZeroAtomLowerMoment.lean:14](../EndOfPaper/ZeroAtomLowerMoment.lean#L14) |
| `ScalarMonotone.EndOfPaper.independent_copy_zero_atom_moment_lower` | [EndOfPaper/ZeroAtomLowerMoment.lean:46](../EndOfPaper/ZeroAtomLowerMoment.lean#L46) |
<a id="result-3-8"></a>

## Remark 3.8

[PDF page 54](../manuscript/monotone_calculus.pdf#page=54). Centering and unequal probability levels

Exactly the original randomized Lipschitz data: arbitrary original probability space and metric spaces, measurable map and nonnegative controls, n>=1, independent identical copy, actual baseline and marginal quantile comparisons, one finite combined positive-log area and arbitrary profile selections. Any actual median is allowed. Prescribed product MemLp is required only for moment conclusions; r>0 for medians and r>=1 for means. No output integrability, separability, atomlessness or individual log-area hypothesis is added. randomized_lipschitz_centering gives the complete conjunction: the sharper whole median graph with the literal completed qDelta*G(control-product) profile at probability u/6 for nonzero inputs, zero distance to every actual median in both zero-input cases, the exact (6*exp(1))^(1/r) median bound for every r>0, and the exact mean-centered norm chain with constant (3*exp(1))^(1/r) for r>=1. Output MemLp and ordinary L1 are derived. Both real-norm wrappers explicitly give finite ordinary norms. The separately proved optimized unequal-level infimum retains arbitrary input and geometric jump selections and equality in the budget. Apply the original-space median-to-copy tail comparison and exact completed probability dilation to the sharper graph. Use the full extended geometric moment theorem for all median exponents and direct zero-input arguments. Obtain an actual median from the half-quantile fiber and derive uncentered MemLp by adding its constant, hence L1 for r>=1. Apply the checked independent-copy product law, derived product-integrability and Jensen/Fubini norm comparison; combine with the original 3e copy bound. Every auxiliary finite moment and graph property is discharged from the manuscript assumptions. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.IsRealMedian` | [EndOfPaper/IndependentCopyTails.lean:12](../EndOfPaper/IndependentCopyTails.lean#L12) |
| `ScalarMonotone.EndOfPaper.indepFun_measureReal_inter` | [EndOfPaper/IndependentCopyTails.lean:15](../EndOfPaper/IndependentCopyTails.lean#L15) |
| `ScalarMonotone.EndOfPaper.median_independent_copy_tail` | [EndOfPaper/IndependentCopyTails.lean:22](../EndOfPaper/IndependentCopyTails.lean#L22) |
| `ScalarMonotone.EndOfPaper.independent_copy_pivot_tail` | [EndOfPaper/IndependentCopyTails.lean:101](../EndOfPaper/IndependentCopyTails.lean#L101) |
| `ScalarMonotone.EndOfPaper.quantile_tail_multiplier_dilation` | [EndOfPaper/QuantileTailDilation.lean:14](../EndOfPaper/QuantileTailDilation.lean#L14) |
| `ScalarMonotone.EndOfPaper.integral_sub_mean_rpow_le` | [EndOfPaper/IndependentMeanJensen.lean:20](../EndOfPaper/IndependentMeanJensen.lean#L20) |
| `ScalarMonotone.EndOfPaper.law_mean_centered_moment_le_product` | [EndOfPaper/IndependentMeanJensen.lean:44](../EndOfPaper/IndependentMeanJensen.lean#L44) |
| `ScalarMonotone.EndOfPaper.independent_copy_mean_moment` | [EndOfPaper/IndependentMeanJensen.lean:58](../EndOfPaper/IndependentMeanJensen.lean#L58) |
| `ScalarMonotone.EndOfPaper.independent_copy_mean_norm` | [EndOfPaper/IndependentMeanJensen.lean:97](../EndOfPaper/IndependentMeanJensen.lean#L97) |
| `ScalarMonotone.EndOfPaper.isRealMedian_of_tailQuantile_half` | [EndOfPaper/RandomizedMedianMoment.lean:17](../EndOfPaper/RandomizedMedianMoment.lean#L17) |
| `ScalarMonotone.EndOfPaper.exists_realMedian` | [EndOfPaper/RandomizedMedianMoment.lean:30](../EndOfPaper/RandomizedMedianMoment.lean#L30) |
| `ScalarMonotone.EndOfPaper.median_difference_zero_of_copy_zero` | [EndOfPaper/RandomizedMedianMoment.lean:38](../EndOfPaper/RandomizedMedianMoment.lean#L38) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_median_geometric_bound` | [EndOfPaper/RandomizedMedianMoment.lean:85](../EndOfPaper/RandomizedMedianMoment.lean#L85) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_median_moment_bound` | [EndOfPaper/RandomizedMedianMoment.lean:110](../EndOfPaper/RandomizedMedianMoment.lean#L110) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_value_memLp` | [EndOfPaper/RandomizedMedianMoment.lean:156](../EndOfPaper/RandomizedMedianMoment.lean#L156) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_sharper_bound` | [EndOfPaper/RandomizedUnequalBound.lean:163](../EndOfPaper/RandomizedUnequalBound.lean#L163) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized` | [EndOfPaper/RandomizedUnequalBound.lean:146](../EndOfPaper/RandomizedUnequalBound.lean#L146) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_median_sharper_bound` | [EndOfPaper/RandomizedCentering.lean:39](../EndOfPaper/RandomizedCentering.lean#L39) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_mean_moment_bound` | [EndOfPaper/RandomizedCentering.lean:69](../EndOfPaper/RandomizedCentering.lean#L69) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_centering` | [EndOfPaper/RandomizedCentering.lean:91](../EndOfPaper/RandomizedCentering.lean#L91) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_median_real_moment_bound` | [EndOfPaper/RandomizedCentering.lean:139](../EndOfPaper/RandomizedCentering.lean#L139) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_mean_real_moment_bound` | [EndOfPaper/RandomizedCentering.lean:156](../EndOfPaper/RandomizedCentering.lean#L156) |
<a id="result-3-9"></a>

## Proposition 3.9

[PDF page 55](../manuscript/monotone_calculus.pdf#page=55). Network tail profiles

Exactly L,N,p_0,...,p_L positive, the actual Euclidean product of HS matrix blocks, entrywise one-Lipschitz activations vanishing at zero, arbitrary original measurable joint parameters and independent identically distributed copy, the original whole baseline comparison for every real one-Lipschitz observation, a nonnegative completed baseline profile on (0,1) with one finite positive-log area on an arbitrary original selection, actual medians of the two normalized norms, and an arbitrary actual median of every HS one-Lipschitz output observation. No independence between data and weights, nonzero profiles, input/output L1 or measurable-selection final hypothesis is added. network_tail_profiles proves maximality, exact domain interior (0,1), and the whole original centered-output quantile comparison with D times the literal completed interior product of qDelta(u/6) and every actual G(max(m_x,m_l)+qDelta/sqrt(min(N*p_0,p_l+p_(l-1))))(u/12). The original exact D and actual matrix network are retained. All control marginal comparisons, nonnegative medians, geometric domains and finite positive-log areas are derived. Zero profiles, atoms, all original dependence and the complete endpoint/jump fibers are included. Use the already checked actual matrix two-point estimate. Derive each normalized norm Lipschitz constant from the actual HS metric and spectral norm estimate. The two-orientation one-sided median lemma followed by a two-event union gives the exact half-level control profile. Derive each affine/dilated area and then the single combined input area from the original baseline. Apply the established sharper centered bound to the actual observation divided by D, with its zero cases included. Prove the exact geometric u/12 identity, construct the literal actual target from its graph factors and prove maximality/domain/completion correspondence. Transfer the whole centered quantile graph by positive scaling. Obtain a measurable representative from an arbitrary original profile selection, with the original area unchanged; the target is independent of that choice. The independent reader expands D, the probability levels, geometric factors and completed finite graph product. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.upper_median_independent_copy_tail` | [EndOfPaper/OneSidedCopyTail.lean:13](../EndOfPaper/OneSidedCopyTail.lean#L13) |
| `ScalarMonotone.EndOfPaper.hsMatrixActivation` | [EndOfPaper/HSMatrixActivation.lean:12](../EndOfPaper/HSMatrixActivation.lean#L12) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_zero` | [EndOfPaper/HSMatrixActivation.lean:15](../EndOfPaper/HSMatrixActivation.lean#L15) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_contraction` | [EndOfPaper/HSMatrixActivation.lean:20](../EndOfPaper/HSMatrixActivation.lean#L20) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_lipschitz` | [EndOfPaper/HSMatrixActivation.lean:33](../EndOfPaper/HSMatrixActivation.lean#L33) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_norm_le` | [EndOfPaper/HSMatrixActivation.lean:39](../EndOfPaper/HSMatrixActivation.lean#L39) |
| `ScalarMonotone.EndOfPaper.HSMatrix` | [EndOfPaper/HSMatrixBasic.lean:13](../EndOfPaper/HSMatrixBasic.lean#L13) |
| `ScalarMonotone.EndOfPaper.hsMatrixToMatrix` | [EndOfPaper/HSMatrixBasic.lean:15](../EndOfPaper/HSMatrixBasic.lean#L15) |
| `ScalarMonotone.EndOfPaper.hsMatrixOfMatrix` | [EndOfPaper/HSMatrixBasic.lean:18](../EndOfPaper/HSMatrixBasic.lean#L18) |
| `ScalarMonotone.EndOfPaper.hs_matrix_to_of` | [EndOfPaper/HSMatrixBasic.lean:21](../EndOfPaper/HSMatrixBasic.lean#L21) |
| `ScalarMonotone.EndOfPaper.hs_matrix_of_to` | [EndOfPaper/HSMatrixBasic.lean:24](../EndOfPaper/HSMatrixBasic.lean#L24) |
| `ScalarMonotone.EndOfPaper.hs_matrix_norm_sq` | [EndOfPaper/HSMatrixBasic.lean:29](../EndOfPaper/HSMatrixBasic.lean#L29) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_difference` | [EndOfPaper/HSMatrixDifference.lean:11](../EndOfPaper/HSMatrixDifference.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_difference_norm_le` | [EndOfPaper/HSMatrixDifference.lean:23](../EndOfPaper/HSMatrixDifference.lean#L23) |
| `ScalarMonotone.EndOfPaper.hsMatrixOp` | [EndOfPaper/HSMatrixOperator.lean:11](../EndOfPaper/HSMatrixOperator.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_apply` | [EndOfPaper/HSMatrixOperator.lean:16](../EndOfPaper/HSMatrixOperator.lean#L16) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_norm_le` | [EndOfPaper/HSMatrixOperator.lean:20](../EndOfPaper/HSMatrixOperator.lean#L20) |
| `ScalarMonotone.EndOfPaper.hsMatrixMul` | [EndOfPaper/HSMatrixOperator.lean:42](../EndOfPaper/HSMatrixOperator.lean#L42) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_apply` | [EndOfPaper/HSMatrixOperator.lean:45](../EndOfPaper/HSMatrixOperator.lean#L45) |
| `ScalarMonotone.EndOfPaper.hsMatrixColumn` | [EndOfPaper/HSMatrixProduct.lean:11](../EndOfPaper/HSMatrixProduct.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_norm_sq_columns` | [EndOfPaper/HSMatrixProduct.lean:14](../EndOfPaper/HSMatrixProduct.lean#L14) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_column` | [EndOfPaper/HSMatrixProduct.lean:21](../EndOfPaper/HSMatrixProduct.lean#L21) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_norm_le` | [EndOfPaper/HSMatrixProduct.lean:27](../EndOfPaper/HSMatrixProduct.lean#L27) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_sub` | [EndOfPaper/HSMatrixProduct.lean:45](../EndOfPaper/HSMatrixProduct.lean#L45) |
| `ScalarMonotone.EndOfPaper.hs_matrix_operator_norm_lipschitz` | [EndOfPaper/HSMatrixProduct.lean:55](../EndOfPaper/HSMatrixProduct.lean#L55) |
| `ScalarMonotone.EndOfPaper.network_control_continuous` | [EndOfPaper/NetworkContinuity.lean:12](../EndOfPaper/NetworkContinuity.lean#L12) |
| `ScalarMonotone.EndOfPaper.finite_network_continuous` | [EndOfPaper/NetworkContinuity.lean:17](../EndOfPaper/NetworkContinuity.lean#L17) |
| `ScalarMonotone.EndOfPaper.finite_network_borel_measurable` | [EndOfPaper/NetworkContinuity.lean:35](../EndOfPaper/NetworkContinuity.lean#L35) |
| `ScalarMonotone.EndOfPaper.networkControl` | [EndOfPaper/NetworkControls.lean:10](../EndOfPaper/NetworkControls.lean#L10) |
| `ScalarMonotone.EndOfPaper.network_control_nonnegative` | [EndOfPaper/NetworkControls.lean:14](../EndOfPaper/NetworkControls.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkActivationsAt` | [EndOfPaper/NetworkControls.lean:18](../EndOfPaper/NetworkControls.lean#L18) |
| `ScalarMonotone.EndOfPaper.network_activations_lipschitz` | [EndOfPaper/NetworkControls.lean:21](../EndOfPaper/NetworkControls.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_activations_zero` | [EndOfPaper/NetworkControls.lean:28](../EndOfPaper/NetworkControls.lean#L28) |
| `ScalarMonotone.EndOfPaper.finiteNetworkMap` | [EndOfPaper/NetworkControls.lean:35](../EndOfPaper/NetworkControls.lean#L35) |
| `ScalarMonotone.EndOfPaper.networkLayer` | [EndOfPaper/NetworkLayers.lean:12](../EndOfPaper/NetworkLayers.lean#L12) |
| `ScalarMonotone.EndOfPaper.networkOutput` | [EndOfPaper/NetworkLayers.lean:20](../EndOfPaper/NetworkLayers.lean#L20) |
| `ScalarMonotone.EndOfPaper.network_layer_norm_step` | [EndOfPaper/NetworkLayers.lean:26](../EndOfPaper/NetworkLayers.lean#L26) |
| `ScalarMonotone.EndOfPaper.network_layer_difference_step` | [EndOfPaper/NetworkLayers.lean:40](../EndOfPaper/NetworkLayers.lean#L40) |
| `ScalarMonotone.EndOfPaper.networkTwoPointControl` | [EndOfPaper/NetworkMajorants.lean:10](../EndOfPaper/NetworkMajorants.lean#L10) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_nonnegative` | [EndOfPaper/NetworkMajorants.lean:14](../EndOfPaper/NetworkMajorants.lean#L14) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_symmetric` | [EndOfPaper/NetworkMajorants.lean:21](../EndOfPaper/NetworkMajorants.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_input` | [EndOfPaper/NetworkMajorants.lean:29](../EndOfPaper/NetworkMajorants.lean#L29) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_operator` | [EndOfPaper/NetworkMajorants.lean:52](../EndOfPaper/NetworkMajorants.lean#L52) |
| `ScalarMonotone.EndOfPaper.NetworkCoordinate` | [EndOfPaper/NetworkParameters.lean:11](../EndOfPaper/NetworkParameters.lean#L11) |
| `ScalarMonotone.EndOfPaper.NetworkParameters` | [EndOfPaper/NetworkParameters.lean:14](../EndOfPaper/NetworkParameters.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkData` | [EndOfPaper/NetworkParameters.lean:16](../EndOfPaper/NetworkParameters.lean#L16) |
| `ScalarMonotone.EndOfPaper.networkWeight` | [EndOfPaper/NetworkParameters.lean:20](../EndOfPaper/NetworkParameters.lean#L20) |
| `ScalarMonotone.EndOfPaper.network_parameter_norm_sq` | [EndOfPaper/NetworkParameters.lean:24](../EndOfPaper/NetworkParameters.lean#L24) |
| `ScalarMonotone.EndOfPaper.network_data_sub` | [EndOfPaper/NetworkParameters.lean:29](../EndOfPaper/NetworkParameters.lean#L29) |
| `ScalarMonotone.EndOfPaper.network_weight_sub` | [EndOfPaper/NetworkParameters.lean:32](../EndOfPaper/NetworkParameters.lean#L32) |
| `ScalarMonotone.EndOfPaper.network_data_norm_le` | [EndOfPaper/NetworkParameters.lean:35](../EndOfPaper/NetworkParameters.lean#L35) |
| `ScalarMonotone.EndOfPaper.network_weight_norm_le` | [EndOfPaper/NetworkParameters.lean:41](../EndOfPaper/NetworkParameters.lean#L41) |
| `ScalarMonotone.EndOfPaper.network_data_lipschitz` | [EndOfPaper/NetworkParameters.lean:49](../EndOfPaper/NetworkParameters.lean#L49) |
| `ScalarMonotone.EndOfPaper.network_weight_lipschitz` | [EndOfPaper/NetworkParameters.lean:55](../EndOfPaper/NetworkParameters.lean#L55) |
| `ScalarMonotone.EndOfPaper.networkWeightsAt` | [EndOfPaper/NetworkParameters.lean:61](../EndOfPaper/NetworkParameters.lean#L61) |
| `ScalarMonotone.EndOfPaper.networkMap` | [EndOfPaper/NetworkParameters.lean:65](../EndOfPaper/NetworkParameters.lean#L65) |
| `ScalarMonotone.EndOfPaper.network_prefix_error_from_majorants` | [EndOfPaper/NetworkPrefixBounds.lean:12](../EndOfPaper/NetworkPrefixBounds.lean#L12) |
| `ScalarMonotone.EndOfPaper.network_product_error_prefix` | [EndOfPaper/NetworkProductRecursion.lean:11](../EndOfPaper/NetworkProductRecursion.lean#L11) |
| `ScalarMonotone.EndOfPaper.network_exact_cauchy_factor` | [EndOfPaper/NetworkProductRecursion.lean:30](../EndOfPaper/NetworkProductRecursion.lean#L30) |
| `ScalarMonotone.EndOfPaper.networkPrefactor` | [EndOfPaper/NetworkTwoPoint.lean:12](../EndOfPaper/NetworkTwoPoint.lean#L12) |
| `ScalarMonotone.EndOfPaper.network_two_point_bound` | [EndOfPaper/NetworkTwoPoint.lean:16](../EndOfPaper/NetworkTwoPoint.lean#L16) |
| `ScalarMonotone.EndOfPaper.positive_log_affine_bound` | [EndOfPaper/AffinePositiveLogArea.lean:13](../EndOfPaper/AffinePositiveLogArea.lean#L13) |
| `ScalarMonotone.EndOfPaper.positive_log_area_affine_finite` | [EndOfPaper/AffinePositiveLogArea.lean:38](../EndOfPaper/AffinePositiveLogArea.lean#L38) |
| `ScalarMonotone.EndOfPaper.interiorProfileAffine` | [EndOfPaper/InitialProfileAffine.lean:11](../EndOfPaper/InitialProfileAffine.lean#L11) |
| `ScalarMonotone.EndOfPaper.interiorProfileAffine_decreasing` | [EndOfPaper/InitialProfileAffine.lean:14](../EndOfPaper/InitialProfileAffine.lean#L14) |
| `ScalarMonotone.EndOfPaper.interiorProfileAffine_domain` | [EndOfPaper/InitialProfileAffine.lean:25](../EndOfPaper/InitialProfileAffine.lean#L25) |
| `ScalarMonotone.EndOfPaper.completedProfileAffine` | [EndOfPaper/InitialProfileAffine.lean:36](../EndOfPaper/InitialProfileAffine.lean#L36) |
| `ScalarMonotone.EndOfPaper.completedProfileAffine_raw_inclusion` | [EndOfPaper/InitialProfileAffine.lean:47](../EndOfPaper/InitialProfileAffine.lean#L47) |
| `ScalarMonotone.EndOfPaper.completedProfileAffine_domain` | [EndOfPaper/InitialProfileAffine.lean:61](../EndOfPaper/InitialProfileAffine.lean#L61) |
| `ScalarMonotone.EndOfPaper.completedProfileAffine_nonnegative` | [EndOfPaper/InitialProfileAffine.lean:76](../EndOfPaper/InitialProfileAffine.lean#L76) |
| `ScalarMonotone.EndOfPaper.completedProfileAffine_selection` | [EndOfPaper/InitialProfileAffine.lean:91](../EndOfPaper/InitialProfileAffine.lean#L91) |
| `ScalarMonotone.EndOfPaper.completedProfileAffine_unique` | [EndOfPaper/InitialProfileAffine.lean:98](../EndOfPaper/InitialProfileAffine.lean#L98) |
| `ScalarMonotone.EndOfPaper.halfAffineProfile` | [EndOfPaper/MaxMedianControlProfile.lean:16](../EndOfPaper/MaxMedianControlProfile.lean#L16) |
| `ScalarMonotone.EndOfPaper.halfAffineProfile_selection` | [EndOfPaper/MaxMedianControlProfile.lean:22](../EndOfPaper/MaxMedianControlProfile.lean#L22) |
| `ScalarMonotone.EndOfPaper.max_median_control_quantile_bound` | [EndOfPaper/MaxMedianControlProfile.lean:42](../EndOfPaper/MaxMedianControlProfile.lean#L42) |
| `ScalarMonotone.EndOfPaper.halfAffineProfile_nonnegative` | [EndOfPaper/MaxMedianControlProfile.lean:68](../EndOfPaper/MaxMedianControlProfile.lean#L68) |
| `ScalarMonotone.EndOfPaper.half_affine_positive_log_area_finite` | [EndOfPaper/MaxMedianControlProfile.lean:84](../EndOfPaper/MaxMedianControlProfile.lean#L84) |
| `ScalarMonotone.EndOfPaper.max_median_control_strict_tail` | [EndOfPaper/MaxMedianControlTail.lean:13](../EndOfPaper/MaxMedianControlTail.lean#L13) |
| `ScalarMonotone.EndOfPaper.nonnegative_realMedian` | [EndOfPaper/NetworkControlProfiles.lean:14](../EndOfPaper/NetworkControlProfiles.lean#L14) |
| `ScalarMonotone.EndOfPaper.network_normalized_norm_lipschitz` | [EndOfPaper/NetworkControlProfiles.lean:26](../EndOfPaper/NetworkControlProfiles.lean#L26) |
| `ScalarMonotone.EndOfPaper.network_control_quantile_bound` | [EndOfPaper/NetworkControlProfiles.lean:52](../EndOfPaper/NetworkControlProfiles.lean#L52) |
| `ScalarMonotone.EndOfPaper.network_prefactor_pos` | [EndOfPaper/NetworkObservation.lean:12](../EndOfPaper/NetworkObservation.lean#L12) |
| `ScalarMonotone.EndOfPaper.normalized_network_observation_continuous` | [EndOfPaper/NetworkObservation.lean:22](../EndOfPaper/NetworkObservation.lean#L22) |
| `ScalarMonotone.EndOfPaper.normalized_network_observation_modulus` | [EndOfPaper/NetworkObservation.lean:29](../EndOfPaper/NetworkObservation.lean#L29) |
| `ScalarMonotone.EndOfPaper.half_affine_geometric_network_level` | [EndOfPaper/NetworkProfileGeometry.lean:15](../EndOfPaper/NetworkProfileGeometry.lean#L15) |
| `ScalarMonotone.EndOfPaper.positive_output_initial_scalar_completion` | [EndOfPaper/NetworkProfileGeometry.lean:42](../EndOfPaper/NetworkProfileGeometry.lean#L42) |
| `ScalarMonotone.EndOfPaper.geometric_product_dilation_selection` | [EndOfPaper/NetworkProfileGeometry.lean:55](../EndOfPaper/NetworkProfileGeometry.lean#L55) |
| `ScalarMonotone.EndOfPaper.interiorFiniteProfileProduct_congr_on` | [EndOfPaper/NetworkProfileGeometry.lean:88](../EndOfPaper/NetworkProfileGeometry.lean#L88) |
| `ScalarMonotone.EndOfPaper.network_tail_profile_geometry` | [EndOfPaper/NetworkTailGeometry.lean:14](../EndOfPaper/NetworkTailGeometry.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkInverseDimension` | [EndOfPaper/NetworkTailProfileDefinition.lean:13](../EndOfPaper/NetworkTailProfileDefinition.lean#L13) |
| `ScalarMonotone.EndOfPaper.networkAffineInputProfile` | [EndOfPaper/NetworkTailProfileDefinition.lean:16](../EndOfPaper/NetworkTailProfileDefinition.lean#L16) |
| `ScalarMonotone.EndOfPaper.networkTailComponent` | [EndOfPaper/NetworkTailProfileDefinition.lean:21](../EndOfPaper/NetworkTailProfileDefinition.lean#L21) |
| `ScalarMonotone.EndOfPaper.networkTailProfile` | [EndOfPaper/NetworkTailProfileDefinition.lean:27](../EndOfPaper/NetworkTailProfileDefinition.lean#L27) |
| `ScalarMonotone.EndOfPaper.network_tail_profiles_of_measurable_selection` | [EndOfPaper/NetworkTailProfiles.lean:33](../EndOfPaper/NetworkTailProfiles.lean#L33) |
| `ScalarMonotone.EndOfPaper.network_tail_profiles` | [EndOfPaper/NetworkTailProfiles.lean:144](../EndOfPaper/NetworkTailProfiles.lean#L144) |
| `ScalarMonotone.EndOfPaper.inv_sqrt_dimension_lipschitz` | [EndOfPaper/NormalizedNormLipschitz.lean:11](../EndOfPaper/NormalizedNormLipschitz.lean#L11) |
| `ScalarMonotone.EndOfPaper.isRealMedian_div_positive` | [EndOfPaper/PositiveMedianScaling.lean:12](../EndOfPaper/PositiveMedianScaling.lean#L12) |
| `ScalarMonotone.EndOfPaper.tailQuantile_random_positive_scale` | [EndOfPaper/PositiveMedianScaling.lean:26](../EndOfPaper/PositiveMedianScaling.lean#L26) |
| `ScalarMonotone.EndOfPaper.centered_quantile_positive_normalization` | [EndOfPaper/PositiveMedianScaling.lean:33](../EndOfPaper/PositiveMedianScaling.lean#L33) |
| `ScalarMonotone.EndOfPaper.tailQuantile_le_nonnegative_profile_of_ae_zero` | [EndOfPaper/RandomizedMedianAllProfiles.lean:13](../EndOfPaper/RandomizedMedianAllProfiles.lean#L13) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_median_with_individual_areas` | [EndOfPaper/RandomizedMedianAllProfiles.lean:32](../EndOfPaper/RandomizedMedianAllProfiles.lean#L32) |
<a id="result-3-10"></a>

## Example 3.10

[PDF page 56](../manuscript/monotone_calculus.pdf#page=56). Subgaussian concentration and depth

The exact original finite network, actual activations, joint-law baseline, independent identical copy and actual output/norm medians. In the Gaussian specialization all parameter entries on the original arbitrary probability space are independent measurable standard Gaussians, with N,d positive. No concentration, comparison inequality, norm median constant, exponential integrability, smoothness, atomlessness or random maximizer is assumed. Retain the literal network depth threshold and uniform two-regime tail for fixed depth and N comparable to d. The original whole Gaussian input profile has A=2. gaussian_network_norm_medians proves both actual network medians simultaneously: mx<=1+sqrt(2*log(2)/(N*d)) and every ml<=sqrt(2)+sqrt(log(2)/d). gaussian_matrix_operator_norm_mgf also supplies exp(a*(sqrt(m)+sqrt(n))+a^2/2), the exact weak upper tail exp(-s^2/2), and the bound for every actual rectangular matrix norm median. Use the previously proved whole Gaussian input profile and Euclidean square-Laplace norm estimates. Prove actual scalar and coordinate Gaussian integration by parts, finite softmax derivatives and Hessian signs, and the full expectation interpolation derivative with every local dominant, L1 and endpoint continuity derived. Disjoint padded coefficient arrays have equal variances and the actual nonnegative unit-pair covariance difference. Derive the smooth comparison, pass to actual finite maxima by an ordinary scalar error limit, and construct the actual independent matrix/scalar/vector samples. Factor their exact moments, pass along one deterministic dense unit-pair sequence using derived dominated convergence, and cancel the independent scalar Gaussian moment. Transfer the resulting sharp matrix norm MGF to arbitrary original Gaussian laws, apply Chernoff and the actual median inequalities, normalize exactly and derive both network block constants from joint coordinate independence. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.sqrt_log_hardy_prefix` | [EndOfPaper/SqrtLogHardy.lean:13](../EndOfPaper/SqrtLogHardy.lean#L13) |
| `ScalarMonotone.EndOfPaper.network_tail_profiles` | [EndOfPaper/NetworkTailProfiles.lean:144](../EndOfPaper/NetworkTailProfiles.lean#L144) |
| `ScalarMonotone.EndOfPaper.network_equal_width_prefactor` | [EndOfPaper/NetworkEqualWidth.lean:12](../EndOfPaper/NetworkEqualWidth.lean#L12) |
| `ScalarMonotone.EndOfPaper.network_equal_width_inverse_dimension` | [EndOfPaper/NetworkEqualWidth.lean:29](../EndOfPaper/NetworkEqualWidth.lean#L29) |
| `ScalarMonotone.EndOfPaper.networkMedianMaximum` | [EndOfPaper/NetworkEqualWidth.lean:37](../EndOfPaper/NetworkEqualWidth.lean#L37) |
| `ScalarMonotone.EndOfPaper.network_medians_le_maximum` | [EndOfPaper/NetworkEqualWidth.lean:41](../EndOfPaper/NetworkEqualWidth.lean#L41) |
| `ScalarMonotone.EndOfPaper.network_depth_prefactor_uniform` | [EndOfPaper/NetworkRateDimensions.lean:11](../EndOfPaper/NetworkRateDimensions.lean#L11) |
| `ScalarMonotone.EndOfPaper.network_depth_threshold_uniform` | [EndOfPaper/NetworkRateDimensions.lean:23](../EndOfPaper/NetworkRateDimensions.lean#L23) |
| `ScalarMonotone.EndOfPaper.network_depth_polynomial_majorant` | [EndOfPaper/NetworkRateGrowth.lean:11](../EndOfPaper/NetworkRateGrowth.lean#L11) |
| `ScalarMonotone.EndOfPaper.network_depth_at_rate_inverse` | [EndOfPaper/NetworkRateGrowth.lean:45](../EndOfPaper/NetworkRateGrowth.lean#L45) |
| `ScalarMonotone.EndOfPaper.networkRateInverse` | [EndOfPaper/NetworkRateInverse.lean:12](../EndOfPaper/NetworkRateInverse.lean#L12) |
| `ScalarMonotone.EndOfPaper.networkRatePower` | [EndOfPaper/NetworkRateInverse.lean:15](../EndOfPaper/NetworkRateInverse.lean#L15) |
| `ScalarMonotone.EndOfPaper.nonnegative_min_square` | [EndOfPaper/NetworkRateInverse.lean:18](../EndOfPaper/NetworkRateInverse.lean#L18) |
| `ScalarMonotone.EndOfPaper.network_rate_root_square` | [EndOfPaper/NetworkRateInverse.lean:25](../EndOfPaper/NetworkRateInverse.lean#L25) |
| `ScalarMonotone.EndOfPaper.network_rate_inverse_properties` | [EndOfPaper/NetworkRateInverse.lean:37](../EndOfPaper/NetworkRateInverse.lean#L37) |
| `ScalarMonotone.EndOfPaper.network_subgaussian_depth` | [EndOfPaper/NetworkSubgaussianDepth.lean:14](../EndOfPaper/NetworkSubgaussianDepth.lean#L14) |
| `ScalarMonotone.EndOfPaper.network_subgaussian_two_regime_tail` | [EndOfPaper/NetworkSubgaussianRate.lean:13](../EndOfPaper/NetworkSubgaussianRate.lean#L13) |
| `ScalarMonotone.EndOfPaper.network_radius_at_exponential` | [EndOfPaper/NetworkTailRate.lean:12](../EndOfPaper/NetworkTailRate.lean#L12) |
| `ScalarMonotone.EndOfPaper.network_profile_implies_two_regime_tail` | [EndOfPaper/NetworkTailRate.lean:21](../EndOfPaper/NetworkTailRate.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_depth_tail_implies_uniform_rate` | [EndOfPaper/NetworkUniformRate.lean:12](../EndOfPaper/NetworkUniformRate.lean#L12) |
| `ScalarMonotone.EndOfPaper.decLE_value_le_singleton` | [EndOfPaper/PowerProfileMajorants.lean:16](../EndOfPaper/PowerProfileMajorants.lean#L16) |
| `ScalarMonotone.EndOfPaper.sqrt_log_control_value_bound` | [EndOfPaper/SqrtLogGeometric.lean:13](../EndOfPaper/SqrtLogGeometric.lean#L13) |
| `ScalarMonotone.EndOfPaper.positive_log_area_of_sqrt_log_control` | [EndOfPaper/SqrtLogGeometric.lean:21](../EndOfPaper/SqrtLogGeometric.lean#L21) |
| `ScalarMonotone.EndOfPaper.affine_sqrt_log_geometric_bound` | [EndOfPaper/SqrtLogGeometric.lean:35](../EndOfPaper/SqrtLogGeometric.lean#L35) |
| `ScalarMonotone.EndOfPaper.affine_geometric_sqrt_log_majorant` | [EndOfPaper/SqrtLogGeometric.lean:58](../EndOfPaper/SqrtLogGeometric.lean#L58) |
| `ScalarMonotone.EndOfPaper.networkDepthRadius` | [EndOfPaper/SqrtLogNetworkMajorant.lean:13](../EndOfPaper/SqrtLogNetworkMajorant.lean#L13) |
| `ScalarMonotone.EndOfPaper.network_depth_radius_geometric` | [EndOfPaper/SqrtLogNetworkMajorant.lean:15](../EndOfPaper/SqrtLogNetworkMajorant.lean#L15) |
| `ScalarMonotone.EndOfPaper.network_depth_radius_baseline` | [EndOfPaper/SqrtLogNetworkMajorant.lean:27](../EndOfPaper/SqrtLogNetworkMajorant.lean#L27) |
| `ScalarMonotone.EndOfPaper.affine_geometricPrefix_sqrt_log_majorant` | [EndOfPaper/SqrtLogNetworkMajorant.lean:34](../EndOfPaper/SqrtLogNetworkMajorant.lean#L34) |
| `ScalarMonotone.EndOfPaper.sqrt_log_network_selection_bound` | [EndOfPaper/SqrtLogNetworkMajorant.lean:51](../EndOfPaper/SqrtLogNetworkMajorant.lean#L51) |
| `ScalarMonotone.EndOfPaper.sqrtLogScalar` | [EndOfPaper/SqrtLogProfile.lean:13](../EndOfPaper/SqrtLogProfile.lean#L13) |
| `ScalarMonotone.EndOfPaper.sqrt_log_scalar_antitone` | [EndOfPaper/SqrtLogProfile.lean:15](../EndOfPaper/SqrtLogProfile.lean#L15) |
| `ScalarMonotone.EndOfPaper.sqrt_log_scalar_integrable` | [EndOfPaper/SqrtLogProfile.lean:19](../EndOfPaper/SqrtLogProfile.lean#L19) |
| `ScalarMonotone.EndOfPaper.positive_log_area_of_nonnegative_integrable` | [EndOfPaper/SqrtLogProfile.lean:23](../EndOfPaper/SqrtLogProfile.lean#L23) |
| `ScalarMonotone.EndOfPaper.affineSqrtLogProfile` | [EndOfPaper/SqrtLogProfile.lean:34](../EndOfPaper/SqrtLogProfile.lean#L34) |
| `ScalarMonotone.EndOfPaper.affine_sqrt_log_profile_properties` | [EndOfPaper/SqrtLogProfile.lean:40](../EndOfPaper/SqrtLogProfile.lean#L40) |
| `ScalarMonotone.EndOfPaper.affine_sqrt_log_integrable` | [EndOfPaper/SqrtLogProfile.lean:62](../EndOfPaper/SqrtLogProfile.lean#L62) |
| `ScalarMonotone.EndOfPaper.affine_sqrt_log_positive_log_area` | [EndOfPaper/SqrtLogProfile.lean:66](../EndOfPaper/SqrtLogProfile.lean#L66) |
| `ScalarMonotone.EndOfPaper.gaussianLogMarginal` | [EndOfPaper/GaussianCoordinateMarginal.lean:15](../EndOfPaper/GaussianCoordinateMarginal.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_coordinate_slice_lipschitz` | [EndOfPaper/GaussianCoordinateMarginal.lean:19](../EndOfPaper/GaussianCoordinateMarginal.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_log_marginal_lipschitz` | [EndOfPaper/GaussianCoordinateMarginal.lean:24](../EndOfPaper/GaussianCoordinateMarginal.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussian_log_marginal_midpoint_bound` | [EndOfPaper/GaussianCoordinateMarginal.lean:37](../EndOfPaper/GaussianCoordinateMarginal.lean#L37) |
| `ScalarMonotone.EndOfPaper.subgaussian_neg_mgf` | [EndOfPaper/GaussianCopyTail.lean:12](../EndOfPaper/GaussianCopyTail.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_weak_tail` | [EndOfPaper/GaussianCopyTail.lean:18](../EndOfPaper/GaussianCopyTail.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_subgaussian_fintype` | [EndOfPaper/GaussianFiniteIndex.lean:12](../EndOfPaper/GaussianFiniteIndex.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_tilt_lipschitz` | [EndOfPaper/GaussianFiniteMGF.lean:12](../EndOfPaper/GaussianFiniteMGF.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_tilt_pair_bound` | [EndOfPaper/GaussianFiniteMGF.lean:20](../EndOfPaper/GaussianFiniteMGF.lean#L20) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_lipschitz_copy_mgf` | [EndOfPaper/GaussianFiniteMGF.lean:31](../EndOfPaper/GaussianFiniteMGF.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_midpoint_log_integral` | [EndOfPaper/GaussianFiniteMidpoint.lean:12](../EndOfPaper/GaussianFiniteMidpoint.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_hs_normalized_median` | [EndOfPaper/GaussianHSNormMedian.lean:13](../EndOfPaper/GaussianHSNormMedian.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_profile_confidence_identity` | [EndOfPaper/GaussianInputProfile.lean:14](../EndOfPaper/GaussianInputProfile.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_input_profile` | [EndOfPaper/GaussianInputProfile.lean:27](../EndOfPaper/GaussianInputProfile.lean#L27) |
| `ScalarMonotone.EndOfPaper.lipschitz_general_exponential_majorant` | [EndOfPaper/GaussianLipschitzGeneral.lean:14](../EndOfPaper/GaussianLipschitzGeneral.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_real_exp_integrable_lipschitz` | [EndOfPaper/GaussianLipschitzGeneral.lean:26](../EndOfPaper/GaussianLipschitzGeneral.lean#L26) |
| `ScalarMonotone.EndOfPaper.gaussian_exp_integrable_lipschitz` | [EndOfPaper/GaussianLipschitzGeneral.lean:35](../EndOfPaper/GaussianLipschitzGeneral.lean#L35) |
| `ScalarMonotone.EndOfPaper.lipschitz_exponential_quadratic_majorant` | [EndOfPaper/GaussianLipschitzIntegrability.lean:12](../EndOfPaper/GaussianLipschitzIntegrability.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_exponential_integrable` | [EndOfPaper/GaussianLipschitzIntegrability.lean:28](../EndOfPaper/GaussianLipschitzIntegrability.lean#L28) |
| `ScalarMonotone.EndOfPaper.gaussianKernel` | [EndOfPaper/GaussianMidpoint.lean:13](../EndOfPaper/GaussianMidpoint.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_midpoint_energy` | [EndOfPaper/GaussianMidpoint.lean:16](../EndOfPaper/GaussianMidpoint.lean#L16) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_midpoint_domination` | [EndOfPaper/GaussianMidpoint.lean:25](../EndOfPaper/GaussianMidpoint.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_euclidean_norm_tail` | [EndOfPaper/GaussianNormMedian.lean:14](../EndOfPaper/GaussianNormMedian.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_euclidean_norm_median` | [EndOfPaper/GaussianNormMedian.lean:27](../EndOfPaper/GaussianNormMedian.lean#L27) |
| `ScalarMonotone.EndOfPaper.realMedian_of_div_positive` | [EndOfPaper/GaussianNormMedian.lean:54](../EndOfPaper/GaussianNormMedian.lean#L54) |
| `ScalarMonotone.EndOfPaper.gaussian_euclidean_normalized_norm_median` | [EndOfPaper/GaussianNormMedian.lean:65](../EndOfPaper/GaussianNormMedian.lean#L65) |
| `ScalarMonotone.EndOfPaper.linear_le_positive_quadratic` | [EndOfPaper/GaussianNormMGF.lean:12](../EndOfPaper/GaussianNormMGF.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_euclidean_norm_mgf` | [EndOfPaper/GaussianNormMGF.lean:19](../EndOfPaper/GaussianNormMGF.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_joint_law` | [EndOfPaper/GaussianOriginalLaw.lean:15](../EndOfPaper/GaussianOriginalLaw.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_exp_integral` | [EndOfPaper/GaussianOriginalLaw.lean:23](../EndOfPaper/GaussianOriginalLaw.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_exp` | [EndOfPaper/GaussianOriginalLaw.lean:37](../EndOfPaper/GaussianOriginalLaw.lean#L37) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_subgaussian` | [EndOfPaper/GaussianOriginalLaw.lean:69](../EndOfPaper/GaussianOriginalLaw.lean#L69) |
| `ScalarMonotone.EndOfPaper.gaussianSplitMeasurableEquiv` | [EndOfPaper/GaussianProductMarginal.lean:14](../EndOfPaper/GaussianProductMarginal.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_split_measure_preserving` | [EndOfPaper/GaussianProductMarginal.lean:18](../EndOfPaper/GaussianProductMarginal.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_split_vector` | [EndOfPaper/GaussianProductMarginal.lean:23](../EndOfPaper/GaussianProductMarginal.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral_marginal` | [EndOfPaper/GaussianProductMarginal.lean:30](../EndOfPaper/GaussianProductMarginal.lean#L30) |
| `ScalarMonotone.EndOfPaper.gaussianProductMeasure` | [EndOfPaper/GaussianProductMeasure.lean:14](../EndOfPaper/GaussianProductMeasure.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussianProductVector` | [EndOfPaper/GaussianProductMeasure.lean:16](../EndOfPaper/GaussianProductMeasure.lean#L16) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral` | [EndOfPaper/GaussianProductMeasure.lean:19](../EndOfPaper/GaussianProductMeasure.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_product_vector_measurable` | [EndOfPaper/GaussianProductMeasure.lean:22](../EndOfPaper/GaussianProductMeasure.lean#L22) |
| `ScalarMonotone.EndOfPaper.gaussian_product_coordinate_law` | [EndOfPaper/GaussianProductMeasure.lean:25](../EndOfPaper/GaussianProductMeasure.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_product_independent` | [EndOfPaper/GaussianProductMeasure.lean:50](../EndOfPaper/GaussianProductMeasure.lean#L50) |
| `ScalarMonotone.EndOfPaper.gaussian_product_exp_integrable` | [EndOfPaper/GaussianProductMeasure.lean:61](../EndOfPaper/GaussianProductMeasure.lean#L61) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral_positive` | [EndOfPaper/GaussianProductMeasure.lean:68](../EndOfPaper/GaussianProductMeasure.lean#L68) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral_zero` | [EndOfPaper/GaussianProductMeasure.lean:73](../EndOfPaper/GaussianProductMeasure.lean#L73) |
| `ScalarMonotone.EndOfPaper.gaussian_real_pdf_scalar` | [EndOfPaper/GaussianRealMidpoint.lean:14](../EndOfPaper/GaussianRealMidpoint.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_real_integrable_iff_weighted` | [EndOfPaper/GaussianRealMidpoint.lean:18](../EndOfPaper/GaussianRealMidpoint.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_real_midpoint_log_integral` | [EndOfPaper/GaussianRealMidpoint.lean:25](../EndOfPaper/GaussianRealMidpoint.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_square_laplace_bound` | [EndOfPaper/GaussianSquareChernoff.lean:13](../EndOfPaper/GaussianSquareChernoff.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_square_sum_chernoff` | [EndOfPaper/GaussianSquareChernoff.lean:30](../EndOfPaper/GaussianSquareChernoff.lean#L30) |
| `ScalarMonotone.EndOfPaper.gaussian_square_sum_norm_tail` | [EndOfPaper/GaussianSquareChernoff.lean:46](../EndOfPaper/GaussianSquareChernoff.lean#L46) |
| `ScalarMonotone.EndOfPaper.gaussian_square_exponential_density` | [EndOfPaper/GaussianSquareLaplace.lean:12](../EndOfPaper/GaussianSquareLaplace.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_square_exponential_integrable` | [EndOfPaper/GaussianSquareLaplace.lean:21](../EndOfPaper/GaussianSquareLaplace.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussian_square_laplace_raw` | [EndOfPaper/GaussianSquareLaplace.lean:31](../EndOfPaper/GaussianSquareLaplace.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_square_laplace` | [EndOfPaper/GaussianSquareLaplace.lean:38](../EndOfPaper/GaussianSquareLaplace.lean#L38) |
| `ScalarMonotone.EndOfPaper.independent_real_finset_product` | [EndOfPaper/GaussianSquareSumLaplace.lean:13](../EndOfPaper/GaussianSquareSumLaplace.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_square_sum_laplace` | [EndOfPaper/GaussianSquareSumLaplace.lean:29](../EndOfPaper/GaussianSquareSumLaplace.lean#L29) |
| `ScalarMonotone.EndOfPaper.gaussianCons` | [EndOfPaper/GaussianVectorSplit.lean:12](../EndOfPaper/GaussianVectorSplit.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussianTail` | [EndOfPaper/GaussianVectorSplit.lean:15](../EndOfPaper/GaussianVectorSplit.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussianCons_zero` | [EndOfPaper/GaussianVectorSplit.lean:18](../EndOfPaper/GaussianVectorSplit.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussianCons_succ` | [EndOfPaper/GaussianVectorSplit.lean:21](../EndOfPaper/GaussianVectorSplit.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussianTail_apply` | [EndOfPaper/GaussianVectorSplit.lean:24](../EndOfPaper/GaussianVectorSplit.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussianCons_sub_norm_sq` | [EndOfPaper/GaussianVectorSplit.lean:27](../EndOfPaper/GaussianVectorSplit.lean#L27) |
| `ScalarMonotone.EndOfPaper.gaussianCons_dist_sq` | [EndOfPaper/GaussianVectorSplit.lean:32](../EndOfPaper/GaussianVectorSplit.lean#L32) |
| `ScalarMonotone.EndOfPaper.gaussianCons_isometry` | [EndOfPaper/GaussianVectorSplit.lean:36](../EndOfPaper/GaussianVectorSplit.lean#L36) |
| `ScalarMonotone.EndOfPaper.gaussianCons_coordinate_isometry` | [EndOfPaper/GaussianVectorSplit.lean:43](../EndOfPaper/GaussianVectorSplit.lean#L43) |
| `ScalarMonotone.EndOfPaper.gaussianCons_head_tail` | [EndOfPaper/GaussianVectorSplit.lean:51](../EndOfPaper/GaussianVectorSplit.lean#L51) |
| `ScalarMonotone.EndOfPaper.logExpIntegral` | [EndOfPaper/LogExpMarginal.lean:14](../EndOfPaper/LogExpMarginal.lean#L14) |
| `ScalarMonotone.EndOfPaper.exponential_integral_comparison` | [EndOfPaper/LogExpMarginal.lean:17](../EndOfPaper/LogExpMarginal.lean#L17) |
| `ScalarMonotone.EndOfPaper.log_exp_integral_lipschitz` | [EndOfPaper/LogExpMarginal.lean:30](../EndOfPaper/LogExpMarginal.lean#L30) |
| `ScalarMonotone.EndOfPaper.positive_sqrt_transport_bound` | [EndOfPaper/MidpointPrekopaLeindler.lean:12](../EndOfPaper/MidpointPrekopaLeindler.lean#L12) |
| `ScalarMonotone.EndOfPaper.midpoint_integral_unit_density` | [EndOfPaper/MidpointPrekopaLeindler.lean:34](../EndOfPaper/MidpointPrekopaLeindler.lean#L34) |
| `ScalarMonotone.EndOfPaper.midpoint_prekopa_leindler_real` | [EndOfPaper/MidpointPrekopaLeindler.lean:49](../EndOfPaper/MidpointPrekopaLeindler.lean#L49) |
| `ScalarMonotone.EndOfPaper.positiveDensityCDF` | [EndOfPaper/PositiveDensityCDF.lean:15](../EndOfPaper/PositiveDensityCDF.lean#L15) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_eq_Iic` | [EndOfPaper/PositiveDensityCDF.lean:18](../EndOfPaper/PositiveDensityCDF.lean#L18) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_hasDerivAt` | [EndOfPaper/PositiveDensityCDF.lean:26](../EndOfPaper/PositiveDensityCDF.lean#L26) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_hasStrictDerivAt` | [EndOfPaper/PositiveDensityCDF.lean:30](../EndOfPaper/PositiveDensityCDF.lean#L30) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_strictMono` | [EndOfPaper/PositiveDensityCDF.lean:34](../EndOfPaper/PositiveDensityCDF.lean#L34) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_continuous` | [EndOfPaper/PositiveDensityCDF.lean:38](../EndOfPaper/PositiveDensityCDF.lean#L38) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_atBot` | [EndOfPaper/PositiveDensityCDF.lean:42](../EndOfPaper/PositiveDensityCDF.lean#L42) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_atTop` | [EndOfPaper/PositiveDensityCDF.lean:53](../EndOfPaper/PositiveDensityCDF.lean#L53) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_mem` | [EndOfPaper/PositiveDensityCDF.lean:60](../EndOfPaper/PositiveDensityCDF.lean#L60) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_range` | [EndOfPaper/PositiveDensityCDF.lean:72](../EndOfPaper/PositiveDensityCDF.lean#L72) |
| `ScalarMonotone.EndOfPaper.positive_density_mass_positive` | [EndOfPaper/PositiveDensityCDF.lean:90](../EndOfPaper/PositiveDensityCDF.lean#L90) |
| `ScalarMonotone.EndOfPaper.densityMidpointTransport` | [EndOfPaper/PositiveDensityMidpoint.lean:13](../EndOfPaper/PositiveDensityMidpoint.lean#L13) |
| `ScalarMonotone.EndOfPaper.densityMidpointJacobian` | [EndOfPaper/PositiveDensityMidpoint.lean:14](../EndOfPaper/PositiveDensityMidpoint.lean#L14) |
| `ScalarMonotone.EndOfPaper.density_midpoint_hasStrictDerivAt` | [EndOfPaper/PositiveDensityMidpoint.lean:22](../EndOfPaper/PositiveDensityMidpoint.lean#L22) |
| `ScalarMonotone.EndOfPaper.density_midpoint_jacobian_positive` | [EndOfPaper/PositiveDensityMidpoint.lean:27](../EndOfPaper/PositiveDensityMidpoint.lean#L27) |
| `ScalarMonotone.EndOfPaper.density_midpoint_continuous` | [EndOfPaper/PositiveDensityMidpoint.lean:30](../EndOfPaper/PositiveDensityMidpoint.lean#L30) |
| `ScalarMonotone.EndOfPaper.density_midpoint_strictMono` | [EndOfPaper/PositiveDensityMidpoint.lean:34](../EndOfPaper/PositiveDensityMidpoint.lean#L34) |
| `ScalarMonotone.EndOfPaper.density_midpoint_atTop` | [EndOfPaper/PositiveDensityMidpoint.lean:39](../EndOfPaper/PositiveDensityMidpoint.lean#L39) |
| `ScalarMonotone.EndOfPaper.density_midpoint_atBot` | [EndOfPaper/PositiveDensityMidpoint.lean:50](../EndOfPaper/PositiveDensityMidpoint.lean#L50) |
| `ScalarMonotone.EndOfPaper.density_midpoint_surjective` | [EndOfPaper/PositiveDensityMidpoint.lean:61](../EndOfPaper/PositiveDensityMidpoint.lean#L61) |
| `ScalarMonotone.EndOfPaper.density_midpoint_change_variables` | [EndOfPaper/PositiveDensityMidpoint.lean:70](../EndOfPaper/PositiveDensityMidpoint.lean#L70) |
| `ScalarMonotone.EndOfPaper.density_midpoint_pullback_integrable` | [EndOfPaper/PositiveDensityMidpoint.lean:86](../EndOfPaper/PositiveDensityMidpoint.lean#L86) |
| `ScalarMonotone.EndOfPaper.densityTransport` | [EndOfPaper/PositiveDensityTransport.lean:13](../EndOfPaper/PositiveDensityTransport.lean#L13) |
| `ScalarMonotone.EndOfPaper.density_transport_cdf` | [EndOfPaper/PositiveDensityTransport.lean:22](../EndOfPaper/PositiveDensityTransport.lean#L22) |
| `ScalarMonotone.EndOfPaper.density_transport_hasStrictDerivAt` | [EndOfPaper/PositiveDensityTransport.lean:31](../EndOfPaper/PositiveDensityTransport.lean#L31) |
| `ScalarMonotone.EndOfPaper.density_transport_continuous` | [EndOfPaper/PositiveDensityTransport.lean:41](../EndOfPaper/PositiveDensityTransport.lean#L41) |
| `ScalarMonotone.EndOfPaper.density_transport_strictMono` | [EndOfPaper/PositiveDensityTransport.lean:45](../EndOfPaper/PositiveDensityTransport.lean#L45) |
| `ScalarMonotone.EndOfPaper.density_transport_surjective` | [EndOfPaper/PositiveDensityTransport.lean:50](../EndOfPaper/PositiveDensityTransport.lean#L50) |
| `ScalarMonotone.EndOfPaper.gaussian_independent_coordinate_groups` | [EndOfPaper/GaussianCoordinateGroups.lean:11](../EndOfPaper/GaussianCoordinateGroups.lean#L11) |
| `ScalarMonotone.EndOfPaper.gaussian_product_coordinate_integration_by_parts` | [EndOfPaper/GaussianCoordinateIBP.lean:13](../EndOfPaper/GaussianCoordinateIBP.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussianPermutation` | [EndOfPaper/GaussianCoordinatePermutation.lean:13](../EndOfPaper/GaussianCoordinatePermutation.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_permutation_apply` | [EndOfPaper/GaussianCoordinatePermutation.lean:17](../EndOfPaper/GaussianCoordinatePermutation.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_permutation_vector` | [EndOfPaper/GaussianCoordinatePermutation.lean:20](../EndOfPaper/GaussianCoordinatePermutation.lean#L20) |
| `ScalarMonotone.EndOfPaper.gaussian_permutation_measure_preserving` | [EndOfPaper/GaussianCoordinatePermutation.lean:28](../EndOfPaper/GaussianCoordinatePermutation.lean#L28) |
| `ScalarMonotone.EndOfPaper.gaussian_product_integral_permutation` | [EndOfPaper/GaussianCoordinatePermutation.lean:33](../EndOfPaper/GaussianCoordinatePermutation.lean#L33) |
| `ScalarMonotone.EndOfPaper.gaussian_product_integrable_permutation` | [EndOfPaper/GaussianCoordinatePermutation.lean:41](../EndOfPaper/GaussianCoordinatePermutation.lean#L41) |
| `ScalarMonotone.EndOfPaper.gaussianReplace` | [EndOfPaper/GaussianCoordinatePermutation.lean:50](../EndOfPaper/GaussianCoordinatePermutation.lean#L50) |
| `ScalarMonotone.EndOfPaper.gaussian_replace_apply` | [EndOfPaper/GaussianCoordinatePermutation.lean:53](../EndOfPaper/GaussianCoordinatePermutation.lean#L53) |
| `ScalarMonotone.EndOfPaper.gaussian_replace_self` | [EndOfPaper/GaussianCoordinatePermutation.lean:56](../EndOfPaper/GaussianCoordinatePermutation.lean#L56) |
| `ScalarMonotone.EndOfPaper.gaussian_permutation_cons_replace` | [EndOfPaper/GaussianCoordinatePermutation.lean:61](../EndOfPaper/GaussianCoordinatePermutation.lean#L61) |
| `ScalarMonotone.EndOfPaper.gaussianFiniteMaxMoment` | [EndOfPaper/GaussianFiniteMaximumMoment.lean:14](../EndOfPaper/GaussianFiniteMaximumMoment.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_finite_maximum_continuous` | [EndOfPaper/GaussianFiniteMaximumMoment.lean:19](../EndOfPaper/GaussianFiniteMaximumMoment.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_finite_maximum_bound` | [EndOfPaper/GaussianFiniteMaximumMoment.lean:24](../EndOfPaper/GaussianFiniteMaximumMoment.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_finite_maximum_exp_integrable` | [EndOfPaper/GaussianFiniteMaximumMoment.lean:31](../EndOfPaper/GaussianFiniteMaximumMoment.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_finite_maximum_comparison_with_error` | [EndOfPaper/GaussianFiniteMaximumMoment.lean:43](../EndOfPaper/GaussianFiniteMaximumMoment.lean#L43) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_finite_maximum_moment_comparison` | [EndOfPaper/GaussianFiniteMaximumMoment.lean:80](../EndOfPaper/GaussianFiniteMaximumMoment.lean#L80) |
| `ScalarMonotone.EndOfPaper.gaussian_norm_one_lipschitz` | [EndOfPaper/GaussianGrowthIntegrability.lean:12](../EndOfPaper/GaussianGrowthIntegrability.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_product_norm_exp_integrable` | [EndOfPaper/GaussianGrowthIntegrability.lean:18](../EndOfPaper/GaussianGrowthIntegrability.lean#L18) |
| `ScalarMonotone.EndOfPaper.polynomial_times_norm_exponential_le` | [EndOfPaper/GaussianGrowthIntegrability.lean:23](../EndOfPaper/GaussianGrowthIntegrability.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_product_polynomial_exp_integrable` | [EndOfPaper/GaussianGrowthIntegrability.lean:32](../EndOfPaper/GaussianGrowthIntegrability.lean#L32) |
| `ScalarMonotone.EndOfPaper.gaussian_product_exp_dominated_integrable` | [EndOfPaper/GaussianGrowthIntegrability.lean:42](../EndOfPaper/GaussianGrowthIntegrability.lean#L42) |
| `ScalarMonotone.EndOfPaper.gaussian_real_pdf_hasDerivAt` | [EndOfPaper/GaussianIntegrationByParts.lean:13](../EndOfPaper/GaussianIntegrationByParts.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_real_integral_weighted` | [EndOfPaper/GaussianIntegrationByParts.lean:23](../EndOfPaper/GaussianIntegrationByParts.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_real_integration_by_parts` | [EndOfPaper/GaussianIntegrationByParts.lean:28](../EndOfPaper/GaussianIntegrationByParts.lean#L28) |
| `ScalarMonotone.EndOfPaper.gaussianCoefficientMass` | [EndOfPaper/GaussianInterpolationBounds.lean:15](../EndOfPaper/GaussianInterpolationBounds.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_coefficient_mass_nonneg` | [EndOfPaper/GaussianInterpolationBounds.lean:18](../EndOfPaper/GaussianInterpolationBounds.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_coefficient_row_le` | [EndOfPaper/GaussianInterpolationBounds.lean:22](../EndOfPaper/GaussianInterpolationBounds.lean#L22) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_process_abs_bound` | [EndOfPaper/GaussianInterpolationBounds.lean:27](../EndOfPaper/GaussianInterpolationBounds.lean#L27) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_softmax_bound` | [EndOfPaper/GaussianInterpolationBounds.lean:46](../EndOfPaper/GaussianInterpolationBounds.lean#L46) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_softmax_measurable` | [EndOfPaper/GaussianInterpolationBounds.lean:64](../EndOfPaper/GaussianInterpolationBounds.lean#L64) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_softmax_integrable` | [EndOfPaper/GaussianInterpolationBounds.lean:74](../EndOfPaper/GaussianInterpolationBounds.lean#L74) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolationMoment` | [EndOfPaper/GaussianInterpolationContinuity.lean:12](../EndOfPaper/GaussianInterpolationContinuity.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_softmax_continuous` | [EndOfPaper/GaussianInterpolationContinuity.lean:17](../EndOfPaper/GaussianInterpolationContinuity.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_moment_continuousOn` | [EndOfPaper/GaussianInterpolationContinuity.lean:30](../EndOfPaper/GaussianInterpolationContinuity.lean#L30) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolationCovarianceWeight` | [EndOfPaper/GaussianInterpolationCovariance.lean:12](../EndOfPaper/GaussianInterpolationCovariance.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_covariance_weight` | [EndOfPaper/GaussianInterpolationCovariance.lean:17](../EndOfPaper/GaussianInterpolationCovariance.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolationVelocity` | [EndOfPaper/GaussianInterpolationDerivative.lean:14](../EndOfPaper/GaussianInterpolationDerivative.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolationDerivative` | [EndOfPaper/GaussianInterpolationDerivative.lean:18](../EndOfPaper/GaussianInterpolationDerivative.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_softmax_hasDerivAt` | [EndOfPaper/GaussianInterpolationDerivative.lean:23](../EndOfPaper/GaussianInterpolationDerivative.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_neighborhood` | [EndOfPaper/GaussianInterpolationDerivative.lean:31](../EndOfPaper/GaussianInterpolationDerivative.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolationDominant` | [EndOfPaper/GaussianInterpolationDomination.lean:12](../EndOfPaper/GaussianInterpolationDomination.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_measurable` | [EndOfPaper/GaussianInterpolationDomination.lean:18](../EndOfPaper/GaussianInterpolationDomination.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_dominant_integrable` | [EndOfPaper/GaussianInterpolationDomination.lean:25](../EndOfPaper/GaussianInterpolationDomination.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_local_bound` | [EndOfPaper/GaussianInterpolationDomination.lean:35](../EndOfPaper/GaussianInterpolationDomination.lean#L35) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_moment_hasDerivAt` | [EndOfPaper/GaussianInterpolationDomination.lean:71](../EndOfPaper/GaussianInterpolationDomination.lean#L71) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_expansion` | [EndOfPaper/GaussianInterpolationExpansion.lean:13](../EndOfPaper/GaussianInterpolationExpansion.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_integral_expansion` | [EndOfPaper/GaussianInterpolationExpansion.lean:26](../EndOfPaper/GaussianInterpolationExpansion.lean#L26) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_gradient_coordinate_ibp_sum` | [EndOfPaper/GaussianInterpolationExpansion.lean:55](../EndOfPaper/GaussianInterpolationExpansion.lean#L55) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_covariance_weight_eq_sum` | [EndOfPaper/GaussianInterpolationExpansion.lean:71](../EndOfPaper/GaussianInterpolationExpansion.lean#L71) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_integral_covariance` | [EndOfPaper/GaussianInterpolationExpansion.lean:82](../EndOfPaper/GaussianInterpolationExpansion.lean#L82) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_integral_orthogonal` | [EndOfPaper/GaussianInterpolationExpansion.lean:102](../EndOfPaper/GaussianInterpolationExpansion.lean#L102) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_gradient_measurable` | [EndOfPaper/GaussianInterpolationIBP.lean:13](../EndOfPaper/GaussianInterpolationIBP.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_hessian_measurable` | [EndOfPaper/GaussianInterpolationIBP.lean:20](../EndOfPaper/GaussianInterpolationIBP.lean#L20) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_gradient_integrable` | [EndOfPaper/GaussianInterpolationIBP.lean:27](../EndOfPaper/GaussianInterpolationIBP.lean#L27) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_hessian_integrable` | [EndOfPaper/GaussianInterpolationIBP.lean:39](../EndOfPaper/GaussianInterpolationIBP.lean#L39) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_weighted_gradient_integrable` | [EndOfPaper/GaussianInterpolationIBP.lean:53](../EndOfPaper/GaussianInterpolationIBP.lean#L53) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_gradient_coordinate_ibp` | [EndOfPaper/GaussianInterpolationIBP.lean:81](../EndOfPaper/GaussianInterpolationIBP.lean#L81) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_hessian_covariance_integral` | [EndOfPaper/GaussianInterpolationMonotonicity.lean:13](../EndOfPaper/GaussianInterpolationMonotonicity.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_derivative_integral_nonpos` | [EndOfPaper/GaussianInterpolationMonotonicity.lean:32](../EndOfPaper/GaussianInterpolationMonotonicity.lean#L32) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_moment_antitoneOn` | [EndOfPaper/GaussianInterpolationMonotonicity.lean:51](../EndOfPaper/GaussianInterpolationMonotonicity.lean#L51) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_process_at_zero` | [EndOfPaper/GaussianInterpolationMonotonicity.lean:69](../EndOfPaper/GaussianInterpolationMonotonicity.lean#L69) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_process_at_one` | [EndOfPaper/GaussianInterpolationMonotonicity.lean:75](../EndOfPaper/GaussianInterpolationMonotonicity.lean#L75) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_softmax_moment_comparison` | [EndOfPaper/GaussianInterpolationMonotonicity.lean:81](../EndOfPaper/GaussianInterpolationMonotonicity.lean#L81) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolationVelocityMass` | [EndOfPaper/GaussianInterpolationVelocity.lean:12](../EndOfPaper/GaussianInterpolationVelocity.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_velocity_mass_nonneg` | [EndOfPaper/GaussianInterpolationVelocity.lean:17](../EndOfPaper/GaussianInterpolationVelocity.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolation_velocity_bound` | [EndOfPaper/GaussianInterpolationVelocity.lean:22](../EndOfPaper/GaussianInterpolationVelocity.lean#L22) |
| `ScalarMonotone.EndOfPaper.gaussianLinearProcess` | [EndOfPaper/GaussianLinearProcess.lean:14](../EndOfPaper/GaussianLinearProcess.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussianLinearCovariance` | [EndOfPaper/GaussianLinearProcess.lean:17](../EndOfPaper/GaussianLinearProcess.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussianInterpolatedProcess` | [EndOfPaper/GaussianLinearProcess.lean:20](../EndOfPaper/GaussianLinearProcess.lean#L20) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_process_abs_le` | [EndOfPaper/GaussianLinearProcess.lean:24](../EndOfPaper/GaussianLinearProcess.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_process_continuous` | [EndOfPaper/GaussianLinearProcess.lean:37](../EndOfPaper/GaussianLinearProcess.lean#L37) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_process_hasDerivAt` | [EndOfPaper/GaussianLinearProcess.lean:42](../EndOfPaper/GaussianLinearProcess.lean#L42) |
| `ScalarMonotone.EndOfPaper.gaussian_linear_process_replace_derivative` | [EndOfPaper/GaussianLinearProcess.lean:49](../EndOfPaper/GaussianLinearProcess.lean#L49) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_process_hasDerivAt` | [EndOfPaper/GaussianLinearProcess.lean:59](../EndOfPaper/GaussianLinearProcess.lean#L59) |
| `ScalarMonotone.EndOfPaper.gaussian_interpolated_process_replace_derivative` | [EndOfPaper/GaussianLinearProcess.lean:69](../EndOfPaper/GaussianLinearProcess.lean#L69) |
| `ScalarMonotone.EndOfPaper.gaussianMatrixCoefficient` | [EndOfPaper/GaussianMatrixCovariance.lean:12](../EndOfPaper/GaussianMatrixCovariance.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussianVectorComparisonCoefficient` | [EndOfPaper/GaussianMatrixCovariance.lean:17](../EndOfPaper/GaussianMatrixCovariance.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_real_euclidean_inner` | [EndOfPaper/GaussianMatrixCovariance.lean:20](../EndOfPaper/GaussianMatrixCovariance.lean#L20) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_coefficient_covariance` | [EndOfPaper/GaussianMatrixCovariance.lean:28](../EndOfPaper/GaussianMatrixCovariance.lean#L28) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_comparison_covariance` | [EndOfPaper/GaussianMatrixCovariance.lean:46](../EndOfPaper/GaussianMatrixCovariance.lean#L46) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_covariance_difference` | [EndOfPaper/GaussianMatrixCovariance.lean:53](../EndOfPaper/GaussianMatrixCovariance.lean#L53) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_covariance_nonneg` | [EndOfPaper/GaussianMatrixCovariance.lean:61](../EndOfPaper/GaussianMatrixCovariance.lean#L61) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_variances` | [EndOfPaper/GaussianMatrixCovariance.lean:71](../EndOfPaper/GaussianMatrixCovariance.lean#L71) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_operator_norm_mgf` | [EndOfPaper/GaussianMatrixDenseMoment.lean:14](../EndOfPaper/GaussianMatrixDenseMoment.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_unit_family_maximum_comparison` | [EndOfPaper/GaussianMatrixFiniteComparison.lean:13](../EndOfPaper/GaussianMatrixFiniteComparison.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_finite_family_moment` | [EndOfPaper/GaussianMatrixFiniteMoment.lean:13](../EndOfPaper/GaussianMatrixFiniteMoment.lean#L13) |
| `ScalarMonotone.EndOfPaper.GaussianMatrixJointIndex` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:14](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussianMatrixJointDimension` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:16](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L16) |
| `ScalarMonotone.EndOfPaper.gaussianMatrixJointCoefficient` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:19](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussianVectorJointCoefficient` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:24](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_joint_index_card` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:29](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L29) |
| `ScalarMonotone.EndOfPaper.gaussianMatrixJointIndexEquiv` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:34](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L34) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_joint_covariance` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:38](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L38) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_joint_covariance` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:45](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L45) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_vector_joint_cross` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:52](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L52) |
| `ScalarMonotone.EndOfPaper.gaussianRelabelCoefficients` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:58](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L58) |
| `ScalarMonotone.EndOfPaper.gaussian_relabel_pairing` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:61](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L61) |
| `ScalarMonotone.EndOfPaper.gaussianMatrixComparisonArray` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:68](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L68) |
| `ScalarMonotone.EndOfPaper.gaussianVectorComparisonArray` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:73](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L73) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_array_cross` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:78](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L78) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_array_covariance` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:85](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L85) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_comparison_array_covariance` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:93](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L93) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_array_diagonal` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:101](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L101) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_comparison_array_order` | [EndOfPaper/GaussianMatrixJointCoefficients.lean:110](../EndOfPaper/GaussianMatrixJointCoefficients.lean#L110) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_group_coordinate_law` | [EndOfPaper/GaussianMatrixJointMoments.lean:15](../EndOfPaper/GaussianMatrixJointMoments.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_group_coordinate_measurable` | [EndOfPaper/GaussianMatrixJointMoments.lean:21](../EndOfPaper/GaussianMatrixJointMoments.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_vector_norm_sum_mgf` | [EndOfPaper/GaussianMatrixJointMoments.lean:25](../EndOfPaper/GaussianMatrixJointMoments.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_scalar_exp_integral` | [EndOfPaper/GaussianMatrixJointMoments.lean:63](../EndOfPaper/GaussianMatrixJointMoments.lean#L63) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_operator_scalar_exp_factor` | [EndOfPaper/GaussianMatrixJointMoments.lean:76](../EndOfPaper/GaussianMatrixJointMoments.lean#L76) |
| `ScalarMonotone.EndOfPaper.gaussianJointCoordinate` | [EndOfPaper/GaussianMatrixJointSample.lean:13](../EndOfPaper/GaussianMatrixJointSample.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussianJointGroup` | [EndOfPaper/GaussianMatrixJointSample.lean:17](../EndOfPaper/GaussianMatrixJointSample.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussianJointMatrix` | [EndOfPaper/GaussianMatrixJointSample.lean:22](../EndOfPaper/GaussianMatrixJointSample.lean#L22) |
| `ScalarMonotone.EndOfPaper.gaussianJointLeftVector` | [EndOfPaper/GaussianMatrixJointSample.lean:26](../EndOfPaper/GaussianMatrixJointSample.lean#L26) |
| `ScalarMonotone.EndOfPaper.gaussianJointRightVector` | [EndOfPaper/GaussianMatrixJointSample.lean:30](../EndOfPaper/GaussianMatrixJointSample.lean#L30) |
| `ScalarMonotone.EndOfPaper.gaussianJointScalar` | [EndOfPaper/GaussianMatrixJointSample.lean:34](../EndOfPaper/GaussianMatrixJointSample.lean#L34) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_coordinate_measurable` | [EndOfPaper/GaussianMatrixJointSample.lean:38](../EndOfPaper/GaussianMatrixJointSample.lean#L38) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_coordinate_law` | [EndOfPaper/GaussianMatrixJointSample.lean:42](../EndOfPaper/GaussianMatrixJointSample.lean#L42) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_group_measurable` | [EndOfPaper/GaussianMatrixJointSample.lean:47](../EndOfPaper/GaussianMatrixJointSample.lean#L47) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_group_independent` | [EndOfPaper/GaussianMatrixJointSample.lean:52](../EndOfPaper/GaussianMatrixJointSample.lean#L52) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_groups_independent` | [EndOfPaper/GaussianMatrixJointSample.lean:58](../EndOfPaper/GaussianMatrixJointSample.lean#L58) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_vector_independence` | [EndOfPaper/GaussianMatrixJointSample.lean:74](../EndOfPaper/GaussianMatrixJointSample.lean#L74) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_matrix_scalar_independence` | [EndOfPaper/GaussianMatrixJointSample.lean:81](../EndOfPaper/GaussianMatrixJointSample.lean#L81) |
| `ScalarMonotone.EndOfPaper.gaussian_relabel_linear_process` | [EndOfPaper/GaussianMatrixJointSample.lean:95](../EndOfPaper/GaussianMatrixJointSample.lean#L95) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_matrix_process` | [EndOfPaper/GaussianMatrixJointSample.lean:102](../EndOfPaper/GaussianMatrixJointSample.lean#L102) |
| `ScalarMonotone.EndOfPaper.gaussian_joint_vector_process` | [EndOfPaper/GaussianMatrixJointSample.lean:124](../EndOfPaper/GaussianMatrixJointSample.lean#L124) |
| `ScalarMonotone.EndOfPaper.realMedian_le_of_gaussian_upper_tails` | [EndOfPaper/GaussianMatrixMedian.lean:13](../EndOfPaper/GaussianMatrixMedian.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_operator_norm_median` | [EndOfPaper/GaussianMatrixMedian.lean:38](../EndOfPaper/GaussianMatrixMedian.lean#L38) |
| `ScalarMonotone.EndOfPaper.gaussian_square_matrix_normalized_operator_median` | [EndOfPaper/GaussianMatrixMedian.lean:48](../EndOfPaper/GaussianMatrixMedian.lean#L48) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_median_normalization` | [EndOfPaper/GaussianMatrixNormalization.lean:10](../EndOfPaper/GaussianMatrixNormalization.lean#L10) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_operator_exponential_integrable` | [EndOfPaper/GaussianMatrixOperatorIntegrability.lean:14](../EndOfPaper/GaussianMatrixOperatorIntegrability.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_joint_identDistrib` | [EndOfPaper/GaussianMatrixOriginalLaw.lean:12](../EndOfPaper/GaussianMatrixOriginalLaw.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_operator_norm_mgf` | [EndOfPaper/GaussianMatrixOriginalLaw.lean:42](../EndOfPaper/GaussianMatrixOriginalLaw.lean#L42) |
| `ScalarMonotone.EndOfPaper.gaussian_matrix_operator_norm_tail` | [EndOfPaper/GaussianMatrixTail.lean:12](../EndOfPaper/GaussianMatrixTail.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_network_data_median` | [EndOfPaper/GaussianNetworkMedians.lean:13](../EndOfPaper/GaussianNetworkMedians.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_network_weight_median` | [EndOfPaper/GaussianNetworkMedians.lean:26](../EndOfPaper/GaussianNetworkMedians.lean#L26) |
| `ScalarMonotone.EndOfPaper.gaussian_network_norm_medians` | [EndOfPaper/GaussianNetworkMedians.lean:44](../EndOfPaper/GaussianNetworkMedians.lean#L44) |
| `ScalarMonotone.EndOfPaper.GaussianUnitVector` | [EndOfPaper/GaussianOperatorUnitPairs.lean:15](../EndOfPaper/GaussianOperatorUnitPairs.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussianUnitPairValue` | [EndOfPaper/GaussianOperatorUnitPairs.lean:29](../EndOfPaper/GaussianOperatorUnitPairs.lean#L29) |
| `ScalarMonotone.EndOfPaper.gaussian_unit_pair_value_continuous` | [EndOfPaper/GaussianOperatorUnitPairs.lean:34](../EndOfPaper/GaussianOperatorUnitPairs.lean#L34) |
| `ScalarMonotone.EndOfPaper.gaussian_unit_pair_value_le` | [EndOfPaper/GaussianOperatorUnitPairs.lean:40](../EndOfPaper/GaussianOperatorUnitPairs.lean#L40) |
| `ScalarMonotone.EndOfPaper.gaussian_unit_pair_value_isLUB` | [EndOfPaper/GaussianOperatorUnitPairs.lean:50](../EndOfPaper/GaussianOperatorUnitPairs.lean#L50) |
| `ScalarMonotone.EndOfPaper.gaussianUnitPairSequence` | [EndOfPaper/GaussianOperatorUnitPairs.lean:87](../EndOfPaper/GaussianOperatorUnitPairs.lean#L87) |
| `ScalarMonotone.EndOfPaper.gaussian_unit_pair_sequence_dense` | [EndOfPaper/GaussianOperatorUnitPairs.lean:91](../EndOfPaper/GaussianOperatorUnitPairs.lean#L91) |
| `ScalarMonotone.EndOfPaper.gaussian_operator_dense_maximum_tendsto` | [EndOfPaper/GaussianOperatorUnitPairs.lean:95](../EndOfPaper/GaussianOperatorUnitPairs.lean#L95) |
| `ScalarMonotone.EndOfPaper.gaussian_product_first_integration_by_parts` | [EndOfPaper/GaussianProductIBP.lean:13](../EndOfPaper/GaussianProductIBP.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussianSplitIntegrand` | [EndOfPaper/GaussianProductIntegralSplit.lean:12](../EndOfPaper/GaussianProductIntegralSplit.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_split_integrand_representation` | [EndOfPaper/GaussianProductIntegralSplit.lean:15](../EndOfPaper/GaussianProductIntegralSplit.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_split_integrand_measurable` | [EndOfPaper/GaussianProductIntegralSplit.lean:23](../EndOfPaper/GaussianProductIntegralSplit.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_split_integrable_iff` | [EndOfPaper/GaussianProductIntegralSplit.lean:32](../EndOfPaper/GaussianProductIntegralSplit.lean#L32) |
| `ScalarMonotone.EndOfPaper.gaussian_product_integral_split` | [EndOfPaper/GaussianProductIntegralSplit.lean:42](../EndOfPaper/GaussianProductIntegralSplit.lean#L42) |
| `ScalarMonotone.EndOfPaper.gaussianSequenceMaximum` | [EndOfPaper/GaussianSequenceMaximum.lean:14](../EndOfPaper/GaussianSequenceMaximum.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_maximum_add_constant` | [EndOfPaper/GaussianSequenceMaximum.lean:17](../EndOfPaper/GaussianSequenceMaximum.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_sequence_maximum_upper` | [EndOfPaper/GaussianSequenceMaximum.lean:27](../EndOfPaper/GaussianSequenceMaximum.lean#L27) |
| `ScalarMonotone.EndOfPaper.gaussian_le_sequence_maximum` | [EndOfPaper/GaussianSequenceMaximum.lean:31](../EndOfPaper/GaussianSequenceMaximum.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_sequence_maximum_monotone` | [EndOfPaper/GaussianSequenceMaximum.lean:35](../EndOfPaper/GaussianSequenceMaximum.lean#L35) |
| `ScalarMonotone.EndOfPaper.gaussian_sequence_maximum_isLUB` | [EndOfPaper/GaussianSequenceMaximum.lean:42](../EndOfPaper/GaussianSequenceMaximum.lean#L42) |
| `ScalarMonotone.EndOfPaper.gaussian_sequence_maximum_tendsto` | [EndOfPaper/GaussianSequenceMaximum.lean:52](../EndOfPaper/GaussianSequenceMaximum.lean#L52) |
| `ScalarMonotone.EndOfPaper.gaussian_dense_continuous_isLUB` | [EndOfPaper/GaussianSequenceMaximum.lean:56](../EndOfPaper/GaussianSequenceMaximum.lean#L56) |
| `ScalarMonotone.EndOfPaper.gaussianExpSum` | [EndOfPaper/GaussianSoftmax.lean:15](../EndOfPaper/GaussianSoftmax.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussianSoftmax` | [EndOfPaper/GaussianSoftmax.lean:18](../EndOfPaper/GaussianSoftmax.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussianSoftmaxWeight` | [EndOfPaper/GaussianSoftmax.lean:21](../EndOfPaper/GaussianSoftmax.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussianSoftmaxMoment` | [EndOfPaper/GaussianSoftmax.lean:24](../EndOfPaper/GaussianSoftmax.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussian_exp_sum_positive` | [EndOfPaper/GaussianSoftmax.lean:27](../EndOfPaper/GaussianSoftmax.lean#L27) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_weight_positive` | [EndOfPaper/GaussianSoftmax.lean:31](../EndOfPaper/GaussianSoftmax.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_weight_sum` | [EndOfPaper/GaussianSoftmax.lean:35](../EndOfPaper/GaussianSoftmax.lean#L35) |
| `ScalarMonotone.EndOfPaper.gaussian_exp_sum_hasDerivAt` | [EndOfPaper/GaussianSoftmax.lean:40](../EndOfPaper/GaussianSoftmax.lean#L40) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_hasDerivAt` | [EndOfPaper/GaussianSoftmax.lean:51](../EndOfPaper/GaussianSoftmax.lean#L51) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_moment_hasDerivAt` | [EndOfPaper/GaussianSoftmax.lean:61](../EndOfPaper/GaussianSoftmax.lean#L61) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_weight_hasDerivAt` | [EndOfPaper/GaussianSoftmax.lean:71](../EndOfPaper/GaussianSoftmax.lean#L71) |
| `ScalarMonotone.EndOfPaper.gaussianSoftmaxGradient` | [EndOfPaper/GaussianSoftmax.lean:87](../EndOfPaper/GaussianSoftmax.lean#L87) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_gradient_hasDerivAt` | [EndOfPaper/GaussianSoftmax.lean:90](../EndOfPaper/GaussianSoftmax.lean#L90) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_off_diagonal_derivative` | [EndOfPaper/GaussianSoftmax.lean:105](../EndOfPaper/GaussianSoftmax.lean#L105) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_off_diagonal_nonpos` | [EndOfPaper/GaussianSoftmax.lean:118](../EndOfPaper/GaussianSoftmax.lean#L118) |
| `ScalarMonotone.EndOfPaper.gaussianFiniteMaximum` | [EndOfPaper/GaussianSoftmaxApprox.lean:13](../EndOfPaper/GaussianSoftmaxApprox.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_le_finite_maximum` | [EndOfPaper/GaussianSoftmaxApprox.lean:16](../EndOfPaper/GaussianSoftmaxApprox.lean#L16) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_maximum_le` | [EndOfPaper/GaussianSoftmaxApprox.lean:19](../EndOfPaper/GaussianSoftmaxApprox.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_maximum_le_softmax` | [EndOfPaper/GaussianSoftmaxApprox.lean:23](../EndOfPaper/GaussianSoftmaxApprox.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_le_finite_maximum` | [EndOfPaper/GaussianSoftmaxApprox.lean:35](../EndOfPaper/GaussianSoftmaxApprox.lean#L35) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_moment_bound` | [EndOfPaper/GaussianSoftmaxApprox.lean:51](../EndOfPaper/GaussianSoftmaxApprox.lean#L51) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_moment_positive` | [EndOfPaper/GaussianSoftmaxBounds.lean:12](../EndOfPaper/GaussianSoftmaxBounds.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_weight_le_one` | [EndOfPaper/GaussianSoftmaxBounds.lean:15](../EndOfPaper/GaussianSoftmaxBounds.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_gradient_abs_bound` | [EndOfPaper/GaussianSoftmaxBounds.lean:21](../EndOfPaper/GaussianSoftmaxBounds.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_hessian_abs_bound` | [EndOfPaper/GaussianSoftmaxBounds.lean:30](../EndOfPaper/GaussianSoftmaxBounds.lean#L30) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_hessian_directional_sum` | [EndOfPaper/GaussianSoftmaxDirectional.lean:12](../EndOfPaper/GaussianSoftmaxDirectional.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_moment_path_derivative` | [EndOfPaper/GaussianSoftmaxDirectional.lean:26](../EndOfPaper/GaussianSoftmaxDirectional.lean#L26) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_gradient_path_derivative` | [EndOfPaper/GaussianSoftmaxDirectional.lean:38](../EndOfPaper/GaussianSoftmaxDirectional.lean#L38) |
| `ScalarMonotone.EndOfPaper.gaussianSoftmaxHessian` | [EndOfPaper/GaussianSoftmaxHessian.lean:12](../EndOfPaper/GaussianSoftmaxHessian.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_hessian_hasDerivAt` | [EndOfPaper/GaussianSoftmaxHessian.lean:17](../EndOfPaper/GaussianSoftmaxHessian.lean#L17) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_hessian_off_diagonal_nonpos` | [EndOfPaper/GaussianSoftmaxHessian.lean:28](../EndOfPaper/GaussianSoftmaxHessian.lean#L28) |
| `ScalarMonotone.EndOfPaper.gaussian_softmax_covariance_contraction_nonpos` | [EndOfPaper/GaussianSoftmaxHessian.lean:34](../EndOfPaper/GaussianSoftmaxHessian.lean#L34) |
<a id="result-3-11"></a>

## Example 3.11

[PDF page 56](../manuscript/monotone_calculus.pdf#page=56). Power tails

Exactly the original positive network dimensions and depth, actual HS parameter/network model and activation assumptions, arbitrary original measurable joint law and independent identical copy, actual normalized norm medians and output median, nonnegative completed baseline profile on (0,1) with the original comparison for every one-Lipschitz real observation, and A,alpha>0 with qDelta below the actual completed A*u^(-alpha). Positive-log area and measurable representatives are derived. No marginal-entry independence or ordinary power-profile/input/output L1 is assumed, including alpha>=1. network_power_tails proves the whole completed quantile comparison, maximality, exact domain interior (0,1), every interior quantile value bound and strict tails for the literal D*A*exp(alpha*L)*(6/u)^alpha times the product of max(m_x,m_i)+A*(12/u)^alpha/sqrt(min(N*p_0,p_(i+1)+p_i)). The exact formula is proved separately. network_power_far_tail proves that multiplying this displayed upper profile by u^(alpha*(L+1)) tends to an explicit strictly positive constant as u decreases to zero. This certifies the exponent of the displayed bound, without asserting a lower tail for every actual output. Derive log-area finiteness from power control. Compare actual completed affine geometric profiles with the checked affine-power transform for all alpha>0. Construct the displayed product as a maximal completed continuous scalar profile and bound the actual network target selection. Transfer strict-tail tests to the whole quantile graph and every interior fiber. Collect the exponential factors exactly. Prove the exact rescaled product identity and its limit, with positivity from the original dimensions. Independent readers expand D and every dimension and probability factor. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.affine_power_geometric_bound` | [EndOfPaper/AffinePowerProfile.lean:66](../EndOfPaper/AffinePowerProfile.lean#L66) |
| `ScalarMonotone.EndOfPaper.network_tail_profiles` | [EndOfPaper/NetworkTailProfiles.lean:144](../EndOfPaper/NetworkTailProfiles.lean#L144) |
| `ScalarMonotone.EndOfPaper.network_inverse_dimension_pos` | [EndOfPaper/NetworkPowerTails.lean:14](../EndOfPaper/NetworkPowerTails.lean#L14) |
| `ScalarMonotone.EndOfPaper.power_network_bound_network_formula` | [EndOfPaper/NetworkPowerTails.lean:21](../EndOfPaper/NetworkPowerTails.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_power_far_tail` | [EndOfPaper/NetworkPowerTails.lean:36](../EndOfPaper/NetworkPowerTails.lean#L36) |
| `ScalarMonotone.EndOfPaper.network_power_tails` | [EndOfPaper/NetworkPowerTails.lean:48](../EndOfPaper/NetworkPowerTails.lean#L48) |
| `ScalarMonotone.EndOfPaper.power_network_bound_rescaled` | [EndOfPaper/PowerNetworkAsymptotic.lean:13](../EndOfPaper/PowerNetworkAsymptotic.lean#L13) |
| `ScalarMonotone.EndOfPaper.power_network_far_tail_limit` | [EndOfPaper/PowerNetworkAsymptotic.lean:42](../EndOfPaper/PowerNetworkAsymptotic.lean#L42) |
| `ScalarMonotone.EndOfPaper.power_network_far_tail_constant_positive` | [EndOfPaper/PowerNetworkAsymptotic.lean:63](../EndOfPaper/PowerNetworkAsymptotic.lean#L63) |
| `ScalarMonotone.EndOfPaper.affine_geometricPrefix_power_majorant` | [EndOfPaper/PowerNetworkProfile.lean:13](../EndOfPaper/PowerNetworkProfile.lean#L13) |
| `ScalarMonotone.EndOfPaper.negative_power_division` | [EndOfPaper/PowerNetworkProfile.lean:29](../EndOfPaper/PowerNetworkProfile.lean#L29) |
| `ScalarMonotone.EndOfPaper.powerNetworkBound` | [EndOfPaper/PowerNetworkProfile.lean:36](../EndOfPaper/PowerNetworkProfile.lean#L36) |
| `ScalarMonotone.EndOfPaper.power_network_bound_nonnegative` | [EndOfPaper/PowerNetworkProfile.lean:40](../EndOfPaper/PowerNetworkProfile.lean#L40) |
| `ScalarMonotone.EndOfPaper.power_network_bound_antitone` | [EndOfPaper/PowerNetworkProfile.lean:49](../EndOfPaper/PowerNetworkProfile.lean#L49) |
| `ScalarMonotone.EndOfPaper.power_network_bound_continuous` | [EndOfPaper/PowerNetworkProfile.lean:72](../EndOfPaper/PowerNetworkProfile.lean#L72) |
| `ScalarMonotone.EndOfPaper.powerNetworkProfile` | [EndOfPaper/PowerNetworkProfile.lean:81](../EndOfPaper/PowerNetworkProfile.lean#L81) |
| `ScalarMonotone.EndOfPaper.power_network_profile_properties` | [EndOfPaper/PowerNetworkProfile.lean:88](../EndOfPaper/PowerNetworkProfile.lean#L88) |
| `ScalarMonotone.EndOfPaper.power_network_bound_collect` | [EndOfPaper/PowerNetworkProfile.lean:104](../EndOfPaper/PowerNetworkProfile.lean#L104) |
| `ScalarMonotone.EndOfPaper.power_network_selection_bound` | [EndOfPaper/PowerNetworkProfile.lean:113](../EndOfPaper/PowerNetworkProfile.lean#L113) |
| `ScalarMonotone.EndOfPaper.decLE_value_le_singleton` | [EndOfPaper/PowerProfileMajorants.lean:16](../EndOfPaper/PowerProfileMajorants.lean#L16) |
| `ScalarMonotone.EndOfPaper.power_control_value_bound` | [EndOfPaper/PowerProfileMajorants.lean:25](../EndOfPaper/PowerProfileMajorants.lean#L25) |
| `ScalarMonotone.EndOfPaper.positive_log_area_of_power_control` | [EndOfPaper/PowerProfileMajorants.lean:33](../EndOfPaper/PowerProfileMajorants.lean#L33) |
| `ScalarMonotone.EndOfPaper.affine_geometric_power_majorant` | [EndOfPaper/PowerProfileMajorants.lean:49](../EndOfPaper/PowerProfileMajorants.lean#L49) |
<a id="result-A-1"></a>

## Lemma A.1

[PDF page 58](../manuscript/monotone_calculus.pdf#page=58). Power–geometric limit

Arbitrary positive a,b and every weight in the closed interval [0,1], including both endpoint weights. Kappa tends to infinity through the real numbers, with the paper's exact varying real exponent. The weighted negative-power mean tends to a^weight*b^(1-weight). Every weighted base and mean is positive, including degenerate endpoint weights. Differentiate the logarithm of the weighted exponential mixture at zero and evaluate its slope along 1/kappa tending to zero. The exact negative-kappa logarithm tends to the weighted logarithm. Continuity of exp and the positive-base rpow identity produce the literal weighted geometric mean. The independent expected type expands the definition of the mean. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.weightedPowerMean` | [EndOfPaper/PowerGeometric.lean:15](../EndOfPaper/PowerGeometric.lean#L15) |
| `ScalarMonotone.EndOfPaper.weighted_power_base_positive` | [EndOfPaper/PowerGeometric.lean:18](../EndOfPaper/PowerGeometric.lean#L18) |
| `ScalarMonotone.EndOfPaper.weightedPowerMean_positive` | [EndOfPaper/PowerGeometric.lean:28](../EndOfPaper/PowerGeometric.lean#L28) |
| `ScalarMonotone.EndOfPaper.weighted_power_geometric_limit` | [EndOfPaper/PowerGeometric.lean:33](../EndOfPaper/PowerGeometric.lean#L33) |
<a id="claim-1"></a>

## After Proposition 1.2

[PDF page 6](../manuscript/monotone_calculus.pdf#page=6). Graph topology, interval domains/ranges/fibers, and inversion

Both maximal orientations have closed connected entire graphs, interval domains/ranges, and closed interval nonempty fibers; boundedness is not imposed at boundary fibers. Relational inversion preserves maximality and orientation. These are direct manuscript statements, supplied by the listed declarations. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.graph_closed` | [MonotoneOperators/Minty.lean:173](../MonotoneOperators/Minty.lean#L173) |
| `ScalarMonotone.graph_connected` | [MonotoneOperators/Minty.lean:181](../MonotoneOperators/Minty.lean#L181) |
| `ScalarMonotone.dom_ordConnected` | [MonotoneOperators/Minty.lean:150](../MonotoneOperators/Minty.lean#L150) |
| `ScalarMonotone.ran_ordConnected` | [MonotoneOperators/Minty.lean:154](../MonotoneOperators/Minty.lean#L154) |
| `ScalarMonotone.maximal_fiber_closed` | [MonotoneOperators/Basic.lean:196](../MonotoneOperators/Basic.lean#L196) |
| `ScalarMonotone.maximal_fiber_ordConnected` | [MonotoneOperators/Basic.lean:184](../MonotoneOperators/Basic.lean#L184) |
| `ScalarMonotone.inverse_maximal` | [MonotoneOperators/Basic.lean:119](../MonotoneOperators/Basic.lean#L119) |
| `ScalarMonotone.decreasing_graph_closed` | [MonotoneOperators/Minty.lean:305](../MonotoneOperators/Minty.lean#L305) |
| `ScalarMonotone.decreasing_graph_connected` | [MonotoneOperators/Minty.lean:313](../MonotoneOperators/Minty.lean#L313) |
| `ScalarMonotone.decreasing_dom_ordConnected` | [MonotoneOperators/Minty.lean:318](../MonotoneOperators/Minty.lean#L318) |
| `ScalarMonotone.decreasing_ran_ordConnected` | [MonotoneOperators/Minty.lean:329](../MonotoneOperators/Minty.lean#L329) |
| `ScalarMonotone.decreasing_fiber_closed` | [MonotoneOperators/Minty.lean:343](../MonotoneOperators/Minty.lean#L343) |
| `ScalarMonotone.decreasing_fiber_ordConnected` | [MonotoneOperators/Minty.lean:333](../MonotoneOperators/Minty.lean#L333) |
| `ScalarMonotone.inverse_maximal_decreasing` | [MonotoneOperators/Basic.lean:222](../MonotoneOperators/Basic.lean#L222) |
<a id="claim-2"></a>

## Equation (1.33)

[PDF page 24](../manuscript/monotone_calculus.pdf#page=24). Ordinary and parallel algebra definitions, associativity, commutativity, domain/range identities

The definitions are the exact relational inverse of the ordinary sum/product of inverse graphs. Associativity, commutativity and the entire range intersection hold for arbitrary graphs. For either maximal orientation, a nonempty range intersection gives parallel-sum maximality and the exact Minkowski domain sum, including a singleton intersection. The two parallel-product iff criteria require nonnegative domains and retain the zero degeneracy, so nonnegativity alone is not asserted to imply maximality. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.parallelAdd_comm` | [MonotoneOperators/Algebra.lean:91](../MonotoneOperators/Algebra.lean#L91) |
| `ScalarMonotone.parallelAdd_assoc` | [MonotoneOperators/Algebra.lean:95](../MonotoneOperators/Algebra.lean#L95) |
| `ScalarMonotone.parallelMul_comm` | [MonotoneOperators/Algebra.lean:99](../MonotoneOperators/Algebra.lean#L99) |
| `ScalarMonotone.parallelMul_assoc` | [MonotoneOperators/Algebra.lean:103](../MonotoneOperators/Algebra.lean#L103) |
| `ScalarMonotone.ran_parallelAdd` | [MonotoneOperators/Algebra.lean:107](../MonotoneOperators/Algebra.lean#L107) |
| `ScalarMonotone.ran_parallelMul` | [MonotoneOperators/Algebra.lean:110](../MonotoneOperators/Algebra.lean#L110) |
| `ScalarMonotone.parallelAdd_maximal` | [MonotoneOperators/Sums.lean:195](../MonotoneOperators/Sums.lean#L195) |
| `ScalarMonotone.dom_parallelAdd_eq` | [MonotoneOperators/Sums.lean:201](../MonotoneOperators/Sums.lean#L201) |
| `ScalarMonotone.parallelAdd_maximal_decreasing` | [MonotoneOperators/Sums.lean:301](../MonotoneOperators/Sums.lean#L301) |
| `ScalarMonotone.dom_parallelAdd_eq_decreasing` | [MonotoneOperators/Sums.lean:308](../MonotoneOperators/Sums.lean#L308) |
| `ScalarMonotone.parallelMul_maximal_iff` | [MonotoneOperators/ProductsDual.lean:98](../MonotoneOperators/ProductsDual.lean#L98) |
| `ScalarMonotone.parallelMul_maximal_decreasing_iff` | [MonotoneOperators/ProductsDual.lean:107](../MonotoneOperators/ProductsDual.lean#L107) |
<a id="claim-3"></a>

## After Lemma 1.19

[PDF page 17](../manuscript/monotone_calculus.pdf#page=17). Finite distributive lattice identities

Both completed monotonicity orientations. Finite graph-point claims retain arbitrary finite nonempty index types. Existing arbitrary extrema retain exactly nonemptiness and the appropriate order bound, rather than claiming unrestricted completeness. Both distributive identities hold in both operator lattices. Every point in the graph of a finite nonempty infimum or supremum belongs to one input graph. The complete upper-bound/leastness equivalence is also explicit for arbitrary existing suprema. The inherited actual resolvents identify binary extrema with real min/max, giving the audited DistribLattice instances. The new named bridges state both identities explicitly. Finite scalar resolvent extrema attain their values, and the checked Minty membership equivalence transfers attainment to graph points. The conditional complete lattice supplies the exact universal property. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncGraph.J_inf` | [MonotoneOperators/Extrema.lean:111](../MonotoneOperators/Extrema.lean#L111) |
| `ScalarMonotone.IncGraph.J_sup` | [MonotoneOperators/Extrema.lean:115](../MonotoneOperators/Extrema.lean#L115) |
| `ScalarMonotone.DecGraph.J_inf` | [MonotoneOperators/Extrema.lean:119](../MonotoneOperators/Extrema.lean#L119) |
| `ScalarMonotone.DecGraph.J_sup` | [MonotoneOperators/Extrema.lean:123](../MonotoneOperators/Extrema.lean#L123) |
| `ScalarMonotone.EndOfPaper.inc_sup_universal_property` | [EndOfPaper/ExtremaReader.lean:13](../EndOfPaper/ExtremaReader.lean#L13) |
| `ScalarMonotone.EndOfPaper.dec_sup_universal_property` | [EndOfPaper/ExtremaReader.lean:23](../EndOfPaper/ExtremaReader.lean#L23) |
| `ScalarMonotone.EndOfPaper.inc_graph_distributivity` | [EndOfPaper/ExtremaReader.lean:33](../EndOfPaper/ExtremaReader.lean#L33) |
| `ScalarMonotone.EndOfPaper.dec_graph_distributivity` | [EndOfPaper/ExtremaReader.lean:38](../EndOfPaper/ExtremaReader.lean#L38) |
| `ScalarMonotone.EndOfPaper.inc_finite_extremum_graph_points` | [EndOfPaper/ExtremaReader.lean:43](../EndOfPaper/ExtremaReader.lean#L43) |
| `ScalarMonotone.EndOfPaper.dec_finite_extremum_graph_points` | [EndOfPaper/ExtremaReader.lean:49](../EndOfPaper/ExtremaReader.lean#L49) |
<a id="claim-4"></a>

## After Proposition 1.22

[PDF page 20](../manuscript/monotone_calculus.pdf#page=20). Vertical-graph and infinite-step extrema examples

The exact two vertical graphs at zero and one, and the countable completed 0-to-1 steps at reciprocal positive integers. Lean's natural index n starts at zero, so n+1 explicitly enumerates all positive integers in the manuscript example. The infimum of the vertical graphs is the graph at one although the graph at zero has empty value there. Every positive-step input graph has singleton zero value at zero, whereas their actual infinite supremum has the full jump interval [0,1] there. The existing vertical order theorem gives the infimum and its exact empty fiber. The explicit step resolvent is proved to represent the stated left/right/jump fibers. Its pointwise limit gives the actual infinite lattice supremum at the step at zero. A new literal expected type checks both examples together against the current core declarations. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncGraph.inf_vertical_zero_one` | [MonotoneOperators/ExtremaExamples.lean:40](../MonotoneOperators/ExtremaExamples.lean#L40) |
| `ScalarMonotone.IncGraph.vertical_zero_empty_at_one` | [MonotoneOperators/ExtremaExamples.lean:45](../MonotoneOperators/ExtremaExamples.lean#L45) |
| `ScalarMonotone.IncGraph.step_fiber_left` | [MonotoneOperators/ExtremaExamples.lean:70](../MonotoneOperators/ExtremaExamples.lean#L70) |
| `ScalarMonotone.IncGraph.step_fiber_right` | [MonotoneOperators/ExtremaExamples.lean:78](../MonotoneOperators/ExtremaExamples.lean#L78) |
| `ScalarMonotone.IncGraph.step_fiber_at_jump` | [MonotoneOperators/ExtremaExamples.lean:94](../MonotoneOperators/ExtremaExamples.lean#L94) |
| `ScalarMonotone.IncGraph.iSup_step_sequence` | [MonotoneOperators/ExtremaExamples.lean:126](../MonotoneOperators/ExtremaExamples.lean#L126) |
| `ScalarMonotone.IncGraph.infinite_fiber_completion_example` | [MonotoneOperators/ExtremaExamples.lean:133](../MonotoneOperators/ExtremaExamples.lean#L133) |
<a id="claim-5"></a>

## Equation (1.44)

[PDF page 30](../manuscript/monotone_calculus.pdf#page=30). Nonnegative tail-area and signed quantile expectation formulas

An arbitrary measurable nonnegative random variable on its original probability space; nonnegativity may hold almost surely. Arbitrary selections of the actual positive-half-line completed survival and its inverse are allowed. The signed clause assumes exactly X in L1. The actual completion has zero fiber [P(Y>0),infinity), its inverse retains the entire quantile fiber for every p in (0,1), and its inverse is exactly {0} above one. Extended expectation equals survival area and both full positive inverse area and quantile area on (0,1), with infinity allowed. Signed expectation equals the quantile area, with quantile L1 derived and no added global measurability of the selection. Use the explicit compatible-point completion and right continuity of strict tails to prove the boundary fiber; derive the nonnegative-law quantile domain and exact inverse fibers. Combine the already proved arbitrary-selection moment/quantile identity at exponent one with the null endpoint and exact zero extension. Transfer signed L1 and expectation through a derived measurable representative and the actual quantile law. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.quantile_selection_lintegral_comp` | [EndOfPaper/QuantileMoments.lean:19](../EndOfPaper/QuantileMoments.lean#L19) |
| `ScalarMonotone.EndOfPaper.randomVariable_quantile_lintegral_comp` | [EndOfPaper/QuantileMoments.lean:30](../EndOfPaper/QuantileMoments.lean#L30) |
| `ScalarMonotone.EndOfPaper.quantile_selection_expectation` | [EndOfPaper/QuantileArea.lean:35](../EndOfPaper/QuantileArea.lean#L35) |
| `ScalarMonotone.EndOfPaper.inverse_area_identity` | [EndOfPaper/InverseArea.lean:108](../EndOfPaper/InverseArea.lean#L108) |
| `ScalarMonotone.EndOfPaper.positive_survival_inverse_positive_domain` | [EndOfPaper/ExpectationArea.lean:13](../EndOfPaper/ExpectationArea.lean#L13) |
| `ScalarMonotone.EndOfPaper.positive_survival_inverse_area_restriction` | [EndOfPaper/ExpectationArea.lean:29](../EndOfPaper/ExpectationArea.lean#L29) |
| `ScalarMonotone.EndOfPaper.positive_survival_expectation_area` | [EndOfPaper/ExpectationArea.lean:50](../EndOfPaper/ExpectationArea.lean#L50) |
| `ScalarMonotone.EndOfPaper.signed_expectation_quantile_area` | [EndOfPaper/ExpectationArea.lean:82](../EndOfPaper/ExpectationArea.lean#L82) |
| `ScalarMonotone.EndOfPaper.positiveSurvivalCompletion` | [EndOfPaper/PositiveSurvivalCompletion.lean:14](../EndOfPaper/PositiveSurvivalCompletion.lean#L14) |
| `ScalarMonotone.EndOfPaper.positive_survival_properties` | [EndOfPaper/PositiveSurvivalCompletion.lean:17](../EndOfPaper/PositiveSurvivalCompletion.lean#L17) |
| `ScalarMonotone.EndOfPaper.positive_survival_zero` | [EndOfPaper/PositiveSurvivalCompletion.lean:32](../EndOfPaper/PositiveSurvivalCompletion.lean#L32) |
| `ScalarMonotone.EndOfPaper.positive_survival_nonnegative` | [EndOfPaper/PositiveSurvivalCompletion.lean:59](../EndOfPaper/PositiveSurvivalCompletion.lean#L59) |
| `ScalarMonotone.EndOfPaper.nonnegative_law_quantile_nonnegative` | [EndOfPaper/PositiveSurvivalCompletion.lean:70](../EndOfPaper/PositiveSurvivalCompletion.lean#L70) |
| `ScalarMonotone.EndOfPaper.positive_survival_inverse_interior` | [EndOfPaper/PositiveSurvivalCompletion.lean:84](../EndOfPaper/PositiveSurvivalCompletion.lean#L84) |
| `ScalarMonotone.EndOfPaper.positive_survival_inverse_above_one` | [EndOfPaper/PositiveSurvivalCompletion.lean:114](../EndOfPaper/PositiveSurvivalCompletion.lean#L114) |
<a id="claim-6"></a>

## Equation (2.4)

[PDF page 35](../manuscript/monotone_calculus.pdf#page=35). Superadditive transform and least-majorant properties

The finite-list construction is exactly the supremum over all finite nonnegative families with coordinatewise sum at most a. Appending a zero vector proves the nonempty-family convention without restricting the number of summands. On the cone, the supplied results prove finiteness, F(a) lower bound, F(1) times coordinate mass upper bound, monotonicity, nonnegative homogeneity, superadditivity, concavity, and both least-majorant properties. The Lean F is a total real-vector function whose values outside the nonnegative cone are unconstrained and unused; any paper function has such an extension. Continuity is not needed for these algebraic claims, so no additional regularity assumption is imposed. Norm instantiations and probabilistic aggregation/sharpness are supplied in their separate inventory items. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.AggregationAxioms` | [EndOfPaper/Superadditive.lean:24](../EndOfPaper/Superadditive.lean#L24) |
| `ScalarMonotone.EndOfPaper.AdmissibleDecomposition` | [EndOfPaper/Superadditive.lean:29](../EndOfPaper/Superadditive.lean#L29) |
| `ScalarMonotone.EndOfPaper.sharpValues` | [EndOfPaper/Superadditive.lean:33](../EndOfPaper/Superadditive.lean#L33) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform` | [EndOfPaper/Superadditive.lean:39](../EndOfPaper/Superadditive.lean#L39) |
| `ScalarMonotone.EndOfPaper.sharpValues_nonempty_family` | [EndOfPaper/Superadditive.lean:119](../EndOfPaper/Superadditive.lean#L119) |
| `ScalarMonotone.EndOfPaper.sharpValues_bddAbove` | [EndOfPaper/Superadditive.lean:141](../EndOfPaper/Superadditive.lean#L141) |
| `ScalarMonotone.EndOfPaper.le_superadditiveTransform` | [EndOfPaper/Superadditive.lean:150](../EndOfPaper/Superadditive.lean#L150) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_linear_bound` | [EndOfPaper/Superadditive.lean:161](../EndOfPaper/Superadditive.lean#L161) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_nonneg` | [EndOfPaper/Superadditive.lean:156](../EndOfPaper/Superadditive.lean#L156) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_zero` | [EndOfPaper/Superadditive.lean:170](../EndOfPaper/Superadditive.lean#L170) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_mono` | [EndOfPaper/Superadditive.lean:176](../EndOfPaper/Superadditive.lean#L176) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_smul` | [EndOfPaper/Superadditive.lean:257](../EndOfPaper/Superadditive.lean#L257) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_superadditive` | [EndOfPaper/Superadditive.lean:198](../EndOfPaper/Superadditive.lean#L198) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_concaveOn` | [EndOfPaper/Superadditive.lean:311](../EndOfPaper/Superadditive.lean#L311) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_le_majorant` | [EndOfPaper/Superadditive.lean:272](../EndOfPaper/Superadditive.lean#L272) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_le_concave_majorant` | [EndOfPaper/Superadditive.lean:414](../EndOfPaper/Superadditive.lean#L414) |
| `ScalarMonotone.EndOfPaper.superadditiveTransform_eq_self` | [EndOfPaper/Superadditive.lean:302](../EndOfPaper/Superadditive.lean#L302) |
<a id="claim-7"></a>

## Equation (2.9)

[PDF page 38](../manuscript/monotone_calculus.pdf#page=38). Deterministic Hardy aggregation inequality

The standing continuous monotone nonnegative positively homogeneous F and maximal decreasing graphs nonnegative on their common initial domain interior (0,L), with L finite or infinite. The finite-area hypothesis of the preceding area lemma at any one common finite b>0 is enough; the final theorem derives every local L1 premise instead of assuming global integrability or finite L. The zero-scalar homogeneity case is discharged by the proved positive-homogeneity bridge in the reader expected type. At every positive interior level, the value of the actual completed Hardy integral of the actual completed aggregation is bounded by F-sharp of the actual completed Hardy values of the input graphs. The aggregate Hardy graph is maximal and has exactly the common domain interior. All initial-interval geometry is proved for genuine EReal L, including infinity; all boundary fibers are retained by the actual constructors. The full aggregation-area lemma gives integrability and the prefix inequality. Monotonicity on compact subintervals propagates the single finite prefix area to every prefix, even on an unbounded domain. Apply the actual Hardy family-integral constructor to both the aggregate and all inputs. Divide the area inequality by p and use the proved positive homogeneity of F-sharp. The scalar values are conclusions of the completed constructors, not assumed replacements for the operators. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.aggregationAxioms_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:20](../EndOfPaper/HardyTailAggregation.lean#L20) |
| `ScalarMonotone.EndOfPaper.positiveInitialInterval` | [EndOfPaper/HardyOperatorAggregation.lean:17](../EndOfPaper/HardyOperatorAggregation.lean#L17) |
| `ScalarMonotone.EndOfPaper.positiveInitialInterval_geometry` | [EndOfPaper/HardyOperatorAggregation.lean:19](../EndOfPaper/HardyOperatorAggregation.lean#L19) |
| `ScalarMonotone.EndOfPaper.hardy_operator_aggregation_on` | [EndOfPaper/HardyOperatorAggregation.lean:43](../EndOfPaper/HardyOperatorAggregation.lean#L43) |
| `ScalarMonotone.EndOfPaper.hardy_operator_aggregation` | [EndOfPaper/HardyOperatorAggregation.lean:113](../EndOfPaper/HardyOperatorAggregation.lean#L113) |
| `ScalarMonotone.EndOfPaper.antitone_prefix_integrable_all` | [EndOfPaper/HardyOperatorAggregation.lean:132](../EndOfPaper/HardyOperatorAggregation.lean#L132) |
| `ScalarMonotone.EndOfPaper.hardy_operator_aggregation_of_finite_area` | [EndOfPaper/HardyOperatorAggregation.lean:158](../EndOfPaper/HardyOperatorAggregation.lean#L158) |
<a id="claim-8"></a>

## Equation (2.12)

[PDF page 38](../manuscript/monotone_calculus.pdf#page=38). Hardy tail-envelope transform definition

A maximal decreasing beta whose inverse admits Hardy averaging. The well-definedness theorem derives this from the exact positive initial-domain geometry and prefix integrability of an arbitrary inverse selection; global L1 on an unbounded interval is not assumed. The Hardy tail transform is the inverse of the actual completed dilation-family Hardy integral of inverse beta, on its actual domain interior. It is maximal decreasing, its inverse is exactly that Hardy graph, and its range interior agrees with beta's range interior. Apply the fully proved locally integrable Hardy construction to inverse beta, use maximality under inversion and the exact inverse involution. This definition uses the completed operator integral rather than an independently defined scalar surrogate. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.positiveScalarGraph` | [EndOfPaper/CompletedProfiles.lean:18](../EndOfPaper/CompletedProfiles.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_domain` | [EndOfPaper/CompletedProfiles.lean:22](../EndOfPaper/CompletedProfiles.lean#L22) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_maximal` | [EndOfPaper/CompletedProfiles.lean:28](../EndOfPaper/CompletedProfiles.lean#L28) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_affine_maximal` | [EndOfPaper/CompletedProfiles.lean:68](../EndOfPaper/CompletedProfiles.lean#L68) |
| `ScalarMonotone.EndOfPaper.powerQuantileProfile` | [EndOfPaper/CompletedProfiles.lean:83](../EndOfPaper/CompletedProfiles.lean#L83) |
| `ScalarMonotone.EndOfPaper.exponentialQuantileProfile` | [EndOfPaper/CompletedProfiles.lean:84](../EndOfPaper/CompletedProfiles.lean#L84) |
| `ScalarMonotone.EndOfPaper.powerQuantileProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:86](../EndOfPaper/CompletedProfiles.lean#L86) |
| `ScalarMonotone.EndOfPaper.exponentialQuantileProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:104](../EndOfPaper/CompletedProfiles.lean#L104) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_mem` | [EndOfPaper/CompletedProfiles.lean:119](../EndOfPaper/CompletedProfiles.lean#L119) |
| `ScalarMonotone.EndOfPaper.powerProfile` | [EndOfPaper/CompletedProfiles.lean:123](../EndOfPaper/CompletedProfiles.lean#L123) |
| `ScalarMonotone.EndOfPaper.exponentialProfile` | [EndOfPaper/CompletedProfiles.lean:124](../EndOfPaper/CompletedProfiles.lean#L124) |
| `ScalarMonotone.EndOfPaper.power_profile_level_iff` | [EndOfPaper/CompletedProfiles.lean:126](../EndOfPaper/CompletedProfiles.lean#L126) |
| `ScalarMonotone.EndOfPaper.inverse_powerProfile` | [EndOfPaper/CompletedProfiles.lean:156](../EndOfPaper/CompletedProfiles.lean#L156) |
| `ScalarMonotone.EndOfPaper.inverse_exponentialProfile` | [EndOfPaper/CompletedProfiles.lean:170](../EndOfPaper/CompletedProfiles.lean#L170) |
| `ScalarMonotone.EndOfPaper.powerProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:187](../EndOfPaper/CompletedProfiles.lean#L187) |
| `ScalarMonotone.EndOfPaper.exponentialProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:192](../EndOfPaper/CompletedProfiles.lean#L192) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_hardy_unique` | [EndOfPaper/CompletedProfiles.lean:198](../EndOfPaper/CompletedProfiles.lean#L198) |
| `ScalarMonotone.EndOfPaper.hardy_powerProfile_whole` | [EndOfPaper/CompletedProfiles.lean:217](../EndOfPaper/CompletedProfiles.lean#L217) |
| `ScalarMonotone.EndOfPaper.hardy_exponentialProfile_whole` | [EndOfPaper/CompletedProfiles.lean:237](../EndOfPaper/CompletedProfiles.lean#L237) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform` | [EndOfPaper/CompletedProfiles.lean:253](../EndOfPaper/CompletedProfiles.lean#L253) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_well_defined` | [EndOfPaper/CompletedProfiles.lean:256](../EndOfPaper/CompletedProfiles.lean#L256) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_power` | [EndOfPaper/CompletedProfiles.lean:269](../EndOfPaper/CompletedProfiles.lean#L269) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_exponential` | [EndOfPaper/CompletedProfiles.lean:276](../EndOfPaper/CompletedProfiles.lean#L276) |
| `ScalarMonotone.EndOfPaper.powerProfile_outputScale` | [EndOfPaper/CompletedProfiles.lean:282](../EndOfPaper/CompletedProfiles.lean#L282) |
| `ScalarMonotone.EndOfPaper.exponentialProfile_outputScale` | [EndOfPaper/CompletedProfiles.lean:291](../EndOfPaper/CompletedProfiles.lean#L291) |
| `ScalarMonotone.EndOfPaper.hardy_regularized_profiles` | [EndOfPaper/CompletedProfiles.lean:304](../EndOfPaper/CompletedProfiles.lean#L304) |
| `ScalarMonotone.EndOfPaper.hardy_profile_identities` | [EndOfPaper/CompletedProfiles.lean:312](../EndOfPaper/CompletedProfiles.lean#L312) |
<a id="claim-9"></a>

## Equation (2.13)

[PDF page 39](../manuscript/monotone_calculus.pdf#page=39). General aggregated survival-envelope bound

The original continuous nonnegative monotone homogeneous F, arbitrary original-space measurable inputs with AE nonnegativity, and each original maximal decreasing envelope beta_i satisfying S[X_i]<=beta_i<=1, greatest lower bound zero for its range, and finite extended absolute inverse area on (0,1). Arbitrary inverse selections are allowed. No original input L1, extra inverse-domain coverage, output maximality, or F-sharp continuity hypothesis is added. tail_envelope_aggregation proves the whole completed survival comparison with the inverse actual aggregationOperator F-sharp of the completed Hardy integrals of inverse beta_i, and proves that this inverse is maximal decreasing. All graph boundary fibers, atoms, and original dependence are retained. The input quantiles and inverse profiles have the required probability domains and L1 as derived conclusions. Derive inverse-domain geometry from the actual survival comparisons, probability-one cap and zero range infimum, then derive all L1 by the actual quantile-law comparison. Apply whole Hardy order preservation and the complete original Hardy aggregation theorem. Prove that the literal singleton Hardy-fiber aggregation has the actual monotone maximal completion, using the explicit constructor and monotonicity alone. Extend the interior scalar comparison to the whole completed order and invert. Clipping transfers AE-nonnegative inputs and their exact laws without adding measurability of an arbitrary extension of F outside the positive cone. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.admissible_tail_hardy_data` | [EndOfPaper/AdmissibleHardyEnvelope.lean:13](../EndOfPaper/AdmissibleHardyEnvelope.lean#L13) |
| `ScalarMonotone.EndOfPaper.admissible_tail_inverse_geometry` | [EndOfPaper/AdmissibleTailEnvelope.lean:14](../EndOfPaper/AdmissibleTailEnvelope.lean#L14) |
| `ScalarMonotone.EndOfPaper.admissible_tail_integrability` | [EndOfPaper/AdmissibleTailEnvelope.lean:53](../EndOfPaper/AdmissibleTailEnvelope.lean#L53) |
| `ScalarMonotone.EndOfPaper.antitone_scalar_completion_properties` | [EndOfPaper/MonotoneScalarAggregation.lean:12](../EndOfPaper/MonotoneScalarAggregation.lean#L12) |
| `ScalarMonotone.EndOfPaper.aggregation_singleton_completion` | [EndOfPaper/MonotoneScalarAggregation.lean:44](../EndOfPaper/MonotoneScalarAggregation.lean#L44) |
| `ScalarMonotone.EndOfPaper.aggregation_singleton_monotone_properties` | [EndOfPaper/MonotoneScalarAggregation.lean:61](../EndOfPaper/MonotoneScalarAggregation.lean#L61) |
| `ScalarMonotone.EndOfPaper.tail_envelope_aggregation_of_nonnegative` | [EndOfPaper/TailEnvelopeAggregation.lean:14](../EndOfPaper/TailEnvelopeAggregation.lean#L14) |
| `ScalarMonotone.EndOfPaper.tail_envelope_aggregation` | [EndOfPaper/TailEnvelopeAggregation.lean:108](../EndOfPaper/TailEnvelopeAggregation.lean#L108) |
<a id="claim-10"></a>

## Equation (2.14)

[PDF page 39](../manuscript/monotone_calculus.pdf#page=39). Common-envelope homogeneous aggregation bound

The same original admissible common envelope beta and arbitrary original inputs, with a nonempty coordinate family. The zero aggregation is handled separately; in the nonzero positive-cone case strict positivity of C=F-sharp(ones) is proved. Arbitrary inverse selections and finite absolute inverse area are retained. common_envelope_survival_bound proves C>0, the whole survival bound by HardyTail(beta) composed with id/C, and for every t in C times its actual domain the exact strict-tail bound by inf HardyTail(beta)(t/C). The independent reader uses the literal graph composition. zero_aggregation_law proves that the zero branch has exactly the delta-zero law. Use the derived full Hardy envelope data and scalar homogeneity at the common Hardy value to obtain the exact coefficient, with no continuity premise on F-sharp. Apply whole initial-interval order, exact inversion/output scaling and the original-space strict-tail criterion. Clipping retains AE nonnegativity and complete laws. The infimum statement is derived at every nonempty completed fiber, rather than assumed at a scalar selection. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.admissible_tail_hardy_data` | [EndOfPaper/AdmissibleHardyEnvelope.lean:13](../EndOfPaper/AdmissibleHardyEnvelope.lean#L13) |
| `ScalarMonotone.EndOfPaper.admissible_tail_inverse_geometry` | [EndOfPaper/AdmissibleTailEnvelope.lean:14](../EndOfPaper/AdmissibleTailEnvelope.lean#L14) |
| `ScalarMonotone.EndOfPaper.admissible_tail_integrability` | [EndOfPaper/AdmissibleTailEnvelope.lean:53](../EndOfPaper/AdmissibleTailEnvelope.lean#L53) |
| `ScalarMonotone.EndOfPaper.zero_aggregation_law` | [EndOfPaper/CommonSurvivalEnvelope.lean:12](../EndOfPaper/CommonSurvivalEnvelope.lean#L12) |
| `ScalarMonotone.EndOfPaper.common_envelope_survival_bound` | [EndOfPaper/CommonSurvivalEnvelope.lean:22](../EndOfPaper/CommonSurvivalEnvelope.lean#L22) |
| `ScalarMonotone.EndOfPaper.sharp_one_positive_of_nonzero` | [EndOfPaper/CommonTailAggregation.lean:14](../EndOfPaper/CommonTailAggregation.lean#L14) |
| `ScalarMonotone.EndOfPaper.common_envelope_quantile_bound_of_nonnegative` | [EndOfPaper/CommonTailAggregation.lean:29](../EndOfPaper/CommonTailAggregation.lean#L29) |
<a id="claim-11"></a>

## Equation (2.15)

[PDF page 39](../manuscript/monotone_calculus.pdf#page=39). Hardy survival bound for sums

The original nonnegative finite input family with n>=1 and the same original admissible envelope assumptions. All input L1 is derived from finite absolute inverse area. No independence, atomlessness or finite-valued law is assumed. The auxiliary signed theorem is valid for every nonempty finite family of integrable signed variables. hardy_sum_survival_of_envelopes derives all original input integrability and proves the whole survival comparison with the inverse ordinary finite graph sum of the actual marginal Hardy quantiles. The right side is maximal decreasing. The independent reader expands the graph sum as its literal coordinate-witness set, retaining every completed boundary fiber. Combine the complete signed whole Hardy sum inequality with quantile<=Hardy on the original aggregate law, then invert. The original-envelope wrapper discharges every integrability assumption using admissible_tail_integrability; no union-bound factor is introduced. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.signed_hardy_sum_operator_bound` | [EndOfPaper/SignedHardySum.lean:52](../EndOfPaper/SignedHardySum.lean#L52) |
| `ScalarMonotone.EndOfPaper.tailQuantile_le_quantileHardy` | [EndOfPaper/ReplicatedHardyEnvelope.lean:60](../EndOfPaper/ReplicatedHardyEnvelope.lean#L60) |
| `ScalarMonotone.EndOfPaper.admissible_tail_inverse_geometry` | [EndOfPaper/AdmissibleTailEnvelope.lean:14](../EndOfPaper/AdmissibleTailEnvelope.lean#L14) |
| `ScalarMonotone.EndOfPaper.admissible_tail_integrability` | [EndOfPaper/AdmissibleTailEnvelope.lean:53](../EndOfPaper/AdmissibleTailEnvelope.lean#L53) |
| `ScalarMonotone.EndOfPaper.hardy_sum_survival_bound` | [EndOfPaper/HardySumSurvival.lean:13](../EndOfPaper/HardySumSurvival.lean#L13) |
| `ScalarMonotone.EndOfPaper.hardy_sum_survival_of_envelopes` | [EndOfPaper/HardySumSurvival.lean:32](../EndOfPaper/HardySumSurvival.lean#L32) |
<a id="claim-12"></a>

## After Proposition 2.10

[PDF page 41](../manuscript/monotone_calculus.pdf#page=41). Comonotone aggregate quantile identity

The standing continuous monotone nonnegative positively homogeneous F, arbitrary nonnegative original variables and a joint-law representation by decreasing functions of one uniform variable on an auxiliary model. The original space may be atomic and need not carry any uniform variable. No finite-range or L1 assumption is added for the whole-graph identity. AEMeasurability suffices. Each decreasing uniform profile has its actual completed quantile graph as its unique maximal completion on [0,1]. The aggregate quantile equals the actual completed aggregation of marginal quantiles as a whole operator, including jumps, endpoints and domains. This holds both for an actual common uniform input and for a representation only in joint law on an auxiliary space. Antitonicity supplies strict/weak mass brackets and completion uniqueness. The profile aggregate is a selection of the actual aggregation constructor. For the law-level extension, measurable pushforwards transfer the full joint law to each marginal and to the aggregate. Clip the uniform profiles at zero and prove that clipping preserves their joint law because the actual original variables are nonnegative. Use the globally continuous positive extension of F only as a measurability bridge, with exact equality on all nonnegative values. No atomless original-space assumption is hidden. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.aggregationAxioms_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:20](../EndOfPaper/HardyTailAggregation.lean#L20) |
| `ScalarMonotone.EndOfPaper.antitone_uniform_quantile_selection` | [EndOfPaper/ComonotoneQuantiles.lean:18](../EndOfPaper/ComonotoneQuantiles.lean#L18) |
| `ScalarMonotone.EndOfPaper.antitone_uniform_quantile_unique` | [EndOfPaper/ComonotoneQuantiles.lean:47](../EndOfPaper/ComonotoneQuantiles.lean#L47) |
| `ScalarMonotone.EndOfPaper.antitone_uniform_quantile_nonnegative` | [EndOfPaper/ComonotoneQuantiles.lean:77](../EndOfPaper/ComonotoneQuantiles.lean#L77) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile` | [EndOfPaper/ComonotoneQuantiles.lean:92](../EndOfPaper/ComonotoneQuantiles.lean#L92) |
| `ScalarMonotone.EndOfPaper.uniform_profile_law_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:120](../EndOfPaper/ComonotoneQuantiles.lean#L120) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:131](../EndOfPaper/ComonotoneQuantiles.lean#L131) |
| `ScalarMonotone.EndOfPaper.constant_uniform_quantile` | [EndOfPaper/ComonotoneQuantiles.lean:149](../EndOfPaper/ComonotoneQuantiles.lean#L149) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_fiber` | [EndOfPaper/ComonotoneQuantiles.lean:158](../EndOfPaper/ComonotoneQuantiles.lean#L158) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_fiber_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:181](../EndOfPaper/ComonotoneQuantiles.lean#L181) |
| `ScalarMonotone.EndOfPaper.comonotoneQuantileValues` | [EndOfPaper/ComonotoneQuantiles.lean:200](../EndOfPaper/ComonotoneQuantiles.lean#L200) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_sharp_isGreatest` | [EndOfPaper/ComonotoneQuantiles.lean:208](../EndOfPaper/ComonotoneQuantiles.lean#L208) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_sharp` | [EndOfPaper/ComonotoneQuantiles.lean:222](../EndOfPaper/ComonotoneQuantiles.lean#L222) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_nonnegative_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:232](../EndOfPaper/ComonotoneQuantiles.lean#L232) |
| `ScalarMonotone.EndOfPaper.comonotone_fixed_quantile_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:260](../EndOfPaper/ComonotoneQuantiles.lean#L260) |
| `ScalarMonotone.EndOfPaper.antitone_profile_vector_aemeasurable` | [EndOfPaper/ComonotoneLawRepresentation.lean:16](../EndOfPaper/ComonotoneLawRepresentation.lean#L16) |
| `ScalarMonotone.EndOfPaper.joint_law_map` | [EndOfPaper/ComonotoneLawRepresentation.lean:28](../EndOfPaper/ComonotoneLawRepresentation.lean#L28) |
| `ScalarMonotone.EndOfPaper.comonotone_joint_law_positive_profiles` | [EndOfPaper/ComonotoneLawRepresentation.lean:38](../EndOfPaper/ComonotoneLawRepresentation.lean#L38) |
| `ScalarMonotone.EndOfPaper.comonotone_joint_law_marginals_aggregate` | [EndOfPaper/ComonotoneLawRepresentation.lean:62](../EndOfPaper/ComonotoneLawRepresentation.lean#L62) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile_joint_law` | [EndOfPaper/ComonotoneLawRepresentation.lean:92](../EndOfPaper/ComonotoneLawRepresentation.lean#L92) |
| `ScalarMonotone.EndOfPaper.comonotone_fixed_quantile_joint_law` | [EndOfPaper/ComonotoneLawRepresentation.lean:108](../EndOfPaper/ComonotoneLawRepresentation.lean#L108) |
<a id="claim-13"></a>

## Equation (2.21)

[PDF page 41](../manuscript/monotone_calculus.pdf#page=41). Pointwise comonotone quantile sharpness

Every p in (0,1), nonnegative a and the standing continuous monotone positively homogeneous F. All nonnegative finite-valued comonotone tuples on arbitrary original spaces are included through their joint-law uniform representation; the original space may be atomic. The upper identity actually requires neither finite-valuedness nor L1. The exact fixed-fiber supremum equals F(a), every admissible aggregate fiber is the singleton F(a), and constant nonnegative finite-valued variables attain it. The following failure assertion without comonotonicity is also proved by the explicit complementary Bernoulli pair with both marginal quantiles zero and sum quantile one at p=3/4. The new joint-law bridge proves the universal upper identity on every original space without constructing a uniform variable there. The checked common-uniform candidate set attains F(a) by constants, providing a valid lower example and the exact supremum over all spaces. The separate two-atom counterexample proves that removing comonotonicity destroys even the upper bound. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.antitone_uniform_quantile_selection` | [EndOfPaper/ComonotoneQuantiles.lean:18](../EndOfPaper/ComonotoneQuantiles.lean#L18) |
| `ScalarMonotone.EndOfPaper.antitone_uniform_quantile_unique` | [EndOfPaper/ComonotoneQuantiles.lean:47](../EndOfPaper/ComonotoneQuantiles.lean#L47) |
| `ScalarMonotone.EndOfPaper.antitone_uniform_quantile_nonnegative` | [EndOfPaper/ComonotoneQuantiles.lean:77](../EndOfPaper/ComonotoneQuantiles.lean#L77) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile` | [EndOfPaper/ComonotoneQuantiles.lean:92](../EndOfPaper/ComonotoneQuantiles.lean#L92) |
| `ScalarMonotone.EndOfPaper.uniform_profile_law_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:120](../EndOfPaper/ComonotoneQuantiles.lean#L120) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:131](../EndOfPaper/ComonotoneQuantiles.lean#L131) |
| `ScalarMonotone.EndOfPaper.constant_uniform_quantile` | [EndOfPaper/ComonotoneQuantiles.lean:149](../EndOfPaper/ComonotoneQuantiles.lean#L149) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_fiber` | [EndOfPaper/ComonotoneQuantiles.lean:158](../EndOfPaper/ComonotoneQuantiles.lean#L158) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_fiber_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:181](../EndOfPaper/ComonotoneQuantiles.lean#L181) |
| `ScalarMonotone.EndOfPaper.comonotoneQuantileValues` | [EndOfPaper/ComonotoneQuantiles.lean:200](../EndOfPaper/ComonotoneQuantiles.lean#L200) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_sharp_isGreatest` | [EndOfPaper/ComonotoneQuantiles.lean:208](../EndOfPaper/ComonotoneQuantiles.lean#L208) |
| `ScalarMonotone.EndOfPaper.comonotone_quantile_sharp` | [EndOfPaper/ComonotoneQuantiles.lean:222](../EndOfPaper/ComonotoneQuantiles.lean#L222) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_nonnegative_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:232](../EndOfPaper/ComonotoneQuantiles.lean#L232) |
| `ScalarMonotone.EndOfPaper.comonotone_fixed_quantile_original_space` | [EndOfPaper/ComonotoneQuantiles.lean:260](../EndOfPaper/ComonotoneQuantiles.lean#L260) |
| `ScalarMonotone.EndOfPaper.aggregationAxioms_of_positive_homogeneity` | [EndOfPaper/HardyTailAggregation.lean:20](../EndOfPaper/HardyTailAggregation.lean#L20) |
| `ScalarMonotone.EndOfPaper.tailQuantile_dirac_interior` | [EndOfPaper/QuantileDependenceCounterexample.lean:17](../EndOfPaper/QuantileDependenceCounterexample.lean#L17) |
| `ScalarMonotone.EndOfPaper.tailQuantile_constant_randomVariable` | [EndOfPaper/QuantileDependenceCounterexample.lean:26](../EndOfPaper/QuantileDependenceCounterexample.lean#L26) |
| `ScalarMonotone.EndOfPaper.tailQuantile_symmetricBernoulli_upper` | [EndOfPaper/QuantileDependenceCounterexample.lean:32](../EndOfPaper/QuantileDependenceCounterexample.lean#L32) |
| `ScalarMonotone.EndOfPaper.bernoulliIndicator` | [EndOfPaper/QuantileDependenceCounterexample.lean:50](../EndOfPaper/QuantileDependenceCounterexample.lean#L50) |
| `ScalarMonotone.EndOfPaper.bernoulliIndicator_measurable` | [EndOfPaper/QuantileDependenceCounterexample.lean:52](../EndOfPaper/QuantileDependenceCounterexample.lean#L52) |
| `ScalarMonotone.EndOfPaper.bernoulliIndicator_finite_nonnegative` | [EndOfPaper/QuantileDependenceCounterexample.lean:56](../EndOfPaper/QuantileDependenceCounterexample.lean#L56) |
| `ScalarMonotone.EndOfPaper.bernoulliIndicator_law` | [EndOfPaper/QuantileDependenceCounterexample.lean:69](../EndOfPaper/QuantileDependenceCounterexample.lean#L69) |
| `ScalarMonotone.EndOfPaper.complementary_bernoulliIndicator_law` | [EndOfPaper/QuantileDependenceCounterexample.lean:78](../EndOfPaper/QuantileDependenceCounterexample.lean#L78) |
| `ScalarMonotone.EndOfPaper.quantile_sharpness_fails_without_comonotonicity` | [EndOfPaper/QuantileDependenceCounterexample.lean:87](../EndOfPaper/QuantileDependenceCounterexample.lean#L87) |
| `ScalarMonotone.EndOfPaper.antitone_profile_vector_aemeasurable` | [EndOfPaper/ComonotoneLawRepresentation.lean:16](../EndOfPaper/ComonotoneLawRepresentation.lean#L16) |
| `ScalarMonotone.EndOfPaper.joint_law_map` | [EndOfPaper/ComonotoneLawRepresentation.lean:28](../EndOfPaper/ComonotoneLawRepresentation.lean#L28) |
| `ScalarMonotone.EndOfPaper.comonotone_joint_law_positive_profiles` | [EndOfPaper/ComonotoneLawRepresentation.lean:38](../EndOfPaper/ComonotoneLawRepresentation.lean#L38) |
| `ScalarMonotone.EndOfPaper.comonotone_joint_law_marginals_aggregate` | [EndOfPaper/ComonotoneLawRepresentation.lean:62](../EndOfPaper/ComonotoneLawRepresentation.lean#L62) |
| `ScalarMonotone.EndOfPaper.comonotone_aggregation_quantile_joint_law` | [EndOfPaper/ComonotoneLawRepresentation.lean:92](../EndOfPaper/ComonotoneLawRepresentation.lean#L92) |
| `ScalarMonotone.EndOfPaper.comonotone_fixed_quantile_joint_law` | [EndOfPaper/ComonotoneLawRepresentation.lean:108](../EndOfPaper/ComonotoneLawRepresentation.lean#L108) |
<a id="claim-14"></a>

## After Proposition 2.14

[PDF page 45](../manuscript/monotone_calculus.pdf#page=45). Bernoulli example showing replication is essential

Every original probability space and every measurable coupling with exactly the symmetric Bernoulli and zero point-mass laws, at every level 1/2<p<1. No independence or atomlessness is assumed. The fixed-pair average has the literal quantile fiber {0}, while the actual averaged Hardy quantile sum has the strictly positive singleton {1/(4p)}. A measurable integrable model with exactly those laws is supplied. Transfer the zero point-mass law to AE zero. Prove whole quantile scaling, the Bernoulli step selection and its actual Hardy integral; compute both finite-sum fibers including the normalization. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.tailQuantile_positive_smul` | [EndOfPaper/ReplicationNecessity.lean:16](../EndOfPaper/ReplicationNecessity.lean#L16) |
| `ScalarMonotone.EndOfPaper.bernoulli_quantile_step_selection` | [EndOfPaper/ReplicationNecessity.lean:33](../EndOfPaper/ReplicationNecessity.lean#L33) |
| `ScalarMonotone.EndOfPaper.bernoulli_integrable` | [EndOfPaper/ReplicationNecessity.lean:55](../EndOfPaper/ReplicationNecessity.lean#L55) |
| `ScalarMonotone.EndOfPaper.bernoulli_hardy_value` | [EndOfPaper/ReplicationNecessity.lean:62](../EndOfPaper/ReplicationNecessity.lean#L62) |
| `ScalarMonotone.EndOfPaper.dirac_hardy_value` | [EndOfPaper/ReplicationNecessity.lean:74](../EndOfPaper/ReplicationNecessity.lean#L74) |
| `ScalarMonotone.EndOfPaper.fixed_pair_bernoulli_quantile` | [EndOfPaper/ReplicationNecessity.lean:89](../EndOfPaper/ReplicationNecessity.lean#L89) |
| `ScalarMonotone.EndOfPaper.replication_is_essential` | [EndOfPaper/ReplicationNecessity.lean:112](../EndOfPaper/ReplicationNecessity.lean#L112) |
| `ScalarMonotone.EndOfPaper.replication_counterexample_model` | [EndOfPaper/ReplicationNecessity.lean:137](../EndOfPaper/ReplicationNecessity.lean#L137) |
<a id="claim-15"></a>

## Equation (2.16)

[PDF page 39](../manuscript/monotone_calculus.pdf#page=39). Exact scalar Hardy averages for power and exponential profiles

Every real kappa>1 and every positive level p. The power graph is empty on nonpositive inputs and equals the singleton t^(-kappa) on positive inputs; the exponential graph is defined on the whole real line. Profiles are not capped at probability one. Both graphs are maximal decreasing, their inverse domain interiors are exactly (0,infinity), and the actual completed Hardy fibers are exactly the paper power and logarithmic singleton values for every p>0. Stronger scaled theorems identify the entire Hardy graphs, including all boundary fibers. Construct the positive scalar inverse graphs as maximal completions. Unbounded upper inverse values force the full zero fiber to be empty. Logarithms prove exact inverse identities. Prefix L1 follows from the checked power and logarithm integral theorems. Whole-operator uniqueness identifies the actual Hardy construction with the explicit inverse profile; the named manuscript theorem supplies both literal scalar formulas and both domain/maximality assertions. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.positiveScalarGraph` | [EndOfPaper/CompletedProfiles.lean:18](../EndOfPaper/CompletedProfiles.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_domain` | [EndOfPaper/CompletedProfiles.lean:22](../EndOfPaper/CompletedProfiles.lean#L22) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_maximal` | [EndOfPaper/CompletedProfiles.lean:28](../EndOfPaper/CompletedProfiles.lean#L28) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_affine_maximal` | [EndOfPaper/CompletedProfiles.lean:68](../EndOfPaper/CompletedProfiles.lean#L68) |
| `ScalarMonotone.EndOfPaper.powerQuantileProfile` | [EndOfPaper/CompletedProfiles.lean:83](../EndOfPaper/CompletedProfiles.lean#L83) |
| `ScalarMonotone.EndOfPaper.exponentialQuantileProfile` | [EndOfPaper/CompletedProfiles.lean:84](../EndOfPaper/CompletedProfiles.lean#L84) |
| `ScalarMonotone.EndOfPaper.powerQuantileProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:86](../EndOfPaper/CompletedProfiles.lean#L86) |
| `ScalarMonotone.EndOfPaper.exponentialQuantileProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:104](../EndOfPaper/CompletedProfiles.lean#L104) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_mem` | [EndOfPaper/CompletedProfiles.lean:119](../EndOfPaper/CompletedProfiles.lean#L119) |
| `ScalarMonotone.EndOfPaper.powerProfile` | [EndOfPaper/CompletedProfiles.lean:123](../EndOfPaper/CompletedProfiles.lean#L123) |
| `ScalarMonotone.EndOfPaper.exponentialProfile` | [EndOfPaper/CompletedProfiles.lean:124](../EndOfPaper/CompletedProfiles.lean#L124) |
| `ScalarMonotone.EndOfPaper.power_profile_level_iff` | [EndOfPaper/CompletedProfiles.lean:126](../EndOfPaper/CompletedProfiles.lean#L126) |
| `ScalarMonotone.EndOfPaper.inverse_powerProfile` | [EndOfPaper/CompletedProfiles.lean:156](../EndOfPaper/CompletedProfiles.lean#L156) |
| `ScalarMonotone.EndOfPaper.inverse_exponentialProfile` | [EndOfPaper/CompletedProfiles.lean:170](../EndOfPaper/CompletedProfiles.lean#L170) |
| `ScalarMonotone.EndOfPaper.powerProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:187](../EndOfPaper/CompletedProfiles.lean#L187) |
| `ScalarMonotone.EndOfPaper.exponentialProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:192](../EndOfPaper/CompletedProfiles.lean#L192) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_hardy_unique` | [EndOfPaper/CompletedProfiles.lean:198](../EndOfPaper/CompletedProfiles.lean#L198) |
| `ScalarMonotone.EndOfPaper.hardy_powerProfile_whole` | [EndOfPaper/CompletedProfiles.lean:217](../EndOfPaper/CompletedProfiles.lean#L217) |
| `ScalarMonotone.EndOfPaper.hardy_exponentialProfile_whole` | [EndOfPaper/CompletedProfiles.lean:237](../EndOfPaper/CompletedProfiles.lean#L237) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform` | [EndOfPaper/CompletedProfiles.lean:253](../EndOfPaper/CompletedProfiles.lean#L253) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_well_defined` | [EndOfPaper/CompletedProfiles.lean:256](../EndOfPaper/CompletedProfiles.lean#L256) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_power` | [EndOfPaper/CompletedProfiles.lean:269](../EndOfPaper/CompletedProfiles.lean#L269) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_exponential` | [EndOfPaper/CompletedProfiles.lean:276](../EndOfPaper/CompletedProfiles.lean#L276) |
| `ScalarMonotone.EndOfPaper.powerProfile_outputScale` | [EndOfPaper/CompletedProfiles.lean:282](../EndOfPaper/CompletedProfiles.lean#L282) |
| `ScalarMonotone.EndOfPaper.exponentialProfile_outputScale` | [EndOfPaper/CompletedProfiles.lean:291](../EndOfPaper/CompletedProfiles.lean#L291) |
| `ScalarMonotone.EndOfPaper.hardy_regularized_profiles` | [EndOfPaper/CompletedProfiles.lean:304](../EndOfPaper/CompletedProfiles.lean#L304) |
| `ScalarMonotone.EndOfPaper.hardy_profile_identities` | [EndOfPaper/CompletedProfiles.lean:312](../EndOfPaper/CompletedProfiles.lean#L312) |
<a id="claim-16"></a>

## Equation (2.17)

[PDF page 39](../manuscript/monotone_calculus.pdf#page=39). Exact scaled inverse Hardy envelopes

Every real kappa>1 and every C>0, with the paper's uncapped power and exponential graphs and actual output scaling. Their inverse graphs have unbounded positive averaging intervals and only prefix integrability is used. The actual Hardy tail transform of C times the power graph equals C*(kappa/(kappa-1))^kappa times that graph. The exponential transform equals C*exp(1) times the exponential graph. These are equalities of whole operators with their domains and boundary fibers retained. Whole completed Hardy identities are inverted using the inverse involution. Exact positive-base real-power algebra gives the new power coefficient, and the logarithm/exponential identities give the exponential coefficient. Proved output-scaling bridges put the result in precisely the displayed manuscript notation. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.positiveScalarGraph` | [EndOfPaper/CompletedProfiles.lean:18](../EndOfPaper/CompletedProfiles.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_domain` | [EndOfPaper/CompletedProfiles.lean:22](../EndOfPaper/CompletedProfiles.lean#L22) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_maximal` | [EndOfPaper/CompletedProfiles.lean:28](../EndOfPaper/CompletedProfiles.lean#L28) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_affine_maximal` | [EndOfPaper/CompletedProfiles.lean:68](../EndOfPaper/CompletedProfiles.lean#L68) |
| `ScalarMonotone.EndOfPaper.powerQuantileProfile` | [EndOfPaper/CompletedProfiles.lean:83](../EndOfPaper/CompletedProfiles.lean#L83) |
| `ScalarMonotone.EndOfPaper.exponentialQuantileProfile` | [EndOfPaper/CompletedProfiles.lean:84](../EndOfPaper/CompletedProfiles.lean#L84) |
| `ScalarMonotone.EndOfPaper.powerQuantileProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:86](../EndOfPaper/CompletedProfiles.lean#L86) |
| `ScalarMonotone.EndOfPaper.exponentialQuantileProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:104](../EndOfPaper/CompletedProfiles.lean#L104) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_mem` | [EndOfPaper/CompletedProfiles.lean:119](../EndOfPaper/CompletedProfiles.lean#L119) |
| `ScalarMonotone.EndOfPaper.powerProfile` | [EndOfPaper/CompletedProfiles.lean:123](../EndOfPaper/CompletedProfiles.lean#L123) |
| `ScalarMonotone.EndOfPaper.exponentialProfile` | [EndOfPaper/CompletedProfiles.lean:124](../EndOfPaper/CompletedProfiles.lean#L124) |
| `ScalarMonotone.EndOfPaper.power_profile_level_iff` | [EndOfPaper/CompletedProfiles.lean:126](../EndOfPaper/CompletedProfiles.lean#L126) |
| `ScalarMonotone.EndOfPaper.inverse_powerProfile` | [EndOfPaper/CompletedProfiles.lean:156](../EndOfPaper/CompletedProfiles.lean#L156) |
| `ScalarMonotone.EndOfPaper.inverse_exponentialProfile` | [EndOfPaper/CompletedProfiles.lean:170](../EndOfPaper/CompletedProfiles.lean#L170) |
| `ScalarMonotone.EndOfPaper.powerProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:187](../EndOfPaper/CompletedProfiles.lean#L187) |
| `ScalarMonotone.EndOfPaper.exponentialProfile_maximal` | [EndOfPaper/CompletedProfiles.lean:192](../EndOfPaper/CompletedProfiles.lean#L192) |
| `ScalarMonotone.EndOfPaper.positiveScalarGraph_hardy_unique` | [EndOfPaper/CompletedProfiles.lean:198](../EndOfPaper/CompletedProfiles.lean#L198) |
| `ScalarMonotone.EndOfPaper.hardy_powerProfile_whole` | [EndOfPaper/CompletedProfiles.lean:217](../EndOfPaper/CompletedProfiles.lean#L217) |
| `ScalarMonotone.EndOfPaper.hardy_exponentialProfile_whole` | [EndOfPaper/CompletedProfiles.lean:237](../EndOfPaper/CompletedProfiles.lean#L237) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform` | [EndOfPaper/CompletedProfiles.lean:253](../EndOfPaper/CompletedProfiles.lean#L253) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_well_defined` | [EndOfPaper/CompletedProfiles.lean:256](../EndOfPaper/CompletedProfiles.lean#L256) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_power` | [EndOfPaper/CompletedProfiles.lean:269](../EndOfPaper/CompletedProfiles.lean#L269) |
| `ScalarMonotone.EndOfPaper.hardyTailTransform_exponential` | [EndOfPaper/CompletedProfiles.lean:276](../EndOfPaper/CompletedProfiles.lean#L276) |
| `ScalarMonotone.EndOfPaper.powerProfile_outputScale` | [EndOfPaper/CompletedProfiles.lean:282](../EndOfPaper/CompletedProfiles.lean#L282) |
| `ScalarMonotone.EndOfPaper.exponentialProfile_outputScale` | [EndOfPaper/CompletedProfiles.lean:291](../EndOfPaper/CompletedProfiles.lean#L291) |
| `ScalarMonotone.EndOfPaper.hardy_regularized_profiles` | [EndOfPaper/CompletedProfiles.lean:304](../EndOfPaper/CompletedProfiles.lean#L304) |
| `ScalarMonotone.EndOfPaper.hardy_profile_identities` | [EndOfPaper/CompletedProfiles.lean:312](../EndOfPaper/CompletedProfiles.lean#L312) |
<a id="claim-17"></a>

## After Example 3.11

[PDF page 57](../manuscript/monotone_calculus.pdf#page=57). Equivalence of logarithmic convexity and limiting power convexity

An arbitrary real profile positive on its convexity domain. No continuity or monotonicity of the profile is added. The reverse implication retains arbitrary positive exponents tending to infinity, with no monotonicity restriction on that sequence. Convexity of minus log alpha implies convexity of alpha to the power minus one over kappa for every real kappa>0. Conversely power convexity for exponents tending to infinity implies logarithmic convexity. The rescaled functions kappa*(alpha^(-1/kappa)-1) converge pointwise to minus log alpha. The separately checked exact Hardy constant tends to exp(1). The derivative of exp at zero gives the rescaled exponential limit; the positive-base real-power identity gives the logarithmic limit. Positive scaling and subtraction of a constant preserve convexity, so each convexity inequality passes to the pointwise limit. The forward direction composes the positive multiple of minus log alpha with the increasing convex exponential. Independent expected types check both directions and the actual scaled limit. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hardy_power_constant_limit` | [EndOfPaper/ConvexTransforms.lean:115](../EndOfPaper/ConvexTransforms.lean#L115) |
| `ScalarMonotone.EndOfPaper.scaled_exponential_limit` | [EndOfPaper/LogPowerConvexity.lean:15](../EndOfPaper/LogPowerConvexity.lean#L15) |
| `ScalarMonotone.EndOfPaper.scaled_power_log_limit` | [EndOfPaper/LogPowerConvexity.lean:35](../EndOfPaper/LogPowerConvexity.lean#L35) |
| `ScalarMonotone.EndOfPaper.log_convex_implies_all_power_convex` | [EndOfPaper/LogPowerConvexity.lean:44](../EndOfPaper/LogPowerConvexity.lean#L44) |
| `ScalarMonotone.EndOfPaper.limiting_power_convex_implies_log_convex` | [EndOfPaper/LogPowerConvexity.lean:63](../EndOfPaper/LogPowerConvexity.lean#L63) |
<a id="claim-18"></a>

## After Example 3.11

[PDF page 57](../manuscript/monotone_calculus.pdf#page=57). Limit of the power-envelope constant to e

The real parameter kappa tends to positive infinity, hence is eventually greater than one. No integer-exponent restriction or fixed exponent is imposed. The exact paper factor (kappa/(kappa-1))^kappa tends to exp(1). This record concerns that separately inventoried constant limit; the distinct profile-specific log/power convexity equivalence remains separately tracked. Write kappa/(kappa-1)=1+1/(kappa-1), split the exponent into (kappa-1)+1 on the eventually positive base, and combine the pinned real-power exponential limit with the base limit to one. The full varying real exponent is retained. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.eventually_positive_one_add_div` | [EndOfPaper/ConvexTransforms.lean:15](../EndOfPaper/ConvexTransforms.lean#L15) |
| `ScalarMonotone.EndOfPaper.negative_power_exponential_limit` | [EndOfPaper/ConvexTransforms.lean:21](../EndOfPaper/ConvexTransforms.lean#L21) |
| `ScalarMonotone.EndOfPaper.continuous_power_exponential_limit` | [EndOfPaper/ConvexTransforms.lean:28](../EndOfPaper/ConvexTransforms.lean#L28) |
| `ScalarMonotone.EndOfPaper.all_power_convex_implies_exponential_convex` | [EndOfPaper/ConvexTransforms.lean:35](../EndOfPaper/ConvexTransforms.lean#L35) |
| `ScalarMonotone.EndOfPaper.exponential_convex_implies_power_convex` | [EndOfPaper/ConvexTransforms.lean:55](../EndOfPaper/ConvexTransforms.lean#L55) |
| `ScalarMonotone.EndOfPaper.all_power_concave_implies_exponential_concave` | [EndOfPaper/ConvexTransforms.lean:76](../EndOfPaper/ConvexTransforms.lean#L76) |
| `ScalarMonotone.EndOfPaper.exponential_concave_implies_power_concave` | [EndOfPaper/ConvexTransforms.lean:85](../EndOfPaper/ConvexTransforms.lean#L85) |
| `ScalarMonotone.EndOfPaper.power_exponential_convex_transforms` | [EndOfPaper/ConvexTransforms.lean:98](../EndOfPaper/ConvexTransforms.lean#L98) |
| `ScalarMonotone.EndOfPaper.hardy_power_constant_limit` | [EndOfPaper/ConvexTransforms.lean:115](../EndOfPaper/ConvexTransforms.lean#L115) |
<a id="claim-19"></a>

## Equation (1.9)

[PDF page 11](../manuscript/monotone_calculus.pdf#page=11). Compatible-point criterion used for product maximality

The product graph is increasing, as already established in the product proof. No maximality of the product is assumed. Adjoining (x,w) preserves monotonicity exactly when (x-y)*(w-v)>=0 for every point (y,v) of the original product graph. Prove the general compatible-point and graph-insertion equivalence, then specialize to the literal graph product. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.graphPointExtension` | [EndOfPaper/ProductCompatibility.lean:11](../EndOfPaper/ProductCompatibility.lean#L11) |
| `ScalarMonotone.EndOfPaper.compatible_graph_criterion` | [EndOfPaper/ProductCompatibility.lean:14](../EndOfPaper/ProductCompatibility.lean#L14) |
| `ScalarMonotone.EndOfPaper.compatible_extension_iff` | [EndOfPaper/ProductCompatibility.lean:22](../EndOfPaper/ProductCompatibility.lean#L22) |
| `ScalarMonotone.EndOfPaper.product_compatibility_criterion` | [EndOfPaper/ProductCompatibility.lean:37](../EndOfPaper/ProductCompatibility.lean#L37) |
<a id="claim-20"></a>

## Equation (1.13)

[PDF page 13](../manuscript/monotone_calculus.pdf#page=13). Upward and downward interval hulls

The downward and upward hulls equal Minkowski addition by (-∞,0] and [0,∞) respectively, for arbitrary real sets, hence for the paper nonempty intervals. Endpoint inclusion is retained. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.lowerHull_eq_setAdd` | [MonotoneOperators/OrderConsequences.lean:10](../MonotoneOperators/OrderConsequences.lean#L10) |
| `ScalarMonotone.upperHull_eq_setAdd` | [MonotoneOperators/OrderConsequences.lean:18](../MonotoneOperators/OrderConsequences.lean#L18) |
<a id="claim-21"></a>

## Equation (1.23)

[PDF page 17](../manuscript/monotone_calculus.pdf#page=17). Universal property of the supremum in increasing resolvent order

Arbitrary nonempty index type in either common orientation and an existing supremum. Boundedness is precisely its previously proved existence criterion; no countability or finiteness restriction is added. h equals the actual supremum if and only if every input lies below h and h lies below every competing upper bound. Both implications and both orientations are stated by named manuscript-facing theorems. Use the actual conditional-lattice supremum, the audited least-upper-bound characterization and antisymmetry. If a competing h satisfies the right side, its upper-bound clause itself supplies boundedness; the nonempty bounded family is exactly the paper's existing extremum convention. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.inc_exists_isLUB_iff` | [MonotoneOperators/Extrema.lean:254](../MonotoneOperators/Extrema.lean#L254) |
| `ScalarMonotone.dec_exists_isLUB_iff` | [MonotoneOperators/Extrema.lean:270](../MonotoneOperators/Extrema.lean#L270) |
| `ScalarMonotone.EndOfPaper.inc_sup_universal_property` | [EndOfPaper/ExtremaReader.lean:13](../EndOfPaper/ExtremaReader.lean#L13) |
| `ScalarMonotone.EndOfPaper.dec_sup_universal_property` | [EndOfPaper/ExtremaReader.lean:23](../EndOfPaper/ExtremaReader.lean#L23) |
| `ScalarMonotone.EndOfPaper.inc_graph_distributivity` | [EndOfPaper/ExtremaReader.lean:33](../EndOfPaper/ExtremaReader.lean#L33) |
| `ScalarMonotone.EndOfPaper.dec_graph_distributivity` | [EndOfPaper/ExtremaReader.lean:38](../EndOfPaper/ExtremaReader.lean#L38) |
| `ScalarMonotone.EndOfPaper.inc_finite_extremum_graph_points` | [EndOfPaper/ExtremaReader.lean:43](../EndOfPaper/ExtremaReader.lean#L43) |
| `ScalarMonotone.EndOfPaper.dec_finite_extremum_graph_points` | [EndOfPaper/ExtremaReader.lean:49](../EndOfPaper/ExtremaReader.lean#L49) |
<a id="claim-22"></a>

## Equation (1.29)

[PDF page 19](../manuscript/monotone_calculus.pdf#page=19). Ranges of finite envelopes of continuous scalar functions of one orientation

For any finite nonempty family of continuous real functions with either one common monotonicity direction, the ranges of the pointwise infimum/supremum equal the corresponding interval-order extrema of their ranges. No common Lipschitz bound, endpoint boundedness or attainment hypothesis is added. The two manuscript-facing wrappers use exactly continuity and the global common-orientation alternative. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.continuous_finite_ciInf` | [MonotoneOperators/ContinuousEnvelopes.lean:15](../MonotoneOperators/ContinuousEnvelopes.lean#L15) |
| `ScalarMonotone.continuous_finite_ciSup` | [MonotoneOperators/ContinuousEnvelopes.lean:22](../MonotoneOperators/ContinuousEnvelopes.lean#L22) |
| `ScalarMonotone.range_finite_ciInf_monotone` | [MonotoneOperators/ContinuousEnvelopes.lean:29](../MonotoneOperators/ContinuousEnvelopes.lean#L29) |
| `ScalarMonotone.range_finite_ciSup_monotone` | [MonotoneOperators/ContinuousEnvelopes.lean:49](../MonotoneOperators/ContinuousEnvelopes.lean#L49) |
| `ScalarMonotone.range_finite_ciInf_antitone` | [MonotoneOperators/ContinuousEnvelopes.lean:71](../MonotoneOperators/ContinuousEnvelopes.lean#L71) |
| `ScalarMonotone.range_finite_ciSup_antitone` | [MonotoneOperators/ContinuousEnvelopes.lean:91](../MonotoneOperators/ContinuousEnvelopes.lean#L91) |
| `ScalarMonotone.range_ciInf_eq_intervalInf_continuous` | [MonotoneOperators/ContinuousEnvelopes.lean:115](../MonotoneOperators/ContinuousEnvelopes.lean#L115) |
| `ScalarMonotone.range_ciSup_eq_intervalSup_continuous` | [MonotoneOperators/ContinuousEnvelopes.lean:140](../MonotoneOperators/ContinuousEnvelopes.lean#L140) |
<a id="claim-23"></a>

## Equation (1.46)

[PDF page 30](../manuscript/monotone_calculus.pdf#page=30). Extended moment bound from a capped operator survival envelope

The original measurable real random variable, arbitrary real pivot c, maximal decreasing alpha containing (0,infinity) in its domain with nonnegative values there, the original whole survival comparison, and every real r>0. Any selection of the actual operator cap is allowed; the cap positive domain is proved. For beta equal to the literal finite lattice infimum inf{alpha,1}, survival is bounded by beta on the whole graph. The extended centered r-th moment is bounded by integral beta(t^(1/r)), exactly equal to r times integral t^(r-1)*beta(t), including divergent values. The independent reader uses sInf{alpha,constant 1}, bridged by csInf_pair. Prove membership of the scalar minimum in the true binary lattice infimum by the exact resolvent characterization, deriving the cap domain. Apply the lattice universal property to the original survival bound and its probability-one bound. Use layer cake and the exact positive-root strict superlevel equivalence for the moment inequality; derive the full extended substitution from the pinned Jacobian change-of-variables theorem on the positive half-line, with injectivity, derivative and onto-image obligations proved. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.moment_le_capped_tail_area` | [EndOfPaper/Moments.lean:45](../EndOfPaper/Moments.lean#L45) |
| `ScalarMonotone.EndOfPaper.centered_moment_le_capped_tail_area` | [EndOfPaper/Moments.lean:61](../EndOfPaper/Moments.lean#L61) |
| `ScalarMonotone.EndOfPaper.moment_identities_of_selections` | [EndOfPaper/QuantileMoments.lean:106](../EndOfPaper/QuantileMoments.lean#L106) |
| `ScalarMonotone.EndOfPaper.decreasing_inf_min_mem` | [EndOfPaper/CappedOperatorMoments.lean:15](../EndOfPaper/CappedOperatorMoments.lean#L15) |
| `ScalarMonotone.EndOfPaper.survival_le_operator_cap` | [EndOfPaper/CappedOperatorMoments.lean:32](../EndOfPaper/CappedOperatorMoments.lean#L32) |
| `ScalarMonotone.EndOfPaper.operator_cap_positive_domain` | [EndOfPaper/CappedOperatorMoments.lean:44](../EndOfPaper/CappedOperatorMoments.lean#L44) |
| `ScalarMonotone.EndOfPaper.centered_moment_operator_cap` | [EndOfPaper/CappedOperatorMoments.lean:50](../EndOfPaper/CappedOperatorMoments.lean#L50) |
| `ScalarMonotone.EndOfPaper.lintegral_image_eq_abs_deriv_mul` | [EndOfPaper/PositivePowerArea.lean:13](../EndOfPaper/PositivePowerArea.lean#L13) |
| `ScalarMonotone.EndOfPaper.positive_power_area_substitution` | [EndOfPaper/PositivePowerArea.lean:21](../EndOfPaper/PositivePowerArea.lean#L21) |
<a id="claim-24"></a>

## Equation (1.48)

[PDF page 31](../manuscript/monotone_calculus.pdf#page=31). Median-to-copy and copy-to-pivot tail comparisons

The original real-valued random variable and independent identically distributed copy on any original probability space, any median and any real pivot, with the displayed t>0. The median definition is exactly the two closed-half-line probabilities at least one half; atoms are allowed and no integrability is imposed. median_independent_copy_tail proves the exact factor-two median-to-copy bound, in fact also at t=0. independent_copy_pivot_tail proves the exact factor-two copy-to-pivot bound at t/2 for every real threshold, including the original positive thresholds. Pair each one-sided strict deviation event with the opposite closed half-line of the independent copy. Their disjoint union lies in the copy-difference event; independence, identical laws and both median inequalities yield the first bound. The triangle inequality, a union bound and identical pivot-tail laws give the second. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.IsRealMedian` | [EndOfPaper/IndependentCopyTails.lean:12](../EndOfPaper/IndependentCopyTails.lean#L12) |
| `ScalarMonotone.EndOfPaper.indepFun_measureReal_inter` | [EndOfPaper/IndependentCopyTails.lean:15](../EndOfPaper/IndependentCopyTails.lean#L15) |
| `ScalarMonotone.EndOfPaper.median_independent_copy_tail` | [EndOfPaper/IndependentCopyTails.lean:22](../EndOfPaper/IndependentCopyTails.lean#L22) |
| `ScalarMonotone.EndOfPaper.independent_copy_pivot_tail` | [EndOfPaper/IndependentCopyTails.lean:101](../EndOfPaper/IndependentCopyTails.lean#L101) |
<a id="claim-25"></a>

## Equation (2.2)

[PDF page 32](../manuscript/monotone_calculus.pdf#page=32). Scalar value of the completed Hardy transform on its domain interior

The paper maximal decreasing graph, integrability of a scalar selection, and zero lower domain endpoint with a positive domain point. IsGLB(dom f,0) expresses the actual greatest lower bound; existence of a positive domain point expresses positivity of the possibly infinite supremum. No finite upper endpoint, common-domain geometry or integrability of endpoint maps is assumed. The actual completed Aumann integral of restricted positive dilations is well defined and maximal decreasing. Its domain interior equals the original interior, its domain lies in that closure, and every interior fiber is the singleton (integral from 0 to p of s)/p. The full completed graph is unique, including every boundary fiber. It is independent of the integrable selection because the operator definition contains only I and f. Derive a nonempty positive initial interval from the domain greatest lower bound and maximality. Prove positive dilations and their completed restrictions maximal with the exact common interior. Affine substitution and ae selection equality prove both endpoint maps integrable and give the same scalar area. The full FamilyIntegral theorems then preserve those singleton fibers and prove whole-graph uniqueness. hardyFamilyIntegral is defined by decreasingFamilyIntegral of the actual completed dilations, not by the desired scalar formula. hardyFamilyIntegral_eq_actual_dilations proves equality of the entire completed integral with the literal r-dilation family. The harmless parameter extension outside (0,1) is eliminated by a proved ae family-congruence theorem. Integrability on the domain implies integrability on its interior. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.positiveInputDilation` | [EndOfPaper/HardyIntegral.lean:18](../EndOfPaper/HardyIntegral.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveInputDilation_maximal` | [EndOfPaper/HardyIntegral.lean:20](../EndOfPaper/HardyIntegral.lean#L20) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction` | [EndOfPaper/HardyIntegral.lean:47](../EndOfPaper/HardyIntegral.lean#L47) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_value` | [EndOfPaper/HardyIntegral.lean:50](../EndOfPaper/HardyIntegral.lean#L50) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_maximal` | [EndOfPaper/HardyIntegral.lean:61](../EndOfPaper/HardyIntegral.lean#L61) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_domain` | [EndOfPaper/HardyIntegral.lean:70](../EndOfPaper/HardyIntegral.lean#L70) |
| `ScalarMonotone.EndOfPaper.hardyParameter` | [EndOfPaper/HardyIntegral.lean:87](../EndOfPaper/HardyIntegral.lean#L87) |
| `ScalarMonotone.EndOfPaper.hardyParameter_bounds` | [EndOfPaper/HardyIntegral.lean:89](../EndOfPaper/HardyIntegral.lean#L89) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily` | [EndOfPaper/HardyIntegral.lean:95](../EndOfPaper/HardyIntegral.lean#L95) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily_properties` | [EndOfPaper/HardyIntegral.lean:98](../EndOfPaper/HardyIntegral.lean#L98) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral` | [EndOfPaper/HardyIntegral.lean:116](../EndOfPaper/HardyIntegral.lean#L116) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_congr_ae` | [EndOfPaper/HardyIntegral.lean:121](../EndOfPaper/HardyIntegral.lean#L121) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_eq_actual_dilations` | [EndOfPaper/HardyIntegral.lean:135](../EndOfPaper/HardyIntegral.lean#L135) |
| `ScalarMonotone.EndOfPaper.decreasing_zero_inf_domain_geometry` | [EndOfPaper/HardyIntegral.lean:144](../EndOfPaper/HardyIntegral.lean#L144) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily_endpoint_areas` | [EndOfPaper/HardyIntegral.lean:179](../EndOfPaper/HardyIntegral.lean#L179) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_well_defined` | [EndOfPaper/HardyIntegral.lean:205](../EndOfPaper/HardyIntegral.lean#L205) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_of_integrable` | [EndOfPaper/HardyIntegral.lean:248](../EndOfPaper/HardyIntegral.lean#L248) |
<a id="claim-26"></a>

## Equation (A.1)

[PDF page 61](../manuscript/monotone_calculus.pdf#page=61). Odd-median subset-sum upper bound

For every r including zero, every natural ell, every nonnegative vector in Fin(2*r+1) and every subset of cardinal r+ell, the full inequality ell times scalarMedian <= its coordinate sum is proved. The argument uses a median lower majority and intersection cardinality, with no sortedness or additional positivity of ell required. The sorted-prefix equality and reverse transform bound are separate obligations. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.median_subset_sum_bound` | [EndOfPaper/MedianBounds.lean:123](../EndOfPaper/MedianBounds.lean#L123) |
<a id="claim-27"></a>

## Equation (A.2)

[PDF page 61](../manuscript/monotone_calculus.pdf#page=61). Exact truncation identity at the minimizing median-transform level

Exactly the nonnegative vector and the specific finite minimum over sorted prefix ratios in the manuscript. The truncation sum equals (r+1)t. All cut inequalities and attainment of a minimizing index are derived; none remains a hypothesis. Use the full transform formula and subset upper estimates for the lower capacity inequality, then an attained sorted-prefix cut for the reverse inequality. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.truncation_sum_ge_iff_cuts` | [EndOfPaper/MedianCapacity.lean:48](../EndOfPaper/MedianCapacity.lean#L48) |
| `ScalarMonotone.EndOfPaper.truncation_sum_eq_of_attained_cut` | [EndOfPaper/MedianCapacity.lean:64](../EndOfPaper/MedianCapacity.lean#L64) |
| `ScalarMonotone.EndOfPaper.odd_median_truncation_capacity` | [EndOfPaper/MedianCapacity.lean:72](../EndOfPaper/MedianCapacity.lean#L72) |
| `ScalarMonotone.EndOfPaper.median_transform_truncation_identity` | [EndOfPaper/MedianTransform.lean:164](../EndOfPaper/MedianTransform.lean#L164) |
| `ScalarMonotone.EndOfPaper.median_transform_formula` | [EndOfPaper/MedianTransform.lean:155](../EndOfPaper/MedianTransform.lean#L155) |
| `ScalarMonotone.EndOfPaper.median_transform_ordered_coordinates` | [EndOfPaper/MedianTransform.lean:105](../EndOfPaper/MedianTransform.lean#L105) |
<a id="claim-28"></a>

## Equation (2.11)

[PDF page 38](../manuscript/monotone_calculus.pdf#page=38). Original-space feasible-weight formula for Hardy tail averages

The full original-space Hardy variational theorem proves the displayed literal unnormalized product supremum divided by p for every integrable random variable, hence for nonnegative Y. It uses the actual completed Hardy family integral and an attained feasible weight on Ω; atoms are permitted. Multiplication commutes, so E[Yξ]=E[ξY]. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hardy_tailQuantile_fiber` | [EndOfPaper/HardyVariational.lean:27](../EndOfPaper/HardyVariational.lean#L27) |
| `ScalarMonotone.EndOfPaper.weightedProductCandidates` | [EndOfPaper/HardyVariational.lean:75](../EndOfPaper/HardyVariational.lean#L75) |
| `ScalarMonotone.EndOfPaper.dualCandidates_greatest_unnormalized` | [EndOfPaper/HardyVariational.lean:80](../EndOfPaper/HardyVariational.lean#L80) |
| `ScalarMonotone.EndOfPaper.hardy_quantile_original_variational` | [EndOfPaper/HardyVariational.lean:95](../EndOfPaper/HardyVariational.lean#L95) |
<a id="claim-29"></a>

## Equation (3.3)

[PDF page 49](../manuscript/monotone_calculus.pdf#page=49). Geometric Hardy averaging commutes with completed products

The original admissible nonnegative maximal profiles with common domain interior (0,1) and finite positive-log areas for arbitrary selections. The finite-family extension requires no strict positivity, global log L1, output-class closure or finite negative-log area. geometric_hardy_finite_product proves the whole completed finite-product identity for the literal common-interior graph products on both sides. geometricPrefixValue_finite_product proves the all-level scalar prefix identity for arbitrary original selections, including zeros and internal jump levels. The original binary identity remains included. Use the actual finite graph-product constructor and its proved properties. Reuse the checked binary extended prefix multiplicativity on finite subproducts, derive measurable representatives, transfer scalar values pointwise through AE prefix equality, and conclude whole graph equality from actual selections and maximality. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.interiorProfileProduct` | [EndOfPaper/InitialProfileProduct.lean:13](../EndOfPaper/InitialProfileProduct.lean#L13) |
| `ScalarMonotone.EndOfPaper.interiorProfileProduct_decreasing` | [EndOfPaper/InitialProfileProduct.lean:16](../EndOfPaper/InitialProfileProduct.lean#L16) |
| `ScalarMonotone.EndOfPaper.interiorProfileProduct_domain` | [EndOfPaper/InitialProfileProduct.lean:32](../EndOfPaper/InitialProfileProduct.lean#L32) |
| `ScalarMonotone.EndOfPaper.completedProfileProduct` | [EndOfPaper/InitialProfileProduct.lean:47](../EndOfPaper/InitialProfileProduct.lean#L47) |
| `ScalarMonotone.EndOfPaper.completedProfileProduct_raw_inclusion` | [EndOfPaper/InitialProfileProduct.lean:61](../EndOfPaper/InitialProfileProduct.lean#L61) |
| `ScalarMonotone.EndOfPaper.completedProfileProduct_domain` | [EndOfPaper/InitialProfileProduct.lean:78](../EndOfPaper/InitialProfileProduct.lean#L78) |
| `ScalarMonotone.EndOfPaper.completedProfileProduct_nonnegative` | [EndOfPaper/InitialProfileProduct.lean:97](../EndOfPaper/InitialProfileProduct.lean#L97) |
| `ScalarMonotone.EndOfPaper.completedProfileProduct_selection` | [EndOfPaper/InitialProfileProduct.lean:116](../EndOfPaper/InitialProfileProduct.lean#L116) |
| `ScalarMonotone.EndOfPaper.completedProfileProduct_unique` | [EndOfPaper/InitialProfileProduct.lean:128](../EndOfPaper/InitialProfileProduct.lean#L128) |
| `ScalarMonotone.EndOfPaper.initial_decLE_of_selection_ae_le` | [EndOfPaper/GeometricProduct.lean:15](../EndOfPaper/GeometricProduct.lean#L15) |
| `ScalarMonotone.EndOfPaper.initial_profile_eq_of_selection_ae_eq` | [EndOfPaper/GeometricProduct.lean:46](../EndOfPaper/GeometricProduct.lean#L46) |
| `ScalarMonotone.EndOfPaper.positive_log_mul_le` | [EndOfPaper/GeometricProduct.lean:57](../EndOfPaper/GeometricProduct.lean#L57) |
| `ScalarMonotone.EndOfPaper.negative_log_mul_le` | [EndOfPaper/GeometricProduct.lean:68](../EndOfPaper/GeometricProduct.lean#L68) |
| `ScalarMonotone.EndOfPaper.positive_log_area_mul_finite` | [EndOfPaper/GeometricProduct.lean:82](../EndOfPaper/GeometricProduct.lean#L82) |
| `ScalarMonotone.EndOfPaper.negative_log_area_mul_top_left` | [EndOfPaper/GeometricProduct.lean:102](../EndOfPaper/GeometricProduct.lean#L102) |
| `ScalarMonotone.EndOfPaper.logarithmic_mul_prefix_integrable` | [EndOfPaper/GeometricProduct.lean:126](../EndOfPaper/GeometricProduct.lean#L126) |
| `ScalarMonotone.EndOfPaper.hardy_log_mul_prefix` | [EndOfPaper/GeometricProduct.lean:136](../EndOfPaper/GeometricProduct.lean#L136) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_mul` | [EndOfPaper/GeometricProduct.lean:151](../EndOfPaper/GeometricProduct.lean#L151) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_product` | [EndOfPaper/GeometricProduct.lean:190](../EndOfPaper/GeometricProduct.lean#L190) |
| `ScalarMonotone.EndOfPaper.positive_log_area_finset_prod_finite` | [EndOfPaper/FiniteGeometricProduct.lean:15](../EndOfPaper/FiniteGeometricProduct.lean#L15) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_one` | [EndOfPaper/FiniteGeometricProduct.lean:30](../EndOfPaper/FiniteGeometricProduct.lean#L30) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_finset_prod` | [EndOfPaper/FiniteGeometricProduct.lean:36](../EndOfPaper/FiniteGeometricProduct.lean#L36) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_finite_product` | [EndOfPaper/FiniteGeometricProduct.lean:69](../EndOfPaper/FiniteGeometricProduct.lean#L69) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_finite_product` | [EndOfPaper/FiniteGeometricProduct.lean:95](../EndOfPaper/FiniteGeometricProduct.lean#L95) |
<a id="claim-30"></a>

## Equation (3.4)

[PDF page 49](../manuscript/monotone_calculus.pdf#page=49). Geometric Hardy averaging commutes with completed positive dilations

Exactly the admissible q on (0,1) with finite positive-log area under an arbitrary input selection, and c>0. The unit theorem derives positivity and coverage of J_c=(0,min(1,1/c)); they are not added final assumptions. There is no global log L1, strict positivity, endpoint sign, global measurability of the original selection, or admissible-class closure assumption about G(q). geometric_hardy_dilation proves equality of the whole maximal completions on J_c: G of the completed restriction of q(c*id) equals the completed restriction of G(q)(c*id). completedProfileDilation is the actual restriction/negation/completion construction and has the exact required interior and values. Both outward boundary fibers and internal zero jumps are retained. Prove the exact push-forward of restricted Lebesgue measure and change of variables for both extended logarithmic parts, including infinity. Treat finite negative area by derived local log L1 and the ordinary Hardy dilation identity. Treat infinite negative area by the explicit zero convention. Derive measurable representatives and identify the full completed graphs by uniqueness of the scalar completion. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.geometric_hardy_scalar_completion` | [EndOfPaper/GeometricScalarCompletion.lean:233](../EndOfPaper/GeometricScalarCompletion.lean#L233) |
| `ScalarMonotone.EndOfPaper.positive_prefix_map_dilation` | [EndOfPaper/GeometricDilation.lean:16](../EndOfPaper/GeometricDilation.lean#L16) |
| `ScalarMonotone.EndOfPaper.lintegral_positive_prefix_dilation` | [EndOfPaper/GeometricDilation.lean:28](../EndOfPaper/GeometricDilation.lean#L28) |
| `ScalarMonotone.EndOfPaper.negativeLogWithZero_measurable` | [EndOfPaper/GeometricDilation.lean:36](../EndOfPaper/GeometricDilation.lean#L36) |
| `ScalarMonotone.EndOfPaper.hardyScalar_positive_dilation` | [EndOfPaper/GeometricDilation.lean:42](../EndOfPaper/GeometricDilation.lean#L42) |
| `ScalarMonotone.EndOfPaper.positive_log_area_dilation_finite` | [EndOfPaper/GeometricDilation.lean:48](../EndOfPaper/GeometricDilation.lean#L48) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_positive_dilation` | [EndOfPaper/GeometricDilation.lean:61](../EndOfPaper/GeometricDilation.lean#L61) |
| `ScalarMonotone.EndOfPaper.initial_dilation_mapsTo` | [EndOfPaper/GeometricDilation.lean:97](../EndOfPaper/GeometricDilation.lean#L97) |
| `ScalarMonotone.EndOfPaper.completedProfileDilation` | [EndOfPaper/GeometricDilation.lean:102](../EndOfPaper/GeometricDilation.lean#L102) |
| `ScalarMonotone.EndOfPaper.completedProfileDilation_properties` | [EndOfPaper/GeometricDilation.lean:114](../EndOfPaper/GeometricDilation.lean#L114) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_dilation_on_initial_interval` | [EndOfPaper/GeometricDilation.lean:135](../EndOfPaper/GeometricDilation.lean#L135) |
| `ScalarMonotone.EndOfPaper.geometric_hardy_dilation` | [EndOfPaper/GeometricDilation.lean:179](../EndOfPaper/GeometricDilation.lean#L179) |
<a id="claim-31"></a>

## Equation (3.13)

[PDF page 52](../manuscript/monotone_calculus.pdf#page=52). Logarithmic control means bounded by marginal quantile areas

Exactly the initial strictly positive-profile proof context, actual marginal quantile bounds, arbitrary original-space controls and selections, and the single combined positive-log area for baseline and every control. Selected cutoff values c_i belong to q_i(b); their strict positivity is derived. No individual area, random L1 or measurable-selection final hypothesis is added. Every logarithmic excess and its finite sum are integrable; expectation of the sum is the sum of expectations, bounded by the sum of normalized positive-log profile areas, which equals exactly the integral on (0,b) of the logarithm of the product divided by the product of cutoffs. Derive all individual areas from the single original Option-indexed product, obtain arbitrary-selection L1 using measurable representatives, and use the actual quantile-law expectation bound. Establish the exact prefix product identity by monotonicity on either side of b, retaining graph-valued cutoffs and omitting only the Lebesgue-null point b. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.local_logarithmic_mean` | [EndOfPaper/LocalLogMean.lean:14](../EndOfPaper/LocalLogMean.lean#L14) |
| `ScalarMonotone.EndOfPaper.finite_log_excess_product_area` | [EndOfPaper/LogExcessProductArea.lean:12](../EndOfPaper/LogExcessProductArea.lean#L12) |
| `ScalarMonotone.EndOfPaper.profile_log_excess_integrable_of_selection` | [EndOfPaper/ProfileExcessArbitrary.lean:13](../EndOfPaper/ProfileExcessArbitrary.lean#L13) |
| `ScalarMonotone.EndOfPaper.logarithmic_excess_mean_bound_of_selection` | [EndOfPaper/ProfileExcessArbitrary.lean:31](../EndOfPaper/ProfileExcessArbitrary.lean#L31) |
<a id="claim-32"></a>

## Equation (3.14)

[PDF page 53](../manuscript/monotone_calculus.pdf#page=53). Two-parameter randomized Lipschitz tail estimate with budget a+2b

The original metric spaces, arbitrary original probability space, independent identical copy, measurable map and controls, baseline and marginal whole quantile comparisons, n>=1, no identically zero input and a single combined positive-log area on arbitrary selections. Individual areas and actual output-profile properties are derived. randomized_lipschitz_two_parameter_geometric proves the a+2b strict-tail bound for every t in qDelta(a) and every selected value of the actual completed G(control product) at b, including jumps and probability budgets at least one. randomized_lipschitz_optimized proves the actual minimum output quantile is at most the infimum over a,b>0 with a+2b<=u, for arbitrary scalar selections of the actual geometric profile. randomized_lipschitz_sharper_bound proves the whole completed product qDelta*G(control product) at probability u/3, including both endpoints. Derive the control-product geometric graph and actual scalar selection, prove whole comparison to its literal unequal-level product for alpha+2beta<=1, then choose alpha=a/u and beta=b/u. Every input jump value lies in the target fiber; interval order bounds the attained minimum output quantile. Take the literal infimum, and use the whole equal-dilation product identity for the sharper graph. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.quantile_lower_endpoint_isLeast` | [EndOfPaper/OptimizedTailBudget.lean:13](../EndOfPaper/OptimizedTailBudget.lean#L13) |
| `ScalarMonotone.EndOfPaper.randomized_individual_log_areas` | [EndOfPaper/RandomizedProfileData.lean:15](../EndOfPaper/RandomizedProfileData.lean#L15) |
| `ScalarMonotone.EndOfPaper.geometricFiniteProfileProduct` | [EndOfPaper/RandomizedProfileData.lean:49](../EndOfPaper/RandomizedProfileData.lean#L49) |
| `ScalarMonotone.EndOfPaper.geometricFiniteProfileProduct_properties` | [EndOfPaper/RandomizedProfileData.lean:66](../EndOfPaper/RandomizedProfileData.lean#L66) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_unequal_bound` | [EndOfPaper/RandomizedUnequalBound.lean:43](../EndOfPaper/RandomizedUnequalBound.lean#L43) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized_at` | [EndOfPaper/RandomizedUnequalBound.lean:85](../EndOfPaper/RandomizedUnequalBound.lean#L85) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_two_parameter_geometric` | [EndOfPaper/RandomizedUnequalBound.lean:120](../EndOfPaper/RandomizedUnequalBound.lean#L120) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized` | [EndOfPaper/RandomizedUnequalBound.lean:146](../EndOfPaper/RandomizedUnequalBound.lean#L146) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_sharper_bound` | [EndOfPaper/RandomizedUnequalBound.lean:163](../EndOfPaper/RandomizedUnequalBound.lean#L163) |
<a id="claim-33"></a>

## Equation (3.15)

[PDF page 53](../manuscript/monotone_calculus.pdf#page=53). Optimized lower-quantile estimate over unequal probability levels

The original metric spaces, arbitrary original probability space, independent identical copy, measurable map and controls, baseline and marginal whole quantile comparisons, n>=1, no identically zero input and a single combined positive-log area on arbitrary selections. Individual areas and actual output-profile properties are derived. randomized_lipschitz_two_parameter_geometric proves the a+2b strict-tail bound for every t in qDelta(a) and every selected value of the actual completed G(control product) at b, including jumps and probability budgets at least one. randomized_lipschitz_optimized proves the actual minimum output quantile is at most the infimum over a,b>0 with a+2b<=u, for arbitrary scalar selections of the actual geometric profile. randomized_lipschitz_sharper_bound proves the whole completed product qDelta*G(control product) at probability u/3, including both endpoints. Derive the control-product geometric graph and actual scalar selection, prove whole comparison to its literal unequal-level product for alpha+2beta<=1, then choose alpha=a/u and beta=b/u. Every input jump value lies in the target fiber; interval order bounds the attained minimum output quantile. Take the literal infimum, and use the whole equal-dilation product identity for the sharper graph. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.quantile_lower_endpoint_isLeast` | [EndOfPaper/OptimizedTailBudget.lean:13](../EndOfPaper/OptimizedTailBudget.lean#L13) |
| `ScalarMonotone.EndOfPaper.quantile_lower_endpoint_le_of_strict_tail` | [EndOfPaper/OptimizedTailBudget.lean:18](../EndOfPaper/OptimizedTailBudget.lean#L18) |
| `ScalarMonotone.EndOfPaper.quantile_lower_endpoint_le_of_decLE` | [EndOfPaper/OptimizedTailBudget.lean:35](../EndOfPaper/OptimizedTailBudget.lean#L35) |
| `ScalarMonotone.EndOfPaper.twoParameterThresholds` | [EndOfPaper/OptimizedTailBudget.lean:44](../EndOfPaper/OptimizedTailBudget.lean#L44) |
| `ScalarMonotone.EndOfPaper.twoParameterThresholds_nonempty` | [EndOfPaper/OptimizedTailBudget.lean:47](../EndOfPaper/OptimizedTailBudget.lean#L47) |
| `ScalarMonotone.EndOfPaper.quantile_lower_endpoint_le_two_parameter_inf` | [EndOfPaper/OptimizedTailBudget.lean:52](../EndOfPaper/OptimizedTailBudget.lean#L52) |
| `ScalarMonotone.EndOfPaper.randomized_individual_log_areas` | [EndOfPaper/RandomizedProfileData.lean:15](../EndOfPaper/RandomizedProfileData.lean#L15) |
| `ScalarMonotone.EndOfPaper.geometricFiniteProfileProduct` | [EndOfPaper/RandomizedProfileData.lean:49](../EndOfPaper/RandomizedProfileData.lean#L49) |
| `ScalarMonotone.EndOfPaper.geometricFiniteProfileProduct_properties` | [EndOfPaper/RandomizedProfileData.lean:66](../EndOfPaper/RandomizedProfileData.lean#L66) |
| `ScalarMonotone.EndOfPaper.completedProfileDilation_nonnegative` | [EndOfPaper/UnequalProfileProduct.lean:13](../EndOfPaper/UnequalProfileProduct.lean#L13) |
| `ScalarMonotone.EndOfPaper.completedUnequalProfileProduct` | [EndOfPaper/UnequalProfileProduct.lean:26](../EndOfPaper/UnequalProfileProduct.lean#L26) |
| `ScalarMonotone.EndOfPaper.completedUnequalProfileProduct_properties` | [EndOfPaper/UnequalProfileProduct.lean:40](../EndOfPaper/UnequalProfileProduct.lean#L40) |
| `ScalarMonotone.EndOfPaper.completedUnequalProfileProduct_selection` | [EndOfPaper/UnequalProfileProduct.lean:67](../EndOfPaper/UnequalProfileProduct.lean#L67) |
| `ScalarMonotone.EndOfPaper.completedUnequalProfileProduct_equal_dilation` | [EndOfPaper/UnequalProfileProduct.lean:82](../EndOfPaper/UnequalProfileProduct.lean#L82) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_unequal_bound` | [EndOfPaper/RandomizedUnequalBound.lean:43](../EndOfPaper/RandomizedUnequalBound.lean#L43) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized_at` | [EndOfPaper/RandomizedUnequalBound.lean:85](../EndOfPaper/RandomizedUnequalBound.lean#L85) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_two_parameter_geometric` | [EndOfPaper/RandomizedUnequalBound.lean:120](../EndOfPaper/RandomizedUnequalBound.lean#L120) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized` | [EndOfPaper/RandomizedUnequalBound.lean:146](../EndOfPaper/RandomizedUnequalBound.lean#L146) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_sharper_bound` | [EndOfPaper/RandomizedUnequalBound.lean:163](../EndOfPaper/RandomizedUnequalBound.lean#L163) |
<a id="claim-34"></a>

## Equation (3.16)

[PDF page 53](../manuscript/monotone_calculus.pdf#page=53). Completed sharper randomized Lipschitz bound with dilation 3

The original metric spaces, arbitrary original probability space, independent identical copy, measurable map and controls, baseline and marginal whole quantile comparisons, n>=1, no identically zero input and a single combined positive-log area on arbitrary selections. Individual areas and actual output-profile properties are derived. randomized_lipschitz_two_parameter_geometric proves the a+2b strict-tail bound for every t in qDelta(a) and every selected value of the actual completed G(control product) at b, including jumps and probability budgets at least one. randomized_lipschitz_optimized proves the actual minimum output quantile is at most the infimum over a,b>0 with a+2b<=u, for arbitrary scalar selections of the actual geometric profile. randomized_lipschitz_sharper_bound proves the whole completed product qDelta*G(control product) at probability u/3, including both endpoints. Derive the control-product geometric graph and actual scalar selection, prove whole comparison to its literal unequal-level product for alpha+2beta<=1, then choose alpha=a/u and beta=b/u. Every input jump value lies in the target fiber; interval order bounds the attained minimum output quantile. Take the literal infimum, and use the whole equal-dilation product identity for the sharper graph. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.quantile_lower_endpoint_isLeast` | [EndOfPaper/OptimizedTailBudget.lean:13](../EndOfPaper/OptimizedTailBudget.lean#L13) |
| `ScalarMonotone.EndOfPaper.randomized_individual_log_areas` | [EndOfPaper/RandomizedProfileData.lean:15](../EndOfPaper/RandomizedProfileData.lean#L15) |
| `ScalarMonotone.EndOfPaper.geometricFiniteProfileProduct` | [EndOfPaper/RandomizedProfileData.lean:49](../EndOfPaper/RandomizedProfileData.lean#L49) |
| `ScalarMonotone.EndOfPaper.geometricFiniteProfileProduct_properties` | [EndOfPaper/RandomizedProfileData.lean:66](../EndOfPaper/RandomizedProfileData.lean#L66) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_unequal_bound` | [EndOfPaper/RandomizedUnequalBound.lean:43](../EndOfPaper/RandomizedUnequalBound.lean#L43) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized_at` | [EndOfPaper/RandomizedUnequalBound.lean:85](../EndOfPaper/RandomizedUnequalBound.lean#L85) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_two_parameter_geometric` | [EndOfPaper/RandomizedUnequalBound.lean:120](../EndOfPaper/RandomizedUnequalBound.lean#L120) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_optimized` | [EndOfPaper/RandomizedUnequalBound.lean:146](../EndOfPaper/RandomizedUnequalBound.lean#L146) |
| `ScalarMonotone.EndOfPaper.randomized_lipschitz_sharper_bound` | [EndOfPaper/RandomizedUnequalBound.lean:163](../EndOfPaper/RandomizedUnequalBound.lean#L163) |
<a id="claim-35"></a>

## Equation (3.19)

[PDF page 55](../manuscript/monotone_calculus.pdf#page=55). Random feed-forward network definition and normalization

The original finite data/weight dimensions, N>0 and p_i>0 through depth L, and entrywise one-Lipschitz activations vanishing at zero. The theorem permits depth zero as well. No measurability of the final network is assumed. networkLayer is the literal normalized matrix recurrence, networkOutput is H_L/sqrt(p_L), and finiteNetworkMap is this construction on the actual finite Euclidean product of HS matrix blocks. network_parameter_norm_sq proves the exact product metric. finite_network_borel_measurable derives Borel measurability. Represent HS matrices by EuclideanSpace on their entry index set. Use actual Matrix.toEuclideanLin and actual matrix multiplication. Fin L indexes paper layers 1 through L by l.val+1; the arbitrary extensions outside this range do not enter the depth-L output. The independent reader expands the layer recurrence and exact Euclidean squared norm. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hsMatrixActivation` | [EndOfPaper/HSMatrixActivation.lean:12](../EndOfPaper/HSMatrixActivation.lean#L12) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_zero` | [EndOfPaper/HSMatrixActivation.lean:15](../EndOfPaper/HSMatrixActivation.lean#L15) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_contraction` | [EndOfPaper/HSMatrixActivation.lean:20](../EndOfPaper/HSMatrixActivation.lean#L20) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_lipschitz` | [EndOfPaper/HSMatrixActivation.lean:33](../EndOfPaper/HSMatrixActivation.lean#L33) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_norm_le` | [EndOfPaper/HSMatrixActivation.lean:39](../EndOfPaper/HSMatrixActivation.lean#L39) |
| `ScalarMonotone.EndOfPaper.HSMatrix` | [EndOfPaper/HSMatrixBasic.lean:13](../EndOfPaper/HSMatrixBasic.lean#L13) |
| `ScalarMonotone.EndOfPaper.hsMatrixToMatrix` | [EndOfPaper/HSMatrixBasic.lean:15](../EndOfPaper/HSMatrixBasic.lean#L15) |
| `ScalarMonotone.EndOfPaper.hsMatrixOfMatrix` | [EndOfPaper/HSMatrixBasic.lean:18](../EndOfPaper/HSMatrixBasic.lean#L18) |
| `ScalarMonotone.EndOfPaper.hs_matrix_to_of` | [EndOfPaper/HSMatrixBasic.lean:21](../EndOfPaper/HSMatrixBasic.lean#L21) |
| `ScalarMonotone.EndOfPaper.hs_matrix_of_to` | [EndOfPaper/HSMatrixBasic.lean:24](../EndOfPaper/HSMatrixBasic.lean#L24) |
| `ScalarMonotone.EndOfPaper.hs_matrix_norm_sq` | [EndOfPaper/HSMatrixBasic.lean:29](../EndOfPaper/HSMatrixBasic.lean#L29) |
| `ScalarMonotone.EndOfPaper.hsMatrixOp` | [EndOfPaper/HSMatrixOperator.lean:11](../EndOfPaper/HSMatrixOperator.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_apply` | [EndOfPaper/HSMatrixOperator.lean:16](../EndOfPaper/HSMatrixOperator.lean#L16) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_norm_le` | [EndOfPaper/HSMatrixOperator.lean:20](../EndOfPaper/HSMatrixOperator.lean#L20) |
| `ScalarMonotone.EndOfPaper.hsMatrixMul` | [EndOfPaper/HSMatrixOperator.lean:42](../EndOfPaper/HSMatrixOperator.lean#L42) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_apply` | [EndOfPaper/HSMatrixOperator.lean:45](../EndOfPaper/HSMatrixOperator.lean#L45) |
| `ScalarMonotone.EndOfPaper.network_control_continuous` | [EndOfPaper/NetworkContinuity.lean:12](../EndOfPaper/NetworkContinuity.lean#L12) |
| `ScalarMonotone.EndOfPaper.finite_network_continuous` | [EndOfPaper/NetworkContinuity.lean:17](../EndOfPaper/NetworkContinuity.lean#L17) |
| `ScalarMonotone.EndOfPaper.finite_network_borel_measurable` | [EndOfPaper/NetworkContinuity.lean:35](../EndOfPaper/NetworkContinuity.lean#L35) |
| `ScalarMonotone.EndOfPaper.networkControl` | [EndOfPaper/NetworkControls.lean:10](../EndOfPaper/NetworkControls.lean#L10) |
| `ScalarMonotone.EndOfPaper.network_control_nonnegative` | [EndOfPaper/NetworkControls.lean:14](../EndOfPaper/NetworkControls.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkActivationsAt` | [EndOfPaper/NetworkControls.lean:18](../EndOfPaper/NetworkControls.lean#L18) |
| `ScalarMonotone.EndOfPaper.network_activations_lipschitz` | [EndOfPaper/NetworkControls.lean:21](../EndOfPaper/NetworkControls.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_activations_zero` | [EndOfPaper/NetworkControls.lean:28](../EndOfPaper/NetworkControls.lean#L28) |
| `ScalarMonotone.EndOfPaper.finiteNetworkMap` | [EndOfPaper/NetworkControls.lean:35](../EndOfPaper/NetworkControls.lean#L35) |
| `ScalarMonotone.EndOfPaper.networkLayer` | [EndOfPaper/NetworkLayers.lean:12](../EndOfPaper/NetworkLayers.lean#L12) |
| `ScalarMonotone.EndOfPaper.networkOutput` | [EndOfPaper/NetworkLayers.lean:20](../EndOfPaper/NetworkLayers.lean#L20) |
| `ScalarMonotone.EndOfPaper.network_layer_norm_step` | [EndOfPaper/NetworkLayers.lean:26](../EndOfPaper/NetworkLayers.lean#L26) |
| `ScalarMonotone.EndOfPaper.network_layer_difference_step` | [EndOfPaper/NetworkLayers.lean:40](../EndOfPaper/NetworkLayers.lean#L40) |
| `ScalarMonotone.EndOfPaper.NetworkCoordinate` | [EndOfPaper/NetworkParameters.lean:11](../EndOfPaper/NetworkParameters.lean#L11) |
| `ScalarMonotone.EndOfPaper.NetworkParameters` | [EndOfPaper/NetworkParameters.lean:14](../EndOfPaper/NetworkParameters.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkData` | [EndOfPaper/NetworkParameters.lean:16](../EndOfPaper/NetworkParameters.lean#L16) |
| `ScalarMonotone.EndOfPaper.networkWeight` | [EndOfPaper/NetworkParameters.lean:20](../EndOfPaper/NetworkParameters.lean#L20) |
| `ScalarMonotone.EndOfPaper.network_parameter_norm_sq` | [EndOfPaper/NetworkParameters.lean:24](../EndOfPaper/NetworkParameters.lean#L24) |
| `ScalarMonotone.EndOfPaper.network_data_sub` | [EndOfPaper/NetworkParameters.lean:29](../EndOfPaper/NetworkParameters.lean#L29) |
| `ScalarMonotone.EndOfPaper.network_weight_sub` | [EndOfPaper/NetworkParameters.lean:32](../EndOfPaper/NetworkParameters.lean#L32) |
| `ScalarMonotone.EndOfPaper.network_data_norm_le` | [EndOfPaper/NetworkParameters.lean:35](../EndOfPaper/NetworkParameters.lean#L35) |
| `ScalarMonotone.EndOfPaper.network_weight_norm_le` | [EndOfPaper/NetworkParameters.lean:41](../EndOfPaper/NetworkParameters.lean#L41) |
| `ScalarMonotone.EndOfPaper.network_data_lipschitz` | [EndOfPaper/NetworkParameters.lean:49](../EndOfPaper/NetworkParameters.lean#L49) |
| `ScalarMonotone.EndOfPaper.network_weight_lipschitz` | [EndOfPaper/NetworkParameters.lean:55](../EndOfPaper/NetworkParameters.lean#L55) |
| `ScalarMonotone.EndOfPaper.networkWeightsAt` | [EndOfPaper/NetworkParameters.lean:61](../EndOfPaper/NetworkParameters.lean#L61) |
| `ScalarMonotone.EndOfPaper.networkMap` | [EndOfPaper/NetworkParameters.lean:65](../EndOfPaper/NetworkParameters.lean#L65) |
<a id="claim-36"></a>

## Equation (3.21)

[PDF page 55](../manuscript/monotone_calculus.pdf#page=55). Two-point network modulus with the stated dimension factor

Exactly the original positive finite dimensions and one-Lipschitz activations vanishing at zero, with arbitrary two actual parameter points in the Euclidean HS product. Controls may vanish; no strict positivity of controls is added. network_two_point_bound proves the actual HS output difference bound with D=(sqrt(p_L))^(-1)*sqrt(1+N*p_0*sum_l 1/(p_(l+1)+p_l)), Euclidean parameter distance, and the literal product of maxima of the two displayed normalized controls. The independent reader expands D and every control. Prove the actual row/column matrix norm estimates and activation contractions, then a zero-safe prefix induction using R<=sqrt(N*p_0)*B_l. Apply finite Cauchy--Schwarz and the exact product squared-norm identity. No division by a control and no assumed two-point modulus is used. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hsMatrixActivation` | [EndOfPaper/HSMatrixActivation.lean:12](../EndOfPaper/HSMatrixActivation.lean#L12) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_zero` | [EndOfPaper/HSMatrixActivation.lean:15](../EndOfPaper/HSMatrixActivation.lean#L15) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_contraction` | [EndOfPaper/HSMatrixActivation.lean:20](../EndOfPaper/HSMatrixActivation.lean#L20) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_lipschitz` | [EndOfPaper/HSMatrixActivation.lean:33](../EndOfPaper/HSMatrixActivation.lean#L33) |
| `ScalarMonotone.EndOfPaper.hs_matrix_activation_norm_le` | [EndOfPaper/HSMatrixActivation.lean:39](../EndOfPaper/HSMatrixActivation.lean#L39) |
| `ScalarMonotone.EndOfPaper.HSMatrix` | [EndOfPaper/HSMatrixBasic.lean:13](../EndOfPaper/HSMatrixBasic.lean#L13) |
| `ScalarMonotone.EndOfPaper.hsMatrixToMatrix` | [EndOfPaper/HSMatrixBasic.lean:15](../EndOfPaper/HSMatrixBasic.lean#L15) |
| `ScalarMonotone.EndOfPaper.hsMatrixOfMatrix` | [EndOfPaper/HSMatrixBasic.lean:18](../EndOfPaper/HSMatrixBasic.lean#L18) |
| `ScalarMonotone.EndOfPaper.hs_matrix_to_of` | [EndOfPaper/HSMatrixBasic.lean:21](../EndOfPaper/HSMatrixBasic.lean#L21) |
| `ScalarMonotone.EndOfPaper.hs_matrix_of_to` | [EndOfPaper/HSMatrixBasic.lean:24](../EndOfPaper/HSMatrixBasic.lean#L24) |
| `ScalarMonotone.EndOfPaper.hs_matrix_norm_sq` | [EndOfPaper/HSMatrixBasic.lean:29](../EndOfPaper/HSMatrixBasic.lean#L29) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_difference` | [EndOfPaper/HSMatrixDifference.lean:11](../EndOfPaper/HSMatrixDifference.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_difference_norm_le` | [EndOfPaper/HSMatrixDifference.lean:23](../EndOfPaper/HSMatrixDifference.lean#L23) |
| `ScalarMonotone.EndOfPaper.hsMatrixOp` | [EndOfPaper/HSMatrixOperator.lean:11](../EndOfPaper/HSMatrixOperator.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_apply` | [EndOfPaper/HSMatrixOperator.lean:16](../EndOfPaper/HSMatrixOperator.lean#L16) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_norm_le` | [EndOfPaper/HSMatrixOperator.lean:20](../EndOfPaper/HSMatrixOperator.lean#L20) |
| `ScalarMonotone.EndOfPaper.hsMatrixMul` | [EndOfPaper/HSMatrixOperator.lean:42](../EndOfPaper/HSMatrixOperator.lean#L42) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_apply` | [EndOfPaper/HSMatrixOperator.lean:45](../EndOfPaper/HSMatrixOperator.lean#L45) |
| `ScalarMonotone.EndOfPaper.hsMatrixColumn` | [EndOfPaper/HSMatrixProduct.lean:11](../EndOfPaper/HSMatrixProduct.lean#L11) |
| `ScalarMonotone.EndOfPaper.hs_matrix_norm_sq_columns` | [EndOfPaper/HSMatrixProduct.lean:14](../EndOfPaper/HSMatrixProduct.lean#L14) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_column` | [EndOfPaper/HSMatrixProduct.lean:21](../EndOfPaper/HSMatrixProduct.lean#L21) |
| `ScalarMonotone.EndOfPaper.hs_matrix_mul_norm_le` | [EndOfPaper/HSMatrixProduct.lean:27](../EndOfPaper/HSMatrixProduct.lean#L27) |
| `ScalarMonotone.EndOfPaper.hs_matrix_op_sub` | [EndOfPaper/HSMatrixProduct.lean:45](../EndOfPaper/HSMatrixProduct.lean#L45) |
| `ScalarMonotone.EndOfPaper.hs_matrix_operator_norm_lipschitz` | [EndOfPaper/HSMatrixProduct.lean:55](../EndOfPaper/HSMatrixProduct.lean#L55) |
| `ScalarMonotone.EndOfPaper.network_control_continuous` | [EndOfPaper/NetworkContinuity.lean:12](../EndOfPaper/NetworkContinuity.lean#L12) |
| `ScalarMonotone.EndOfPaper.finite_network_continuous` | [EndOfPaper/NetworkContinuity.lean:17](../EndOfPaper/NetworkContinuity.lean#L17) |
| `ScalarMonotone.EndOfPaper.finite_network_borel_measurable` | [EndOfPaper/NetworkContinuity.lean:35](../EndOfPaper/NetworkContinuity.lean#L35) |
| `ScalarMonotone.EndOfPaper.networkControl` | [EndOfPaper/NetworkControls.lean:10](../EndOfPaper/NetworkControls.lean#L10) |
| `ScalarMonotone.EndOfPaper.network_control_nonnegative` | [EndOfPaper/NetworkControls.lean:14](../EndOfPaper/NetworkControls.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkActivationsAt` | [EndOfPaper/NetworkControls.lean:18](../EndOfPaper/NetworkControls.lean#L18) |
| `ScalarMonotone.EndOfPaper.network_activations_lipschitz` | [EndOfPaper/NetworkControls.lean:21](../EndOfPaper/NetworkControls.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_activations_zero` | [EndOfPaper/NetworkControls.lean:28](../EndOfPaper/NetworkControls.lean#L28) |
| `ScalarMonotone.EndOfPaper.finiteNetworkMap` | [EndOfPaper/NetworkControls.lean:35](../EndOfPaper/NetworkControls.lean#L35) |
| `ScalarMonotone.EndOfPaper.networkLayer` | [EndOfPaper/NetworkLayers.lean:12](../EndOfPaper/NetworkLayers.lean#L12) |
| `ScalarMonotone.EndOfPaper.networkOutput` | [EndOfPaper/NetworkLayers.lean:20](../EndOfPaper/NetworkLayers.lean#L20) |
| `ScalarMonotone.EndOfPaper.network_layer_norm_step` | [EndOfPaper/NetworkLayers.lean:26](../EndOfPaper/NetworkLayers.lean#L26) |
| `ScalarMonotone.EndOfPaper.network_layer_difference_step` | [EndOfPaper/NetworkLayers.lean:40](../EndOfPaper/NetworkLayers.lean#L40) |
| `ScalarMonotone.EndOfPaper.networkTwoPointControl` | [EndOfPaper/NetworkMajorants.lean:10](../EndOfPaper/NetworkMajorants.lean#L10) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_nonnegative` | [EndOfPaper/NetworkMajorants.lean:14](../EndOfPaper/NetworkMajorants.lean#L14) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_symmetric` | [EndOfPaper/NetworkMajorants.lean:21](../EndOfPaper/NetworkMajorants.lean#L21) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_input` | [EndOfPaper/NetworkMajorants.lean:29](../EndOfPaper/NetworkMajorants.lean#L29) |
| `ScalarMonotone.EndOfPaper.network_two_point_control_operator` | [EndOfPaper/NetworkMajorants.lean:52](../EndOfPaper/NetworkMajorants.lean#L52) |
| `ScalarMonotone.EndOfPaper.NetworkCoordinate` | [EndOfPaper/NetworkParameters.lean:11](../EndOfPaper/NetworkParameters.lean#L11) |
| `ScalarMonotone.EndOfPaper.NetworkParameters` | [EndOfPaper/NetworkParameters.lean:14](../EndOfPaper/NetworkParameters.lean#L14) |
| `ScalarMonotone.EndOfPaper.networkData` | [EndOfPaper/NetworkParameters.lean:16](../EndOfPaper/NetworkParameters.lean#L16) |
| `ScalarMonotone.EndOfPaper.networkWeight` | [EndOfPaper/NetworkParameters.lean:20](../EndOfPaper/NetworkParameters.lean#L20) |
| `ScalarMonotone.EndOfPaper.network_parameter_norm_sq` | [EndOfPaper/NetworkParameters.lean:24](../EndOfPaper/NetworkParameters.lean#L24) |
| `ScalarMonotone.EndOfPaper.network_data_sub` | [EndOfPaper/NetworkParameters.lean:29](../EndOfPaper/NetworkParameters.lean#L29) |
| `ScalarMonotone.EndOfPaper.network_weight_sub` | [EndOfPaper/NetworkParameters.lean:32](../EndOfPaper/NetworkParameters.lean#L32) |
| `ScalarMonotone.EndOfPaper.network_data_norm_le` | [EndOfPaper/NetworkParameters.lean:35](../EndOfPaper/NetworkParameters.lean#L35) |
| `ScalarMonotone.EndOfPaper.network_weight_norm_le` | [EndOfPaper/NetworkParameters.lean:41](../EndOfPaper/NetworkParameters.lean#L41) |
| `ScalarMonotone.EndOfPaper.network_data_lipschitz` | [EndOfPaper/NetworkParameters.lean:49](../EndOfPaper/NetworkParameters.lean#L49) |
| `ScalarMonotone.EndOfPaper.network_weight_lipschitz` | [EndOfPaper/NetworkParameters.lean:55](../EndOfPaper/NetworkParameters.lean#L55) |
| `ScalarMonotone.EndOfPaper.networkWeightsAt` | [EndOfPaper/NetworkParameters.lean:61](../EndOfPaper/NetworkParameters.lean#L61) |
| `ScalarMonotone.EndOfPaper.networkMap` | [EndOfPaper/NetworkParameters.lean:65](../EndOfPaper/NetworkParameters.lean#L65) |
| `ScalarMonotone.EndOfPaper.network_prefix_error_from_majorants` | [EndOfPaper/NetworkPrefixBounds.lean:12](../EndOfPaper/NetworkPrefixBounds.lean#L12) |
| `ScalarMonotone.EndOfPaper.network_product_error_prefix` | [EndOfPaper/NetworkProductRecursion.lean:11](../EndOfPaper/NetworkProductRecursion.lean#L11) |
| `ScalarMonotone.EndOfPaper.network_exact_cauchy_factor` | [EndOfPaper/NetworkProductRecursion.lean:30](../EndOfPaper/NetworkProductRecursion.lean#L30) |
| `ScalarMonotone.EndOfPaper.networkPrefactor` | [EndOfPaper/NetworkTwoPoint.lean:12](../EndOfPaper/NetworkTwoPoint.lean#L12) |
| `ScalarMonotone.EndOfPaper.network_two_point_bound` | [EndOfPaper/NetworkTwoPoint.lean:16](../EndOfPaper/NetworkTwoPoint.lean#L16) |
<a id="claim-37"></a>

## After Proposition 1.7

[PDF page 10](../manuscript/monotone_calculus.pdf#page=10). The maximal zero-ray operator has a nonmonotone self-composition

The exact maximal normal-halfline graph takes (-∞,0] at zero, {0} for positive inputs and empty values for negative inputs. Its self-composition has the stated halfline fibers and is neither increasing nor decreasing. Thus the rectangle qualification cannot be dropped. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.normalHalfline_maximal` | [MonotoneOperators/Examples.lean:23](../MonotoneOperators/Examples.lean#L23) |
| `ScalarMonotone.normalHalfline_self_comp` | [MonotoneOperators/Examples.lean:40](../MonotoneOperators/Examples.lean#L40) |
| `ScalarMonotone.normalHalfline_self_comp_not_increasing` | [MonotoneOperators/Examples.lean:50](../MonotoneOperators/Examples.lean#L50) |
| `ScalarMonotone.normalHalfline_self_comp_not_decreasing` | [MonotoneOperators/Examples.lean:58](../MonotoneOperators/Examples.lean#L58) |
<a id="claim-38"></a>

## After Definition 1.11

[PDF page 12](../manuscript/monotone_calculus.pdf#page=12). Opposite resolvent-order conventions on vertical graphs

Vertical graphs at a,b compare by b≤a in the increasing class and a≤b in the decreasing class. The quantified no_orientation_independent_order theorem proves that a single relation cannot satisfy both conventions on their union. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.incLE_vertical_iff` | [MonotoneOperators/OrderGeometry.lean:121](../MonotoneOperators/OrderGeometry.lean#L121) |
| `ScalarMonotone.decLE_vertical_iff` | [MonotoneOperators/OrderGeometry.lean:135](../MonotoneOperators/OrderGeometry.lean#L135) |
| `ScalarMonotone.no_orientation_independent_order` | [MonotoneOperators/OrderGeometry.lean:170](../MonotoneOperators/OrderGeometry.lean#L170) |
<a id="claim-39"></a>

## After Definition 1.14

[PDF page 14](../manuscript/monotone_calculus.pdf#page=14). Partial order and endpoint-sensitive interval examples

The closed bounded endpoint iff retains a≤b and c≤d. Exact half-open examples prove [0,1)≤(0,1] and both noncomparisons between (0,1) and [0,1], so endpoint inclusion is not silently discarded. The Egli--Milner terminology is attribution; the equivalent hull predicate and its order laws are explicitly defined and proved. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.intervalLE_Icc_iff` | [MonotoneOperators/IntervalExtrema.lean:204](../MonotoneOperators/IntervalExtrema.lean#L204) |
| `ScalarMonotone.intervalLE_Ico_Ioc` | [MonotoneOperators/IntervalExtrema.lean:218](../MonotoneOperators/IntervalExtrema.lean#L218) |
| `ScalarMonotone.interval_Ioo_Icc_incomparable` | [MonotoneOperators/IntervalExtrema.lean:225](../MonotoneOperators/IntervalExtrema.lean#L225) |
<a id="claim-40"></a>

## After Lemma 1.13

[PDF page 14](../manuscript/monotone_calculus.pdf#page=14). Resolvent order agrees with ordinary pointwise comparison for continuous full-domain monotone scalar functions

For continuous globally monotone scalar functions, the appropriate resolvent order of singleton graphs is equivalent to pointwise scalar comparison. Both orientations are stated, on all of ℝ, exactly as this assertion. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.continuous_monotone_comparison` | [MonotoneOperators/OrderConsequences.lean:76](../MonotoneOperators/OrderConsequences.lean#L76) |
| `ScalarMonotone.continuous_antitone_comparison` | [MonotoneOperators/OrderConsequences.lean:81](../MonotoneOperators/OrderConsequences.lean#L81) |
<a id="claim-41"></a>

## After Lemma 1.8

[PDF page 10](../manuscript/monotone_calculus.pdf#page=10). The logarithm of the identically zero maximal graph is empty and not maximal

The global constant zero graph, which is maximal in the decreasing orientation. The actual logarithmic operator is empty at every input and cannot be maximal decreasing, proving the positive-range exception is necessary. Strict positivity of exponential makes every logarithmic fiber empty; the positive-witness characterization of maximality excludes the empty graph. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.logarithm_of_zero_graph_empty` | [EndOfPaper/LogZeroCounterexample.lean:13](../EndOfPaper/LogZeroCounterexample.lean#L13) |
| `ScalarMonotone.EndOfPaper.logarithm_of_zero_graph_not_maximal` | [EndOfPaper/LogZeroCounterexample.lean:19](../EndOfPaper/LogZeroCounterexample.lean#L19) |
| `ScalarMonotone.EndOfPaper.logarithmic_zero_exception` | [EndOfPaper/LogZeroCounterexample.lean:29](../EndOfPaper/LogZeroCounterexample.lean#L29) |
<a id="claim-42"></a>

## After Proposition 1.36

[PDF page 32](../manuscript/monotone_calculus.pdf#page=32). Hardy averaging is the completed Aumann integral of restricted dilations

The paper maximal decreasing graph, integrability of a scalar selection, and zero lower domain endpoint with a positive domain point. IsGLB(dom f,0) expresses the actual greatest lower bound; existence of a positive domain point expresses positivity of the possibly infinite supremum. No finite upper endpoint, common-domain geometry or integrability of endpoint maps is assumed. The actual completed Aumann integral of restricted positive dilations is well defined and maximal decreasing. Its domain interior equals the original interior, its domain lies in that closure, and every interior fiber is the singleton (integral from 0 to p of s)/p. The full completed graph is unique, including every boundary fiber. It is independent of the integrable selection because the operator definition contains only I and f. Derive a nonempty positive initial interval from the domain greatest lower bound and maximality. Prove positive dilations and their completed restrictions maximal with the exact common interior. Affine substitution and ae selection equality prove both endpoint maps integrable and give the same scalar area. The full FamilyIntegral theorems then preserve those singleton fibers and prove whole-graph uniqueness. hardyFamilyIntegral is defined by decreasingFamilyIntegral of the actual completed dilations, not by the desired scalar formula. hardyFamilyIntegral_eq_actual_dilations proves equality of the entire completed integral with the literal r-dilation family. The harmless parameter extension outside (0,1) is eliminated by a proved ae family-congruence theorem. Integrability on the domain implies integrability on its interior. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.positiveInputDilation` | [EndOfPaper/HardyIntegral.lean:18](../EndOfPaper/HardyIntegral.lean#L18) |
| `ScalarMonotone.EndOfPaper.positiveInputDilation_maximal` | [EndOfPaper/HardyIntegral.lean:20](../EndOfPaper/HardyIntegral.lean#L20) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction` | [EndOfPaper/HardyIntegral.lean:47](../EndOfPaper/HardyIntegral.lean#L47) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_value` | [EndOfPaper/HardyIntegral.lean:50](../EndOfPaper/HardyIntegral.lean#L50) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_maximal` | [EndOfPaper/HardyIntegral.lean:61](../EndOfPaper/HardyIntegral.lean#L61) |
| `ScalarMonotone.EndOfPaper.completedDecreasingRestriction_domain` | [EndOfPaper/HardyIntegral.lean:70](../EndOfPaper/HardyIntegral.lean#L70) |
| `ScalarMonotone.EndOfPaper.hardyParameter` | [EndOfPaper/HardyIntegral.lean:87](../EndOfPaper/HardyIntegral.lean#L87) |
| `ScalarMonotone.EndOfPaper.hardyParameter_bounds` | [EndOfPaper/HardyIntegral.lean:89](../EndOfPaper/HardyIntegral.lean#L89) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily` | [EndOfPaper/HardyIntegral.lean:95](../EndOfPaper/HardyIntegral.lean#L95) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily_properties` | [EndOfPaper/HardyIntegral.lean:98](../EndOfPaper/HardyIntegral.lean#L98) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral` | [EndOfPaper/HardyIntegral.lean:116](../EndOfPaper/HardyIntegral.lean#L116) |
| `ScalarMonotone.EndOfPaper.decreasingFamilyIntegral_congr_ae` | [EndOfPaper/HardyIntegral.lean:121](../EndOfPaper/HardyIntegral.lean#L121) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_eq_actual_dilations` | [EndOfPaper/HardyIntegral.lean:135](../EndOfPaper/HardyIntegral.lean#L135) |
| `ScalarMonotone.EndOfPaper.decreasing_zero_inf_domain_geometry` | [EndOfPaper/HardyIntegral.lean:144](../EndOfPaper/HardyIntegral.lean#L144) |
| `ScalarMonotone.EndOfPaper.hardyDilationFamily_endpoint_areas` | [EndOfPaper/HardyIntegral.lean:179](../EndOfPaper/HardyIntegral.lean#L179) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_well_defined` | [EndOfPaper/HardyIntegral.lean:205](../EndOfPaper/HardyIntegral.lean#L205) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_of_integrable` | [EndOfPaper/HardyIntegral.lean:248](../EndOfPaper/HardyIntegral.lean#L248) |
<a id="claim-43"></a>

## After Definition 2.1

[PDF page 32](../manuscript/monotone_calculus.pdf#page=32). Compatible Hardy transforms of integrable restrictions define the locally integrable extension

Maximal decreasing f with zero greatest lower domain bound and a positive domain point, an interior selection, and integrability on every prefix (0,p). No global integrability or finite upper endpoint is required. The comparison version permits different initial intervals, while addition uses the common interior. The local construction is the same unique maximal completed Hardy operator, with exact domain interior, closure containment, and singleton prefix-average values. Existing restriction compatibility and explicit b1/b2 independence identify it with the paper construction by integrable restrictions. All order, addition, positive scaling, convexity and concavity properties hold for this entire operator under only local L1. Reuse the actual family-integral constructor with prefix integrability directly. Derive geometry from the original domain and extend separated interior comparisons to every boundary fiber. Whole-graph uniqueness proves algebraic equality. For shape preservation, integrability of the convex/concave selection on each prefix follows from ae equality with the supplied local selection; it is not an extra assumption. IntervalIntegrable s volume 0 p is exactly L1 on (0,p) for p>0, by the pinned interval-integrability equivalence. The graph integral definition contains no selection or truncation choice. All mathematical equalities and order conclusions concern completed operators. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_well_defined` | [EndOfPaper/HardyIntegral.lean:205](../EndOfPaper/HardyIntegral.lean#L205) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_restriction_compatible` | [EndOfPaper/HardyIntegral.lean:362](../EndOfPaper/HardyIntegral.lean#L362) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_local_independence` | [EndOfPaper/HardyIntegral.lean:400](../EndOfPaper/HardyIntegral.lean#L400) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_of_locally_integrable` | [EndOfPaper/LocalHardy.lean:15](../EndOfPaper/LocalHardy.lean#L15) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_mono_locally_integrable` | [EndOfPaper/LocalHardy.lean:31](../EndOfPaper/LocalHardy.lean#L31) |
| `ScalarMonotone.EndOfPaper.le_hardyFamilyIntegral_locally_integrable` | [EndOfPaper/LocalHardy.lean:71](../EndOfPaper/LocalHardy.lean#L71) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_add_locally_integrable` | [EndOfPaper/LocalHardy.lean:95](../EndOfPaper/LocalHardy.lean#L95) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_outputScale_locally_integrable` | [EndOfPaper/LocalHardy.lean:154](../EndOfPaper/LocalHardy.lean#L154) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_calculus_locally_integrable` | [EndOfPaper/LocalHardy.lean:181](../EndOfPaper/LocalHardy.lean#L181) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_preserves_convexity_locally_integrable` | [EndOfPaper/LocalHardy.lean:204](../EndOfPaper/LocalHardy.lean#L204) |
| `ScalarMonotone.EndOfPaper.hardyFamilyIntegral_preserves_concavity_locally_integrable` | [EndOfPaper/LocalHardy.lean:232](../EndOfPaper/LocalHardy.lean#L232) |
<a id="claim-44"></a>

## After Proposition 2.6

[PDF page 37](../manuscript/monotone_calculus.pdf#page=37). Continuous monotone aggregation of interval endpoints defines a maximal decreasing operator

The standing continuous coordinatewise monotone homogeneous nonnegative F, finitely many maximal decreasing graphs nonnegative on a nonempty open common interval I, and coverage of I by every graph. The individual domains may differ; only their chosen common interior is used. No finite endpoint of I is assumed. The literal interval with endpoints F of the input infima and suprema survives completion at every interior argument, including all jumps. The completed graph is maximal decreasing, its domain interior is exactly I and its domain is contained in its closure. It is the unique entire maximal graph with those fibers and closure containment. Applying F to any scalar selections yields a selection of this actual completed operator. Prove a reusable completion theorem for ordered interval endpoints with the correct one-sided limits. Derive both decreasing selection limits from maximal graph closedness. Continuity of F on the nonnegative cone transfers the vector endpoint limits, while monotonicity orders the intervals. Maximal completion and restriction uniqueness determine all boundary fibers. No scalar-only identification is used. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.intervalGraphOn` | [EndOfPaper/AggregationOperator.lean:15](../EndOfPaper/AggregationOperator.lean#L15) |
| `ScalarMonotone.EndOfPaper.intervalCompletionI` | [EndOfPaper/AggregationOperator.lean:19](../EndOfPaper/AggregationOperator.lean#L19) |
| `ScalarMonotone.EndOfPaper.intervalCompletionI_properties` | [EndOfPaper/AggregationOperator.lean:21](../EndOfPaper/AggregationOperator.lean#L21) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_tendsto_left` | [EndOfPaper/AggregationOperator.lean:91](../EndOfPaper/AggregationOperator.lean#L91) |
| `ScalarMonotone.EndOfPaper.decreasing_selection_tendsto_right` | [EndOfPaper/AggregationOperator.lean:104](../EndOfPaper/AggregationOperator.lean#L104) |
| `ScalarMonotone.EndOfPaper.aggregationOperator` | [EndOfPaper/AggregationOperator.lean:117](../EndOfPaper/AggregationOperator.lean#L117) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_properties` | [EndOfPaper/AggregationOperator.lean:122](../EndOfPaper/AggregationOperator.lean#L122) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_unique` | [EndOfPaper/AggregationOperator.lean:188](../EndOfPaper/AggregationOperator.lean#L188) |
| `ScalarMonotone.EndOfPaper.decreasing_interior_value_bounds` | [EndOfPaper/AggregationOperator.lean:211](../EndOfPaper/AggregationOperator.lean#L211) |
| `ScalarMonotone.EndOfPaper.aggregationOperator_selection` | [EndOfPaper/AggregationOperator.lean:224](../EndOfPaper/AggregationOperator.lean#L224) |
<a id="claim-45"></a>

## In Example 2.5

[PDF page 36](../manuscript/monotone_calculus.pdf#page=36). For 0<q<=1 the nonnegative l^q quasi-norm is superadditive and equals its sharp transform

Every real 0<q<=1 and arbitrary finite dimension, including zero, on the full nonnegative cone with zero coordinates permitted. The actual sum-of-powers quasi-norm is superadditive and its finite-decomposition sharp transform equals itself. This separately inventoried duplicate of the example's quasi-norm clause is now mapped to the same checked proofs and literal expected types. Normalize nonzero vectors by their actual quasi-norms and sum the coordinatewise concavity inequalities with weights proportional to those quasi-norms. Derive reverse Minkowski by raising to the positive reciprocal exponent. Handle zero quasi-norms by proving their vectors are zero, then apply the checked fixed-point theorem for already-superadditive aggregations. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm` | [EndOfPaper/QuasiNormTransform.lean:16](../EndOfPaper/QuasiNormTransform.lean#L16) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_aggregation_axioms` | [EndOfPaper/QuasiNormTransform.lean:53](../EndOfPaper/QuasiNormTransform.lean#L53) |
| `ScalarMonotone.EndOfPaper.coordinateQuasiNorm_superadditive` | [EndOfPaper/QuasiNormTransform.lean:69](../EndOfPaper/QuasiNormTransform.lean#L69) |
| `ScalarMonotone.EndOfPaper.quasi_norm_superadditive_transform` | [EndOfPaper/QuasiNormTransform.lean:114](../EndOfPaper/QuasiNormTransform.lean#L114) |
<a id="claim-46"></a>

## After Proposition 2.14

[PDF page 46](../manuscript/monotone_calculus.pdf#page=46). Exponentiating the completed zero profile gives a nonclosed value (0,1] at 1

The actual maximal decreasing completion of the zero profile on (0,1), realized by the quantile of the point mass at zero. Its raw exponential image at one is exactly (0,1], and the entire composed graph is not maximal decreasing. Domain interior and every interior zero value are checked. Compute both actual point-mass quantile endpoint rays, exponentiate the lower ray, and use closure at zero to contradict closed maximal fibers. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.dirac_quantile_zero_fiber` | [EndOfPaper/ExponentialBoundaryCounterexample.lean:13](../EndOfPaper/ExponentialBoundaryCounterexample.lean#L13) |
| `ScalarMonotone.EndOfPaper.dirac_quantile_one_fiber` | [EndOfPaper/ExponentialBoundaryCounterexample.lean:22](../EndOfPaper/ExponentialBoundaryCounterexample.lean#L22) |
| `ScalarMonotone.EndOfPaper.exponential_zero_quantile_one` | [EndOfPaper/ExponentialBoundaryCounterexample.lean:31](../EndOfPaper/ExponentialBoundaryCounterexample.lean#L31) |
| `ScalarMonotone.EndOfPaper.exponential_zero_quantile_not_maximal` | [EndOfPaper/ExponentialBoundaryCounterexample.lean:43](../EndOfPaper/ExponentialBoundaryCounterexample.lean#L43) |
| `ScalarMonotone.EndOfPaper.geometric_exponential_boundary_counterexample` | [EndOfPaper/ExponentialBoundaryCounterexample.lean:54](../EndOfPaper/ExponentialBoundaryCounterexample.lean#L54) |
<a id="claim-47"></a>

## After Proposition 3.7

[PDF page 51](../manuscript/monotone_calculus.pdf#page=51). The universal lower coefficient 2^(-1/r) is optimal for r>=1

Exactly the original admissible scalar maps for the prescribed unit profiles, on arbitrary original probability and metric spaces, with measurable maps and nonnegative measurable controls, independent identical copies, the original whole marginal and baseline quantile constraints, n>=1 and r>=1. The completed unit profile is the actual quantile graph of delta_1. No boundedness, output integrability, essential-range diameter, or copy-distance bound is assumed. unit_profile_moment_optimality proves the universal one-half moment upper bound and exact 2^(-1/r) norm upper bound and supplies an actual admissible Bernoulli attainer. unit_profile_no_larger_coefficient excludes every larger proposed coefficient for all original admissible models with these prescribed profiles. The input product norm is exactly one, and the actual Bernoulli model has every original constraint and exact moment/norm equality; its logarithmic area is zero. copy_moment_cdf_unit_interval proves the manuscript identity E|V-Vprime|=2*integral_0^1 F(t)*(1-F(t))dt after translation, with atoms allowed. Optimality is asserted only for r>=1; Bernoulli equalities themselves also hold for every r>0. Derive control bounds AE directly from the actual quantile constraints, construct the genuine McShane extension on their common full-measure set, and use the baseline constraint to prove the copy-distance bound. Transfer the actual independent joint law and use a countable rational-null-neighborhood argument to derive an essential interval of length one. Translate that derived interval to [0,1]; prove the sharp moment estimate from the pointwise polynomial bound and independence, deriving all L1 before integration. Independently prove the exact CDF identity by measurable half-open crossing indicators and nonnegative Tonelli, then restrict to the unit interval and derive ordinary integrability, retaining atoms. Compute the actual Bernoulli product law explicitly and verify its whole baseline and marginal profile bounds, modulus, finite log area and exact norms. The independent reader uses the literal delta_1 quantile graph rather than assuming a scalar-only profile correspondence. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.law_copy_moment_le_half_of_gap` | [EndOfPaper/BoundedCopyMoment.lean:14](../EndOfPaper/BoundedCopyMoment.lean#L14) |
| `ScalarMonotone.EndOfPaper.independent_copy_moment_le_half_of_gap` | [EndOfPaper/BoundedCopyMoment.lean:41](../EndOfPaper/BoundedCopyMoment.lean#L41) |
| `ScalarMonotone.EndOfPaper.copyCrossingIndicator` | [EndOfPaper/CopyCdfIntegral.lean:15](../EndOfPaper/CopyCdfIntegral.lean#L15) |
| `ScalarMonotone.EndOfPaper.copyCrossingIndicator_measurable` | [EndOfPaper/CopyCdfIntegral.lean:18](../EndOfPaper/CopyCdfIntegral.lean#L18) |
| `ScalarMonotone.EndOfPaper.copyCrossingIndicator_integral` | [EndOfPaper/CopyCdfIntegral.lean:28](../EndOfPaper/CopyCdfIntegral.lean#L28) |
| `ScalarMonotone.EndOfPaper.copyCrossingIndicator_pair_integral` | [EndOfPaper/CopyCdfIntegral.lean:42](../EndOfPaper/CopyCdfIntegral.lean#L42) |
| `ScalarMonotone.EndOfPaper.copy_moment_cdf_extended` | [EndOfPaper/CopyCdfIntegral.lean:58](../EndOfPaper/CopyCdfIntegral.lean#L58) |
| `ScalarMonotone.EndOfPaper.nullRationalNeighborhoods` | [EndOfPaper/EssentialDiameter.lean:15](../EndOfPaper/EssentialDiameter.lean#L15) |
| `ScalarMonotone.EndOfPaper.nullRationalNeighborhoods_null` | [EndOfPaper/EssentialDiameter.lean:19](../EndOfPaper/EssentialDiameter.lean#L19) |
| `ScalarMonotone.EndOfPaper.nullRationalNeighborhoods_measurable` | [EndOfPaper/EssentialDiameter.lean:28](../EndOfPaper/EssentialDiameter.lean#L28) |
| `ScalarMonotone.EndOfPaper.positive_neighborhood_of_outside_null` | [EndOfPaper/EssentialDiameter.lean:37](../EndOfPaper/EssentialDiameter.lean#L37) |
| `ScalarMonotone.EndOfPaper.copy_gap_support_sub_le_one` | [EndOfPaper/EssentialDiameter.lean:55](../EndOfPaper/EssentialDiameter.lean#L55) |
| `ScalarMonotone.EndOfPaper.law_essential_interval_of_copy_gap` | [EndOfPaper/EssentialDiameter.lean:78](../EndOfPaper/EssentialDiameter.lean#L78) |
| `ScalarMonotone.EndOfPaper.independent_copy_essential_interval` | [EndOfPaper/EssentialDiameter.lean:101](../EndOfPaper/EssentialDiameter.lean#L101) |
| `ScalarMonotone.EndOfPaper.cdf_complement_tail_real` | [EndOfPaper/UnitIntervalCdf.lean:13](../EndOfPaper/UnitIntervalCdf.lean#L13) |
| `ScalarMonotone.EndOfPaper.cdf_crossing_integrand` | [EndOfPaper/UnitIntervalCdf.lean:19](../EndOfPaper/UnitIntervalCdf.lean#L19) |
| `ScalarMonotone.EndOfPaper.copy_moment_cdf_ofReal` | [EndOfPaper/UnitIntervalCdf.lean:35](../EndOfPaper/UnitIntervalCdf.lean#L35) |
| `ScalarMonotone.EndOfPaper.cdf_unit_interval_outside` | [EndOfPaper/UnitIntervalCdf.lean:41](../EndOfPaper/UnitIntervalCdf.lean#L41) |
| `ScalarMonotone.EndOfPaper.cdf_unit_interval_integrable` | [EndOfPaper/UnitIntervalCdf.lean:69](../EndOfPaper/UnitIntervalCdf.lean#L69) |
| `ScalarMonotone.EndOfPaper.copy_moment_cdf_unit_interval` | [EndOfPaper/UnitIntervalCdf.lean:79](../EndOfPaper/UnitIntervalCdf.lean#L79) |
| `ScalarMonotone.EndOfPaper.unit_interval_copy_rpow_bound` | [EndOfPaper/UnitIntervalCopyMoment.lean:14](../EndOfPaper/UnitIntervalCopyMoment.lean#L14) |
| `ScalarMonotone.EndOfPaper.unit_interval_product_moment_le_half` | [EndOfPaper/UnitIntervalCopyMoment.lean:24](../EndOfPaper/UnitIntervalCopyMoment.lean#L24) |
| `ScalarMonotone.EndOfPaper.ae_le_constant_of_quantile_mem` | [EndOfPaper/UnitProfileAdmissibility.lean:14](../EndOfPaper/UnitProfileAdmissibility.lean#L14) |
| `ScalarMonotone.EndOfPaper.unit_profile_modulus_copy_bound` | [EndOfPaper/UnitProfileAdmissibility.lean:24](../EndOfPaper/UnitProfileAdmissibility.lean#L24) |
| `ScalarMonotone.EndOfPaper.unitQuantileProfile` | [EndOfPaper/UnitProfileBernoulli.lean:15](../EndOfPaper/UnitProfileBernoulli.lean#L15) |
| `ScalarMonotone.EndOfPaper.unitQuantileProfile_value` | [EndOfPaper/UnitProfileBernoulli.lean:17](../EndOfPaper/UnitProfileBernoulli.lean#L17) |
| `ScalarMonotone.EndOfPaper.unitQuantileProfile_domain` | [EndOfPaper/UnitProfileBernoulli.lean:20](../EndOfPaper/UnitProfileBernoulli.lean#L20) |
| `ScalarMonotone.EndOfPaper.unitQuantileProfile_one_mem` | [EndOfPaper/UnitProfileBernoulli.lean:23](../EndOfPaper/UnitProfileBernoulli.lean#L23) |
| `ScalarMonotone.EndOfPaper.symmetricBernoulli_ae_unit_interval` | [EndOfPaper/UnitProfileBernoulli.lean:28](../EndOfPaper/UnitProfileBernoulli.lean#L28) |
| `ScalarMonotone.EndOfPaper.symmetricBernoulli_copy_moment` | [EndOfPaper/UnitProfileBernoulli.lean:32](../EndOfPaper/UnitProfileBernoulli.lean#L32) |
| `ScalarMonotone.EndOfPaper.symmetricBernoulli_copy_norm` | [EndOfPaper/UnitProfileBernoulli.lean:47](../EndOfPaper/UnitProfileBernoulli.lean#L47) |
| `ScalarMonotone.EndOfPaper.bernoulli_unit_profile_baseline` | [EndOfPaper/UnitProfileBernoulli.lean:65](../EndOfPaper/UnitProfileBernoulli.lean#L65) |
| `ScalarMonotone.EndOfPaper.unit_profile_constant_control` | [EndOfPaper/UnitProfileBernoulli.lean:90](../EndOfPaper/UnitProfileBernoulli.lean#L90) |
| `ScalarMonotone.EndOfPaper.bernoulli_unit_profile_modulus` | [EndOfPaper/UnitProfileBernoulli.lean:99](../EndOfPaper/UnitProfileBernoulli.lean#L99) |
| `ScalarMonotone.EndOfPaper.unit_profile_log_area` | [EndOfPaper/UnitProfileBernoulli.lean:102](../EndOfPaper/UnitProfileBernoulli.lean#L102) |
| `ScalarMonotone.EndOfPaper.unit_profile_universal_moment_upper` | [EndOfPaper/UnitProfileMomentUpper.lean:13](../EndOfPaper/UnitProfileMomentUpper.lean#L13) |
| `ScalarMonotone.EndOfPaper.unit_profile_no_larger_coefficient` | [EndOfPaper/UnitProfileObstruction.lean:12](../EndOfPaper/UnitProfileObstruction.lean#L12) |
| `ScalarMonotone.EndOfPaper.unit_profile_product_norm_one` | [EndOfPaper/UnitProfileOptimality.lean:13](../EndOfPaper/UnitProfileOptimality.lean#L13) |
| `ScalarMonotone.EndOfPaper.unit_profile_moment_optimality` | [EndOfPaper/UnitProfileOptimality.lean:22](../EndOfPaper/UnitProfileOptimality.lean#L22) |
<a id="claim-48"></a>

## Introduction

[PDF page 4](../manuscript/monotone_calculus.pdf#page=4). Standard Gaussian input admits the uniform profile 2 sqrt(log(2/u))

Exactly an actual finite Euclidean standard Gaussian input, expressed by independent measurable standard Gaussian coordinates, on an arbitrary original probability space; a measurable independent identical copy; and every real one-Lipschitz observation. The finite coordinate index may be any Fintype, including the empty index. No concentration estimate, transport map, midpoint inequality, exponential integrability, absence of atoms, output L1, positive dimension or smoothness of the observation is assumed. gaussian_lipschitz_copy_weak_tail proves the literal weak tail P(|f(X)-f(Xprime)|>=t)<=2*exp(-t^2/4) for every t>=0. gaussian_input_profile proves the whole completed quantile comparison for every real one-Lipschitz f with the actual maximally decreasing affineSqrtLogProfile 0 2. Its domain interior is (0,1) and every interior fiber is exactly {2*sqrt(log(2/u))}; the independent reader checks both this literal scalar formula and the whole comparison, retaining atoms and endpoint fibers. Prove the actual scalar Gaussian square Laplace transform and derive all Lipschitz exponential integrability. Construct positive-density cumulative functions, their actual inverse transport, its derivative and full range, then prove the midpoint Lebesgue integral inequality by change of variables. Apply it to Gaussian-weighted exponentials. Prove exact Euclidean coordinate isometries, actual finite Gaussian product marginals and independence, and the genuine Fubini identity. Coordinate integration preserves the Lipschitz constant and quadratic midpoint bound, allowing finite-dimensional induction. Derive the copy exponential moment bound, transfer the actual joint Gaussian law to arbitrary original spaces, reindex arbitrary finite coordinates, and obtain both weak tails with the exact exponent through Chernoff. Finally use strict-tail tests to prove the entire completed quantile comparison. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.tailQuantile_decLE_of_profile_selection_tail_bounds` | [EndOfPaper/QuantileTailCompletion.lean:49](../EndOfPaper/QuantileTailCompletion.lean#L49) |
| `ScalarMonotone.EndOfPaper.affine_sqrt_log_profile_properties` | [EndOfPaper/SqrtLogProfile.lean:40](../EndOfPaper/SqrtLogProfile.lean#L40) |
| `ScalarMonotone.EndOfPaper.gaussianLogMarginal` | [EndOfPaper/GaussianCoordinateMarginal.lean:15](../EndOfPaper/GaussianCoordinateMarginal.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_coordinate_slice_lipschitz` | [EndOfPaper/GaussianCoordinateMarginal.lean:19](../EndOfPaper/GaussianCoordinateMarginal.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_log_marginal_lipschitz` | [EndOfPaper/GaussianCoordinateMarginal.lean:24](../EndOfPaper/GaussianCoordinateMarginal.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussian_log_marginal_midpoint_bound` | [EndOfPaper/GaussianCoordinateMarginal.lean:37](../EndOfPaper/GaussianCoordinateMarginal.lean#L37) |
| `ScalarMonotone.EndOfPaper.subgaussian_neg_mgf` | [EndOfPaper/GaussianCopyTail.lean:12](../EndOfPaper/GaussianCopyTail.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_weak_tail` | [EndOfPaper/GaussianCopyTail.lean:18](../EndOfPaper/GaussianCopyTail.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_subgaussian_fintype` | [EndOfPaper/GaussianFiniteIndex.lean:12](../EndOfPaper/GaussianFiniteIndex.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_tilt_lipschitz` | [EndOfPaper/GaussianFiniteMGF.lean:12](../EndOfPaper/GaussianFiniteMGF.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_tilt_pair_bound` | [EndOfPaper/GaussianFiniteMGF.lean:20](../EndOfPaper/GaussianFiniteMGF.lean#L20) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_lipschitz_copy_mgf` | [EndOfPaper/GaussianFiniteMGF.lean:31](../EndOfPaper/GaussianFiniteMGF.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_finite_midpoint_log_integral` | [EndOfPaper/GaussianFiniteMidpoint.lean:12](../EndOfPaper/GaussianFiniteMidpoint.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_profile_confidence_identity` | [EndOfPaper/GaussianInputProfile.lean:14](../EndOfPaper/GaussianInputProfile.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_input_profile` | [EndOfPaper/GaussianInputProfile.lean:27](../EndOfPaper/GaussianInputProfile.lean#L27) |
| `ScalarMonotone.EndOfPaper.lipschitz_general_exponential_majorant` | [EndOfPaper/GaussianLipschitzGeneral.lean:14](../EndOfPaper/GaussianLipschitzGeneral.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_real_exp_integrable_lipschitz` | [EndOfPaper/GaussianLipschitzGeneral.lean:26](../EndOfPaper/GaussianLipschitzGeneral.lean#L26) |
| `ScalarMonotone.EndOfPaper.gaussian_exp_integrable_lipschitz` | [EndOfPaper/GaussianLipschitzGeneral.lean:35](../EndOfPaper/GaussianLipschitzGeneral.lean#L35) |
| `ScalarMonotone.EndOfPaper.gaussianKernel` | [EndOfPaper/GaussianMidpoint.lean:13](../EndOfPaper/GaussianMidpoint.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_midpoint_energy` | [EndOfPaper/GaussianMidpoint.lean:16](../EndOfPaper/GaussianMidpoint.lean#L16) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_midpoint_domination` | [EndOfPaper/GaussianMidpoint.lean:25](../EndOfPaper/GaussianMidpoint.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_joint_law` | [EndOfPaper/GaussianOriginalLaw.lean:15](../EndOfPaper/GaussianOriginalLaw.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussian_vector_exp_integral` | [EndOfPaper/GaussianOriginalLaw.lean:23](../EndOfPaper/GaussianOriginalLaw.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_exp` | [EndOfPaper/GaussianOriginalLaw.lean:37](../EndOfPaper/GaussianOriginalLaw.lean#L37) |
| `ScalarMonotone.EndOfPaper.gaussian_lipschitz_copy_subgaussian` | [EndOfPaper/GaussianOriginalLaw.lean:69](../EndOfPaper/GaussianOriginalLaw.lean#L69) |
| `ScalarMonotone.EndOfPaper.gaussianSplitMeasurableEquiv` | [EndOfPaper/GaussianProductMarginal.lean:14](../EndOfPaper/GaussianProductMarginal.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_split_measure_preserving` | [EndOfPaper/GaussianProductMarginal.lean:18](../EndOfPaper/GaussianProductMarginal.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_split_vector` | [EndOfPaper/GaussianProductMarginal.lean:23](../EndOfPaper/GaussianProductMarginal.lean#L23) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral_marginal` | [EndOfPaper/GaussianProductMarginal.lean:30](../EndOfPaper/GaussianProductMarginal.lean#L30) |
| `ScalarMonotone.EndOfPaper.gaussianProductMeasure` | [EndOfPaper/GaussianProductMeasure.lean:14](../EndOfPaper/GaussianProductMeasure.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussianProductVector` | [EndOfPaper/GaussianProductMeasure.lean:16](../EndOfPaper/GaussianProductMeasure.lean#L16) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral` | [EndOfPaper/GaussianProductMeasure.lean:19](../EndOfPaper/GaussianProductMeasure.lean#L19) |
| `ScalarMonotone.EndOfPaper.gaussian_product_vector_measurable` | [EndOfPaper/GaussianProductMeasure.lean:22](../EndOfPaper/GaussianProductMeasure.lean#L22) |
| `ScalarMonotone.EndOfPaper.gaussian_product_coordinate_law` | [EndOfPaper/GaussianProductMeasure.lean:25](../EndOfPaper/GaussianProductMeasure.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_product_independent` | [EndOfPaper/GaussianProductMeasure.lean:50](../EndOfPaper/GaussianProductMeasure.lean#L50) |
| `ScalarMonotone.EndOfPaper.gaussian_product_exp_integrable` | [EndOfPaper/GaussianProductMeasure.lean:61](../EndOfPaper/GaussianProductMeasure.lean#L61) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral_positive` | [EndOfPaper/GaussianProductMeasure.lean:68](../EndOfPaper/GaussianProductMeasure.lean#L68) |
| `ScalarMonotone.EndOfPaper.gaussianExpIntegral_zero` | [EndOfPaper/GaussianProductMeasure.lean:73](../EndOfPaper/GaussianProductMeasure.lean#L73) |
| `ScalarMonotone.EndOfPaper.gaussian_real_pdf_scalar` | [EndOfPaper/GaussianRealMidpoint.lean:14](../EndOfPaper/GaussianRealMidpoint.lean#L14) |
| `ScalarMonotone.EndOfPaper.gaussian_real_integrable_iff_weighted` | [EndOfPaper/GaussianRealMidpoint.lean:18](../EndOfPaper/GaussianRealMidpoint.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussian_real_midpoint_log_integral` | [EndOfPaper/GaussianRealMidpoint.lean:25](../EndOfPaper/GaussianRealMidpoint.lean#L25) |
| `ScalarMonotone.EndOfPaper.gaussian_square_exponential_density` | [EndOfPaper/GaussianSquareLaplace.lean:12](../EndOfPaper/GaussianSquareLaplace.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussian_square_exponential_integrable` | [EndOfPaper/GaussianSquareLaplace.lean:21](../EndOfPaper/GaussianSquareLaplace.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussian_square_laplace_raw` | [EndOfPaper/GaussianSquareLaplace.lean:31](../EndOfPaper/GaussianSquareLaplace.lean#L31) |
| `ScalarMonotone.EndOfPaper.gaussian_square_laplace` | [EndOfPaper/GaussianSquareLaplace.lean:38](../EndOfPaper/GaussianSquareLaplace.lean#L38) |
| `ScalarMonotone.EndOfPaper.independent_real_finset_product` | [EndOfPaper/GaussianSquareSumLaplace.lean:13](../EndOfPaper/GaussianSquareSumLaplace.lean#L13) |
| `ScalarMonotone.EndOfPaper.gaussian_square_sum_laplace` | [EndOfPaper/GaussianSquareSumLaplace.lean:29](../EndOfPaper/GaussianSquareSumLaplace.lean#L29) |
| `ScalarMonotone.EndOfPaper.gaussianCons` | [EndOfPaper/GaussianVectorSplit.lean:12](../EndOfPaper/GaussianVectorSplit.lean#L12) |
| `ScalarMonotone.EndOfPaper.gaussianTail` | [EndOfPaper/GaussianVectorSplit.lean:15](../EndOfPaper/GaussianVectorSplit.lean#L15) |
| `ScalarMonotone.EndOfPaper.gaussianCons_zero` | [EndOfPaper/GaussianVectorSplit.lean:18](../EndOfPaper/GaussianVectorSplit.lean#L18) |
| `ScalarMonotone.EndOfPaper.gaussianCons_succ` | [EndOfPaper/GaussianVectorSplit.lean:21](../EndOfPaper/GaussianVectorSplit.lean#L21) |
| `ScalarMonotone.EndOfPaper.gaussianTail_apply` | [EndOfPaper/GaussianVectorSplit.lean:24](../EndOfPaper/GaussianVectorSplit.lean#L24) |
| `ScalarMonotone.EndOfPaper.gaussianCons_sub_norm_sq` | [EndOfPaper/GaussianVectorSplit.lean:27](../EndOfPaper/GaussianVectorSplit.lean#L27) |
| `ScalarMonotone.EndOfPaper.gaussianCons_dist_sq` | [EndOfPaper/GaussianVectorSplit.lean:32](../EndOfPaper/GaussianVectorSplit.lean#L32) |
| `ScalarMonotone.EndOfPaper.gaussianCons_isometry` | [EndOfPaper/GaussianVectorSplit.lean:36](../EndOfPaper/GaussianVectorSplit.lean#L36) |
| `ScalarMonotone.EndOfPaper.gaussianCons_coordinate_isometry` | [EndOfPaper/GaussianVectorSplit.lean:43](../EndOfPaper/GaussianVectorSplit.lean#L43) |
| `ScalarMonotone.EndOfPaper.gaussianCons_head_tail` | [EndOfPaper/GaussianVectorSplit.lean:51](../EndOfPaper/GaussianVectorSplit.lean#L51) |
| `ScalarMonotone.EndOfPaper.logExpIntegral` | [EndOfPaper/LogExpMarginal.lean:14](../EndOfPaper/LogExpMarginal.lean#L14) |
| `ScalarMonotone.EndOfPaper.exponential_integral_comparison` | [EndOfPaper/LogExpMarginal.lean:17](../EndOfPaper/LogExpMarginal.lean#L17) |
| `ScalarMonotone.EndOfPaper.log_exp_integral_lipschitz` | [EndOfPaper/LogExpMarginal.lean:30](../EndOfPaper/LogExpMarginal.lean#L30) |
| `ScalarMonotone.EndOfPaper.positive_sqrt_transport_bound` | [EndOfPaper/MidpointPrekopaLeindler.lean:12](../EndOfPaper/MidpointPrekopaLeindler.lean#L12) |
| `ScalarMonotone.EndOfPaper.midpoint_integral_unit_density` | [EndOfPaper/MidpointPrekopaLeindler.lean:34](../EndOfPaper/MidpointPrekopaLeindler.lean#L34) |
| `ScalarMonotone.EndOfPaper.midpoint_prekopa_leindler_real` | [EndOfPaper/MidpointPrekopaLeindler.lean:49](../EndOfPaper/MidpointPrekopaLeindler.lean#L49) |
| `ScalarMonotone.EndOfPaper.positiveDensityCDF` | [EndOfPaper/PositiveDensityCDF.lean:15](../EndOfPaper/PositiveDensityCDF.lean#L15) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_eq_Iic` | [EndOfPaper/PositiveDensityCDF.lean:18](../EndOfPaper/PositiveDensityCDF.lean#L18) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_hasDerivAt` | [EndOfPaper/PositiveDensityCDF.lean:26](../EndOfPaper/PositiveDensityCDF.lean#L26) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_hasStrictDerivAt` | [EndOfPaper/PositiveDensityCDF.lean:30](../EndOfPaper/PositiveDensityCDF.lean#L30) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_strictMono` | [EndOfPaper/PositiveDensityCDF.lean:34](../EndOfPaper/PositiveDensityCDF.lean#L34) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_continuous` | [EndOfPaper/PositiveDensityCDF.lean:38](../EndOfPaper/PositiveDensityCDF.lean#L38) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_atBot` | [EndOfPaper/PositiveDensityCDF.lean:42](../EndOfPaper/PositiveDensityCDF.lean#L42) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_atTop` | [EndOfPaper/PositiveDensityCDF.lean:53](../EndOfPaper/PositiveDensityCDF.lean#L53) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_mem` | [EndOfPaper/PositiveDensityCDF.lean:60](../EndOfPaper/PositiveDensityCDF.lean#L60) |
| `ScalarMonotone.EndOfPaper.positive_density_cdf_range` | [EndOfPaper/PositiveDensityCDF.lean:72](../EndOfPaper/PositiveDensityCDF.lean#L72) |
| `ScalarMonotone.EndOfPaper.positive_density_mass_positive` | [EndOfPaper/PositiveDensityCDF.lean:90](../EndOfPaper/PositiveDensityCDF.lean#L90) |
| `ScalarMonotone.EndOfPaper.densityMidpointTransport` | [EndOfPaper/PositiveDensityMidpoint.lean:13](../EndOfPaper/PositiveDensityMidpoint.lean#L13) |
| `ScalarMonotone.EndOfPaper.densityMidpointJacobian` | [EndOfPaper/PositiveDensityMidpoint.lean:14](../EndOfPaper/PositiveDensityMidpoint.lean#L14) |
| `ScalarMonotone.EndOfPaper.density_midpoint_hasStrictDerivAt` | [EndOfPaper/PositiveDensityMidpoint.lean:22](../EndOfPaper/PositiveDensityMidpoint.lean#L22) |
| `ScalarMonotone.EndOfPaper.density_midpoint_jacobian_positive` | [EndOfPaper/PositiveDensityMidpoint.lean:27](../EndOfPaper/PositiveDensityMidpoint.lean#L27) |
| `ScalarMonotone.EndOfPaper.density_midpoint_continuous` | [EndOfPaper/PositiveDensityMidpoint.lean:30](../EndOfPaper/PositiveDensityMidpoint.lean#L30) |
| `ScalarMonotone.EndOfPaper.density_midpoint_strictMono` | [EndOfPaper/PositiveDensityMidpoint.lean:34](../EndOfPaper/PositiveDensityMidpoint.lean#L34) |
| `ScalarMonotone.EndOfPaper.density_midpoint_atTop` | [EndOfPaper/PositiveDensityMidpoint.lean:39](../EndOfPaper/PositiveDensityMidpoint.lean#L39) |
| `ScalarMonotone.EndOfPaper.density_midpoint_atBot` | [EndOfPaper/PositiveDensityMidpoint.lean:50](../EndOfPaper/PositiveDensityMidpoint.lean#L50) |
| `ScalarMonotone.EndOfPaper.density_midpoint_surjective` | [EndOfPaper/PositiveDensityMidpoint.lean:61](../EndOfPaper/PositiveDensityMidpoint.lean#L61) |
| `ScalarMonotone.EndOfPaper.density_midpoint_change_variables` | [EndOfPaper/PositiveDensityMidpoint.lean:70](../EndOfPaper/PositiveDensityMidpoint.lean#L70) |
| `ScalarMonotone.EndOfPaper.density_midpoint_pullback_integrable` | [EndOfPaper/PositiveDensityMidpoint.lean:86](../EndOfPaper/PositiveDensityMidpoint.lean#L86) |
| `ScalarMonotone.EndOfPaper.densityTransport` | [EndOfPaper/PositiveDensityTransport.lean:13](../EndOfPaper/PositiveDensityTransport.lean#L13) |
| `ScalarMonotone.EndOfPaper.density_transport_cdf` | [EndOfPaper/PositiveDensityTransport.lean:22](../EndOfPaper/PositiveDensityTransport.lean#L22) |
| `ScalarMonotone.EndOfPaper.density_transport_hasStrictDerivAt` | [EndOfPaper/PositiveDensityTransport.lean:31](../EndOfPaper/PositiveDensityTransport.lean#L31) |
| `ScalarMonotone.EndOfPaper.density_transport_continuous` | [EndOfPaper/PositiveDensityTransport.lean:41](../EndOfPaper/PositiveDensityTransport.lean#L41) |
| `ScalarMonotone.EndOfPaper.density_transport_strictMono` | [EndOfPaper/PositiveDensityTransport.lean:45](../EndOfPaper/PositiveDensityTransport.lean#L45) |
| `ScalarMonotone.EndOfPaper.density_transport_surjective` | [EndOfPaper/PositiveDensityTransport.lean:50](../EndOfPaper/PositiveDensityTransport.lean#L50) |
<a id="claim-49"></a>

## In Example 3.11

[PDF page 57](../manuscript/monotone_calculus.pdf#page=57). G(m+c id^(-alpha))(v)<=exp(alpha)(m+c v^(-alpha))

Exactly m,c>=0 and alpha>0, on the actual maximal completion of m+c*x^(-alpha) on (0,1). Zero parameters and alpha>=1 are included. No arithmetic L1 or finite power-profile integral is added. geometricPrefixValue_affine_power_bound proves the scalar bound at every v>0. affine_power_geometric_bound proves maximality, the whole completed comparison G(q)<=exp(alpha)*q and the bound for every actual output fiber on (0,1). Bound every normalized logarithmic prefix by the integral of alpha*(log(v)-log(x)); derive logarithmic L1 by comparison with integrable log(x). Handle the identically zero profile separately. Construct the actual interval completion and extend the scalar bound to the whole completed order. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.affine_power_prefix_log_bounds` | [EndOfPaper/AffinePowerGeometric.lean:13](../EndOfPaper/AffinePowerGeometric.lean#L13) |
| `ScalarMonotone.EndOfPaper.affine_power_prefix_log_integrable` | [EndOfPaper/AffinePowerGeometric.lean:40](../EndOfPaper/AffinePowerGeometric.lean#L40) |
| `ScalarMonotone.EndOfPaper.hardyScalar_affine` | [EndOfPaper/AffinePowerGeometric.lean:63](../EndOfPaper/AffinePowerGeometric.lean#L63) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_zero` | [EndOfPaper/AffinePowerGeometric.lean:72](../EndOfPaper/AffinePowerGeometric.lean#L72) |
| `ScalarMonotone.EndOfPaper.geometricPrefixValue_affine_power_bound` | [EndOfPaper/AffinePowerGeometric.lean:79](../EndOfPaper/AffinePowerGeometric.lean#L79) |
| `ScalarMonotone.EndOfPaper.affine_power_scalar_antitone` | [EndOfPaper/AffinePowerProfile.lean:16](../EndOfPaper/AffinePowerProfile.lean#L16) |
| `ScalarMonotone.EndOfPaper.affinePowerProfile` | [EndOfPaper/AffinePowerProfile.lean:22](../EndOfPaper/AffinePowerProfile.lean#L22) |
| `ScalarMonotone.EndOfPaper.affine_power_profile_properties` | [EndOfPaper/AffinePowerProfile.lean:27](../EndOfPaper/AffinePowerProfile.lean#L27) |
| `ScalarMonotone.EndOfPaper.affine_power_positive_log_area` | [EndOfPaper/AffinePowerProfile.lean:51](../EndOfPaper/AffinePowerProfile.lean#L51) |
| `ScalarMonotone.EndOfPaper.affine_power_geometric_bound` | [EndOfPaper/AffinePowerProfile.lean:66](../EndOfPaper/AffinePowerProfile.lean#L66) |
<a id="claim-50"></a>

## After Lemma 1.19

[PDF page 17](../manuscript/monotone_calculus.pdf#page=17). Every graph point of either finite extremum belongs to an input graph

For an arbitrary finite nonempty index type and either maximal orientation, every (x,u) in either completed extremum lies in some input graph. No common domain or fiber singleton assumption is added. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.IncGraph.mem_iInf_imp_exists` | [MonotoneOperators/ExtremaFinite.lean:45](../MonotoneOperators/ExtremaFinite.lean#L45) |
| `ScalarMonotone.IncGraph.mem_iSup_imp_exists` | [MonotoneOperators/ExtremaFinite.lean:51](../MonotoneOperators/ExtremaFinite.lean#L51) |
| `ScalarMonotone.DecGraph.mem_iInf_imp_exists` | [MonotoneOperators/ExtremaFinite.lean:57](../MonotoneOperators/ExtremaFinite.lean#L57) |
| `ScalarMonotone.DecGraph.mem_iSup_imp_exists` | [MonotoneOperators/ExtremaFinite.lean:63](../MonotoneOperators/ExtremaFinite.lean#L63) |
<a id="claim-51"></a>

## After Proposition 1.20

[PDF page 18](../manuscript/monotone_calculus.pdf#page=18). Extrema inequalities for orientation-changing and order-reversing maps

All four arbitrary-family inequalities apply to either source or target maximal orientation by instantiating their established bundled preorders. P x is precisely maximality of the raw image and the dependent map bundles that image only on admissible inputs. Thus image maximality is required only for the displayed arguments, as in the manuscript; no total admissibility, countability or finiteness assumption is added. IsGLB/IsLUB express exactly the existing extrema. Reversing maps exchange the target infimum and supremum. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.partial_orderPreserving_inf_bound` | [MonotoneOperators/ExtremaOperations.lean:63](../MonotoneOperators/ExtremaOperations.lean#L63) |
| `ScalarMonotone.partial_orderPreserving_sup_bound` | [MonotoneOperators/ExtremaOperations.lean:71](../MonotoneOperators/ExtremaOperations.lean#L71) |
| `ScalarMonotone.partial_orderReversing_inf_bound` | [MonotoneOperators/ExtremaOperations.lean:79](../MonotoneOperators/ExtremaOperations.lean#L79) |
| `ScalarMonotone.partial_orderReversing_sup_bound` | [MonotoneOperators/ExtremaOperations.lean:87](../MonotoneOperators/ExtremaOperations.lean#L87) |
<a id="claim-52"></a>

## After Definition 1.21

[PDF page 18](../manuscript/monotone_calculus.pdf#page=18). Four hull identities for finite interval infima and suprema

All four hull identities hold for arbitrary finite nonempty families of nonempty sets, so include the manuscript intervals with open, closed or infinite endpoints. The input nonemptiness and family finiteness hypotheses are retained. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.upperHull_intervalInf` | [MonotoneOperators/IntervalExtrema.lean:64](../MonotoneOperators/IntervalExtrema.lean#L64) |
| `ScalarMonotone.lowerHull_intervalInf` | [MonotoneOperators/IntervalExtrema.lean:82](../MonotoneOperators/IntervalExtrema.lean#L82) |
| `ScalarMonotone.upperHull_intervalSup` | [MonotoneOperators/IntervalExtrema.lean:98](../MonotoneOperators/IntervalExtrema.lean#L98) |
| `ScalarMonotone.lowerHull_intervalSup` | [MonotoneOperators/IntervalExtrema.lean:114](../MonotoneOperators/IntervalExtrema.lean#L114) |
<a id="claim-53"></a>

## After Proposition 2.2

[PDF page 33](../manuscript/monotone_calculus.pdf#page=33). Convex or concave interior selections are continuous and force singleton values

ConvexOn.continuousOn and ConcaveOn.continuousOn give continuity on the open interior. The one-sided selection limits force both attained fiber endpoints to equal the selected value, for either maximal orientation. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.increasing_fiber_of_continuous_selection` | [EndOfPaper/ContinuousSelections.lean:16](../EndOfPaper/ContinuousSelections.lean#L16) |
| `ScalarMonotone.EndOfPaper.fiber_of_continuous_selection` | [EndOfPaper/ContinuousSelections.lean:27](../EndOfPaper/ContinuousSelections.lean#L27) |
| `ScalarMonotone.EndOfPaper.fiber_of_convex_selection` | [EndOfPaper/ContinuousSelections.lean:44](../EndOfPaper/ContinuousSelections.lean#L44) |
| `ScalarMonotone.EndOfPaper.fiber_of_concave_selection` | [EndOfPaper/ContinuousSelections.lean:51](../EndOfPaper/ContinuousSelections.lean#L51) |
<a id="claim-54"></a>

## After Lemma 2.4

[PDF page 34](../manuscript/monotone_calculus.pdf#page=34). One-sided derivatives of the expected-shortfall objective

An arbitrary original probability space, measurable integrable real X, every positive p (hence 0<p<1) and every real threshold a. Neither an atomless law nor differentiability of the pointwise positive part at an atom is assumed. The finite real objective is convex. Its actual HasDerivWithinAt derivatives on Iio a and Ioi a are respectively 1-P(X>=a)/p and 1-P(X>a)/p. Thus the left derivative retains the atom at a and the right derivative excludes it. All expectations are on the original space. The positive-part difference quotient is bounded in absolute value by one for every threshold pair. Pointwise right/left limits are the strict/weak tail indicators, including the equality case X=a. Filter dominated convergence transfers these limits to expectations. Integrability discharges subtraction and normalization identities, and the pinned slope/derivative equivalence proves the actual one-sided derivatives. A direct integral convexity proof establishes the finite convex objective without assuming the desired subdifferential. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.excessSlope` | [EndOfPaper/ShortfallDerivatives.lean:19](../EndOfPaper/ShortfallDerivatives.lean#L19) |
| `ScalarMonotone.EndOfPaper.excessSlope_abs_le_one` | [EndOfPaper/ShortfallDerivatives.lean:21](../EndOfPaper/ShortfallDerivatives.lean#L21) |
| `ScalarMonotone.EndOfPaper.excessSlope_tendsto_right` | [EndOfPaper/ShortfallDerivatives.lean:29](../EndOfPaper/ShortfallDerivatives.lean#L29) |
| `ScalarMonotone.EndOfPaper.excessSlope_tendsto_left` | [EndOfPaper/ShortfallDerivatives.lean:48](../EndOfPaper/ShortfallDerivatives.lean#L48) |
| `ScalarMonotone.EndOfPaper.excessSlope_integral_right` | [EndOfPaper/ShortfallDerivatives.lean:69](../EndOfPaper/ShortfallDerivatives.lean#L69) |
| `ScalarMonotone.EndOfPaper.excessSlope_integral_left` | [EndOfPaper/ShortfallDerivatives.lean:92](../EndOfPaper/ShortfallDerivatives.lean#L92) |
| `ScalarMonotone.EndOfPaper.shortfall_slope_eq` | [EndOfPaper/ShortfallDerivatives.lean:115](../EndOfPaper/ShortfallDerivatives.lean#L115) |
| `ScalarMonotone.EndOfPaper.shortfall_one_sided_derivatives` | [EndOfPaper/ShortfallDerivatives.lean:130](../EndOfPaper/ShortfallDerivatives.lean#L130) |
| `ScalarMonotone.EndOfPaper.realSubgradient` | [EndOfPaper/ShortfallDerivatives.lean:152](../EndOfPaper/ShortfallDerivatives.lean#L152) |
| `ScalarMonotone.EndOfPaper.shortfallObjective_convex` | [EndOfPaper/ShortfallDerivatives.lean:157](../EndOfPaper/ShortfallDerivatives.lean#L157) |
| `ScalarMonotone.EndOfPaper.realSubgradient_eq_Icc` | [EndOfPaper/ShortfallDerivatives.lean:190](../EndOfPaper/ShortfallDerivatives.lean#L190) |
| `ScalarMonotone.EndOfPaper.shortfall_subgradient_interval` | [EndOfPaper/ShortfallDerivatives.lean:221](../EndOfPaper/ShortfallDerivatives.lean#L221) |
| `ScalarMonotone.EndOfPaper.shortfall_subgradient_survival` | [EndOfPaper/ShortfallDerivatives.lean:229](../EndOfPaper/ShortfallDerivatives.lean#L229) |
| `ScalarMonotone.EndOfPaper.shortfall_zero_subgradient_iff_quantile` | [EndOfPaper/ShortfallDerivatives.lean:259](../EndOfPaper/ShortfallDerivatives.lean#L259) |
<a id="claim-55"></a>

## After Lemma 2.4

[PDF page 34](../manuscript/monotone_calculus.pdf#page=34). The convex subdifferential is the interval 1-p^(-1) S[X](a)

The original probability space and measurable L1 random variable X, every p>0 and every real a. The paper 0<p<1 is a special case. No subgradient, survival bracket, minimizer condition or differentiability is assumed as a premise. The ordinary global supporting-line subdifferential equals the closed interval between the left and right derivatives, exactly 1-p^(-1) times the entire strict/weak survival fiber in the affine sense. Zero belongs to this subdifferential exactly when a is in the completed quantile fiber. Together with the existing full original-space argmin theorem this retains every nonunique minimizer and all atoms. Define the ordinary real subdifferential by all global supporting lines. For any convex real function with the two actual one-sided derivatives, slope monotonicity proves that this set is exactly the interval between those derivatives. Apply the proved finite convexity and dominated-convergence derivative formulas. Prove the affine image equality with the actual survival law and the exact zero/quantile equivalence algebraically; no custom subgradient convention or equality premise is used. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.shortfall_minimizers_eq_tailQuantile` | [EndOfPaper/ShortfallMinimizers.lean:110](../EndOfPaper/ShortfallMinimizers.lean#L110) |
| `ScalarMonotone.EndOfPaper.excessSlope` | [EndOfPaper/ShortfallDerivatives.lean:19](../EndOfPaper/ShortfallDerivatives.lean#L19) |
| `ScalarMonotone.EndOfPaper.excessSlope_abs_le_one` | [EndOfPaper/ShortfallDerivatives.lean:21](../EndOfPaper/ShortfallDerivatives.lean#L21) |
| `ScalarMonotone.EndOfPaper.excessSlope_tendsto_right` | [EndOfPaper/ShortfallDerivatives.lean:29](../EndOfPaper/ShortfallDerivatives.lean#L29) |
| `ScalarMonotone.EndOfPaper.excessSlope_tendsto_left` | [EndOfPaper/ShortfallDerivatives.lean:48](../EndOfPaper/ShortfallDerivatives.lean#L48) |
| `ScalarMonotone.EndOfPaper.excessSlope_integral_right` | [EndOfPaper/ShortfallDerivatives.lean:69](../EndOfPaper/ShortfallDerivatives.lean#L69) |
| `ScalarMonotone.EndOfPaper.excessSlope_integral_left` | [EndOfPaper/ShortfallDerivatives.lean:92](../EndOfPaper/ShortfallDerivatives.lean#L92) |
| `ScalarMonotone.EndOfPaper.shortfall_slope_eq` | [EndOfPaper/ShortfallDerivatives.lean:115](../EndOfPaper/ShortfallDerivatives.lean#L115) |
| `ScalarMonotone.EndOfPaper.shortfall_one_sided_derivatives` | [EndOfPaper/ShortfallDerivatives.lean:130](../EndOfPaper/ShortfallDerivatives.lean#L130) |
| `ScalarMonotone.EndOfPaper.realSubgradient` | [EndOfPaper/ShortfallDerivatives.lean:152](../EndOfPaper/ShortfallDerivatives.lean#L152) |
| `ScalarMonotone.EndOfPaper.shortfallObjective_convex` | [EndOfPaper/ShortfallDerivatives.lean:157](../EndOfPaper/ShortfallDerivatives.lean#L157) |
| `ScalarMonotone.EndOfPaper.realSubgradient_eq_Icc` | [EndOfPaper/ShortfallDerivatives.lean:190](../EndOfPaper/ShortfallDerivatives.lean#L190) |
| `ScalarMonotone.EndOfPaper.shortfall_subgradient_interval` | [EndOfPaper/ShortfallDerivatives.lean:221](../EndOfPaper/ShortfallDerivatives.lean#L221) |
| `ScalarMonotone.EndOfPaper.shortfall_subgradient_survival` | [EndOfPaper/ShortfallDerivatives.lean:229](../EndOfPaper/ShortfallDerivatives.lean#L229) |
| `ScalarMonotone.EndOfPaper.shortfall_zero_subgradient_iff_quantile` | [EndOfPaper/ShortfallDerivatives.lean:259](../EndOfPaper/ShortfallDerivatives.lean#L259) |
<a id="claim-56"></a>

## Appendix A.5, proof of Proposition 2.6

[PDF page 62](../manuscript/monotone_calculus.pdf#page=62). The hypersimplex is the convex hull of fixed-cardinality zero-one vectors

For every natural n,k, the slice [0,1]^n with coordinate sum k has exactly the binary points of that sum as its extreme points, equals their convex hull, and admits an explicit finite convex decomposition with nonnegative weights summing to one. The integer sum excludes a single fractional coordinate; two fractional coordinates admit opposite perturbations. The pinned compact-convex theorem and finiteness of binary vertices give the actual convex hull, not merely its closure. The full median-transform assembly is now supplied separately by MedianTransform. Author correspondence review recorded on 2026-11-09.

| Lean declaration | Source |
|---|---|
| `ScalarMonotone.EndOfPaper.hypersimplex` | [EndOfPaper/Hypersimplex.lean:17](../EndOfPaper/Hypersimplex.lean#L17) |
| `ScalarMonotone.EndOfPaper.hypersimplexVertices` | [EndOfPaper/Hypersimplex.lean:20](../EndOfPaper/Hypersimplex.lean#L20) |
| `ScalarMonotone.EndOfPaper.hypersimplex_convex` | [EndOfPaper/Hypersimplex.lean:23](../EndOfPaper/Hypersimplex.lean#L23) |
| `ScalarMonotone.EndOfPaper.hypersimplex_compact` | [EndOfPaper/Hypersimplex.lean:30](../EndOfPaper/Hypersimplex.lean#L30) |
| `ScalarMonotone.EndOfPaper.hypersimplexVertices_finite` | [EndOfPaper/Hypersimplex.lean:34](../EndOfPaper/Hypersimplex.lean#L34) |
| `ScalarMonotone.EndOfPaper.hypersimplex_second_fractional` | [EndOfPaper/Hypersimplex.lean:42](../EndOfPaper/Hypersimplex.lean#L42) |
| `ScalarMonotone.EndOfPaper.hypersimplex_extremePoints_subset_vertices` | [EndOfPaper/Hypersimplex.lean:71](../EndOfPaper/Hypersimplex.lean#L71) |
| `ScalarMonotone.EndOfPaper.hypersimplex_vertices_subset_extremePoints` | [EndOfPaper/Hypersimplex.lean:132](../EndOfPaper/Hypersimplex.lean#L132) |
| `ScalarMonotone.EndOfPaper.hypersimplex_extremePoints_eq_vertices` | [EndOfPaper/Hypersimplex.lean:160](../EndOfPaper/Hypersimplex.lean#L160) |
| `ScalarMonotone.EndOfPaper.hypersimplex_eq_convexHull_vertices` | [EndOfPaper/Hypersimplex.lean:166](../EndOfPaper/Hypersimplex.lean#L166) |
| `ScalarMonotone.EndOfPaper.hypersimplex_eq_convexHull_binary` | [EndOfPaper/Hypersimplex.lean:177](../EndOfPaper/Hypersimplex.lean#L177) |
| `ScalarMonotone.EndOfPaper.hypersimplex_finite_decomposition` | [EndOfPaper/Hypersimplex.lean:199](../EndOfPaper/Hypersimplex.lean#L199) |
