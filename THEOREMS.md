# Theorems and definitions

Each entry below was a public root of the same checked export. Both independent checkers accepted the dependency closure. An empty dependency list means that Lean reported no axioms for that declaration. The compiler also checked 15 internal helper theorems in the generator module. [Checker record](VERIFICATION.md) · [Raw axiom readback](evidence/axioms.txt)

| Module | Public declarations | Public theorems |
| --- | ---: | ---: |
| [Shor1994Invalidation](#shor1994invalidation) | 87 | 61 |
| [ShorGeneratorCertificate](#shorgeneratorcertificate) | 14 | 14 |
| [ShorPrimorialCertificate](#shorprimorialcertificate) | 8 | 8 |
| [Shor1994Integrated](#shor1994integrated) | 1 | 1 |
| [ShorWindowFamily](#shorwindowfamily) | 9 | 7 |
| [ShorWindowSourceBridge](#shorwindowsourcebridge) | 4 | 4 |
| [LeanFiberVariance](#leanfibervariance) | 6 | 6 |
| [LeanFourierParseval](#leanfourierparseval) | 6 | 6 |
| [LeanFiberFourier](#leanfiberfourier) | 19 | 17 |
| [LeanFourierNormalization](#leanfouriernormalization) | 3 | 3 |
| [LeanMeasurementNoGo](#leanmeasurementnogo) | 8 | 6 |
| [LeanGraphCopies](#leangraphcopies) | 11 | 6 |
| [LeanFiniteCopyNoGo](#leanfinitecopynogo) | 4 | 4 |
| [Shor2AdicTorsionHierarchy](#shor2adictorsionhierarchy) | 38 | 31 |
| [Shor2AdicMasterBridge](#shor2adicmasterbridge) | 4 | 4 |
| [Shor2AdicQFTBridge](#shor2adicqftbridge) | 10 | 9 |
| [ShorArithmeticStrengthening](#shorarithmeticstrengthening) | 4 | 3 |
| [ShorResidueWorkspace](#shorresidueworkspace) | 15 | 12 |

## Shor1994Invalidation

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`Shor1994Invalidation.p`](Shor1994Invalidation.lean#L27) | def | None |
| [`Shor1994Invalidation.n`](Shor1994Invalidation.lean#L28) | def | None |
| [`Shor1994Invalidation.q`](Shor1994Invalidation.lean#L29) | def | None |
| [`Shor1994Invalidation.h`](Shor1994Invalidation.lean#L30) | def | None |
| [`Shor1994Invalidation.parameter_arithmetic`](Shor1994Invalidation.lean#L32) | theorem | `propext` |
| [`Shor1994Invalidation.p_is_prime`](Shor1994Invalidation.lean#L36) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.primePrefix`](Shor1994Invalidation.lean#L39) | def | None |
| [`Shor1994Invalidation.primeProduct`](Shor1994Invalidation.lean#L40) | def | None |
| [`Shor1994Invalidation.candidateFactors`](Shor1994Invalidation.lean#L41) | def | None |
| [`Shor1994Invalidation.selectedFactor`](Shor1994Invalidation.lean#L43) | def | None |
| [`Shor1994Invalidation.paperQ`](Shor1994Invalidation.lean#L46) | def | None |
| [`Shor1994Invalidation.paper_modulus_certificate`](Shor1994Invalidation.lean#L49) | theorem | None |
| [`Shor1994Invalidation.prime_prefix_complete`](Shor1994Invalidation.lean#L58) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.prime_prefix_contains_all_primes_through_seventeen`](Shor1994Invalidation.lean#L64) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.no_larger_removable_factor`](Shor1994Invalidation.lean#L69) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.GoodFirst`](Shor1994Invalidation.lean#L80) | def | `propext` |
| [`Shor1994Invalidation.GoodPair`](Shor1994Invalidation.lean#L90) | def | `propext` |
| [`Shor1994Invalidation.good_pair_has_good_first`](Shor1994Invalidation.lean#L96) | theorem | `propext` |
| [`Shor1994Invalidation.reconstructedInteger`](Shor1994Invalidation.lean#L102) | def | None |
| [`Shor1994Invalidation.paper_rounding_identity`](Shor1994Invalidation.lean#L105) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.paper_rounding_and_congruence`](Shor1994Invalidation.lean#L119) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.nearest_integer_unique`](Shor1994Invalidation.lean#L132) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.every_good_residue_zero`](Shor1994Invalidation.lean#L147) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.every_good_coefficient_shape`](Shor1994Invalidation.lean#L160) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.each_index_is_good`](Shor1994Invalidation.lean#L176) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.good_first_iff_exact_lattice`](Shor1994Invalidation.lean#L182) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.goodCoefficientSet`](Shor1994Invalidation.lean#L190) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.good_coefficient_membership`](Shor1994Invalidation.lean#L193) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.good_coefficient_count`](Shor1994Invalidation.lean#L207) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.divisibleGoodCoefficients`](Shor1994Invalidation.lean#L215) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.divisible_coefficient_set_exact`](Shor1994Invalidation.lean#L218) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.divisible_good_coefficient_count`](Shor1994Invalidation.lean#L249) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.printed_ten_over_thirty_two_bound_false`](Shor1994Invalidation.lean#L259) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.no_good_coefficient_coprime_32`](Shor1994Invalidation.lean#L266) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.LargePrimePowerDivisor`](Shor1994Invalidation.lean#L282) | def | `propext` |
| [`Shor1994Invalidation.PaperUnitExistenceClaim`](Shor1994Invalidation.lean#L285) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.thirty_two_is_required`](Shor1994Invalidation.lean#L291) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.paper_unit_existence_claim_false`](Shor1994Invalidation.lean#L295) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.no_good_pair_unit_32`](Shor1994Invalidation.lean#L302) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.PaperCompletePairUnitClaim`](Shor1994Invalidation.lean#L306) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.paper_complete_pair_unit_claim_false`](Shor1994Invalidation.lean#L313) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.explicit_complete_good_pair`](Shor1994Invalidation.lean#L322) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.explicit_decoded_relation`](Shor1994Invalidation.lean#L325) | theorem | `propext` |
| [`Shor1994Invalidation.paperGraphOutput`](Shor1994Invalidation.lean#L333) | def | None |
| [`Shor1994Invalidation.paperGraphFiber`](Shor1994Invalidation.lean#L336) | def | None |
| [`Shor1994Invalidation.source_graph_fiber_iff`](Shor1994Invalidation.lean#L338) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.paperFourierNumerator`](Shor1994Invalidation.lean#L348) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.paperFourierRawNumerator`](Shor1994Invalidation.lean#L357) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.power_reduction_at_root_of_unity`](Shor1994Invalidation.lean#L364) | theorem | `propext` |
| [`Shor1994Invalidation.raw_fourier_equals_reduced`](Shor1994Invalidation.lean#L373) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_fourier_fiber_reindex`](Shor1994Invalidation.lean#L387) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.graphFirstExponent`](Shor1994Invalidation.lean#L420) | def | None |
| [`Shor1994Invalidation.source_graph_fiber`](Shor1994Invalidation.lean#L422) | theorem | None |
| [`Shor1994Invalidation.graph_fiber_label`](Shor1994Invalidation.lean#L425) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.phase_residue_on_every_fiber`](Shor1994Invalidation.lean#L431) | theorem | `propext`, `Quot.sound` |
| [`Shor1994Invalidation.fiberNumerator`](Shor1994Invalidation.lean#L440) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_fourier_equals_fiber`](Shor1994Invalidation.lean#L444) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.fiber_numerator_exact`](Shor1994Invalidation.lean#L451) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.fiber_amplitude_exact`](Shor1994Invalidation.lean#L456) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.fiber_born_probability`](Shor1994Invalidation.lean#L464) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.good_pair_probability`](Shor1994Invalidation.lean#L476) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.good_pair_probability_positive`](Shor1994Invalidation.lean#L492) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.goodSecondFrequency`](Shor1994Invalidation.lean#L503) | def | None |
| [`Shor1994Invalidation.every_index_is_complete_good_pair`](Shor1994Invalidation.lean#L505) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.every_complete_good_pair_exact`](Shor1994Invalidation.lean#L534) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.every_complete_good_pair_has_unique_index`](Shor1994Invalidation.lean#L575) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.complete_good_pair_iff_indexed`](Shor1994Invalidation.lean#L587) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.phase_residue_all_good_indices`](Shor1994Invalidation.lean#L599) | theorem | `propext` |
| [`Shor1994Invalidation.fiberNumeratorAllGood`](Shor1994Invalidation.lean#L638) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_fourier_equals_all_good`](Shor1994Invalidation.lean#L644) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_raw_fourier_equals_all_good`](Shor1994Invalidation.lean#L651) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.fiber_numerator_all_good`](Shor1994Invalidation.lean#L659) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.fiber_amplitude_all_good`](Shor1994Invalidation.lean#L665) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.fiber_born_all_good`](Shor1994Invalidation.lean#L673) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.pair_probability_all_good`](Shor1994Invalidation.lean#L685) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_raw_pair_probability_all_good`](Shor1994Invalidation.lean#L701) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.total_good_probability`](Shor1994Invalidation.lean#L727) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_raw_total_good_probability`](Shor1994Invalidation.lean#L745) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.evenGoodIndices`](Shor1994Invalidation.lean#L767) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.even_good_indices_exact`](Shor1994Invalidation.lean#L770) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.even_good_indices_count`](Shor1994Invalidation.lean#L785) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.source_raw_divisible_good_probability`](Shor1994Invalidation.lean#L794) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.physical_conditional_bound_false`](Shor1994Invalidation.lean#L818) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.explicit_qft_root_pow`](Shor1994Invalidation.lean#L839) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.explicit_qft_root_normSq_one`](Shor1994Invalidation.lean#L854) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.explicit_qft_root_primitive`](Shor1994Invalidation.lean#L862) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor1994Invalidation.actual_qft_conditional_bound_false`](Shor1994Invalidation.lean#L871) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## ShorGeneratorCertificate

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorGenerator.p_prime`](ShorGeneratorCertificate.lean#L8) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGenerator.fifth_power_target`](ShorGeneratorCertificate.lean#L11) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.full_power`](ShorGeneratorCertificate.lean#L15) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGenerator.half_residue`](ShorGeneratorCertificate.lean#L165) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.half_power`](ShorGeneratorCertificate.lean#L177) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.third_residue`](ShorGeneratorCertificate.lean#L183) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.third_power`](ShorGeneratorCertificate.lean#L195) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.seventh_residue`](ShorGeneratorCertificate.lean#L201) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.seventh_power`](ShorGeneratorCertificate.lean#L213) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.eleventh_residue`](ShorGeneratorCertificate.lean#L219) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.eleventh_power`](ShorGeneratorCertificate.lean#L231) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.thirteenth_residue`](ShorGeneratorCertificate.lean#L237) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.thirteenth_power`](ShorGeneratorCertificate.lean#L249) | theorem | `propext`, `Quot.sound` |
| [`ShorGenerator.generator_order`](ShorGeneratorCertificate.lean#L255) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## ShorPrimorialCertificate

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorPrimorial.prime_product`](ShorPrimorialCertificate.lean#L8) | theorem | `propext` |
| [`ShorPrimorial.prime_factors`](ShorPrimorialCertificate.lean#L12) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorPrimorial.quotient_by_five`](ShorPrimorialCertificate.lean#L27) | theorem | `propext` |
| [`ShorPrimorial.above_p`](ShorPrimorialCertificate.lean#L31) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorPrimorial.quotient_by_seven`](ShorPrimorialCertificate.lean#L35) | theorem | `propext` |
| [`ShorPrimorial.below_p`](ShorPrimorialCertificate.lean#L39) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorPrimorial.no_larger_removal`](ShorPrimorialCertificate.lean#L43) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorPrimorial.five_is_largest`](ShorPrimorialCertificate.lean#L52) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## Shor1994Integrated

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`Shor1994Integrated.certified_prime_field_counterexample`](Shor1994Integrated.lean#L7) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## ShorWindowFamily

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorWindowFamily.GoodFirst`](ShorWindowFamily.lean#L13) | def | `propext` |
| [`ShorWindowFamily.good_residue_zero`](ShorWindowFamily.lean#L19) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.every_good_coefficient_shape`](ShorWindowFamily.lean#L47) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.each_index_is_good`](ShorWindowFamily.lean#L79) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.good_first_iff_exact_lattice`](ShorWindowFamily.lean#L98) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.no_good_unit_of_common_factor`](ShorWindowFamily.lean#L109) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.SampleSuppliesUnit`](ShorWindowFamily.lean#L127) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.no_finite_good_sample_supplies_unit`](ShorWindowFamily.lean#L133) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowFamily.original_instance_is_a_family_member`](ShorWindowFamily.lean#L144) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## ShorWindowSourceBridge

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorWindowSourceBridge.source_good_first_is_family_good_first`](ShorWindowSourceBridge.lean#L6) | theorem | `propext` |
| [`ShorWindowSourceBridge.source_complete_pair_has_no_unit`](ShorWindowSourceBridge.lean#L11) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowSourceBridge.source_claim_false_via_general_family`](ShorWindowSourceBridge.lean#L21) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorWindowSourceBridge.certified_source_counterexample_via_general_family`](ShorWindowSourceBridge.lean#L29) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanFiberVariance

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`LeanFiberVariance.norm_sum_sq_as_double_inner`](LeanFiberVariance.lean#L17) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberVariance.pairwise_variance`](LeanFiberVariance.lean#L23) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberVariance.normalized_fiber_variance`](LeanFiberVariance.lean#L35) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberVariance.fiber_variance_zero_iff`](LeanFiberVariance.lean#L49) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberVariance.fiber_coherence_iff`](LeanFiberVariance.lean#L74) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberVariance.exact_coherence_defect`](LeanFiberVariance.lean#L91) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanFourierParseval

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`LeanFourierParseval.standard_character_conjugate`](LeanFourierParseval.lean#L13) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierParseval.standard_character_product`](LeanFourierParseval.lean#L18) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierParseval.standard_character_sum`](LeanFourierParseval.lean#L25) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierParseval.twisted_inner`](LeanFourierParseval.lean#L35) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierParseval.fourier_inner_sum`](LeanFourierParseval.lean#L42) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierParseval.vector_parseval`](LeanFourierParseval.lean#L65) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanFiberFourier

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`LeanFiberFourier.rawNumerator`](LeanFiberFourier.lean#L14) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.amplitude`](LeanFiberFourier.lean#L21) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.raw_fiber_formula`](LeanFiberFourier.lean#L27) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.raw_zero_frequencies`](LeanFiberFourier.lean#L44) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.standard_character_norm`](LeanFiberFourier.lean#L53) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.standard_character_sum`](LeanFiberFourier.lean#L58) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.graph_preparation_normalized`](LeanFiberFourier.lean#L69) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.amplitude_norm_sq`](LeanFiberFourier.lean#L77) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.fourier_pair_probability`](LeanFiberFourier.lean#L84) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.zero_pair_probability`](LeanFiberFourier.lean#L94) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.raw_of_fiber_constant`](LeanFiberFourier.lean#L102) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.ideal_pair_law_of_fiber_constant`](LeanFiberFourier.lean#L115) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.line_probability_formula`](LeanFiberFourier.lean#L139) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.line_probability_one_iff_fiber_constant`](LeanFiberFourier.lean#L157) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.ideal_pair_law_iff_fiber_constant`](LeanFiberFourier.lean#L169) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.exact_fourier_line_defect`](LeanFiberFourier.lean#L189) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.fiber_constant_iff_output_factor`](LeanFiberFourier.lean#L204) | theorem | `propext`, `Quot.sound` |
| [`LeanFiberFourier.ideal_pair_law_iff_output_factor`](LeanFiberFourier.lean#L216) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFiberFourier.unequal_fiber_vectors_forbid_ideal_law`](LeanFiberFourier.lean#L226) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanFourierNormalization

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`LeanFourierNormalization.shifted_parseval`](LeanFourierNormalization.lean#L12) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierNormalization.fixed_first_frequency_and_output_mass`](LeanFourierNormalization.lean#L25) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanFourierNormalization.total_probability_one`](LeanFourierNormalization.lean#L38) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanMeasurementNoGo

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`LeanMeasurementNoGo.FinitePOVM`](LeanMeasurementNoGo.lean#L13) | structure | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.PerfectlyDistinguishes`](LeanMeasurementNoGo.lean#L20) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.wrong_effect_annihilates`](LeanMeasurementNoGo.lean#L25) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.correct_effect_fixes`](LeanMeasurementNoGo.lean#L32) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.perfect_discrimination_implies_orthogonal`](LeanMeasurementNoGo.lean#L49) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.no_perfect_povm_of_nonzero_inner`](LeanMeasurementNoGo.lean#L68) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.decoded_measurement_gives_label_povm`](LeanMeasurementNoGo.lean#L76) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`LeanMeasurementNoGo.no_perfect_decoded_povm_of_nonzero_inner`](LeanMeasurementNoGo.lean#L114) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanGraphCopies

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorGraphCopies.Register`](LeanGraphCopies.lean#L14) | abbrev | None |
| [`ShorGraphCopies.Basis`](LeanGraphCopies.lean#L15) | abbrev | None |
| [`ShorGraphCopies.outputWord`](LeanGraphCopies.lean#L17) | def | `propext`, `Quot.sound` |
| [`ShorGraphCopies.graphVector`](LeanGraphCopies.lean#L20) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.graphVector_apply`](LeanGraphCopies.lean#L25) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.singleCopyAmplitude`](LeanGraphCopies.lean#L30) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.graphVector_is_independent_copy_product`](LeanGraphCopies.lean#L34) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.graphVector_norm_sq`](LeanGraphCopies.lean#L54) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.graphVector_norm`](LeanGraphCopies.lean#L63) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.graphVector_inner_re_pos`](LeanGraphCopies.lean#L69) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorGraphCopies.graphVector_inner_ne_zero`](LeanGraphCopies.lean#L97) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## LeanFiniteCopyNoGo

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorFiniteCopyNoGo.no_perfect_measurement_on_graph_copies`](LeanFiniteCopyNoGo.lean#L10) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorFiniteCopyNoGo.no_perfect_decoded_measurement_on_graph_copies`](LeanFiniteCopyNoGo.lean#L20) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorFiniteCopyNoGo.normalized_states_and_no_perfect_measurement`](LeanFiniteCopyNoGo.lean#L35) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorFiniteCopyNoGo.every_group_order_and_finite_copy_count`](LeanFiniteCopyNoGo.lean#L43) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## Shor2AdicTorsionHierarchy

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`Shor2AdicTorsionHierarchy.binary_control_stage_invariance`](Shor2AdicTorsionHierarchy.lean#L16) | theorem | `propext` |
| [`Shor2AdicTorsionHierarchy.elliptic_116_six_of_seven_controls_identical`](Shor2AdicTorsionHierarchy.lean#L33) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.elliptic_116_mod4_upper_controls_identical`](Shor2AdicTorsionHierarchy.lean#L41) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.shor_100_six_of_seven_controls_identical`](Shor2AdicTorsionHierarchy.lean#L50) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.shor_101_multiplicative_sign_flip`](Shor2AdicTorsionHierarchy.lean#L57) | theorem | `propext` |
| [`Shor2AdicTorsionHierarchy.coherence_block_phase_difference_invariance`](Shor2AdicTorsionHierarchy.lean#L65) | theorem | `propext`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.residue_class_fiber_shift`](Shor2AdicTorsionHierarchy.lean#L78) | theorem | `propext` |
| [`Shor2AdicTorsionHierarchy.residueClassFiberNumerator`](Shor2AdicTorsionHierarchy.lean#L89) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.residue_class_numerator_shifted_fiber`](Shor2AdicTorsionHierarchy.lean#L95) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.zmod_fiber_sum_invariant_on_residue_class`](Shor2AdicTorsionHierarchy.lean#L105) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.rounded_congruence_satisfied_by_entire_coset`](Shor2AdicTorsionHierarchy.lean#L132) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.modular_congruence_coset_invariance`](Shor2AdicTorsionHierarchy.lean#L142) | theorem | `propext` |
| [`Shor2AdicTorsionHierarchy.GoodFirst1997`](Shor2AdicTorsionHierarchy.lean#L153) | abbrev | `propext` |
| [`Shor2AdicTorsionHierarchy.good_residue_zero_1997`](Shor2AdicTorsionHierarchy.lean#L159) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.every_good_coefficient_shape_1997`](Shor2AdicTorsionHierarchy.lean#L188) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.shor_100_good_table_row_1`](Shor2AdicTorsionHierarchy.lean#L221) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.shor_100_good_table_row_2`](Shor2AdicTorsionHierarchy.lean#L229) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.shor_100_good_table_row_3`](Shor2AdicTorsionHierarchy.lean#L236) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.paddedGraphFiber`](Shor2AdicTorsionHierarchy.lean#L256) | def | None |
| [`Shor2AdicTorsionHierarchy.padded_graph_fiber_period_step`](Shor2AdicTorsionHierarchy.lean#L258) | theorem | `propext` |
| [`Shor2AdicTorsionHierarchy.padded_graph_fiber_half_period`](Shor2AdicTorsionHierarchy.lean#L269) | theorem | `propext` |
| [`Shor2AdicTorsionHierarchy.rawPaddedFiberSum`](Shor2AdicTorsionHierarchy.lean#L276) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.raw_padded_general_torsion_factorization`](Shor2AdicTorsionHierarchy.lean#L282) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.raw_padded_fiber_sum_factorization`](Shor2AdicTorsionHierarchy.lean#L318) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.zero_column_of_half_period_neg_one`](Shor2AdicTorsionHierarchy.lean#L349) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.elliptic_116_and_shor_100_zero_column_frequencies`](Shor2AdicTorsionHierarchy.lean#L357) | theorem | None |
| [`Shor2AdicTorsionHierarchy.hadamardUnnorm`](Shor2AdicTorsionHierarchy.lean#L372) | def | `propext` |
| [`Shor2AdicTorsionHierarchy.hadamardMod2`](Shor2AdicTorsionHierarchy.lean#L375) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.hadamard_int_sq_eq_two_id`](Shor2AdicTorsionHierarchy.lean#L377) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.hadamard_mod2_sq_eq_zero`](Shor2AdicTorsionHierarchy.lean#L383) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.booleanSignCharacter`](Shor2AdicTorsionHierarchy.lean#L388) | def | `propext` |
| [`Shor2AdicTorsionHierarchy.boolean_sign_character_period_two`](Shor2AdicTorsionHierarchy.lean#L390) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.parity_twist_shifts_second_frequency`](Shor2AdicTorsionHierarchy.lean#L398) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.first_marginal_invariant_of_frequency_shift`](Shor2AdicTorsionHierarchy.lean#L417) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.even_reduced_order_collision_even_diff`](Shor2AdicTorsionHierarchy.lean#L425) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.parity_phase_product_one_of_same_parity`](Shor2AdicTorsionHierarchy.lean#L444) | theorem | `propext`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.second_marginal_invariant_of_even_collisions`](Shor2AdicTorsionHierarchy.lean#L455) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicTorsionHierarchy.elliptic_116_and_shor_100_collisions_preserve_parity`](Shor2AdicTorsionHierarchy.lean#L485) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## Shor2AdicMasterBridge

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`Shor2AdicMasterBridge.two_adic_workspace_line_defect_and_survival`](Shor2AdicMasterBridge.lean#L29) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicMasterBridge.source_good_pair_sixteen_coset_blindness`](Shor2AdicMasterBridge.lean#L67) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicMasterBridge.source_even_good_pair_thirty_two_coset_blindness`](Shor2AdicMasterBridge.lean#L81) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicMasterBridge.four_interlocking_shor_obstructions`](Shor2AdicMasterBridge.lean#L108) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## Shor2AdicQFTBridge

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`Shor2AdicQFTBridge.root_power_reduce`](Shor2AdicQFTBridge.lean#L9) | theorem | `propext` |
| [`Shor2AdicQFTBridge.explicit_qft_128_root_primitive`](Shor2AdicQFTBridge.lean#L18) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.explicit_qft_128_root_pow`](Shor2AdicQFTBridge.lean#L23) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.explicit_qft_128_root_half_period`](Shor2AdicQFTBridge.lean#L27) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.certified_root_zero_columns`](Shor2AdicQFTBridge.lean#L37) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.actual_qft_zero_columns`](Shor2AdicQFTBridge.lean#L57) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.actual_qft_zero_column_born_mass`](Shor2AdicQFTBridge.lean#L67) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.GoodPair1997`](Shor2AdicQFTBridge.lean#L97) | abbrev | `propext` |
| [`Shor2AdicQFTBridge.shor_100_complete_table_rows`](Shor2AdicQFTBridge.lean#L102) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`Shor2AdicQFTBridge.odd_torsion_filter_counterexample`](Shor2AdicQFTBridge.lean#L109) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## ShorArithmeticStrengthening

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorArithmeticStrengthening.GoodCoefficientKernel`](ShorArithmeticStrengthening.lean#L8) | def | `propext` |
| [`ShorArithmeticStrengthening.all_good_congruences_exact_kernel`](ShorArithmeticStrengthening.lean#L14) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorArithmeticStrengthening.sixteen_distinct_common_candidates`](ShorArithmeticStrengthening.lean#L33) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorArithmeticStrengthening.power_two_modulus_for_96097`](ShorArithmeticStrengthening.lean#L39) | theorem | `propext`, `Classical.choice`, `Quot.sound` |

## ShorResidueWorkspace

| Declaration in Lean | Kind | Axiom dependencies |
| --- | --- | --- |
| [`ShorResidueWorkspace.BalancedLabels`](ShorResidueWorkspace.lean#L10) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.balanced_label_distance_sum`](ShorResidueWorkspace.lean#L15) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.balanced_workspace_variance`](ShorResidueWorkspace.lean#L40) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.balanced_workspace_variance_fraction`](ShorResidueWorkspace.lean#L56) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.balanced_workspace_line_defect_and_survival`](ShorResidueWorkspace.lean#L74) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.two_adic_balanced_workspace_survival`](ShorResidueWorkspace.lean#L100) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.labelWorkspace`](ShorResidueWorkspace.lean#L117) | def | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.label_workspace_norm`](ShorResidueWorkspace.lean#L121) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.label_workspace_distance`](ShorResidueWorkspace.lean#L125) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.canonical_label_workspace_survival`](ShorResidueWorkspace.lean#L137) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.residueLabel`](ShorResidueWorkspace.lean#L148) | def | None |
| [`ShorResidueWorkspace.residue_labels_balanced`](ShorResidueWorkspace.lean#L152) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.residue_workspace_variance`](ShorResidueWorkspace.lean#L196) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.residue_workspace_line_survival`](ShorResidueWorkspace.lean#L207) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
| [`ShorResidueWorkspace.two_adic_residue_workspace_line_survival`](ShorResidueWorkspace.lean#L216) | theorem | `propext`, `Classical.choice`, `Quot.sound` |
