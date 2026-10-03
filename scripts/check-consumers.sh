#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/verification
log=.lake/verification/independent-consumers.log
: > "$log"
for source in \
  tests/CorollaryConsumer.lean \
  tests/Geometry/DefinitionOwnerRepairConsumer.lean \
  tests/ActualCommonOpenColumnGlueConsumer.lean \
  tests/ActualWitnessCommonOpenColumnGlueConsumer.lean \
  tests/ActualWitnessSelectedChartIndexConsumer.lean \
  tests/ActualSameWitnessDivisorNumeratorCheck.lean \
  tests/ActualPointAxisLiftCheck.lean \
  tests/ActualSelectedNormalizationDivisorEtaleCheck.lean \
  tests/ActualSameWitnessGroundPointCompletionConsumer.lean \
  tests/ActualSameWitnessAffineFibreClosureConsumer.lean \
  tests/ActualSameWitnessOriginalPrimeConsumer.lean \
  tests/Geometry/CommonOpenArcCompatibilityConsumer.lean \
  tests/ActualPointCommonOpenAssemblyCheck.lean \
  tests/DirectSummandInputAxisConsumer.lean \
  tests/Geometry/FiniteParameterTangentConsumer.lean \
  tests/Geometry/OptionNormalizedLatticeProjectiveConeConsumer.lean \
  tests/CorollaryChallengeOwnerConsumer.lean \
  tests/LocalizedDifferentialConsumer.lean \
  tests/FixedSourceChallengeConsumer.lean \
  tests/TorsionCyclicityConsumer.lean \
  tests/NoncharacteristicConsumer.lean \
  tests/PaperEulerGradingConsumer.lean \
  tests/PaperHamiltonianFlowConsumer.lean \
  tests/PaperRouteConsumer.lean \
  tests/SymplecticComplementConsumer.lean \
  tests/PairReplacementConsumer.lean \
  tests/PaperBasisRightMonicConsumer.lean \
  tests/PowerSeriesFirstCoefficientConsumer.lean \
  tests/CanonicalStaffordPredicateConsumer.lean \
  tests/ProjectiveChartCoordinatesConsumer.lean \
  tests/PaperCompletedColumnsConsumer.lean \
  tests/ProjectiveDVRCenterConsumer.lean \
  tests/ProjectiveTangentOwnerConsumer.lean \
  tests/GeneralDivisorialWitnessProducerConsumer.lean \
  tests/GeneralDivisorialVisibleFrameResidueSupportConsumer.lean \
  tests/PaperSameWitnessTangentAxiomAudit.lean \
  tests/PaperActualAxisConsumer.lean \
  tests/PaperActualGeometryAxiomAudit.lean \
  tests/ProjectiveDivisorChartBridgeConsumer.lean \
  tests/ResidueBasisLocalizationConsumer.lean \
  tests/RetainedChartQuotientEmbeddingConsumer.lean \
  tests/ChartGenericPointFractionRingConsumer.lean \
  tests/ChartNormalizationFiniteTypeConsumer.lean \
  tests/ProjectiveNormalizationFiniteConsumer.lean \
  tests/ProjectiveNormalizationCenterConsumer.lean \
  tests/ValuationCenterDominatesLocalPrimeConsumer.lean \
  tests/Geometry/TiltedArcAvoidanceConsumer.lean \
  tests/Geometry/SmoothLocalTiltedArcAxisConsumer.lean \
  tests/Geometry/FormallyEtaleCompletionEquivalenceConsumer.lean \
  tests/Geometry/KaehlerTranscendenceBasisAxiomAudit.lean \
  tests/Geometry/SameWitnessTrdegAxiomAudit.lean \
  tests/DVRParameterSmoothnessConsumer.lean \
  tests/PrescribedEtaleGroundPointConsumer.lean \
  tests/DVRUniformizerNumeratorConsumer.lean \
  tests/Geometry/PaperUnitPowerFactorizationConsumer.lean \
  tests/CoordinateLocalizationAxiomAudit.lean \
  tests/ProjectiveCoefficientLocalizationGenericConsumer.lean \
  tests/ActualChartValuationImageConsumer.lean \
  tests/ActualSelectedResidueBasisConsumer.lean \
  tests/SelectedResidueCoefficientLocalizationConsumer.lean \
  tests/SelectedResidueNormalizationLocalizationConsumer.lean \
  tests/ActualChartCenterNonzeroConsumer.lean \
  tests/FiniteBirationalAwayActualConsumer.lean \
  tests/SameWitnessRelativeTrdegConsumer.lean \
  tests/MvPolynomialFractionFieldBasisConsumer.lean \
  tests/MvPolynomialFractionFieldGenericConsumer.lean \
  tests/EtaleCotangentTangentConsumer.lean \
  tests/ActualSelectedResidueBasisRowExclusionConsumer.lean \
  tests/ActualWitnessStrictOrderGapConsumer.lean \
  tests/GeneralTangentLimitCriterionKernelExportConsumer.lean \
  tests/ProjectiveChartNormalizationBridgeConsumer.lean \
  tests/OptionCoordinateEtaleCompositionConsumer.lean \
  tests/FieldEquivFiniteTypeConsumer.lean \
  tests/Geometry/UnitPowerNonzeroPrimeOracle.lean \
  tests/Geometry/CoefficientRegularityOracle.lean \
  tests/Geometry/AffinePointCompletionConsumer.lean \
  tests/Geometry/CompletionInfrastructureAxioms.lean \
  tests/Geometry/PrescribedGroundPointPowerSeriesMapConsumer.lean \
  tests/Geometry/SmoothLocalDirectSummandAdapterConsumer.lean \
  tests/Geometry/CorrectedVelocitySpanConsumer.lean \
  tests/Geometry/HomogenizedAffineEvaluationConsumer.lean \
  tests/Geometry/SmoothAffinePointScalarExtensionConsumer.lean \
  tests/Geometry/NonAlgebraicallyClosedSmoothConsumer.lean \
  tests/Geometry/PrescribedGroundPointUnitPowerConsumer.lean \
  tests/Geometry/SelectedCorrectionConsumer.lean \
  tests/Geometry/ActualSmoothOpenChartNumeratorConsumer.lean \
  tests/ActualColumnBindingConsumer.lean \
  tests/Geometry/LocalizationInStagesAtPrimeConsumer.lean \
  tests/Geometry/SelectedCoordinateAxisLiftConsumer.lean \
  tests/Geometry/ExactChartTangentConsumer.lean \
  tests/Geometry/ProjectiveDerivationDehomogenizationConsumer.lean \
  tests/Geometry/LocalizationStageFractionCoefficientsConsumer.lean \
  tests/Geometry/EtaleGenericOpenExtraAwayBCheck.lean \
  tests/Geometry/ExtraAwayBNoRtoQOracle.lean \
  tests/Geometry/EtaleProjectiveTangentComparisonConsumer.lean \
  tests/Geometry/ProjectiveChartSameFieldOverlapConsumer.lean \
  tests/PrescribedCompletionDerivationCommutationConsumer.lean \
  tests/ActualColumnCompletionBindingConsumer.lean \
  tests/Geometry/A0ChartFormalEtaleConsumer.lean \
  tests/LocalNormalizationCenterEquivalenceConsumer.lean \
  tests/Geometry/GenericFibreMatrixColumnsConsumer.lean \
  tests/ActualResidueCenterHeightConsumer.lean \
  tests/ActualChartResidueMapCoherenceConsumer.lean \
  tests/ActualNormalizationCenterResidueKernelConsumer.lean \
  tests/ActualChartNormalizationCenterConsumer.lean \
  tests/Geometry/ActualNormalizationDivisorEtaleConsumer.lean \
  tests/Geometry/ActualOptionCoordinateEtaleConsumer.lean \
  tests/Geometry/A0NormalizedProjectiveCoordinatesConsumer.lean \
  tests/Geometry/CorrectedNormalizedTangentLatticeConcreteOracle.lean \
  tests/GeneralTangentLimitAffineClosureConsumer.lean \
  tests/Geometry/ActualCenterParameterTransportConsumer.lean \
  tests/Geometry/ActualCommonOpenCompletionDerivationConsumer.lean \
  tests/Geometry/ActualWitnessSelectedChartBindingConsumer.lean \
  tests/Geometry/PrescribedCompletionInjectivityConsumer.lean \
  tests/ActualOptionGroundPointCompletionConsumer.lean \
  tests/FiniteTypeCurveHeightConsumer.lean; do
  lake env lean --trust=0 "$source" >> "$log" 2>&1
done
python3 - "$log" <<'PY'
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
expected = {
    'Stafford38.Geometry.ActualPointCommonOpenAssembly.pointLocalArc_unit_of_not_mem',
    'Stafford38.Geometry.ActualPointCommonOpenAssembly.exists_directSummandInput_of_selected_axis_lift',
    'Stafford38.Geometry.ActualSelectedNormalizationDivisorEtale.formallyEtale_at_selected_actual_normalization_center_core',
    'Stafford38.Geometry.ActualPointAxisLift.exists_actual_point_axis_lift',
    'Stafford38.Geometry.ActualSameWitnessDivisorNumerator.selected_basis_and_parameter_output',
    'corrected_velocity_span_example',
    'Stafford38.Geometry.CorrectedVelocitySpan.span_map_range_union_singleton_eq_of_corrected_velocity',
    'Stafford38.Geometry.CorrectedVelocitySpan.span_range_union_singleton_eq_of_corrected_velocity',
    'Stafford38.Geometry.SmoothLocalDirectSummandAdapter.exists_directSummandInput_of_tilted_local_axis_lift',
    'Stafford38.Geometry.SmoothLocalDirectSummandAdapter.directSummandInput_of_tiltedAxisLiftFields',
    'Stafford38.Geometry.GeneralConstantCoordinateAxis.coordinate_axis_mem_smooth_fibre_closure_of_coordinate_algebraic',
    'Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.originalAlgebraToPowerSeriesArc_coordinate',
    'Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.originalAlgebraToPowerSeries_coordinate',
    'Stafford38.Geometry.PrescribedGroundPointPowerSeriesMap.localToPowerSeries',
    'Stafford38.Geometry.PrescribedGroundPointPowerSeriesMapConsumer.twoCoordinateLinearCombination',
    'Stafford38.Geometry.AffinePointCompletion.powerSeriesCompletionAtPoint',
    'Stafford38.Geometry.FormallyEtaleCompletion.extendFormalSmoothLift',
    'Stafford38.Geometry.FormallyEtaleCompletion.exists_formalSmooth_lift_to_baseCompletion',
    'Stafford38.Geometry.AdicCompletionRingEquiv.ofRingEquiv',
    'Stafford38.Geometry.AdicCompletionMap.mapOfRingHom_comp',
    'Stafford38.Geometry.PaperDivisorTangent.projectiveTangentCone_eq_span_of_position_and_tangent',
    'Stafford38.Geometry.ActualWitnessStrictOrderGap.exists_actual_witness_strict_orderGap',
    'Stafford38.Geometry.ActualSelectedResidueBasisRowExclusion.witness_q1_residue_eq_zero',
    'Stafford38.Geometry.ActualSelectedResidueBasisRowExclusion.selected_basis_rows_avoid_zero_one_chart',
    'Stafford38.Geometry.ActualSelectedResidueBasisRowExclusion.transcendenceBasis_value_ne_zero',
    'Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_criterion_of_directSummand',
    'Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_criterion_of_directSummand_with_fibre_closure',
    'Stafford38.Geometry.GeneralTangentLimitCriterion.exists_axis_laurent_smooth_conormal_direction',
    'Stafford38.Geometry.GeneralTangentLimitCriterion.exists_axis_laurent_smooth_conormal_direction_with_fibre_closure',
    'Stafford38.Geometry.ProjectiveChartNormalizationBridge.componentChartEquationIdeal_map_eq_any',
    'Stafford38.Geometry.ProjectiveChartNormalizationBridge.componentChartClosedRingEquivAny',
    'Stafford38.Geometry.OptionCoordinateEtaleComposition.finitePresentation_of_finiteType_target',
    'Stafford38.Geometry.OptionCoordinateEtaleComposition.formallyEtale_of_optionCoordinate_generator_images',
    'Stafford38.Geometry.OptionCoordinateEtaleCompositionConsumer.selected_local_chart_formallyEtale',
    'Stafford38.Geometry.OptionCoordinateEtaleCompositionConsumer.polynomial_target_finitePresentation',
    'Stafford38.Geometry.FieldEquivFiniteType.finiteType_of_equiv_base',
    'Stafford38.Geometry.FieldEquivFiniteType.fractionField_map_coherence',
    'Stafford38.Geometry.FieldEquivFiniteType.exists_finiteType_domain_fractionField_localization',
    'Stafford38.Geometry.FieldEquivFiniteType.exists_finiteType_selected_localization',
    'Stafford38.Geometry.FieldEquivFiniteType.exists_fractionField_map_to_localization',
    'Stafford38.Geometry.FieldEquivFiniteType.exists_localized_fractionField_map',
    'Stafford38.Geometry.FieldEquivFiniteType.fractionField_of_equiv_domain',
    'Stafford38.Geometry.EtaleDerivationExtension.extendDerivation_algebraMap',
    'Stafford38.Geometry.EtaleDerivationExtension.extendDerivation',
    'Stafford38.Geometry.EtaleTangentChartSpan.tangentVector_eq_sum_parameterDerivations',
    'rational_affine_line_tangent_oracle',
    'Stafford38.Geometry.EtaleTangentChartSpan.zariskiTangentSpace_eq_span_parameterDerivations',
    'nonlinear_projective_derivation_oracle',
    'Stafford38.Geometry.ProjectiveConormalDehomogenization.dehomogenizedTangentColumn_derivation',
    'Stafford38.Geometry.LocalizationStageFractionCoefficients.fractionRingToAtPrime_polynomial_X_add_two',
    'Stafford38.Geometry.LocalizationStageFractionCoefficients.polynomial_fraction_field_stage_coefficients',
    'Stafford38.Geometry.LocalizationStageFractionCoefficients.polynomial_identity_parameter_oracle',
    'Stafford38.Geometry.EtaleGenericOpenTransport.formallyEtale_genericOpenRing_of_pointLocal',
    'Stafford38.Geometry.EtaleGenericOpenTransport.formallyEtale_genericOpenExtraAway_of_pointLocal',
    'Stafford38.Geometry.EtaleGenericOpenTransport.genericOpenExtraAwayEquiv_pointLocalAwayB',
    'ExtraAwayBNoRtoQOracle.no_algebra',
    'ExtraAwayBNoRtoQOracle.actual_B_only_instance',

    'Stafford38.Geometry.EtaleTangentKernel.mkDerivation_vanishes_of_mem_zariskiTangentSpace',
    'rankOne_literal_restricted_coordinate_ring_finite',
    'Stafford38CorollaryChallengeOwnerConsumer.phaseVar_alias',
    'Stafford38CorollaryChallengeOwnerConsumer.relation_alias',
    'Stafford38CorollaryChallengeOwnerConsumer.algebra_alias',
    'Stafford38CorollaryChallengeOwnerConsumer.rightTorsion_alias',
    'Stafford38CorollaryChallengeOwnerConsumer.cyclicity_statement_uses_canonical_owners',
    'rankOne_conormal_support_zero_momentum',
    'Stafford38CorollaryChallenge.torsionCyclicStatement_consumer',
    'Stafford38FixedSourceChallengeConsumer.unit_degree_intrinsic',
    'Stafford38FixedSourceChallengeConsumer.unit_degree',
    'Stafford38FixedSourceChallengeConsumer.coordinate_degree',
    'Stafford38FixedSourceChallengeConsumer.rank_one_unit_consumer',
    'Stafford38FixedSourceChallengeConsumer.rank_one_coordinate_consumer',
    'orePaperConsumer', 'exactDegreePaperConsumer', 'leftPaperConsumer',
    'evolutionConsumer', 'Stafford38.Evolution.tensorEvolutionaryCorollary',
    'actualLocalizedOperatorConsumer', 'actualPrincipalOpenConsumer',
    'actualPartialLaurentConsumer', 'actualRationalOperatorConsumer',
    'Stafford38.PaperEulerGrading.orderedPBWMonomial_eulerWeight',
    'Stafford38.PaperEulerGrading.pbwNonnegativeEulerPart_eq_transverseEulerSubring',
    'Stafford38.PaperEulerGrading.orderedPBWMonomial_positive_eulerFactor',
    'Stafford38.PaperEulerGrading.presentedCanonicalQuotient_rightMul_coordinate_surjective',
    'Stafford38.WeylQuotientTransport.presentedCanonicalRightQuotient_rightMul_coordinate_surjective',
    'Stafford38.Geometry.PaperHamiltonianFlow.paperHamiltonianFlow_preserves_commonZero',
    'Stafford38.Geometry.PaperHamiltonianFlow.paperHamiltonianFlows_preserve_commonZero',
    'Stafford38.Geometry.PaperHamiltonianFlow.affineConormal_coordinatePoint_isCommonZero',
    'Stafford38.LinearAlgebra.SymplecticComplement.pairComplementData',
    'Stafford38.PaperCyclicity.exists_span_singleton_eq_span_pair_via_matrix',
    'Stafford38.PaperCyclicity.paper_matrix_pair_spans',
    'Stafford38.PaperCyclicity.exists_common_right_annihilator_of_torsion',
    'Stafford38.PaperCyclicity.span_adjusted_pair_eq_span_pair_via_matrix',
    'Stafford38.PaperCyclicity.paper_torsion_module_is_cyclic',
    'Stafford38.TorsionCyclicity.weyl_isCyclic_of_isRightTorsion',
    'Stafford38.PaperQuotientDescent.canonicalRightQuotient_scalarExtension_equiv',
    'Stafford38.PaperQuotientDescent.canonicalRightQuotient_subsingleton_of_scalarExtension',
    'Stafford38.PaperQuotientDescent.canonicalSupport_empty_of_scalarExtension_empty',
    'Stafford38.PaperQuotientDescent.canonicalAssociatedGraded_annihilator_scalarExtension',
    'Stafford38.PaperQuotientDescent.canonicalSupportDescent_via_quotient',
    'Stafford38.FoundationClosure.canonicalSupportVanishingViaGeneralCoisotropic',
    'Stafford38.universalStatement',
    'Stafford38.LinearAlgebra.PairReplacement.matrix_pair_spans',
    'Stafford38.LinearAlgebra.PairReplacement.span_adjusted_pair_eq_span_pair',
    'Stafford38.LinearAlgebra.PairReplacement.finite_torsion_module_is_cyclic',
    'paperBasis_literal_plane_oracle',
    'rightMonic_degreeOne_literal_oracle',
    'generic_first_coefficient_reads_linear_term',
    'arcVelocity_reads_linear_term',
    'projectiveFirstJet_reads_linear_term',
    'first_coefficient_is_derivative_at_constant_term',
    'Stafford38.Geometry.PowerSeriesArcTangency.arcVelocity_eq_constantCoeff_derivative',
    'arcVelocity_uses_canonical_first_coefficient',
    'projectiveFirstJet_uses_canonical_first_coefficient',
    'reduction_predicate_keeps_exact_certificate',
    'challenge_uses_canonical_predicate',
    'challenge_keeps_original_operator_order',
    'old_reduction_api_still_targets_canonical_predicate',
    'projectiveChart_zero_literal_oracle',
    'projectiveChart_middle_literal_oracle',
    'projectiveChart_middle_ideal_literal_oracle',
    'Stafford38.Geometry.ProjectiveChartCoordinates.eval_eq_zero_of_mem_dehomogenizedEquationIdeal',
    'Stafford38.Geometry.ProjectiveChartCoordinates.eval_dehomogenizeProjectiveChart',
    'Stafford38.Geometry.ProjectiveChartCoordinates.insertProjectiveChart_zero',
    'Stafford38.Geometry.ProjectiveChartCoordinates.insertProjectiveChart_zero_transport',
    'Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero',
    'Stafford38.Geometry.ProjectiveChartCoordinates.dehomogenizeProjectiveChart_zero_transport',
    'Stafford38.Geometry.PaperCompletedResidueDerivationFrame.exists_completed_derivation_frame_of_residue_coordinates',
    'Stafford38.Geometry.PaperCompletedResidueDerivationFrame.exists_projective_derivation_frame_of_residue_coordinates',
    'Stafford38.Geometry.PaperRetainedChartAssembly.exists_retained_projective_derivation_columns',
    'Stafford38.Geometry.PaperRetainedChartAssembly.component_equations_vanish_after_point_transport',
    'Stafford38.Geometry.PaperRetainedChartAssembly.component_generic_kernel_after_point_transport',
    'Stafford38.Geometry.ProjectiveDVRCenter.dvr_eq_of_dominated_by_valuationSubring',
    'dvr_center_consumer',
    'generic_chart_tangent_literal_oracle',
    'arbitrary_chart_tangent_literal_oracle',
    'zero_chart_tangent_literal_oracle',
    'zero_chart_second_coordinate_literal_oracle',
    'chart_one_quotient_difference_literal_oracle',
    'chart_zero_quotient_difference_literal_oracle',
    'Stafford38.Geometry.GeneralDivisorialVisibleFrame.generalDivisorialVisibleFrameWithResidueAlgebraicity',
    'Stafford38.Geometry.GeneralDivisorialVisibleFrame.generalDivisorialVisibleFrameExistence',
    'Stafford38.Geometry.GeneralDivisorialVisibleFrame.witness_q0_residue_consumer',
    'Stafford38.Geometry.GeneralDivisorialVisibleFrame.witness_retained_halg_consumer',
    'Stafford38.Geometry.PaperSameWitnessTangentDimension.tangent_finrank_le_residue_add_one_of_witness',
    'Stafford38.Geometry.GeneralConormalAxis.exists_groundConormalAxis_of_minimalPrime_unit_transcendental',
    'paper_actual_axis_literal_consumer',
    'Stafford38.Geometry.PaperRetainedChartWitnessColumns.columns_of_visible_witness',
    'Stafford38.Geometry.PaperActualDivisorTangent.exists_regularizedOneRowConormalData_of_actual_columns',
    'Stafford38.Geometry.PaperActualWitnessConormalData.exists_regularizedOneRowConormalData_of_actual_witness',
    'Stafford38.Tests.ProjectiveDivisorChartBridgeConsumer.chart_membership_iff_generic_ratio_evaluation',
    'Stafford38.Tests.ProjectiveDivisorChartBridgeConsumer.maximal_height_bound_from_polynomial_normalization',
    'Stafford38.Geometry.ResidueBasisLocalization.finiteType_fractionField_localization',
    'Stafford38.Geometry.ResidueBasisLocalization.fractionField_localization_isDomain',
    'Stafford38.Geometry.ResidueBasisLocalization.ker_isMaximal_of_algebraic_residue',
    'rational_evaluation_kernel',
    'Stafford38.Geometry.ActualSelectedResidueBasis.exists_selected_residue_basis_indices',
    'Stafford38.Geometry.ActualSelectedResidueBasis.exists_actual_selected_residue_basis',
    'Stafford38.Geometry.SelectedResidueCoefficientLocalization.selected_lifts_algebraicallyIndependent',
    'Stafford38.Geometry.SelectedResidueCoefficientLocalization.selectedCoefficientResidueMap_injective',
    'Stafford38.Geometry.SelectedResidueCoefficientLocalization.exists_selected_fraction_field_maps',
    'Stafford38.Geometry.SelectedResidueCoefficientLocalization.exists_localization_map_of_residue_injective',
    'Stafford38.Geometry.SelectedResidueCoefficientLocalization.exists_chart_normalization_localization_map',
    'Stafford38.Geometry.PrescribedEtaleGroundPointConsumer.polynomial_zero_point_oracle',
    'Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer.selected_index_localization',
    'Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer.selected_index_formally_etale',
    'Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer.distinguished_parameter_image',
    'Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer.selected_coefficient_image',
    'Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer.none_is_not_a_denominator',
    'Stafford38.Geometry.ProjectiveCoefficientLocalizationGenericConsumer.legacy_fin_formally_etale',
    'Stafford38.Geometry.PrescribedEtaleGroundPoint.formallyEtale_atPrime_of_away',
    'Stafford38.Geometry.PrescribedEtaleGroundPoint.exists_standardEtale_neighborhood_and_formallyEtale_ground_point',
    'Stafford38.Geometry.PrescribedEtaleGroundPoint.exists_standardEtale_neighborhood_and_formallyEtale_ground_point_avoiding',
    'Stafford38.Geometry.MvPolynomialFractionFieldGenericConsumer.tail_variables_are_a_basis',
    'Stafford38.Geometry.MvPolynomialFractionFieldGenericConsumer.tail_fraction_field_has_finite_trdeg',
    'Stafford38.Geometry.MvPolynomialFractionFieldGenericConsumer.tail_fraction_field_variables_algebraic_extension',
    'Stafford38.Geometry.EtaleCotangentBasis.basisOfFormallyEtale',
    'Stafford38.Geometry.EtaleCotangentBasis.basisOfFormallyEtale_apply',
    'Stafford38.Geometry.EtaleCotangentBasis.basisAfterPoint',
    'Stafford38.Geometry.EtaleCotangentBasis.basisAfterPoint_apply',
    'Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation',
    'Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation_apply_parameter',
    'Stafford38.Geometry.EtaleCotangentBasis.derivationFromValues_apply_parameter',
    'Stafford38.Geometry.EtaleCotangentBasis.derivation_eq_from_parameter_values',
    'Stafford38.Geometry.EtaleCotangentBasis.derivation_eq_sum_coordinateDerivations',
    'Stafford38.Geometry.EtaleTangentKernel.derivation_eq_sum_pderiv',
    'Stafford38.Geometry.EtaleTangentKernel.derivationVector_mem_zariskiTangentSpace_of_vanishes',
    'Stafford38.Geometry.EtaleTangentKernel.chartDerivation_mem_zariskiTangentSpace',
    'retained_chart_map_kernel_exact',
    'chart_function_field_element_is_quotient_of_chart_classes',
    'chart_normalization_finite_type_over_ground',
    'projective_normalization_finite_consumer',
    'Stafford38.Geometry.ProjectiveChartNormalizationCenter.integralClosureCenter_ne_bot_of_nonzero_maximal',
    'Stafford38.Geometry.ProjectiveChartNormalizationCenter.localRing_at_integralClosureCenter_le_valuationSubring',
    'Stafford38.Geometry.ProjectiveChartNormalizationFinite.finite_integralClosure_in_fractionField',
    'normalization_center_nonzero_consumer',
    'normalization_center_prime_consumer',
    'normalization_center_residue_kernel_consumer',
    'normalization_center_domination_consumer',
    'Stafford38.Geometry.localRing_at_contracted_maximalIdeal_le_valuationSubring',
    'Stafford38.Geometry.TiltedArcAvoidanceConsumer.zero_tilt_coefficient_one_oracle',
    'Stafford38.Geometry.TiltedArcAvoidance.exists_eval_ne_zero',
    'Stafford38.Geometry.TiltedArcAvoidance.exists_eval_ne_zero_first_one',
    'Stafford38.Geometry.TiltedArcAvoidance.exists_tilt_subst_ne_zero',
    'literal_tilted_lift_reads_returned_conormal',
    'Stafford38.Geometry.FormallyEtaleCompletionEquivalenceConsumer.identityCompletionEquiv',
    'Stafford38.Geometry.kaehlerDifferentialBasisOfTranscendenceBasis',
    'Stafford38.Geometry.kaehlerFinrankOfTranscendenceBasis',
    'Stafford38.Geometry.kaehlerFiniteOfTranscendenceBasis',
    'Stafford38.Geometry.SameWitnessTranscendenceDegreeBound.component_trdeg_le_residue_trdeg_add_one_of_witness',
    'Stafford38.Geometry.DVRParameterSmoothness.isEtaleAt_of_polynomial_uniformizer_of_maximal',
    'Stafford38.Geometry.DVRUniformizerNumerator.exists_numerator_of_dvr_localization',
    'Stafford38.Geometry.PaperUnitPowerFactorization.exists_common_away_unit_power_factorizations',
    'Stafford38.Geometry.PaperUnitPowerFactorizationConsumer.concrete_common_open_factorization',
    'Stafford38.Geometry.PaperUnitPowerFactorizationConsumer.explicit_common_open_oracle',
    'Stafford38.Geometry.ProjectiveCoefficientLocalization.fractionCoordinateMap_isLocalization',
    'Stafford38.Geometry.ProjectiveCoefficientLocalization.fractionCoordinateMap_formallyEtale',
    'Stafford38.Geometry.ActualChartValuationImage.chartGenericPointSubalgebra_le_valuationSubring',
    'Stafford38.Geometry.ActualChartCenterNonzero.actual_chart_normalization_center_ne_bot',
    'actual_chart_normalization_is_away_equiv',
    'Stafford38.Geometry.SameWitnessRelativeTranscendenceDegreeConsumer.finiteBasisLocalParameterConsumer',
    'Stafford38.Geometry.MvPolynomialFractionFieldBasisConsumer.canonicalFractionFieldBasis',
    'Stafford38.Geometry.MvPolynomialFractionFieldBasisConsumer.canonicalFractionFieldFiniteTrdeg',
    'Stafford38.Geometry.UnitPowerNonzeroPrimeOracle.nonzero_prime_common_open',
    'Stafford38.Geometry.CoefficientRegularityOracle.constants_two_three_multiply_zero',
    'Stafford38.Geometry.CoefficientRegularityOracle.constant_three_nonzero',
    'Stafford38.Geometry.CoefficientRegularityOracle.constant_two_not_regular',
    'Stafford38.Geometry.FiniteTypeCurveHeightConsumer.polynomial_maximal_height_le_one',
    'Stafford38.Geometry.FiniteTypeCurveHeightConsumer.polynomial_localized_maximal_center_height_eq_one',
    'original_affine_open_survives_homogenization',
    'original_affine_open_survives_laurent_arc',
    'rational_homogenized_coordinate_oracle',
    'Stafford38.Geometry.HomogenizedAffineEvaluation.map_homogenizeAtZero',
    'Stafford38.Geometry.SmoothAffinePointScalarExtensionConsumer.original_arc_point_avoiding_open_is_smooth',
    'Stafford38.Geometry.SmoothAffinePointScalarExtensionConsumer.rationalArcField_point_is_smooth',
    'Stafford38.Geometry.SmoothAffinePointScalarExtension.exists_generic_smooth_open_point_criterion',
    'Stafford38.Geometry.PrescribedGroundPointUnitPowerConsumer.x2_x3_have_prescribed_ground_chart',
    'Stafford38.Geometry.SelectedCorrectionConsumer.constant_correction_preserves_explicit_orders',
    'Stafford38.GeometryFormalDivisorTangent.exists_primitive_formalDivisorTangent_of_selected_correction',
    'Stafford38.GeometryFormalDivisorTangent.exists_formalDivisorTangent_residue_injective_of_selected_correction',
    'Stafford38.GeometryFormalDivisorAxisLift.exists_formalDivisorAxisLift_of_selected_correction',
    'Stafford38.Geometry.ActualSmoothOpenChartNumerator.exists_nonzero_homogenized_numerator',
    'Stafford38.Geometry.ActualChartValuationImage.normalizedCoordinate_mem_chartGenericPointSubalgebra',
    'Stafford38.Geometry.ActualChartValuationImage.exists_actual_normalizedProjectiveColumn',
    'Stafford38.Geometry.SelectedResidueCoefficientLocalization.chartSubalgebraToIntegralClosure',
    'Stafford38.Geometry.ActualSmoothOpenChartNumerator.exists_actual_normalizedProjectiveColumn_in_integralClosure',
    'Stafford38.Geometry.LocalizationInStagesAtPrime.polynomial_fraction_field_stage_point',
    'Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.tilted_local_axis_lift_of_selected_coordinate_rows_on_arc',
    'Stafford38.Geometry.SmoothLocalTiltedArcAxisLift.exists_tilted_local_axis_lift_of_selected_coordinate_rows',

    'rational_projective_tangent_cone_oracle',
    'Stafford38.Geometry.EtaleProjectiveTangentComparison.projectiveTangentCone_eq_span_chartDerivation_columns',
    'Stafford38.Geometry.ProjectiveChartSameFieldOverlapConsumer.original_coordinate_action',
    'Stafford38.Geometry.ProjectiveChartSameFieldOverlapConsumer.reverse_coordinate_action',
    'Stafford38.Geometry.ProjectiveChartSameFieldOverlapConsumer.common_function_field_action',
    'actual_prescribed_completion_commutes_with_every_parameter_derivation',
    'actual_option_completion_commutes_with_reindexed_derivation',
    'actual_option_nonlinear_rational_completion_derivative_oracle',
    'actual_tilted_arc_derivative_is_full_parameter_direction',
    'actual_tilted_arc_derivative_lands_in_canonical_laurent_field',
    'actual_nonlinear_rational_element_derivative_oracle',
    'Stafford38.Geometry.ActualOptionColumnBinding.exists_actual_option_coordinate_map',
    'Stafford38.Geometry.ActualOptionColumnBinding.actual_normalized_column_map_eq_retained',
    'Stafford38.Geometry.ActualOptionColumnBinding.retained_frame_coordinate_orders',
    'Stafford38.Geometry.ActualDivisorUniformizerNumerator.exists_numerator_with_two_unit_power_factorizations',
    'Stafford38.Geometry.A0ChartFormalEtale.formallyEtale_originalAffineChartToCommonOpen',
    'Stafford38.Geometry.LocalNormalizationCenterEquivalence.exists_localization_equiv_of_height_one',
    'Stafford38.Geometry.GenericFibreMatrixColumnsConsumer.rational_one_mem_generic_fibre',
    'Stafford38.Geometry.GenericFibreMatrixColumnsConsumer.columns_identify_same_generic_fibre',
    'Stafford38.Geometry.GeneralTangentLimitCriterion.genericFibre_eq_span_matrixColumns',
    'Stafford38.Geometry.ActualResidueCenterHeight.height_one_of_localized_algebraic_residue',
    'Stafford38.Geometry.ActualChartResidueMapCoherence.residue_map_coherence',
    'Stafford38.Geometry.ActualNormalizationCenterResidueKernel.residue_kernel_eq_canonical_center_comap',
    'Stafford38.Geometry.ActualChartNormalizationCenter.actual_chart_normalization_center_height_one_of_basis',
    'Stafford38.Geometry.ActualChartNormalizationCenter.actual_chart_normalization_center_height_one_of_selected_basis',
    'Stafford38.Geometry.ActualChartNormalizationCenter.subalgebraToSubringRingEquiv',
    'Stafford38.Geometry.ActualDivisorUniformizerNumerator.exists_numerator_with_two_unit_power_factorizations_and_span',
    'Stafford38.Geometry.ActualNormalizationDivisorEtale.formallyEtale_at_actual_normalization_center_of_specified_parameter',
    'Stafford38.Geometry.ActualNormalizationDivisorEtale.formallyEtale_at_actual_normalization_center',
    'Stafford38.Geometry.ActualOptionCoordinateEtaleConsumer.actual_map_formallyEtale',
    'Stafford38.Geometry.ActualOptionCoordinateEtaleConsumer.mixed_coordinate_behavior',
    'Stafford38.Geometry.A0NormalizedProjectiveCoordinatesConsumer.canonical_chart_coordinate_consumer',
    'Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle.powerSeriesX_not_unit',
    'Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle.tau_has_explicit_raw_span_coefficients',
    'Stafford38.Geometry.CorrectedNormalizedTangentLattice.ConcreteOracle.example_generic_fibre_identity',
    'Stafford38.Geometry.ActualCenterParameterTransport.atPrimeEquiv',
    'Stafford38.Geometry.ActualCenterParameterTransport.span_transport_across_ring_equiv',
    'Stafford38.Geometry.ActualCenterParameterTransport.transport_parameter_and_two_orders',
    'Stafford38.Geometry.GeneralTangentLimitCriterion.tangent_limit_affine_fibre_closure_of_directSummand',
    'GeneralTangentLimitAffineClosureConsumer.eval_eq_zero_of_directSummand_affine_closure',
    'Stafford38.Geometry.ActualCommonOpenCompletionDerivationConsumer.originalParameter_derivation_bridge',
    'Stafford38.Geometry.ActualCommonOpenCompletionDerivationConsumer.canonicalLaurentArc_preserves_ground',
    'Stafford38.Geometry.ActualWitnessSelectedChartBindingConsumer.actual_retained_witness_projective_relation',
    'Stafford38.Geometry.DefinitionOwnerRepairConsumer.chartMap_generator',
    'Stafford38.Geometry.DefinitionOwnerRepairConsumer.chartMap_unique',
    'Stafford38.Geometry.DefinitionOwnerRepairConsumer.reduction_ad_formula',
    'FiniteParameterTangentConsumer.optionChart_generates_actualCone',
    'FiniteParameterTangentConsumer.oneParameter_span',
    'literal_option_normalized_projective_cone_oracle',
    'Stafford38.Geometry.ActualCommonOpenColumnGlueConsumer.literal_unit_column',
    'Stafford38.Geometry.ActualWitnessCommonOpenColumnGlue.actual_witness_commonOpen_eq_pointLocal',
    'Stafford38.Geometry.ActualWitnessSelectedChartIndex.exists_succ_chart_index',
    'Stafford38.Geometry.ActualSameWitnessDivisorNumerator.exists_actual_parameter_with_retained_orders',
    'Stafford38.Geometry.ActualSameWitnessGroundPointCompletion.exists_actual_same_witness_groundpoint_chart',
    'Stafford38.Geometry.SameWitness.AffineFibreClosureConsumer.axis_in_original_affine_conormal_fibre_closure',
    'Stafford38.Geometry.SameWitness.axis_mem_smoothConormalFibreProjection_closure_of_groundPointOutput',
    'Stafford38IndependentOriginalPrimeConsumer.original_prime_coordinate_avoidance_affine_endpoint',
    'Stafford38.Geometry.SameWitness.coordinate_axis_mem_smooth_fibre_closure',
    'Stafford38IndependentOriginalPrimeConsumer.original_prime_coordinate_avoidance_projective_endpoint',
    'Stafford38.Geometry.EtaleCotangentBasis.coordinateDerivation_algebraMap',
    'Stafford38.Geometry.ActualCommonOpenArcCompatibility.genericArcToExtraAway_comp_commonOpenMap',
    'Stafford38.Geometry.ActualCommonOpenArcCompatibility.pointArc_factors_ne_zero_of_tiltedProduct',
    'Stafford38.Geometry.ActualCommonOpenArcCompatibility.commonOpen_factors_ne_zero_of_tiltedProduct',
    'actual_numerator_survives_common_open',
    'Stafford38.Geometry.DirectSummandInputOfActualChart.directSummandInput_of_actual_chart_columns',
    'PrescribedCompletionInjectivityConsumer.source_nonzero',
    'Stafford38.Geometry.ActualOptionGroundPointCompletion.exists_groundPoint_chart_from_option_map',
    'PrescribedCompletionInjectivityConsumer.parameter_linear_coefficient',
}
reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S))
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    reports[name] = ''
if expected - reports.keys():
    raise SystemExit(f'Missing independent consumers: {expected - reports.keys()}')
for name in expected:
    axioms = {x.strip() for x in reports[name].split(',') if x.strip()}
    if axioms - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit(f'Forbidden consumer axioms: {name}: {axioms}')
if re.search(r'sorryAx|admitAx|Lean\.ofReduceBool|declaration uses .sorry|(^|:) error(\([^)]*\))?:', text):
    raise SystemExit('Forbidden proof mechanism or Lean error in consumer output')
print(f'Literal consumers and import/axiom audits: {len(expected)} reports passed')
PY
