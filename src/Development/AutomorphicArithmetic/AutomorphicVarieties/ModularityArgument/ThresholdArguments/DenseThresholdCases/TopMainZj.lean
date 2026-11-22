import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideExtra
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPow
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvr
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.IntegralSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvr
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeDescentUnramified
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TemperedProductOfSquareIntegrable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.Published
theorem UpperTheory.One.Join.local_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt where
  bz := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_open O)
  bern := (_root_.UpperTheory.LiteratureTheorems.bernstein_unitary_product_irreducible_of_open O)
  geo := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_geometric_of_open O)
  zel := (_root_.UpperTheory.LiteratureTheorems.zelevinsky_polynomial_ring_of_open O)
  disj := (_root_.UpperTheory.LiteratureTheorems.totally_disjoint_product_irreducible_of_open O)
  mp := (_root_.UpperTheory.LiteratureTheorems.moy_prasad_jacquet_iso_of_open O)
  temp := (_root_.UpperTheory.LiteratureTheorems.tempered_product_of_square_integrable_of_open O)
  seg := (_root_.UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_open O)
  sq := (_root_.UpperTheory.LiteratureTheorems.square_integrable_segment_of_open O)
  gen := (_root_.UpperTheory.LiteratureTheorems.generic_unlinked_gl_of_open O)
  multi := (_root_.UpperTheory.LiteratureTheorems.langlands_multisegments_of_open O)
  exh := (_root_.UpperTheory.LiteratureTheorems.langlands_exhaustion_gl_of_open O)
  cos := (_root_.UpperTheory.LiteratureTheorems.standard_cosocle_gl_of_open O)
  conv := (_root_.UpperTheory.LiteratureTheorems.local_converse_gl_of_open O)
  dzi := (_root_.UpperTheory.LiteratureTheorems.depth_zero_induction_of_open O)
  brauer := (_root_.UpperTheory.LiteratureTheorems.brauer_degree_zero_of_open O)
  chev := (_root_.UpperTheory.LiteratureTheorems.chevalley_units_of_open O)
  green := (_root_.UpperTheory.LiteratureTheorems.green_regular_characters_of_open O)
theorem UpperTheory.One.Join.automorphic_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN)
    (gal : _root_.UpperTheory.V.Z.Win.RowT) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis where
  decay := (_root_.UpperTheory.LiteratureTheorems.cusp_rapid_decay_of_open O)
  hc := (_root_.UpperTheory.LiteratureTheorems.harish_chandra_finite_of_open O)
  fin := (_root_.UpperTheory.LiteratureTheorems.automorphic_forms_finite_gl_of_open O)
  js := (_root_.UpperTheory.LiteratureTheorems.jacquet_shalika_of_open O)
  cusp := (_root_.UpperTheory.LiteratureTheorems.cuspidal_spectrum_gl_of_open O)
  bc := bc
  gk := (_root_.UpperTheory.LiteratureTheorems.gelfand_kazhdan_dual_of_open O)
  gal := gal
  pur := (_root_.UpperTheory.LiteratureTheorems.clozel_purity_of_open O)
  coh := (_root_.UpperTheory.LiteratureTheorems.clozel_cohomological_of_open O)
  art := (_root_.UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_open O)
  ray := (_root_.UpperTheory.LiteratureTheorems.ray_class_field_st_of_open O)
  chA := (_root_.UpperTheory.LiteratureTheorems.hecke_ladic_character_above_of_open O)
  chW := (_root_.UpperTheory.LiteratureTheorems.algebraic_character_wd_of_open O)
  berger := (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_open O)
theorem UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition)
 (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (gal : _root_.UpperTheory.V.Z.Win.RowT) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis) :
    UpperTheory.Top.VWin :=
  _root_.UpperTheory.V.v_window_of_literal_automorphy_n ⟨_root_.UpperTheory.One.Join.local_inputs_from_literature O, _root_.UpperTheory.One.Join.automorphic_inputs_from_literature O bc gal, _root_.UpperTheory.LiteratureTheorems.galois_cohomology_from_literature O, cm⟩
theorem UpperTheory.One.Join.cm_abelian_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis where
  gm := (_root_.UpperTheory.LiteratureTheorems.grothendieck_deformation_of_open O)
  dr := (_root_.UpperTheory.LiteratureTheorems.abelian_de_rham_of_open O)
  dual := (GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift (_root_.UpperTheory.LiteratureTheorems.dual_abelian_scheme_of_open O) (GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations))
  per := (GlobalTheory.PeriodFamily.periodComparison_holds)
  gmp := (GlobalTheory.GaussManinTop.main)
  cm := (_root_.UpperTheory.LiteratureTheorems.elliptic_main_theorem_cm_of_open O)
  hj := (_root_.UpperTheory.LiteratureTheorems.hilbert_class_field_j_of_open O)
  dri := (_root_.UpperTheory.LiteratureTheorems.siegel_klingen_deligne_ribet_of_open O)
  pz := (_root_.UpperTheory.LiteratureTheorems.partial_zeta_functional_equation_of_open O)
  fe := (_root_.UpperTheory.LiteratureTheorems.hecke_tate_functional_equation_of_open O)
theorem UpperTheory.One.Join.automorphic_window_of_inputs (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition)
 (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (gal : _root_.UpperTheory.V.Z.Win.RowT) :
    UpperTheory.Top.VWin :=
  _root_.UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm O bc gal (_root_.UpperTheory.One.Join.cm_abelian_inputs_from_literature O)
end
