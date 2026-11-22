module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsosStatement

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoConst

theorem lbIso_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left), P.IsLB → M.IsLB → LBIso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) → LBIso P M := by
  intro W K' _ _ _ _ _ _ G _ hG P M hP hM h
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom inferInstance inferInstance
  let ψ : K' ≃ₐ[W] FractionRing W := IsLocalization.algEquiv (nonZeroDivisors W) K' (FractionRing W)
  have e₂ : Out.jK W ≫ 𝟙 _ = spMap (ψ : K' →+* FractionRing W) ≫ spMap (algebraMap W K') := by
    have hr : (ψ : K' →+* FractionRing W).comp (algebraMap W K') = algebraMap W (FractionRing W) := by
      ext x; simp
    rw [Category.comp_id, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  have h' : LBIso (P.pull (pullback.fst G.hom (Out.jK W))) (M.pull (pullback.fst G.hom (Out.jK W))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp
      (pullback.map G.hom (Out.jK W) G.hom (spMap (algebraMap W K')) (𝟙 _) (spMap (ψ : K' →+* FractionRing W)) (𝟙 _)
        (by simp) e₂) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm h
  exact GlobalTheory.lbIso_of_generic_normal_local W inferInstance inferInstance G.left G.hom (eSec G) inferInstance inferInstance
    inferInstance (Over.w η[G]) P M hP hM h'


end GlobalTheory.GenericIsoConst
