module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsosStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

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
