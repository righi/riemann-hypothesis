module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveSpMapOfDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFractionFieldIsPullbackOfUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodDescW
set_option autoImplicit false

section Sq2
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}

end Sq2

section Sq
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

end Sq

end GlobalTheory.GoodDescW
