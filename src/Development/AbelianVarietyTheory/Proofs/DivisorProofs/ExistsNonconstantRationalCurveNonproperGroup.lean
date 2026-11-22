module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfiniteTorsionOrCocharacterOfArcAtInfinity
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS.ArcInf
variable {k : Type} [Field k] [IsAlgClosed k]

end GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

section Curve
variable {k : Type} [Field k]

variable [Infinite k] {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A]
  {j : algOver k A ⟶ G} {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A}

end Curve
end GlobalTheory.RatCurve

namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

end GlobalTheory.RatCurve
