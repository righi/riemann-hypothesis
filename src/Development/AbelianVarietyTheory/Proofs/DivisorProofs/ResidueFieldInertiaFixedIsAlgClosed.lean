import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaRes

theorem coe_toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (r : R) :
    ((toV R K Ω V hV r : V) : Ω) = algebraMap K Ω (algebraMap R K r) := rfl

open Polynomial

end GlobalTheory.InertiaRes
