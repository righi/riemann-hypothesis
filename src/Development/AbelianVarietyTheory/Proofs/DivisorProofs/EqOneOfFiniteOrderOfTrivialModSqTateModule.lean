module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.MinkowskiTate

section Lemmas

variable {l : ℕ} {M : Type} [CommGroup M]

end Lemmas

end GlobalTheory.MinkowskiTate

namespace GlobalTheory.MinkowskiTate

section Endo

variable {l : ℕ} [Fact l.Prime] {M : Type} [CommGroup M]

end Endo

end GlobalTheory.MinkowskiTate
