import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.MinkowskiTate

section Lemmas

variable {l : ℕ} {M : Type} [CommGroup M]

theorem lev_neg (t : Tate l M) (m : ℕ) : (-t).lev m = (t.lev m)⁻¹ := rfl

end Lemmas

end GlobalTheory.MinkowskiTate

namespace GlobalTheory.MinkowskiTate

end GlobalTheory.MinkowskiTate

