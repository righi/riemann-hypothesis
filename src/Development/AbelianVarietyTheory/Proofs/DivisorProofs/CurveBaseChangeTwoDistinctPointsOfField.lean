import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CurveBaseChange

variable {R F : Type} [CommRing R] [Field F] (ψ : R →+* F) (P₁ : Polynomial R)

theorem eval_map_apply' (a : R) (p : Polynomial R) : (p.map ψ).eval (ψ a) = ψ (p.eval a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

end GlobalTheory.CurveBaseChange

namespace GlobalTheory

end GlobalTheory
